#include <math.h>
#include <stdlib.h>

#include <flint/flint.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpz_mod_poly.h>

#include "flint_util.h"

#include "common.h"
#include "test.h"
#include "bench.h"
#include <assert.h>
#include "blake3.h"

#define ETA         325
#define R           (HEIGHT+2)
#define V           (WIDTH+3)
/* Number of relations proven at once. This drives every large buffer below, so
 * it can be overridden (e.g. make CONFIG=-DTAU=16) to test on a small machine.
 * It must be a power of two: the interpolation nodes are the TAU-th roots of
 * unity, which is what makes l_0 equal X^TAU - 1 and evaluation at the nodes a
 * length-TAU NTT. The paper's 1000 relations are padded to 1024 with zero
 * witnesses, which costs nothing in soundness. */
#ifndef TAU
#define TAU         1024
#endif

/* --- GR(q,2), the challenge domain ---------------------------------------
 * q is a product of two 39-bit primes, so a challenge drawn from Z_q is only
 * worth deg/p_min: an adversary can make the identity vanish modulo one prime
 * and gamble on the other alone. Drawing it from the quadratic Galois
 * extension Z_q[Y]/(Y^2 - AEX_NR) restores deg/p_min^2, because AEX_NR is a
 * non-residue modulo both primes and so Y^2 - AEX_NR stays irreducible in each
 * CRT component. An element is a0 + a1 Y.
 *
 * 3 is the smallest usable constant, and the RNS basis is picked for it: the
 * NTT needs p = 1 mod 2^21, which forces p = 1 mod 8 and so makes both -1 and
 * 2 squares modulo every candidate prime, leaving Y^2+1 and Y^2-2 reducible.
 * Every modulus in the basis is 2 mod 3, which is what makes 3 a non-residue;
 * the test at the bottom of this file checks that rather than assuming it.
 * Being 3, multiplying by it is two modular additions instead of a multiply
 * and a reduction. */
#define AEX_NR      3

/* r <- AEX_NR * a, by addition. Must double into a temporary: gr_inv calls
 * this in place, and accumulating into r would square the doubling and give
 * 4a instead of 3a. */
static void gr_mul_nr(fmpz_t r, const fmpz_t a, const fmpz_mod_ctx_t ctx) {
	fmpz_t d;

	fmpz_init(d);
	fmpz_mod_add(d, a, a, ctx);
	fmpz_mod_add(r, d, a, ctx);
	fmpz_clear(d);
}

typedef struct {
	fmpz_t c0, c1;
} gr_t;

static void gr_init(gr_t & a) { fmpz_init(a.c0); fmpz_init(a.c1); }
static void gr_clear(gr_t & a) { fmpz_clear(a.c0); fmpz_clear(a.c1); }
static void gr_one(gr_t & a) { fmpz_one(a.c0); fmpz_zero(a.c1); }

static void gr_set(gr_t & r, const gr_t & a) {
	fmpz_set(r.c0, a.c0);
	fmpz_set(r.c1, a.c1);
}

static void gr_add(gr_t & r, const gr_t & a, const gr_t & b,
		const fmpz_mod_ctx_t ctx) {
	fmpz_mod_add(r.c0, a.c0, b.c0, ctx);
	fmpz_mod_add(r.c1, a.c1, b.c1, ctx);
}

static void gr_sub(gr_t & r, const gr_t & a, const gr_t & b,
		const fmpz_mod_ctx_t ctx) {
	fmpz_mod_sub(r.c0, a.c0, b.c0, ctx);
	fmpz_mod_sub(r.c1, a.c1, b.c1, ctx);
}

/* (a0 + a1 Y)(b0 + b1 Y) = (a0 b0 + NR a1 b1) + (a0 b1 + a1 b0) Y, by
 * Karatsuba so three Z_q multiplies instead of four. Safe to alias. */
static void gr_mul(gr_t & r, const gr_t & a, const gr_t & b,
		const fmpz_mod_ctx_t ctx) {
	fmpz_t m0, m1, m2, t;

	fmpz_init(m0); fmpz_init(m1); fmpz_init(m2); fmpz_init(t);
	fmpz_mod_mul(m0, a.c0, b.c0, ctx);
	fmpz_mod_mul(m1, a.c1, b.c1, ctx);
	fmpz_mod_add(m2, a.c0, a.c1, ctx);
	fmpz_mod_add(t, b.c0, b.c1, ctx);
	fmpz_mod_mul(m2, m2, t, ctx);
	fmpz_mod_sub(m2, m2, m0, ctx);
	fmpz_mod_sub(m2, m2, m1, ctx);
	gr_mul_nr(t, m1, ctx);
	fmpz_mod_add(r.c0, m0, t, ctx);
	fmpz_set(r.c1, m2);
	fmpz_clear(m0); fmpz_clear(m1); fmpz_clear(m2); fmpz_clear(t);
}

/* GR times a plain Z_q scalar: two multiplies, not three. This is the common
 * case, since every witness stays in Z_q and only the challenge is extended. */
static void gr_scalar(gr_t & r, const gr_t & a, const fmpz_t s,
		const fmpz_mod_ctx_t ctx) {
	fmpz_mod_mul(r.c0, a.c0, s, ctx);
	fmpz_mod_mul(r.c1, a.c1, s, ctx);
}

/* (a0 + a1 Y)^-1 = (a0 - a1 Y)/(a0^2 - NR a1^2). The norm is non-invertible
 * exactly when a is a zero divisor, which for a challenge-derived value has
 * probability about deg/p_min^2; report it instead of letting FLINT abort
 * inside fmpz_mod_inv, and let the caller reject. */
static int gr_inv(gr_t & r, const gr_t & a, const fmpz_mod_ctx_t ctx) {
	fmpz_t n, t, g;
	int ok;

	fmpz_init(n); fmpz_init(t); fmpz_init(g);
	fmpz_mod_mul(n, a.c0, a.c0, ctx);
	fmpz_mod_mul(t, a.c1, a.c1, ctx);
	gr_mul_nr(t, t, ctx);
	fmpz_mod_sub(n, n, t, ctx);
	ok = fmpz_invmod(g, n, fmpz_mod_ctx_modulus(ctx));
	if (ok) {
		fmpz_mod_neg(t, a.c1, ctx);
		fmpz_mod_mul(t, t, g, ctx);
		fmpz_mod_mul(r.c0, a.c0, g, ctx);
		fmpz_set(r.c1, t);
	}
	fmpz_clear(n); fmpz_clear(t); fmpz_clear(g);
	return ok;
}

static void gr_pow_ui(gr_t & r, const gr_t & a, ulong e,
		const fmpz_mod_ctx_t ctx) {
	gr_t base, acc;

	gr_init(base); gr_init(acc);
	gr_set(base, a);
	gr_one(acc);
	while (e) {
		if (e & 1) {
			gr_mul(acc, acc, base, ctx);
		}
		gr_mul(base, base, base, ctx);
		e >>= 1;
	}
	gr_set(r, acc);
	gr_clear(base); gr_clear(acc);
}


/* Everything dimensioned by TAU is far too large to be a local: at TAU = 1000,
 * s is 512 MiB, H is 786 MiB, and the prover's v_i,j are 3 * TAU * V arrays of
 * DEGREE mpz_t, about 1.4 GiB. They are allocated on the heap once at start-up,
 * and the pointers below index exactly like the arrays they replace.
 *
 * NOTE: at TAU = 1000 this binary needs several gigabytes of RAM. Pass e.g.
 * CONFIG=-DTAU=8 to make to try it on a smaller machine. */
params::poly_q A[R][V];
params::poly_q (*s)[V], (*t)[R];
static array < mpz_t, params::poly_q::degree > (*v)[TAU][V];
static gr_t *prover_y;                      /* prover_y[i] = l_i(x) */
static gr_t (*prover_beta)[3];
static gr_t (*prover_wt)[3];                /* l_i(x) l_0(x)^j */
static fmpz_t (*prover_r)[3][ETA];

/* Codeword length. A power of two dividing q - 1, so Z_q has a root of unity
 * of this order; the message is 2N + ETA elements, so it must exceed that. */
#define AEX_COLS    ((size_t) 16384)

/* One codeword: AEX_COLS elements of Z_q packed as two 64-bit limbs each, so a
 * codeword occupies exactly as much as the params::poly_big it replaces. */
typedef struct {
	uint64_t w[2 * AEX_COLS];
} aex_code_t;

static aex_code_t H0[V], _H[V];
static aex_code_t (*H)[3][V];

static void pismall_alloc(void) {
	s = new params::poly_q[TAU][V];
	t = new params::poly_q[TAU][R];
	H = new aex_code_t[TAU][3][V];
	v = new array < mpz_t, params::poly_q::degree >[3][TAU][V];
	prover_y = new gr_t[TAU + 1];
	prover_beta = new gr_t[TAU][3];
	prover_wt = new gr_t[TAU][3];
	prover_r = new fmpz_t[TAU][3][ETA];
}

static void pismall_free(void) {
	delete[]s;
	delete[]t;
	delete[]H;
	delete[]v;
	delete[]prover_y;
	delete[]prover_beta;
	delete[]prover_wt;
	delete[]prover_r;
}

/* --- Reed-Solomon encoding over Z_q ------------------------------------- */

static fmpz *aex_scratch;                              /* symbol buffer */
static std::array < mpz_t, params::poly_big::degree > aex_mpz;
static params::poly_big *aex_poly;                     /* NTT working poly */

static inline void aex_pack(aex_code_t * c, size_t i, const fmpz_t x) {
	fmpz_get_ui_array(c->w + 2 * i, 2, x);
}

static inline void aex_unpack(fmpz_t x, const aex_code_t * c, size_t i) {
	fmpz_set_ui_array(x, c->w + 2 * i, 2);
}


static void aex_ntt_setup(const fmpz_mod_ctx_t ctx) {
	aex_scratch = _fmpz_vec_init(AEX_COLS);
	aex_poly = new params::poly_big;
	for (size_t i = 0; i < params::poly_big::degree; i++) {
		mpz_init2(aex_mpz[i], params::poly_big::bits_in_moduli_product() << 2);
	}
}

static void aex_ntt_clear(void) {
	_fmpz_vec_clear(aex_scratch, AEX_COLS);
	delete aex_poly;
	for (size_t i = 0; i < params::poly_big::degree; i++) {
		mpz_clear(aex_mpz[i]);
	}
}

/* Encode(in0, in1, r): pack the two message blocks and the randomness into the
 * low coefficients, then evaluate at the AEX_COLS roots of unity. */
static void aex_encode(aex_code_t & out, fmpz_mod_poly_t in0,
		fmpz_mod_poly_t in1, const fmpz * in, const fmpz_mod_ctx_t ctx) {
	const size_t N = params::poly_q::degree;
	size_t i;

	for (i = 0; i < N; i++) {
		fmpz_mod_poly_get_coeff_fmpz(aex_scratch + i, in0, i, ctx);
		fmpz_get_mpz(aex_mpz[i], aex_scratch + i);
	}
	for (; i < 2 * N; i++) {
		fmpz_mod_poly_get_coeff_fmpz(aex_scratch + i, in1, i - N, ctx);
		fmpz_get_mpz(aex_mpz[i], aex_scratch + i);
	}
	for (; i < 2 * N + ETA; i++) {
		fmpz_get_mpz(aex_mpz[i], in + (i - 2 * N));
	}
	for (; i < AEX_COLS; i++) {
		mpz_set_ui(aex_mpz[i], 0);
	}

	/* Both NFLlib moduli satisfy p = 1 mod 2 * AEX_COLS, so this is a genuine
	 * length-AEX_COLS transform; poly2mpz then CRTs each symbol back. */
	aex_poly->mpz2poly(aex_mpz);
	aex_poly->ntt_pow_phi();
	aex_poly->poly2mpz(aex_mpz);
	for (i = 0; i < AEX_COLS; i++) {
		fmpz_set_mpz(aex_scratch + i, aex_mpz[i]);
		aex_pack(&out, i, aex_scratch + i);
	}
}

/* Rows of E, as RowsToMatrix lists them: H, H_0, then H_{i,j} for each k. */
#define AEX_ROWS    (V * (2 + 3 * TAU))
/* Codeword length, i.e. number of columns of E. */
/* Columns opened per repetition, and the number of repetitions. */
#define AEX_REPS    2

/* Row r of E, in RowsToMatrix order. */
static aex_code_t & aex_row(size_t r) {
	if (r < V) {
		return _H[r];
	}
	r -= V;
	if (r < V) {
		return H0[r];
	}
	r -= V;
	size_t k = r % V;
	r /= V;
	size_t j = r % 3;
	return H[r / 3][j][k];
}

/* Serialise column c of E: entry (r, c) is the c-th codeword symbol of row r. */
static void aex_column(uint8_t * out, size_t c) {
	for (size_t r = 0; r < AEX_ROWS; r++) {
		const uint64_t *d = aex_row(r).w + 2 * c;
		for (size_t m = 0; m < 2; m++) {
			for (size_t b = 0; b < 8; b++) {
				out[(r * 2 + m) * 8 + b] = (uint8_t) (d[m] >> (8 * b));
			}
		}
	}
}

#define AEX_COLBYTES    (AEX_ROWS * 2 * 8)

/* Merkle tree over the AEX_COLS column hashes, levels concatenated from the
 * leaves up; the last node is the root. */
typedef struct {
	uint8_t *node;
	size_t levels;
} aex_tree_t;

static size_t aex_tree_nodes(void) {
	size_t n = AEX_COLS, total = 0;
	while (n >= 1) {
		total += n;
		if (n == 1) break;
		n >>= 1;
	}
	return total;
}

static void aex_hash_column(uint8_t out[BLAKE3_OUT_LEN], size_t c,
		uint8_t *scratch) {
	blake3_hasher h;
	aex_column(scratch, c);
	blake3_hasher_init(&h);
	blake3_hasher_update(&h, scratch, AEX_COLBYTES);
	blake3_hasher_finalize(&h, out, BLAKE3_OUT_LEN);
}

static void aex_node(uint8_t out[BLAKE3_OUT_LEN], const uint8_t *l,
		const uint8_t *r) {
	blake3_hasher h;
	blake3_hasher_init(&h);
	blake3_hasher_update(&h, l, BLAKE3_OUT_LEN);
	blake3_hasher_update(&h, r, BLAKE3_OUT_LEN);
	blake3_hasher_finalize(&h, out, BLAKE3_OUT_LEN);
}

static void aex_tree_build(aex_tree_t & t) {
	uint8_t *scratch = new uint8_t[AEX_COLBYTES];
	t.node = new uint8_t[aex_tree_nodes() * BLAKE3_OUT_LEN];
	for (size_t c = 0; c < AEX_COLS; c++) {
		aex_hash_column(t.node + c * BLAKE3_OUT_LEN, c, scratch);
	}
	delete[]scratch;
	size_t off = 0, n = AEX_COLS;
	t.levels = 1;
	while (n > 1) {
		uint8_t *cur = t.node + off * BLAKE3_OUT_LEN;
		uint8_t *nxt = cur + n * BLAKE3_OUT_LEN;
		for (size_t i = 0; i < n / 2; i++) {
			aex_node(nxt + i * BLAKE3_OUT_LEN,
					cur + (2 * i) * BLAKE3_OUT_LEN,
					cur + (2 * i + 1) * BLAKE3_OUT_LEN);
		}
		off += n;
		n >>= 1;
		t.levels++;
	}
}

static const uint8_t *aex_tree_root(const aex_tree_t & t) {
	return t.node + (aex_tree_nodes() - 1) * BLAKE3_OUT_LEN;
}

static void aex_tree_clear(aex_tree_t & t) {
	delete[]t.node;
	t.node = NULL;
}

/* Sibling hashes from leaf c up to the root. */
static void aex_path(uint8_t *out, const aex_tree_t & t, size_t c) {
	size_t off = 0, n = AEX_COLS, lvl = 0;
	while (n > 1) {
		size_t sib = (c & 1) ? c - 1 : c + 1;
		memcpy(out + lvl * BLAKE3_OUT_LEN,
				t.node + (off + sib) * BLAKE3_OUT_LEN, BLAKE3_OUT_LEN);
		off += n;
		n >>= 1;
		c >>= 1;
		lvl++;
	}
}

/* Recompute the root from an opened column and its path. */
static int aex_path_verify(const uint8_t *col, const uint8_t *path, size_t c,
		const uint8_t *root) {
	uint8_t acc[BLAKE3_OUT_LEN], tmp[BLAKE3_OUT_LEN];
	blake3_hasher h;

	blake3_hasher_init(&h);
	blake3_hasher_update(&h, col, AEX_COLBYTES);
	blake3_hasher_finalize(&h, acc, BLAKE3_OUT_LEN);

	size_t n = AEX_COLS, lvl = 0;
	while (n > 1) {
		const uint8_t *sib = path + lvl * BLAKE3_OUT_LEN;
		if (c & 1) {
			aex_node(tmp, sib, acc);
		} else {
			aex_node(tmp, acc, sib);
		}
		memcpy(acc, tmp, BLAKE3_OUT_LEN);
		n >>= 1;
		c >>= 1;
		lvl++;
	}
	return memcmp(acc, root, BLAKE3_OUT_LEN) == 0;
}

/* The opened part of the proof: the root, the eta column indices, the columns
 * themselves and their Merkle paths. */
typedef struct {
	uint8_t root[BLAKE3_OUT_LEN];
	size_t I[ETA];
	uint8_t *col;
	uint8_t *path;
	size_t levels;
} aex_open_t;

static aex_tree_t aex_tree;

/* Symbol of row r inside a serialised column. */
static void aex_col_sym(fmpz_t out, const uint8_t * col, size_t r) {
	uint64_t w[2] = { 0, 0 };

	for (size_t m = 0; m < 2; m++) {
		for (size_t b = 0; b < 8; b++) {
			w[m] |= ((uint64_t) col[(r * 2 + m) * 8 + b]) << (8 * b);
		}
	}
	fmpz_set_ui_array(out, w, 2);
}

#define AEX_ROW_H(k)        (k)
#define AEX_ROW_H0(k)       (V + (k))
#define AEX_ROW_HIJ(i,j,k)  (2 * V + (((i) * 3 + (j)) * V + (k)))

static void aex_absorb(blake3_hasher * h, const fmpz_t x) {
	uint64_t w[2];
	uint8_t b[16];

	fmpz_get_ui_array(w, 2, x);
	for (size_t m = 0; m < 2; m++) {
		for (size_t i = 0; i < 8; i++) {
			b[m * 8 + i] = (uint8_t) (w[m] >> (8 * i));
		}
	}
	blake3_hasher_update(h, b, sizeof(b));
}

/* Derive the eta opened columns from the root and the step-9 openings. */
static void aex_sample_I(size_t I[ETA], const uint8_t root[BLAKE3_OUT_LEN],
		fmpz_mod_poly_t f[V][2], gr_t rf[ETA], fmpz_mod_poly_t h[2][V][2],
		gr_t rh[ETA], const fmpz_mod_ctx_t ctx) {
	blake3_hasher hasher;
	fmpz_t c;
	uint8_t *out = new uint8_t[ETA * 8];

	fmpz_init(c);
	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, root, BLAKE3_OUT_LEN);
	for (int cc = 0; cc < 2; cc++) {
		for (size_t k = 0; k < V; k++) {
			for (size_t l = 0; l < 2 * params::poly_q::degree; l++) {
				if (l < params::poly_q::degree) {
					fmpz_mod_poly_get_coeff_fmpz(c, f[k][cc], l, ctx);
					aex_absorb(&hasher, c);
				}
				fmpz_mod_poly_get_coeff_fmpz(c,
						h[l / params::poly_q::degree][k][cc],
						l % params::poly_q::degree, ctx);
				aex_absorb(&hasher, c);
			}
		}
	}
	for (size_t i = 0; i < ETA; i++) {
		aex_absorb(&hasher, rf[i].c0);
		aex_absorb(&hasher, rf[i].c1);
		aex_absorb(&hasher, rh[i].c0);
		aex_absorb(&hasher, rh[i].c1);
	}
	blake3_hasher_finalize(&hasher, out, ETA * 8);
	for (size_t i = 0; i < ETA; i++) {
		uint64_t r = 0;
		for (size_t b = 0; b < 8; b++) {
			r |= ((uint64_t) out[i * 8 + b]) << (8 * b);
		}
		I[i] = (size_t) (r % AEX_COLS);
	}
	fmpz_clear(c);
	delete[]out;
}

/* Step 11: open the columns named by I, with their Merkle paths. */
static void aex_open(aex_open_t & o) {
	o.levels = aex_tree.levels;
	o.col = new uint8_t[ETA * AEX_COLBYTES];
	o.path = new uint8_t[ETA * (o.levels - 1) * BLAKE3_OUT_LEN];
	memcpy(o.root, aex_tree_root(aex_tree), BLAKE3_OUT_LEN);
	for (size_t i = 0; i < ETA; i++) {
		aex_column(o.col + i * AEX_COLBYTES, o.I[i]);
		aex_path(o.path + i * (o.levels - 1) * BLAKE3_OUT_LEN, aex_tree, o.I[i]);
	}
}

static void aex_open_clear(aex_open_t & o) {
	delete[]o.col;
	delete[]o.path;
	o.col = NULL;
	o.path = NULL;
}

/* A primitive TAU-th root of unity modulo the NFLlib moduli product: one of
 * order TAU per prime, recombined by CRT. TAU must be a power of two, which
 * both primes support (p - 1 is divisible by 2^24). */
static void aex_root_tau(fmpz_t w, const fmpz_mod_ctx_t ctx) {
	fmpz_t acc, pj, wj, e, t, m;

	fmpz_init(acc); fmpz_init(pj); fmpz_init(wj);
	fmpz_init(e); fmpz_init(t); fmpz_init(m);
	fmpz_one(m);
	fmpz_zero(acc);
	for (size_t j = 0; j < params::poly_q::nmoduli; j++) {
		fmpz_set_ui(pj, nfl::params < uint64_t >::P[j]);
		fmpz_sub_ui(e, pj, 1);
		fmpz_divexact_ui(e, e, TAU);
		for (ulong g = 2;; g++) {
			fmpz_set_ui(t, g);
			fmpz_powm(wj, t, e, pj);
			fmpz_powm_ui(t, wj, TAU / 2, pj);
			if (!fmpz_is_one(t) && !fmpz_is_zero(wj)) {
				break;
			}
		}
		if (j == 0) {
			fmpz_set(acc, wj);
			fmpz_set(m, pj);
		} else {
			fmpz_CRT(acc, acc, m, wj, pj, 0);
			fmpz_mul(m, m, pj);
		}
	}
	fmpz_mod_set_fmpz(w, acc, ctx);
	fmpz_clear(acc); fmpz_clear(pj); fmpz_clear(wj);
	fmpz_clear(e); fmpz_clear(t); fmpz_clear(m);
}

/* l_i(x) for i = 0..TAU in closed form. With the nodes at the TAU-th roots of
 * unity, l_0 = X^TAU - 1 and l_i(X) = w^{i-1}(X^TAU - 1)/(TAU (X - w^{i-1})),
 * so the whole vector costs O(TAU) multiplies and a single inversion instead of
 * evaluating TAU + 1 dense polynomials. */
static void gr_comp(fmpz * out, gr_t in[ETA], int c) {
	for (size_t i = 0; i < ETA; i++) {
		fmpz_set(out + i, c ? in[i].c1 : in[i].c0);
	}
}

static int aex_lagrange(gr_t * lev, const gr_t & x, const fmpz_mod_ctx_t ctx) {
	static int cached = 0;
	static fmpz_t w_cache;
	fmpz_t tauinv, wi;
	gr_t xt, acc;
	gr_t *den = new gr_t[TAU];
	gr_t *pre = new gr_t[TAU + 1];
	fmpz *wpow = _fmpz_vec_init(TAU);
	int ok;

	if (!cached) {
		fmpz_init(w_cache);
		aex_root_tau(w_cache, ctx);
		cached = 1;
	}
	fmpz_init(tauinv); fmpz_init(wi);
	gr_init(xt); gr_init(acc);
	for (size_t i = 0; i < TAU; i++) {
		gr_init(den[i]);
		gr_init(pre[i]);
	}
	gr_init(pre[TAU]);

	/* l_0(x) = x^TAU - 1, now evaluated in the extension. */
	gr_pow_ui(xt, x, TAU, ctx);
	fmpz_mod_sub_ui(xt.c0, xt.c0, 1, ctx);
	gr_set(lev[0], xt);

	/* TAU is a power of two and q is odd, so TAU stays invertible in Z_q and
	 * needs no extension arithmetic; the same goes for the nodes w^i. */
	fmpz_set_ui(wi, TAU);
	fmpz_mod_inv(tauinv, wi, ctx);

	fmpz_one(wi);
	for (size_t i = 0; i < TAU; i++) {
		fmpz_mod_sub(den[i].c0, x.c0, wi, ctx);
		fmpz_set(den[i].c1, x.c1);
		fmpz_set(wpow + i, wi);
		fmpz_mod_mul(wi, wi, w_cache, ctx);
	}
	/* batch inversion: one gr_inv for all TAU denominators */
	gr_one(pre[0]);
	for (size_t i = 0; i < TAU; i++) {
		gr_mul(pre[i + 1], pre[i], den[i], ctx);
	}
	ok = gr_inv(acc, pre[TAU], ctx);
	if (ok) {
		for (size_t i = TAU; i-- > 0;) {
			gr_mul(pre[i], acc, pre[i], ctx);       /* 1 / den[i] */
			gr_mul(acc, acc, den[i], ctx);
			gr_mul(lev[i + 1], xt, pre[i], ctx);
			gr_scalar(lev[i + 1], lev[i + 1], wpow + i, ctx);
			gr_scalar(lev[i + 1], lev[i + 1], tauinv, ctx);
		}
	}

	fmpz_clear(tauinv); fmpz_clear(wi);
	gr_clear(xt); gr_clear(acc);
	for (size_t i = 0; i < TAU; i++) {
		gr_clear(den[i]);
		gr_clear(pre[i]);
	}
	gr_clear(pre[TAU]);
	delete[]den;
	delete[]pre;
	_fmpz_vec_clear(wpow, TAU);
	return ok;
}

/* Step 12: the two encoding identities, checked at the opened columns.
 *   Encode(fbar, (1/l0(x)) fbar o (fbar-1) o (fbar+1), rfbar)|I
 *      == l0(x) H0|I + sum_ij li(x) l0(x)^j Hij|I
 *   Encode(hbar, rhbar)|I == H|I + b0 H0|I + sum_ij bij Hij|I
 */
static int aex_identities(const aex_open_t & o, fmpz_mod_poly_t f[V][2],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][2], gr_t rh[ETA],
		const gr_t & x, const gr_t & beta0, gr_t beta[TAU][3],
		fmpz_mod_poly_t lag[TAU + 1], const fmpz_mod_ctx_t ctx) {
	fmpz_t tmp, sym, accf[2], acch[2];
	fmpz *rc = _fmpz_vec_init(ETA);
	gr_t l0, l0inv, one, fv, cub, t;
	gr_t lpow[3];
	gr_t *lev = new gr_t[TAU + 1];
	/* l_i(x) l_0(x)^j does not depend on the column or the component, but used
	 * to be recomputed inside both loops; hoisting it out pays for most of the
	 * extra work the extension costs here. */
	gr_t (*wt)[3] = new gr_t[TAU][3];
	fmpz_mod_poly_t g[2];
	aex_code_t *lhs_f = new aex_code_t[2 * V];
	aex_code_t *lhs_h = new aex_code_t[2 * V];
	int ok = 1;

	fmpz_init(tmp); fmpz_init(sym);
	for (int i = 0; i < 2; i++) {
		fmpz_init(accf[i]);
		fmpz_init(acch[i]);
	}
	gr_init(l0); gr_init(l0inv); gr_init(one); gr_init(fv);
	gr_init(cub); gr_init(t);
	for (int i = 0; i < 3; i++) {
		gr_init(lpow[i]);
	}
	for (size_t i = 0; i <= TAU; i++) {
		gr_init(lev[i]);
	}
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_init(wt[i][j]);
		}
	}
	fmpz_mod_poly_init(g[0], ctx);
	fmpz_mod_poly_init(g[1], ctx);
	gr_one(one);

	/* A challenge whose l_0(x) is a zero divisor is not usable; at deg/p^2 it
	 * never happens in practice, and rejecting beats aborting. */
	ok = aex_lagrange(lev, x, ctx);
	if (ok) {
		gr_set(l0, lev[0]);
		ok = gr_inv(l0inv, l0, ctx);
	}
	if (ok) {
		gr_one(lpow[0]);
		gr_set(lpow[1], l0);
		gr_mul(lpow[2], l0, l0, ctx);
		for (size_t i = 0; i < TAU; i++) {
			for (size_t j = 0; j < 3; j++) {
				gr_mul(wt[i][j], lev[i + 1], lpow[j], ctx);
			}
		}

		/* left-hand sides, one codeword per component and per k */
		for (size_t k = 0; k < V; k++) {
			for (size_t l = 0; l < params::poly_q::degree; l++) {
				fmpz_mod_poly_get_coeff_fmpz(fv.c0, f[k][0], l, ctx);
				fmpz_mod_poly_get_coeff_fmpz(fv.c1, f[k][1], l, ctx);
				gr_sub(cub, fv, one, ctx);
				gr_mul(cub, cub, fv, ctx);
				gr_add(t, fv, one, ctx);
				gr_mul(cub, cub, t, ctx);
				gr_mul(cub, cub, l0inv, ctx);
				fmpz_mod_poly_set_coeff_fmpz(g[0], l, cub.c0, ctx);
				fmpz_mod_poly_set_coeff_fmpz(g[1], l, cub.c1, ctx);
			}
			for (int c = 0; c < 2; c++) {
				gr_comp(rc, rf, c);
				aex_encode(lhs_f[k * 2 + c], f[k][c], g[c], rc, ctx);
				gr_comp(rc, rh, c);
				aex_encode(lhs_h[k * 2 + c], h[0][k][c], h[1][k][c], rc, ctx);
			}
		}
	}

	for (size_t n = 0; n < ETA && ok; n++) {
		const uint8_t *col = o.col + n * AEX_COLBYTES;
		for (size_t k = 0; k < V && ok; k++) {
			/* Both identities and both components read the same H_ij symbol,
			 * so unpack the column once per row and fan it out over the four
			 * accumulators instead of fetching it four times. */
			aex_col_sym(acch[0], col, AEX_ROW_H(k));
			fmpz_zero(acch[1]);
			aex_col_sym(sym, col, AEX_ROW_H0(k));
			for (int c = 0; c < 2; c++) {
				fmpz_mod_mul(accf[c], c ? l0.c1 : l0.c0, sym, ctx);
				fmpz_mod_mul(tmp, c ? beta0.c1 : beta0.c0, sym, ctx);
				fmpz_mod_add(acch[c], acch[c], tmp, ctx);
			}
			for (size_t i = 0; i < TAU; i++) {
				for (size_t j = 0; j < 3; j++) {
					aex_col_sym(sym, col, AEX_ROW_HIJ(i, j, k));
					for (int c = 0; c < 2; c++) {
						fmpz_mod_mul(tmp, c ? wt[i][j].c1 : wt[i][j].c0,
								sym, ctx);
						fmpz_mod_add(accf[c], accf[c], tmp, ctx);
						fmpz_mod_mul(tmp, c ? beta[i][j].c1 : beta[i][j].c0,
								sym, ctx);
						fmpz_mod_add(acch[c], acch[c], tmp, ctx);
					}
				}
			}
			for (int c = 0; c < 2; c++) {
				aex_unpack(tmp, lhs_f + k * 2 + c, o.I[n]);
				ok &= fmpz_equal(accf[c], tmp);
				aex_unpack(tmp, lhs_h + k * 2 + c, o.I[n]);
				ok &= fmpz_equal(acch[c], tmp);
			}
		}
	}

	fmpz_clear(tmp); fmpz_clear(sym);
	for (int i = 0; i < 2; i++) {
		fmpz_clear(accf[i]);
		fmpz_clear(acch[i]);
	}
	gr_clear(l0); gr_clear(l0inv); gr_clear(one); gr_clear(fv);
	gr_clear(cub); gr_clear(t);
	for (int i = 0; i < 3; i++) {
		gr_clear(lpow[i]);
	}
	for (size_t i = 0; i <= TAU; i++) {
		gr_clear(lev[i]);
	}
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_clear(wt[i][j]);
		}
	}
	fmpz_mod_poly_clear(g[0], ctx);
	fmpz_mod_poly_clear(g[1], ctx);
	_fmpz_vec_clear(rc, ETA);
	delete[]lev;
	delete[]wt;
	delete[]lhs_f;
	delete[]lhs_h;
	return ok;
}

/* --- v_{i,j} extraction ---------------------------------------------------
 * Per coefficient position, f = s_0 * l_0 + sum_i s_i l_i and
 *   (1/l_0) f o (f-1) o (f+1) = sum_j sum_i v_{i,j} l_i l_0^j.
 * With the nodes at the TAU-th roots of unity, l_0 = X^TAU - 1, evaluating at
 * the nodes is a length-TAU NTT, interpolating is its inverse, and dividing by
 * l_0 is an O(TAU) recurrence. The decomposition is unique, so the v_{i,j} are
 * whatever the three extraction rounds produce; no closed form in s_i alone
 * exists, since v_{i,0} involves g'(a_i) and so depends on every s_m.
 */
static_assert((TAU & (TAU - 1)) == 0, "TAU must be a power of two");

#define AEX_N4  (4 * TAU)

typedef unsigned long long aex_u64;

static inline aex_u64 aex_mul(aex_u64 a, aex_u64 b, aex_u64 p) {
	return (aex_u64) ((__uint128_t) a * b % p);
}

static inline aex_u64 aex_add(aex_u64 a, aex_u64 b, aex_u64 p) {
	aex_u64 s = a + b;
	return s >= p ? s - p : s;
}

static inline aex_u64 aex_sub(aex_u64 a, aex_u64 b, aex_u64 p) {
	return a >= b ? a - b : a + p - b;
}

static aex_u64 aex_pow(aex_u64 a, aex_u64 e, aex_u64 p) {
	aex_u64 r = 1;
	a %= p;
	while (e) {
		if (e & 1) {
			r = aex_mul(r, a, p);
		}
		a = aex_mul(a, a, p);
		e >>= 1;
	}
	return r;
}

/* Shoup multiplication: with wp = floor(w * 2^64 / p) precomputed, a * w mod p
 * costs two multiplies instead of a 128-bit division. */
static inline aex_u64 aex_mul_shoup(aex_u64 a, aex_u64 w, aex_u64 wp,
		aex_u64 p) {
	aex_u64 hi = (aex_u64) (((__uint128_t) a * wp) >> 64);
	aex_u64 r = a * w - hi * p;
	return r >= p ? r - p : r;
}

static inline aex_u64 aex_shoup(aex_u64 w, aex_u64 p) {
	return (aex_u64) ((((__uint128_t) w) << 64) / p);
}

/* Twiddles for one prime: w^k and their Shoup factors, per NTT length. */
typedef struct {
	aex_u64 p;
	aex_u64 *w, *wp;            /* forward, length n/2 */
	aex_u64 *iw, *iwp;          /* inverse */
	aex_u64 ninv, ninvp;
	size_t n;
} aex_tw_t;

static void aex_tw_init(aex_tw_t & t, size_t n, aex_u64 w, aex_u64 p) {
	t.p = p; t.n = n;
	t.w = new aex_u64[n / 2]; t.wp = new aex_u64[n / 2];
	t.iw = new aex_u64[n / 2]; t.iwp = new aex_u64[n / 2];
	aex_u64 iw = aex_pow(w, p - 2, p);
	t.w[0] = 1; t.iw[0] = 1;
	for (size_t i = 1; i < n / 2; i++) {
		t.w[i] = aex_mul(t.w[i - 1], w, p);
		t.iw[i] = aex_mul(t.iw[i - 1], iw, p);
	}
	for (size_t i = 0; i < n / 2; i++) {
		t.wp[i] = aex_shoup(t.w[i], p);
		t.iwp[i] = aex_shoup(t.iw[i], p);
	}
	t.ninv = aex_pow(n % p, p - 2, p);
	t.ninvp = aex_shoup(t.ninv, p);
}

static void aex_tw_clear(aex_tw_t & t) {
	delete[]t.w; delete[]t.wp; delete[]t.iw; delete[]t.iwp;
}

/* in-place radix-2 NTT over a precomputed twiddle table */
static void aex_ntt_tw(aex_u64 * a, const aex_tw_t & t, int inverse) {
	const size_t n = t.n;
	const aex_u64 p = t.p;
	const aex_u64 *W = inverse ? t.iw : t.w;
	const aex_u64 *Wp = inverse ? t.iwp : t.wp;

	for (size_t i = 1, j = 0; i < n; i++) {
		size_t bit = n >> 1;
		for (; j & bit; bit >>= 1) {
			j ^= bit;
		}
		j ^= bit;
		if (i < j) {
			aex_u64 x = a[i]; a[i] = a[j]; a[j] = x;
		}
	}
	for (size_t len = 2; len <= n; len <<= 1) {
		size_t step = n / len;
		for (size_t i = 0; i < n; i += len) {
			for (size_t k = 0; k < len / 2; k++) {
				size_t idx = k * step;
				aex_u64 u = a[i + k];
				aex_u64 v = aex_mul_shoup(a[i + k + len / 2], W[idx], Wp[idx], p);
				a[i + k] = aex_add(u, v, p);
				a[i + k + len / 2] = aex_sub(u, v, p);
			}
		}
	}
	if (inverse) {
		for (size_t i = 0; i < n; i++) {
			a[i] = aex_mul_shoup(a[i], t.ninv, t.ninvp, p);
		}
	}
}

/* Exact division by X^TAU - 1 into a separate buffer: Q_{m-TAU} = c_m + Q_m,
 * taken from the top. src and dst must not alias -- computing it in place
 * silently evaluates a different recurrence. */
static size_t aex_divl0(aex_u64 * dst, const aex_u64 * src, size_t len,
		aex_u64 p) {
	for (size_t i = 0; i < len; i++) {
		dst[i] = 0;
	}
	for (size_t m = len; m-- > TAU;) {
		dst[m - TAU] = aex_add(src[m], dst[m], p);
	}
	return len > TAU ? len - TAU : 1;
}

/* Extract v[j][i] for one coefficient position modulo one prime. */
static void aex_extract(aex_u64 a, const aex_u64 * b, aex_u64 out[3][TAU],
		const aex_tw_t & TT, const aex_tw_t & T4, aex_u64 * bufA,
		aex_u64 * bufB, aex_u64 * buft) {
	const aex_u64 p = TT.p;
	/* g = interpolant of b at the nodes */
	for (size_t i = 0; i < TAU; i++) {
		buft[i] = b[i];
	}
	aex_ntt_tw(buft, TT, 1);
	/* f = a (X^TAU - 1) + g, degree TAU */
	for (size_t i = 0; i < AEX_N4; i++) {
		bufA[i] = 0;
	}
	for (size_t i = 0; i < TAU; i++) {
		bufA[i] = buft[i];
	}
	bufA[0] = aex_sub(bufA[0], a, p);
	bufA[TAU] = aex_add(bufA[TAU], a, p);
	for (size_t i = 0; i <= TAU; i++) {
		bufB[i] = bufA[i];
	}
	/* f^3 on 4 TAU points, then subtract f */
	aex_ntt_tw(bufA, T4, 0);
	for (size_t i = 0; i < AEX_N4; i++) {
		bufA[i] = aex_mul(aex_mul(bufA[i], bufA[i], p), bufA[i], p);
	}
	aex_ntt_tw(bufA, T4, 1);
	for (size_t i = 0; i <= TAU; i++) {
		bufA[i] = aex_sub(bufA[i], bufB[i], p);
	}
	/* Q = (f^3 - f) / (X^TAU - 1) */
	size_t len = aex_divl0(bufB, bufA, AEX_N4, p);
	aex_u64 *cur = bufB, *oth = bufA;

	for (int j = 0; j < 3; j++) {
		for (size_t i = 0; i < TAU; i++) {
			buft[i] = 0;
		}
		for (size_t m = 0; m < len; m++) {
			buft[m % TAU] = aex_add(buft[m % TAU], cur[m], p);
		}
		aex_ntt_tw(buft, TT, 0);
		for (size_t i = 0; i < TAU; i++) {
			out[j][i] = buft[i];
		}
		if (j == 2) {
			break;
		}
		aex_ntt_tw(buft, TT, 1);
		for (size_t i = 0; i < TAU && i < len; i++) {
			cur[i] = aex_sub(cur[i], buft[i], p);
		}
		len = aex_divl0(oth, cur, len, p);
		aex_u64 *sw = cur;
		cur = oth;
		oth = sw;
	}
}

static void pismall_hash(gr_t & x, gr_t & beta0, gr_t beta[TAU][3], fmpz_t q,
		commit_t & com, const uint8_t root[BLAKE3_OUT_LEN]) {
	uint8_t hash[BLAKE3_OUT_LEN];
	blake3_hasher hasher;
	flint_rand_t rand;
	ulong seed[2];

	flint_rand_init(rand);

	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, root, BLAKE3_OUT_LEN);
	blake3_hasher_update(&hasher, (const uint8_t *)com.c1.data(), 16 * DEGREE);
	for (size_t i = 0; i < com.c2.size(); i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)com.c2[i].data(),
				16 * DEGREE);
	}

	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	memcpy(&seed[0], hash, sizeof(ulong));
	memcpy(&seed[1], hash + BLAKE3_OUT_LEN / 2, sizeof(ulong));
	flint_rand_set_seed(rand, seed[0], seed[1]);
	/* Both coordinates of every challenge come from Z_q, so each is uniform
	 * over the whole extension. */
	fmpz_randm(x.c0, rand, q);
	fmpz_randm(x.c1, rand, q);
	fmpz_randm(beta0.c0, rand, q);
	fmpz_randm(beta0.c1, rand, q);
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			fmpz_randm(beta[i][j].c0, rand, q);
			fmpz_randm(beta[i][j].c1, rand, q);
		}
	}

	flint_rand_clear(rand);
}

static void poly_to(params::poly_q & out, fmpz_mod_poly_t & in,
		const fmpz_mod_ctx_t ctx) {
	array < mpz_t, params::poly_q::degree > coeffs;

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		flint_poly_get_coeff_mpz(coeffs[i], in, i, ctx);
	}

	out.mpz2poly(coeffs);
	out.ntt_pow_phi();

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
}

static void poly_from(fmpz_mod_poly_t & out, params::poly_q & in,
		const fmpz_mod_ctx_t ctx) {
	/* in is stored as RNS residues, so recombine them directly rather than
	 * going through poly2mpz and an mpz per coefficient. No centring: out's
	 * modulus is the same moduli product, so centring is a no-op modulo it. */
	static_assert(params::poly_q::nmoduli == 2, "CRT below assumes two moduli");
	static int ready = 0;
	static aex_u64 P0, P1, P0inv;
	const size_t N = params::poly_q::degree;
	if (!ready) {
		P0 = nfl::params < uint64_t >::P[0];
		P1 = nfl::params < uint64_t >::P[1];
		P0inv = aex_pow(P0 % P1, P1 - 2, P1);
		ready = 1;
	}
	in.invntt_pow_invphi();
	const uint64_t *d = in.data();

	/* Write the coefficient array directly: the recombined values are already
	 * reduced, so fmpz_mod_poly_set_coeff_fmpz's bounds check, length update
	 * and redundant reduction are all wasted work at 4096 coefficients. */
	fmpz_mod_poly_fit_length(out, N, ctx);
	for (size_t l = 0; l < N; l++) {
		aex_u64 r0 = d[l], r1 = d[N + l];
		aex_u64 t = aex_mul(aex_sub(r1 % P1, r0 % P1, P1), P0inv, P1);
		__uint128_t val = (__uint128_t) P0 * t + r0;
		unsigned long limb[2] = {
			(unsigned long) (val & 0xffffffffffffffffULL),
			(unsigned long) (val >> 64)
		};
		fmpz_set_ui_array(out->coeffs + l, limb, 2);
	}
	_fmpz_mod_poly_set_length(out, N);
	_fmpz_mod_poly_normalise(out);
	in.ntt_pow_phi();
}

static void pismall_setup(fmpz_mod_poly_t lag[], fmpz_t a[TAU], fmpz_t & q,
		flint_rand_t prng, const fmpz_mod_ctx_t ctx) {
	array < mpz_t, params::poly_q::degree > coeffs;
	fmpz_t t, u;
	fmpz xs[TAU];

	fmpz_init(t);
	fmpz_init(u);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}
	for (size_t i = 0; i < TAU; i++) {
		fmpz_init(&xs[i]);
		fmpz_set(&xs[i], a[i]);
	}

	/* Compute l_0(X) = \Prod(X - a_i) */
	fmpz_mod_poly_product_roots_fmpz_vec(lag[0], xs, TAU, ctx);
	/* Compute l_i(X) = \Prod(X - a_j)(a_i - a_j) */
	for (size_t i = 1; i <= TAU; i++) {
		fmpz_set(t, &xs[i - 1]);
		fmpz_set(&xs[i - 1], &xs[TAU - 1]);
		fmpz_mod_poly_product_roots_fmpz_vec(lag[i], xs, TAU - 1, ctx);

		fmpz_set(&xs[i - 1], t);
		fmpz_set_ui(u, 1);
		for (size_t j = 0; j < TAU; j++) {
			if (i - 1 != j) {
				fmpz_sub(t, a[i - 1], a[j]);
				fmpz_mul(u, u, t);
			}
		}
		fmpz_invmod(u, u, q);
		fmpz_mod_poly_scalar_mul_fmpz(lag[i], lag[i], u, ctx);
	}

	fmpz_clear(t);
	fmpz_clear(u);
	for (size_t i = 0; i < TAU; i++) {
		fmpz_clear(&xs[i]);
	}
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
}

static int pismall_prover(commit_t & com, gr_t & x, fmpz_mod_poly_t f[V][2],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][2], gr_t rh[ETA],
		vector < params::poly_q > rd, comkey_t & key,
		fmpz_mod_poly_t lag[TAU + 1], flint_rand_t prng,
		const fmpz_mod_ctx_t ctx, aex_open_t & o) {
	array < mpz_t, params::poly_q::degree > coeffs, coeffs0;
	fmpz_mod_poly_t poly, poly2, zero;
	fmpz *rc = _fmpz_vec_init(ETA);
	gr_t beta0, gt;
	fmpz_t t, u, q, r0[ETA];
	fmpz_mod_ctx_t ctx_q;
	vector < params::poly_q > d;
	params::poly_q s0[V];

	fmpz_init(t);
	fmpz_init(u);
	fmpz_init(q);
	fmpz_set_mpz(q, params::poly_q::moduli_product());
	fmpz_mod_ctx_init(ctx_q, q);

	fmpz_set_mpz(q, params::poly_q::moduli_product());
	fmpz_mod_poly_init(poly, ctx);
	fmpz_mod_poly_init(poly2, ctx);
	fmpz_mod_poly_init(zero, ctx);
	gr_init(gt);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init(coeffs[i]);
		mpz_init(coeffs0[i]);
	}
	gr_init(prover_y[TAU]);
	for (size_t i = 0; i < TAU; i++) {
		gr_init(prover_y[i]);
		for (size_t j = 0; j < 3; j++) {
			for (size_t k = 0; k < V; k++) {
				for (size_t l = 0; l < params::poly_q::degree; l++) {
					mpz_init(v[j][i][k][l]);
				}
			}
		}
	}
	gr_init(beta0);
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_init(prover_beta[i][j]);
			gr_init(prover_wt[i][j]);
			for (size_t k = 0; k < ETA; k++) {
				fmpz_init(prover_r[i][j][k]);
				fmpz_randm(prover_r[i][j][k], prng, q);
			}
		}
	}
	for (size_t i = 0; i < ETA; i++) {
		fmpz_init(r0[i]);
		fmpz_randm(r0[i], prng, q);
		/* the masks are Z_q values, so they live in the Y^0 coordinate and the
		 * Y^1 coordinate starts empty */
		fmpz_randm(rh[i].c0, prng, q);
		fmpz_zero(rh[i].c1);
	}
	for (size_t i = 0; i < V; i++) {
		fmpz_mod_poly_randtest(h[0][i][0], prng, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(h[1][i][0], prng, params::poly_q::degree, ctx);
		fmpz_mod_poly_zero(h[0][i][1], ctx);
		fmpz_mod_poly_zero(h[1][i][1], ctx);
	}

	/* Generate s_0 = Z_q^vN, h = Z_q^2vn. */
	for (size_t i = 0; i < V; i++) {
		fmpz_mod_poly_randtest(poly, prng, params::poly_q::degree, ctx);
		poly_to(s0[i], poly, ctx);
	}

	/* Compute d = -A * s_0 and convert back from NTT due to commitment. */
	d.resize(R);
	for (int j = 0; j < R; j++) {
		d[j] = 0;
		for (int k = 0; k < V; k++) {
			d[j] = d[j] - A[j][k] * s0[k];
		}
		d[j].invntt_pow_invphi();
	}
	bdlop_commit(com, d, key, rd);

	/* Compute the v_{i,j} by the three-round extraction, one coefficient
	 * position at a time and one prime at a time, recombining by CRT. */
	{
		const size_t N = params::poly_q::degree;
		const size_t NM = params::poly_q::nmoduli;
		aex_u64 P[2], wt[2], w4[2];
		aex_tw_t TT[2], T4[2];
		for (size_t j = 0; j < NM; j++) {
			P[j] = nfl::params < uint64_t >::P[j];
			for (ulong g = 2;; g++) {
				wt[j] = aex_pow(g, (P[j] - 1) / TAU, P[j]);
				if (aex_pow(wt[j], TAU / 2, P[j]) != 1) break;
			}
			for (ulong g = 2;; g++) {
				w4[j] = aex_pow(g, (P[j] - 1) / AEX_N4, P[j]);
				if (aex_pow(w4[j], AEX_N4 / 2, P[j]) != 1) break;
			}
			aex_tw_init(TT[j], TAU, wt[j], P[j]);
			aex_tw_init(T4[j], AEX_N4, w4[j], P[j]);
		}
		/* P0^{-1} mod P1, for the CRT recombination */
		aex_u64 pinv = aex_pow(P[0] % P[1], P[1] - 2, P[1]);

		aex_u64 *sres = new aex_u64[NM * N * TAU];
		aex_u64 *s0res = new aex_u64[NM * N];
		aex_u64 *buf4 = new aex_u64[AEX_N4];
		aex_u64 *buf4b = new aex_u64[AEX_N4];
		aex_u64 *buft = new aex_u64[TAU];
		static aex_u64 out[2][3][TAU];
		mpz_t pz;
		mpz_init(pz);

		for (size_t k = 0; k < V; k++) {
			/* data()[j * N + l] is already coefficient l modulo P[j], so the
			 * residues can be read straight out without going through mpz. */
			s0[k].invntt_pow_invphi();
			{
				const uint64_t *d = s0[k].data();
				for (size_t j = 0; j < NM; j++) {
					for (size_t l = 0; l < N; l++) {
						s0res[j * N + l] = d[j * N + l];
					}
				}
			}
			s0[k].ntt_pow_phi();
			for (size_t i = 0; i < TAU; i++) {
				s[i][k].invntt_pow_invphi();
				const uint64_t *d = s[i][k].data();
				for (size_t j = 0; j < NM; j++) {
					for (size_t l = 0; l < N; l++) {
						sres[(j * N + l) * TAU + i] = d[j * N + l];
					}
				}
				s[i][k].ntt_pow_phi();
			}
			for (size_t l = 0; l < N; l++) {
				for (size_t j = 0; j < NM; j++) {
					aex_extract(s0res[j * N + l], sres + (j * N + l) * TAU,
							out[j], TT[j], T4[j], buf4, buf4b, buft);
				}
				for (size_t jj = 0; jj < 3; jj++) {
					for (size_t i = 0; i < TAU; i++) {
						/* CRT: r0 + P0 * ((r1 - r0) * P0^{-1} mod P1) */
						aex_u64 r0 = out[0][jj][i], r1 = out[1][jj][i];
						aex_u64 d = aex_sub(r1 % P[1], r0 % P[1], P[1]);
						aex_u64 t2 = aex_mul(d, pinv, P[1]);
						__uint128_t val = (__uint128_t) P[0] * t2 + r0;
						unsigned long limb[2] = {
							(unsigned long) (val & 0xffffffffffffffffULL),
							(unsigned long) (val >> 64)
						};
						mpz_import(v[jj][i][k][l], 2, -1, sizeof(limb[0]), 0, 0,
								limb);
					}
				}
			}
		}
		for (size_t j = 0; j < NM; j++) {
			aex_tw_clear(TT[j]);
			aex_tw_clear(T4[j]);
		}
		mpz_clear(pz);
		delete[]sres;
		delete[]s0res;
		delete[]buf4;
		delete[]buf4b;
		delete[]buft;
	}

	/* Encode H's as larger NTT. H_{i,j} has one codeword per component k of
	 * s_i, so it is indexed by k as well; delta_j is 1 only for j = 0. */
	for (size_t k = 0; k < V; k++) {
		fmpz_mod_poly_zero(zero, ctx);
		poly_from(poly, s0[k], ctx);
		aex_encode(H0[k], poly, zero, (const fmpz *) r0, ctx);
		gr_comp(rc, rh, 0);
		aex_encode(_H[k], h[0][k][0], h[1][k][0], rc, ctx);
		for (size_t i = 0; i < TAU; i++) {
			for (size_t j = 0; j < 3; j++) {
				for (size_t l = 0; l < params::poly_q::degree; l++) {
					flint_poly_set_coeff_mpz(poly, l, v[j][i][k][l], ctx_q);
				}
				if (j == 0) {
					poly_from(zero, s[i][k], ctx_q);
				} else {
					fmpz_mod_poly_zero(zero, ctx_q);
				}
				aex_encode(H[i][j][k], zero, poly,
						(const fmpz *) prover_r[i][j], ctx);
			}
		}
		fmpz_mod_poly_zero(zero, ctx);
	}

	/* Steps 5 and 6: commit to the columns and send the root, then draw the
	 * challenge from it. */
	aex_tree_build(aex_tree);
	memcpy(o.root, aex_tree_root(aex_tree), BLAKE3_OUT_LEN);
	pismall_hash(x, beta0, prover_beta, q, com, o.root);

	/* l_i(x) for i = 0..TAU, indexed by i so l_0(x) survives. */
	if (!aex_lagrange(prover_y, x, ctx_q)) {
		/* only reachable when l_0(x) is a zero divisor, at deg/p^2 */
		return 0;
	}
	/* l_i(x) l_0(x)^j, shared by _rf here and by the identities at the
	 * verifier; the j-th power is of l_0(x), not of some l_i(x). */
	for (size_t i = 0; i < TAU; i++) {
		gr_set(prover_wt[i][0], prover_y[i + 1]);
		gr_mul(prover_wt[i][1], prover_wt[i][0], prover_y[0], ctx_q);
		gr_mul(prover_wt[i][2], prover_wt[i][1], prover_y[0], ctx_q);
	}
	/* Compute f = s_0 * l_0(x). */
	for (int i = 0; i < V; i++) {
		poly_from(poly, s0[i], ctx_q);
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_scalar_mul_fmpz(f[i][c], poly,
					c ? prover_y[0].c1 : prover_y[0].c0, ctx_q);
		}
	}
	/* Compute remaining f = f(x) = \Sum s_i * l_i(x). */
	for (size_t i = 1; i <= TAU; i++) {
		for (int j = 0; j < V; j++) {
			poly_from(poly, s[i - 1][j], ctx_q);
			for (int c = 0; c < 2; c++) {
				fmpz_mod_poly_scalar_mul_fmpz(poly2, poly,
						c ? prover_y[i].c1 : prover_y[i].c0, ctx_q);
				fmpz_mod_poly_add(f[j][c], f[j][c], poly2, ctx_q);
			}
		}
	}

	/* Compute _rf = r0 * l_0(x) + Sum r_i,j * l_i(x) * l_0(x)^j */
	/* and _rh = r0 * beta_0 + Sum r_i,j * beta_i,j */
	for (size_t k = 0; k < ETA; k++) {
		gr_scalar(rf[k], prover_y[0], r0[k], ctx);
		gr_scalar(gt, beta0, r0[k], ctx);
		gr_add(rh[k], rh[k], gt, ctx);
		for (size_t i = 1; i <= TAU; i++) {
			for (size_t j = 0; j < 3; j++) {
				gr_scalar(gt, prover_wt[i - 1][j], prover_r[i - 1][j][k],
						ctx_q);
				gr_add(rf[k], rf[k], gt, ctx_q);
				gr_scalar(gt, prover_beta[i - 1][j], prover_r[i - 1][j][k],
						ctx_q);
				gr_add(rh[k], rh[k], gt, ctx_q);
			}
		}
	}

	/* Compute _h = h + s_0 * beta_0 + \sum beta_i,j * (\delta_i * si, v_i,j) */
	for (size_t k = 0; k < V; k++) {
		poly_from(poly, s0[k], ctx);
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_scalar_mul_fmpz(poly2, poly,
					c ? beta0.c1 : beta0.c0, ctx);
			fmpz_mod_poly_add(h[0][k][c], h[0][k][c], poly2, ctx);
		}
		for (size_t i = 1; i <= TAU; i++) {
			for (size_t j = 0; j < 3; j++) {
				const gr_t & b = prover_beta[i - 1][j];
				if (j == 0) {
					/* i runs from 1 to TAU, so this has to be s[i - 1] like
					 * every other access in this loop; s[i] read one row past
					 * the end of the matrix on the last iteration. */
					poly_from(poly, s[i - 1][k], ctx_q);
					for (int c = 0; c < 2; c++) {
						fmpz_mod_poly_scalar_mul_fmpz(poly2, poly,
								c ? b.c1 : b.c0, ctx_q);
						fmpz_mod_poly_add(h[0][k][c], h[0][k][c], poly2, ctx);
					}
				}
				for (size_t l = 0; l < params::poly_q::degree; l++) {
					flint_poly_set_coeff_mpz(poly, l, v[j][i - 1][k][l],
							ctx_q);
				}
				for (int c = 0; c < 2; c++) {
					fmpz_mod_poly_scalar_mul_fmpz(poly2, poly,
							c ? b.c1 : b.c0, ctx_q);
					fmpz_mod_poly_add(h[1][k][c], h[1][k][c], poly2, ctx);
				}
			}
		}
	}

	/* Steps 10 and 11: the opened columns and their paths. */
	aex_sample_I(o.I, o.root, f, rf, h, rh, ctx);
	aex_open(o);
	aex_tree_clear(aex_tree);

	fmpz_clear(t);
	fmpz_clear(u);
	fmpz_clear(q);
	gr_clear(gt);
	_fmpz_vec_clear(rc, ETA);
	fmpz_mod_poly_clear(poly, ctx);
	fmpz_mod_poly_clear(poly2, ctx);
	fmpz_mod_poly_clear(zero, ctx);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
		mpz_clear(coeffs0[i]);
	}
	gr_clear(prover_y[TAU]);
	for (size_t i = 0; i < TAU; i++) {
		gr_clear(prover_y[i]);
		for (size_t j = 0; j < 3; j++) {
			for (size_t k = 0; k < V; k++) {
				for (size_t l = 0; l < params::poly_q::degree; l++) {
					mpz_clear(v[j][i][k][l]);
				}
			}
		}
	}
	gr_clear(beta0);
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_clear(prover_beta[i][j]);
			gr_clear(prover_wt[i][j]);
			for (size_t k = 0; k < ETA; k++) {
				fmpz_clear(prover_r[i][j][k]);
			}
		}
	}
	for (size_t i = 0; i < ETA; i++) {
		fmpz_clear(r0[i]);
	}
	fmpz_mod_ctx_clear(ctx_q);
	return 1;
}

static int pismall_verifier(commit_t & com, fmpz_mod_poly_t f[V][2],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][2], gr_t rh[ETA],
		vector < params::poly_q > rd, comkey_t & key,
		fmpz_mod_poly_t lag[TAU + 1], flint_rand_t prng,
		const fmpz_mod_ctx_t ctx, const aex_open_t & o) {
	array < mpz_t, params::poly_q::degree > coeffs;
	fmpz_mod_poly_t poly, poly2, u0, u1, w, r[R][2];
	fmpz_mod_ctx_t ctx_q;
	fmpz_t q, nrb;
	gr_t x, beta0, l0i;
	gr_t (*beta)[3] = new gr_t[TAU][3];
	gr_t *vlev = new gr_t[TAU + 1];
	params::poly_q one = 1;
	vector < params::poly_q > m;
	int result;

	fmpz_init(q);
	fmpz_init(nrb);
	gr_init(x);
	gr_init(beta0);
	gr_init(l0i);
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_init(beta[i][j]);
		}
	}
	for (size_t i = 0; i <= TAU; i++) {
		gr_init(vlev[i]);
	}

	fmpz_set_mpz(q, params::poly_q::moduli_product());
	pismall_hash(x, beta0, beta, q, com, o.root);

	fmpz_mod_ctx_init(ctx_q, q);
	fmpz_mod_poly_init(poly, ctx_q);
	fmpz_mod_poly_init(poly2, ctx_q);
	fmpz_mod_poly_init(u0, ctx_q);
	fmpz_mod_poly_init(u1, ctx_q);
	fmpz_mod_poly_init(w, ctx_q);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}
	for (int i = 0; i < R; i++) {
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_init(r[i][c], ctx_q);
			fmpz_mod_poly_zero(r[i][c], ctx_q);
		}
	}

	result = aex_lagrange(vlev, x, ctx_q);
	if (result) {
		for (int i = 1; i <= TAU; i++) {
			for (int j = 0; j < R; j++) {
				poly_from(poly, t[i - 1][j], ctx_q);
				for (int c = 0; c < 2; c++) {
					fmpz_mod_poly_scalar_mul_fmpz(poly2, poly,
							c ? vlev[i].c1 : vlev[i].c0, ctx_q);
					fmpz_mod_poly_add(r[j][c], r[j][c], poly2, ctx_q);
				}
			}
		}

		/* Compute d = A * _f. */
		for (int j = 0; j < V; j++) {
			for (int c = 0; c < 2; c++) {
				for (int i = 0; i < R; i++) {
					poly_to(one, f[j][c], ctx_q);
					one = one * A[i][j];
					poly_from(poly, one, ctx_q);
					fmpz_mod_poly_sub(r[i][c], r[i][c], poly, ctx_q);
				}
			}
		}
		result = gr_inv(l0i, vlev[0], ctx_q);
	}

	m.resize(R);
	for (int i = 0; i < R; i++) {
		m[i] = 0;
	}
	if (result) {
		/* m = r / l_0(x), a multiplication by a scalar of the extension:
		 * (r0 + r1 Y)(a + b Y) = (r0 a + NR r1 b) + (r0 b + r1 a) Y. The
		 * committed value is a Z_q element, so the Y^1 coordinate of the
		 * quotient has to come out zero. */
		gr_mul_nr(nrb, l0i.c1, ctx_q);
		for (int i = 0; i < R; i++) {
			fmpz_mod_poly_scalar_mul_fmpz(u0, r[i][0], l0i.c0, ctx_q);
			fmpz_mod_poly_scalar_mul_fmpz(w, r[i][1], nrb, ctx_q);
			fmpz_mod_poly_add(u0, u0, w, ctx_q);
			fmpz_mod_poly_scalar_mul_fmpz(u1, r[i][0], l0i.c1, ctx_q);
			fmpz_mod_poly_scalar_mul_fmpz(w, r[i][1], l0i.c0, ctx_q);
			fmpz_mod_poly_add(u1, u1, w, ctx_q);
			result &= fmpz_mod_poly_is_zero(u1, ctx_q);
			poly_to(m[i], u0, ctx_q);
			m[i].invntt_pow_invphi();
		}
		one = 1;
		one.ntt_pow_phi();
		result &= bdlop_open(com, m, key, rd, one);

		/* Step 12: the opened columns must match the committed root, the index
		 * set must be the one the transcript determines, and both encoding
		 * identities must hold. */
		size_t I[ETA];
		aex_sample_I(I, o.root, f, rf, h, rh, ctx);
		for (size_t n = 0; n < ETA; n++) {
			result &= (I[n] == o.I[n]);
			result &= aex_path_verify(o.col + n * AEX_COLBYTES,
					o.path + n * (o.levels - 1) * BLAKE3_OUT_LEN, o.I[n],
					o.root);
		}
		result &= aex_identities(o, f, rf, h, rh, x, beta0, beta, lag, ctx);
	}

	fmpz_clear(q);
	fmpz_clear(nrb);
	gr_clear(x);
	gr_clear(beta0);
	gr_clear(l0i);
	fmpz_mod_poly_clear(poly, ctx_q);
	fmpz_mod_poly_clear(poly2, ctx_q);
	fmpz_mod_poly_clear(u0, ctx_q);
	fmpz_mod_poly_clear(u1, ctx_q);
	fmpz_mod_poly_clear(w, ctx_q);
	for (int i = 0; i < R; i++) {
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_clear(r[i][c], ctx_q);
		}
	}
	fmpz_mod_ctx_clear(ctx_q);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			gr_clear(beta[i][j]);
		}
	}
	for (size_t i = 0; i <= TAU; i++) {
		gr_clear(vlev[i]);
	}
	delete[]beta;
	delete[]vlev;
	return result;
}

static void test(flint_rand_t rand) {
	fmpz_t q, a[TAU];
	gr_t x, rf[ETA], rh[ETA];
	fmpz_mod_poly_t poly;
	fmpz_mod_ctx_t ctx, ctx_q;
	comkey_t key;
	commit_t com;
	vector < params::poly_q > rd;
	fmpz_mod_poly_t f[V][2], lag[TAU + 1], h[2][V][2];

	fmpz_init(q);
	gr_init(x);

	fmpz_set_mpz(q, params::poly_q::moduli_product());
	fmpz_mod_ctx_init(ctx_q, q);

	fmpz_set_mpz(q, params::poly_q::moduli_product());
	fmpz_mod_ctx_init(ctx, q);
	/* Evaluation points for the Reed-Solomon encoding live in Z_q. */
	aex_ntt_setup(ctx);
	fmpz_mod_poly_init(poly, ctx);
	for (int i = 0; i < V; i++) {
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_init(f[i][c], ctx);
			fmpz_mod_poly_init(h[0][i][c], ctx);
			fmpz_mod_poly_init(h[1][i][c], ctx);
		}
	}
	/* Interpolation nodes are the TAU-th roots of unity, so that l_0 is
	 * X^TAU - 1 and evaluation at the nodes is a length-TAU NTT. Nothing in
	 * the protocol needs them random: soundness comes from x. */
	{
		fmpz_t w;
		fmpz_init(w);
		aex_root_tau(w, ctx);
		for (size_t i = 0; i < TAU; i++) {
			fmpz_init(a[i]);
			fmpz_mod_pow_ui(a[i], w, i, ctx);
		}
		fmpz_clear(w);
	}

	for (int i = 0; i < R; i++) {
		for (int j = 0; j < V; j++) {
			fmpz_mod_poly_randtest(poly, rand, params::poly_q::degree, ctx);
			poly_to(A[i][j], poly, ctx);
		}
	}
	for (size_t i = 0; i < ETA; i++) {
		gr_init(rf[i]);
		gr_init(rh[i]);
	}

	/* Create a total of TAU relations t_i = A * s_i */
	for (int i = 0; i < TAU; i++) {
		fmpz_mod_poly_init(lag[i], ctx);
		for (int j = 0; j < V; j++) {
			s[i][j] = nfl::hwt_dist {
			2 *DEGREE / 3};
			s[i][j].ntt_pow_phi();
		}
		for (int j = 0; j < R; j++) {
			t[i][j] = 0;
			for (int k = 0; k < V; k++) {
				t[i][j] = t[i][j] + A[j][k] * s[i][k];
			}
		}
	}
	fmpz_mod_poly_init(lag[TAU], ctx);

	rd.resize(WIDTH);
	TEST_BEGIN("conversion is correct") {
		for (int i = 0; i < R; i++) {
			for (int j = 0; j < V; j++) {
				poly_from(f[j][0], A[i][j], ctx);
				poly_to(rd[0], f[j][0], ctx);
				TEST_ASSERT(rd[0] == A[i][j], end);
			}
		}
		fmpz_mod_poly_zero(poly, ctx_q);
		fmpz_mod_poly_set_coeff_ui(poly, params::poly_q::degree, 1, ctx_q);
		fmpz_mod_poly_set_coeff_ui(poly, 0, 1, ctx_q);

		for (int i = 0; i < R; i++) {
			for (int j = 0; j < V; j++) {
				rd[0] = A[i][j] * A[i][j];
				poly_from(f[j][0], A[i][j], ctx_q);
				fmpz_mod_poly_mulmod(f[j][0], f[j][0], f[j][0], poly, ctx_q);
				poly_to(rd[1], f[j][0], ctx_q);
				TEST_ASSERT(rd[0] == rd[1], end);
			}
		}
	} TEST_END;

	pismall_setup(lag, a, q, rand, ctx);

	bdlop_keygen(key);
	bdlop_sample_rand(rd);

	TEST_ONCE("encoding is linear in message and randomness") {
		aex_code_t *ca = new aex_code_t, *cb = new aex_code_t;
		aex_code_t *cs = new aex_code_t;
		fmpz_mod_poly_t a0, a1, b0, b1, s0p, s1p;
		fmpz_t ra[ETA], rb[ETA], rs[ETA], ua, ub, us;
		int ok = 1, differs = 0;

		fmpz_mod_poly_init(a0, ctx); fmpz_mod_poly_init(a1, ctx);
		fmpz_mod_poly_init(b0, ctx); fmpz_mod_poly_init(b1, ctx);
		fmpz_mod_poly_init(s0p, ctx); fmpz_mod_poly_init(s1p, ctx);
		fmpz_init(ua); fmpz_init(ub); fmpz_init(us);
		fmpz_mod_poly_randtest(a0, rand, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(a1, rand, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(b0, rand, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(b1, rand, params::poly_q::degree, ctx);
		fmpz_mod_poly_add(s0p, a0, b0, ctx);
		fmpz_mod_poly_add(s1p, a1, b1, ctx);
		for (size_t i = 0; i < ETA; i++) {
			fmpz_init(ra[i]); fmpz_init(rb[i]); fmpz_init(rs[i]);
			fmpz_randm(ra[i], rand, q);
			fmpz_randm(rb[i], rand, q);
			fmpz_mod_add(rs[i], ra[i], rb[i], ctx);
		}

		aex_encode(*ca, a0, a1, (const fmpz *) ra, ctx);
		aex_encode(*cb, b0, b1, (const fmpz *) rb, ctx);
		aex_encode(*cs, s0p, s1p, (const fmpz *) rs, ctx);

		/* Encode(a) + Encode(b) must be Encode(a + b) symbol by symbol; this
		 * is exactly what the step 12 identities rely on. */
		size_t probe[5] = { 0, 1, 2, 999, AEX_COLS - 1 };
		for (size_t n = 0; n < 5; n++) {
			aex_unpack(ua, ca, probe[n]);
			aex_unpack(ub, cb, probe[n]);
			aex_unpack(us, cs, probe[n]);
			fmpz_mod_add(ua, ua, ub, ctx);
			ok &= fmpz_equal(ua, us);
			aex_unpack(ua, ca, probe[n]);
			differs |= !fmpz_equal(ua, us);
		}
		/* and distinct messages must not encode to the same codeword */
		ok &= differs;

		fmpz_mod_poly_clear(a0, ctx); fmpz_mod_poly_clear(a1, ctx);
		fmpz_mod_poly_clear(b0, ctx); fmpz_mod_poly_clear(b1, ctx);
		fmpz_mod_poly_clear(s0p, ctx); fmpz_mod_poly_clear(s1p, ctx);
		fmpz_clear(ua); fmpz_clear(ub); fmpz_clear(us);
		for (size_t i = 0; i < ETA; i++) {
			fmpz_clear(ra[i]); fmpz_clear(rb[i]); fmpz_clear(rs[i]);
		}
		delete ca; delete cb; delete cs;
		TEST_ASSERT(ok == 1, end);
	} TEST_END;

	TEST_ONCE("column commitment detects tampering") {
		aex_tree_t tree;
		uint8_t *col = NULL, *path = NULL;
		int ok = 1;

		aex_open_t o0;
		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o0);
		aex_open_clear(o0);
		aex_tree_build(tree);
		col = new uint8_t[AEX_COLBYTES];
		path = new uint8_t[(tree.levels - 1) * BLAKE3_OUT_LEN];
		size_t c = 1234 % AEX_COLS;
		aex_column(col, c);
		aex_path(path, tree, c);

		/* an honest opening verifies */
		ok &= (aex_path_verify(col, path, c, aex_tree_root(tree)) == 1);
		/* a flipped bit anywhere in the column is caught */
		col[0] ^= 1;
		ok &= (aex_path_verify(col, path, c, aex_tree_root(tree)) == 0);
		col[0] ^= 1;
		col[AEX_COLBYTES - 1] ^= 0x80;
		ok &= (aex_path_verify(col, path, c, aex_tree_root(tree)) == 0);
		col[AEX_COLBYTES - 1] ^= 0x80;
		/* a flipped bit in the path is caught */
		path[0] ^= 1;
		ok &= (aex_path_verify(col, path, c, aex_tree_root(tree)) == 0);
		path[0] ^= 1;
		/* the column only opens at the index it was committed to */
		ok &= (aex_path_verify(col, path, c ^ 1, aex_tree_root(tree)) == 0);
		/* and the honest opening still verifies afterwards */
		ok &= (aex_path_verify(col, path, c, aex_tree_root(tree)) == 1);

		delete[]col;
		delete[]path;
		aex_tree_clear(tree);
		TEST_ASSERT(ok == 1, end);
	} TEST_END;

	TEST_ONCE("AEX proof is consistent") {
		int ok = 1;
		/* The soundness error of one pass is not negligible, so the protocol
		 * is run AEX_REPS times and every pass must verify. */
		for (int rep = 0; rep < AEX_REPS; rep++) {
			aex_open_t o;
			pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
			ok &= pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand, ctx,
					o);
			aex_open_clear(o);
		}
		TEST_ASSERT(ok == 1, end);
	} TEST_END;

	TEST_ONCE("challenge really lives in the extension") {
		aex_open_t o;
		int live, any = 0;

		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		/* Were any of these identically zero, the Y^1 identity would read
		 * 0 == 0 and the extension would buy no soundness at all, while every
		 * other test still passed. Check the openings carry real data in the
		 * second coordinate, and that the proof verifies anyway, so that the
		 * Y^1 identity is satisfied rather than vacuous. */
		/* Y^2 - AEX_NR is only irreducible while AEX_NR is a non-residue
		 * modulo every prime of the basis. If that ever stops holding the
		 * extension silently collapses and the soundness claim with it. */
		live = 1;
		for (size_t i = 0; i < params::poly_q::nmoduli; i++) {
			fmpz_t pi, e, w;
			fmpz_init_set_ui(pi, nfl::params < uint64_t >::P[i]);
			fmpz_init(e);
			fmpz_init(w);
			fmpz_sub_ui(e, pi, 1);
			fmpz_fdiv_q_2exp(e, e, 1);
			fmpz_set_ui(w, AEX_NR);
			fmpz_powm(w, w, e, pi);          /* Euler: -1 iff a non-residue */
			fmpz_sub_ui(e, pi, 1);
			live &= fmpz_equal(w, e);
			fmpz_clear(pi);
			fmpz_clear(e);
			fmpz_clear(w);
		}
		live &= !fmpz_is_zero(x.c1);
		for (int k = 0; k < V; k++) {
			live &= !fmpz_mod_poly_is_zero(f[k][1], ctx);
			live &= !fmpz_mod_poly_is_zero(h[0][k][1], ctx);
			live &= !fmpz_mod_poly_is_zero(h[1][k][1], ctx);
		}
		for (size_t i = 0; i < ETA; i++) {
			any |= !fmpz_is_zero(rf[i].c1);
			any |= !fmpz_is_zero(rh[i].c1);
		}
		live &= any;
		live &= pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		aex_open_clear(o);
		TEST_ASSERT(live == 1, end);
	} TEST_END;

	TEST_ONCE("AEX proof rejects a tampered opening") {
		aex_open_t o;
		int rejected = 1;

		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		/* an honest proof verifies */
		rejected &= (pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand,
						ctx, o) == 1);
		/* corrupting one opened symbol must break an encoding identity */
		o.col[0] ^= 1;
		rejected &= (pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand,
						ctx, o) == 0);
		o.col[0] ^= 1;
		/* so must swapping which column was opened */
		size_t keep = o.I[0];
		o.I[0] ^= 1;
		rejected &= (pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand,
						ctx, o) == 0);
		o.I[0] = keep;
		/* and the honest proof still verifies afterwards */
		rejected &= (pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand,
						ctx, o) == 1);
		aex_open_clear(o);
		TEST_ASSERT(rejected == 1, end);
	} TEST_END;

	printf("\n** Benchmarks for lattice-based AEX proof:\n\n");
	BENCH_SMALL("pismall_setup", pismall_setup(lag, a, q, rand, ctx));
	aex_open_t ob;
	BENCH_SMALL("pismall_prover", { pismall_prover(com, x, f, rf, h, rh, rd,
						key, lag, rand, ctx, ob); aex_open_clear(ob); });
	pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, ob);
	BENCH_SMALL("pismall_verifier", pismall_verifier(com, f, rf, h, rh, rd, key,
					lag, rand, ctx, ob));
	aex_open_clear(ob);

  end:
	for (int i = 0; i < V; i++) {
		for (int c = 0; c < 2; c++) {
			fmpz_mod_poly_clear(f[i][c], ctx);
			fmpz_mod_poly_clear(h[0][i][c], ctx);
			fmpz_mod_poly_clear(h[1][i][c], ctx);
		}
	}
	for (int i = 0; i <= TAU; i++) {
		fmpz_mod_poly_clear(lag[i], ctx);
	}
	for (size_t i = 0; i < TAU; i++) {
		fmpz_clear(a[i]);
	}
	for (size_t i = 0; i < ETA; i++) {
		gr_clear(rf[i]);
		gr_clear(rh[i]);
	}
	fmpz_mod_poly_clear(poly, ctx);
	aex_ntt_clear();
	fmpz_mod_ctx_clear(ctx);
	fmpz_mod_ctx_clear(ctx_q);
	fmpz_clear(q);
	gr_clear(x);
}

int main() {
	flint_rand_t rand;
	flint_rand_init(rand);
	pismall_alloc();

	printf("\n** Tests for lattice-based AEX proof:\n\n");
	test(rand);

	pismall_free();
	flint_rand_clear(rand);

	return test_failures() != 0;
}
