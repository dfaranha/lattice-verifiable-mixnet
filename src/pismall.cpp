#include <math.h>
#include <stdlib.h>
#include <initializer_list>

#include <flint/flint.h>
#include <flint/fmpz_vec.h>
#include <flint/fmpz_mod_poly.h>

#include "flint_util.h"

#include "common.h"
#include "pismall.h"
#include "serial.h"
#include "test.h"
#include "bench.h"
#include <assert.h>
#include "blake3.h"

/* Columns opened. Lemma 2 of the paper bounds the proximity part of the
 * soundness error by 2 max((g / (l - ETA))^ETA, (1 - 2 (g - g') / 3l)^ETA) over
 * g' <= g <= l, with g' = 2N + ETA the message length and l = AEX_COLS the code
 * length. The two balance at g = 13000-odd, and 451 is where that crosses
 * 2^-LEVEL; 452 for a little room. It used to be 325, which is 2^-95 -- enough
 * when the proof was run twice, and this one runs once. See SOUNDNESS.md 5.5.
 */
#define ETA         452
/* Shape of the relation. The mix-net's own instance of this proof has
 * R = HEIGHT + 2 rows and V = WIDTH + 3 components; the proof of shuffle links
 * this file with the shape of a BDLOP commitment equation, R = HEIGHT + 1 and
 * V = WIDTH + 1, to show that each committed sigma_i is a ring constant. */
#ifndef PISMALL_R
#define PISMALL_R   (HEIGHT+2)
#endif
#ifndef PISMALL_V
#define PISMALL_V   (WIDTH+3)
#endif
#define R           PISMALL_R
#define V           PISMALL_V
/* Number of relations proven at once. This drives every large buffer below, so
 * it can be overridden (e.g. make CONFIG=-DTAU=16) to test on a small machine.
 * It must be a power of two: the interpolation nodes are the TAU-th roots of
 * unity, which is what makes l_0 equal X^TAU - 1 and evaluation at the nodes a
 * length-TAU NTT. The paper's 1000 relations are padded to 1024 with zero
 * witnesses, which costs nothing in soundness. */
#ifndef TAU
#define TAU         1024
#endif

/* --- GR(q, AEX_DEG), the challenge domain ---------------------------------
 * A challenge drawn from Z_q is worth deg/q, which at q = 2^88 is not enough
 * for one pass; drawing it from the Galois extension of degree AEX_DEG makes
 * it deg/q^AEX_DEG. Y^AEX_DEG - AEX_NR is irreducible because AEX_NR is a
 * non-residue modulo q and q = 1 mod 4. See the tower below, and SOUNDNESS.md
 * section 5.5.
 *
 * q = 2^88 - 25 2^16 + 1 is 1 mod 2^16, so -1 and 2 are squares, and 1 mod 3,
 * which makes 3 a square too. 5 is the smallest non-residue; the test at the
 * bottom of this file checks that rather than assuming it. Being 5,
 * multiplying by it is three modular additions instead of a multiply and a
 * reduction. */
#define AEX_NR      5

/* Coefficient sets a witness component can be proven to live in. The pointwise
 * identity is the product of (f - v) over the set, so its degree is the size
 * of the set: AEX_TER is cubic, the other two quadratic. Three quotient levels
 * cover all of them, the quadratics simply leaving the top one zero, so the
 * codeword layout does not change with the set.
 *
 * AEX_ZERO and AEX_SCALAR exist for the proof of shuffle, which needs a
 * committed element to be a ring constant. That is a pointwise property, and
 * an exact one even here: the identity for AEX_ZERO is f = 0, whose only root
 * in Z_q is 0 whether or not q is composite, so unlike the sets above it says
 * the same thing over Z_q as it does in each CRT component. AEX_SCALAR is the
 * component-level declaration that spells "constant": unconstrained at
 * coefficient 0, zero at every other. */
typedef enum {
	AEX_TER = 0,                /* {-1, 0, 1}     */
	AEX_BIN,                    /* {0, 1}         */
	AEX_SGN,                    /* {-1, 1}        */
	AEX_ZERO,                   /* {0}            */
	AEX_FREE,                   /* no constraint  */
	AEX_SCALAR                  /* free at coefficient 0, zero elsewhere */
} aex_set_t;

/* The set each component of the witness lives in, ternary unless a caller says
 * otherwise. */
static aex_set_t aex_sets[V] = { };

/* The set a single coefficient lives in. Every declaration but AEX_SCALAR
 * applies the same set at every coefficient position. */
static inline aex_set_t aex_set_at(size_t k, size_t l) {
	if (aex_sets[k] != AEX_SCALAR) {
		return aex_sets[k];
	}
	return (l == 0) ? AEX_FREE : AEX_ZERO;
}

/* r <- AEX_NR * a, by addition. Must double into a temporary: gr_inv calls
 * this in place, and accumulating into r would compound the doubling. */
static void gr_mul_nr(fmpz_t r, const fmpz_t a, const fmpz_mod_ctx_t ctx) {
	fmpz_t d;

	fmpz_init(d);
	fmpz_mod_add(d, a, a, ctx);
	fmpz_mod_add(d, d, d, ctx);
	fmpz_mod_add(r, d, a, ctx);
	fmpz_clear(d);
}

/* Degree of the challenge extension over Z_q, 2 or 4. Section 6.5: the
 * algebraic term of Lemma 2 is 18 TAU / q^AEX_DEG. With q two 44-bit primes it
 * was 18 TAU / p_min^AEX_DEG, since an adversary worked modulo one of them,
 * and degree 2 gave only 2^-74, so it was 4. With q prime, degree 2 is
 * 2^-160 and one pass carries the whole thing; 4 is kept as an option. */
#ifndef AEX_DEG
#define AEX_DEG     2
#endif
static_assert(AEX_DEG == 2 || AEX_DEG == 4, "the extension is quadratic or quartic");

/* GR(q, AEX_DEG) as a tower: c[0] + c[1] Z over Z_q, with Z^2 = AEX_NR, and
 * at degree 4 u + v Y over that, with Y^2 = Z. So Z^2 = AEX_NR, or Y^4 =
 * AEX_NR, and X^AEX_DEG - AEX_NR is irreducible modulo q exactly when
 * AEX_NR is a non-residue and, at degree 4, q = 1 mod 4, both of which the
 * test at the bottom of this file checks rather than assumes. The coordinates
 * are in tower order, (1, Z, Y, ZY), which is a basis like any other:
 * everything outside this block is Z_q-linear in them and does not care
 * which. */
typedef struct {
	fmpz_t c[AEX_DEG];
} gr_t;

static void gr_init(gr_t & a) {
	for (int i = 0; i < AEX_DEG; i++) fmpz_init(a.c[i]);
}

static void gr_clear(gr_t & a) {
	for (int i = 0; i < AEX_DEG; i++) fmpz_clear(a.c[i]);
}

static void gr_one(gr_t & a) {
	fmpz_one(a.c[0]);
	for (int i = 1; i < AEX_DEG; i++) fmpz_zero(a.c[i]);
}

static void gr_set(gr_t & r, const gr_t & a) {
	for (int i = 0; i < AEX_DEG; i++) fmpz_set(r.c[i], a.c[i]);
}

static void gr_add(gr_t & r, const gr_t & a, const gr_t & b,
		const fmpz_mod_ctx_t ctx) {
	for (int i = 0; i < AEX_DEG; i++) fmpz_mod_add(r.c[i], a.c[i], b.c[i], ctx);
}

/* --- the quadratic base, on pairs of Z_q coordinates ---------------------
 * (a0 + a1 Z)(b0 + b1 Z) = (a0 b0 + NR a1 b1) + (a0 b1 + a1 b0) Z, by
 * Karatsuba so three Z_q multiplies instead of four. Safe to alias. */
static void gq_mul(fmpz_t r0, fmpz_t r1, const fmpz_t a0, const fmpz_t a1,
		const fmpz_t b0, const fmpz_t b1, const fmpz_mod_ctx_t ctx) {
	fmpz_t m0, m1, m2, t;

	fmpz_init(m0); fmpz_init(m1); fmpz_init(m2); fmpz_init(t);
	fmpz_mod_mul(m0, a0, b0, ctx);
	fmpz_mod_mul(m1, a1, b1, ctx);
	fmpz_mod_add(m2, a0, a1, ctx);
	fmpz_mod_add(t, b0, b1, ctx);
	fmpz_mod_mul(m2, m2, t, ctx);
	fmpz_mod_sub(m2, m2, m0, ctx);
	fmpz_mod_sub(m2, m2, m1, ctx);
	gr_mul_nr(t, m1, ctx);
	fmpz_mod_add(r0, m0, t, ctx);
	fmpz_set(r1, m2);
	fmpz_clear(m0); fmpz_clear(m1); fmpz_clear(m2); fmpz_clear(t);
}

/* r <- Z * a in the base, i.e. (a0 + a1 Z) Z = NR a1 + a0 Z. */
static void gq_mul_z(fmpz_t r0, fmpz_t r1, const fmpz_t a0, const fmpz_t a1,
		const fmpz_mod_ctx_t ctx) {
	fmpz_t t;

	fmpz_init(t);
	gr_mul_nr(t, a1, ctx);
	fmpz_set(r1, a0);
	fmpz_set(r0, t);
	fmpz_clear(t);
}

/* (u + v Y)(w + z Y) = (u w + Z v z) + (u z + v w) Y over the base, Karatsuba
 * again: three base multiplies. Safe to alias. */
static void gr_mul(gr_t & r, const gr_t & a, const gr_t & b,
		const fmpz_mod_ctx_t ctx) {
	if (AEX_DEG == 2) {
		gq_mul(r.c[0], r.c[1], a.c[0], a.c[1], b.c[0], b.c[1], ctx);
		return;
	}
	fmpz_t p0, p1, q0, q1, s0, s1, t0, t1;

	fmpz_init(p0); fmpz_init(p1); fmpz_init(q0); fmpz_init(q1);
	fmpz_init(s0); fmpz_init(s1); fmpz_init(t0); fmpz_init(t1);

	gq_mul(p0, p1, a.c[0], a.c[1], b.c[0], b.c[1], ctx);      /* u w */
	gq_mul(q0, q1, a.c[2], a.c[3], b.c[2], b.c[3], ctx);      /* v z */
	fmpz_mod_add(s0, a.c[0], a.c[2], ctx);
	fmpz_mod_add(s1, a.c[1], a.c[3], ctx);
	fmpz_mod_add(t0, b.c[0], b.c[2], ctx);
	fmpz_mod_add(t1, b.c[1], b.c[3], ctx);
	gq_mul(s0, s1, s0, s1, t0, t1, ctx);                      /* (u+v)(w+z) */
	fmpz_mod_sub(s0, s0, p0, ctx);
	fmpz_mod_sub(s1, s1, p1, ctx);
	fmpz_mod_sub(s0, s0, q0, ctx);
	fmpz_mod_sub(s1, s1, q1, ctx);
	gq_mul_z(q0, q1, q0, q1, ctx);                            /* Z v z */
	fmpz_mod_add(r.c[0], p0, q0, ctx);
	fmpz_mod_add(r.c[1], p1, q1, ctx);
	fmpz_set(r.c[2], s0);
	fmpz_set(r.c[3], s1);

	fmpz_clear(p0); fmpz_clear(p1); fmpz_clear(q0); fmpz_clear(q1);
	fmpz_clear(s0); fmpz_clear(s1); fmpz_clear(t0); fmpz_clear(t1);
}

/* The product of two basis elements, for the one place that multiplies
 * extension-valued polynomials by an extension scalar and so cannot go through
 * gr_mul: e0 = 1, e1 = Z, e2 = Y, e3 = ZY with Z^2 = NR and Y^2 = Z, so
 * e1 e1 = NR e0, e1 e2 = e3, e1 e3 = NR e2, e2 e2 = e1, e2 e3 = NR e0 and
 * e3 e3 = NR e1. idx says which basis element the product lands on and nr
 * whether it carries a factor of NR. */
static const int aex_basis_idx4[4][4] = {
	{0, 1, 2, 3},
	{1, 0, 3, 2},
	{2, 3, 1, 0},
	{3, 2, 0, 1},
};
static const int aex_basis_nr4[4][4] = {
	{0, 0, 0, 0},
	{0, 1, 0, 1},
	{0, 0, 0, 1},
	{0, 1, 1, 1},
};
/* At degree 2, the top-left corner: the basis is (1, Z). */
#define aex_basis_idx(i, j) 	(aex_basis_idx4[i][j])
#define aex_basis_nr(i, j) 		(aex_basis_nr4[i][j])

/* GR times a plain Z_q scalar: AEX_DEG multiplies. This is the common case,
 * since every witness stays in Z_q and only the challenge is extended. */
static void gr_scalar(gr_t & r, const gr_t & a, const fmpz_t s,
		const fmpz_mod_ctx_t ctx) {
	for (int i = 0; i < AEX_DEG; i++) fmpz_mod_mul(r.c[i], a.c[i], s, ctx);
}

/* (u + v Y)^-1 = (u - v Y) / (u^2 - Z v^2), whose denominator is in the base,
 * and the base inverse is (a0 - a1 Z)/(a0^2 - NR a1^2). Either norm is
 * non-invertible exactly when a is a zero divisor, which for a
 * challenge-derived value has probability about deg/p_min^AEX_DEG; report it
 * instead of letting FLINT abort inside fmpz_mod_inv, and let the caller
 * reject. */
static int gr_inv(gr_t & r, const gr_t & a, const fmpz_mod_ctx_t ctx) {
	fmpz_t n0, n1, m0, m1, g, t;
	int ok;

	fmpz_init(n0); fmpz_init(n1); fmpz_init(m0); fmpz_init(m1);
	fmpz_init(g); fmpz_init(t);

	if (AEX_DEG == 2) {
		/* a is in the base already. */
		fmpz_set(n0, a.c[0]);
		fmpz_set(n1, a.c[1]);
	} else {
		gq_mul(n0, n1, a.c[0], a.c[1], a.c[0], a.c[1], ctx);  /* u^2 */
		gq_mul(m0, m1, a.c[2], a.c[3], a.c[2], a.c[3], ctx);  /* v^2 */
		gq_mul_z(m0, m1, m0, m1, ctx);                        /* Z v^2 */
		fmpz_mod_sub(n0, n0, m0, ctx);
		fmpz_mod_sub(n1, n1, m1, ctx);
	}

	/* Invert n0 + n1 Z in the base. */
	fmpz_mod_mul(m0, n0, n0, ctx);
	fmpz_mod_mul(t, n1, n1, ctx);
	gr_mul_nr(t, t, ctx);
	fmpz_mod_sub(m0, m0, t, ctx);
	ok = fmpz_invmod(g, m0, fmpz_mod_ctx_modulus(ctx));
	if (ok) {
		fmpz_mod_mul(m0, n0, g, ctx);
		fmpz_mod_neg(m1, n1, ctx);
		fmpz_mod_mul(m1, m1, g, ctx);
		if (AEX_DEG == 2) {
			fmpz_set(r.c[0], m0);
			fmpz_set(r.c[1], m1);
		} else {
			/* r = (u - v Y) * (m0 + m1 Z). */
			gq_mul(n0, n1, a.c[0], a.c[1], m0, m1, ctx);
			fmpz_mod_neg(t, a.c[2], ctx);
			fmpz_mod_neg(g, a.c[3], ctx);
			gq_mul(t, g, t, g, m0, m1, ctx);
			fmpz_set(r.c[0], n0);
			fmpz_set(r.c[1], n1);
			fmpz_set(r.c[AEX_DEG - 2], t);
			fmpz_set(r.c[AEX_DEG - 1], g);
		}
	}

	fmpz_clear(n0); fmpz_clear(n1); fmpz_clear(m0); fmpz_clear(m1);
	fmpz_clear(g); fmpz_clear(t);
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


#ifdef MAIN
/* Sample a ring element whose coefficients are uniform over the set, which
 * hwt_dist and ZO_dist between them do not cover. */
static void aex_sample_set(params::poly_q & out, aex_set_t set) {
	array < mpz_t, params::poly_q::degree > c;
	uint8_t b[params::poly_q::degree];

	if (getrandom(b, sizeof(b), 0) != (ssize_t) sizeof(b)) {
		fprintf(stderr, "ERROR: could not read entropy for sampling\n");
		abort();
	}
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(c[i], (params::poly_q::bits_in_moduli_product() << 2));
		if (set == AEX_SCALAR) {
			mpz_set_ui(c[i], 0);
		} else if (set == AEX_BIN) {
			mpz_set_ui(c[i], b[i] & 1);
		} else {
			mpz_set_si(c[i], (b[i] & 1) ? 1 : -1);
		}
	}
	if (set == AEX_SCALAR) {
		uint64_t v = 0;

		for (size_t i = 0; i < 8; i++) {
			v = (v << 8) | b[i];
		}
		mpz_set_ui(c[0], v);
	}
	out.mpz2poly(c);
	out.ntt_pow_phi();
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(c[i]);
	}
}
#endif

/* Everything dimensioned by TAU is far too large to be a local: at TAU = 1000,
 * s is 512 MiB, H is 786 MiB, and the prover's v_i,j are 3 * TAU * V arrays of
 * DEGREE mpz_t, about 1.4 GiB. They are allocated on the heap once at start-up,
 * and the pointers below index exactly like the arrays they replace.
 *
 * NOTE: at TAU = 1000 this binary needs several gigabytes of RAM. Pass e.g.
 * CONFIG=-DTAU=8 to make to try it on a smaller machine. */
static params::poly_q A[R][V];
static params::poly_q (*s)[V], (*t)[R];
/* The v_{i,j} of the prover, one element of Z_q per coefficient. Held as the
 * two limbs the value already is rather than as mpz_t: an initialised mpz_t
 * costs its struct, its limbs and a malloc header, which is five times the 16
 * bytes of the value and 3.7 GiB of the difference at TAU = 1024. */
/* v[j][i][k] in aex_rpoly's layout: coefficient l at l. */
static zq::u128 (*v)[TAU][V][params::poly_q::degree];
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
	v = new zq::u128[3][TAU][V][params::poly_q::degree];
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

/* --- Arithmetic and transforms modulo q ------------------------------- */

/* A value of Z_q. q is one 88-bit prime (include/zq.hpp), so a value is one
 * unsigned __int128 and the arithmetic is zq's. */
typedef zq::u128 aex_w;

static inline aex_w aex_mul(aex_w a, aex_w b) {
	return zq::mul(a, b);
}

static inline aex_w aex_add(aex_w a, aex_w b) {
	return zq::add(a, b);
}

static inline aex_w aex_sub(aex_w a, aex_w b) {
	return zq::sub(a, b);
}

static aex_w aex_pow(aex_w a, aex_w e) {
	return zq::pow(a % zq::MODULUS, e);
}

/* A value of Z_q from an fmpz in [0, q), and back. */
static inline aex_w aex_from_fmpz(const fmpz_t x) {
	ulong w[2] = { 0, 0 };

	fmpz_get_ui_array(w, 2, x);
	return (aex_w) w[0] | ((aex_w) w[1] << 64);
}

static inline void aex_to_fmpz(fmpz_t r, aex_w x) {
	const ulong w[2] = { (ulong) x, (ulong) (x >> 64) };

	fmpz_set_ui_array(r, w, 2);
}

/* A primitive n-th root of unity mod q, for n a power of two dividing q - 1:
 * the first g^((q - 1) / n) whose n/2-th power is not 1. */
static aex_w aex_root(size_t n) {
	for (aex_w g = 2;; g++) {
		const aex_w w = aex_pow(g, (zq::MODULUS - 1) / n);

		if (aex_pow(w, n / 2) != 1) {
			return w;
		}
	}
}

/* Twiddles of a transform of length n: w^k, per NTT length. */
typedef struct {
	aex_w *w;                   /* forward, length n/2 */
	aex_w *iw;                  /* inverse */
	aex_w ninv;
	size_t n;
	/* What aex_ntt_tw reads: the bit-reversal permutation, and each stage's
	 * twiddles stored contiguously, the stage of half-length h at h - 1
	 * (n - 1 of them), instead of w[k * n / 2h] strided across the table. */
	size_t *rev;
	aex_w *sw, *siw;
} aex_tw_t;

static void aex_tw_init(aex_tw_t & t, size_t n, aex_w w) {
	t.n = n;
	t.w = new aex_w[n / 2];
	t.iw = new aex_w[n / 2];
	aex_w iw = zq::inv(w);
	t.w[0] = 1; t.iw[0] = 1;
	for (size_t i = 1; i < n / 2; i++) {
		t.w[i] = aex_mul(t.w[i - 1], w);
		t.iw[i] = aex_mul(t.iw[i - 1], iw);
	}
	t.ninv = zq::inv((aex_w) n);
	t.rev = new size_t[n];
	for (size_t i = 0, j = 0; i < n; i++) {
		t.rev[i] = j;
		size_t bit = n >> 1;
		for (; bit && (j & bit); bit >>= 1) {
			j ^= bit;
		}
		j ^= bit;
	}
	t.sw = new aex_w[n];
	t.siw = new aex_w[n];
	for (size_t h = 1; h < n; h <<= 1) {
		const size_t step = n / (2 * h);
		for (size_t k = 0; k < h; k++) {
			t.sw[h - 1 + k] = t.w[k * step];
			t.siw[h - 1 + k] = t.iw[k * step];
		}
	}
}

static void aex_tw_clear(aex_tw_t & t) {
	delete[]t.w; delete[]t.iw;
	delete[]t.rev;
	delete[]t.sw; delete[]t.siw;
}

/* The transform of length t.n, natural order in and out, fully reduced in
 * and out, radix 2; the inverse scales by 1/n. The permutation and each
 * stage's twiddles come from tables built once (aex_tw_init). */
static void aex_ntt_tw(aex_w * a, const aex_tw_t & t, int inverse) {
	const size_t n = t.n;
	const aex_w *SW = inverse ? t.siw : t.sw;

	for (size_t i = 0; i < n; i++) {
		const size_t j = t.rev[i];
		if (i < j) {
			aex_w x = a[i]; a[i] = a[j]; a[j] = x;
		}
	}
	for (size_t h = 1; h < n; h <<= 1) {
		const aex_w *W = SW + h - 1;
		for (size_t i = 0; i < n; i += 2 * h) {
			aex_w *x = a + i, *y = a + i + h;
			for (size_t k = 0; k < h; k++) {
				const aex_w u = x[k], v = aex_mul(y[k], W[k]);
				x[k] = aex_add(u, v);
				y[k] = aex_sub(u, v);
			}
		}
	}
	if (inverse) {
		for (size_t i = 0; i < n; i++) {
			a[i] = aex_mul(a[i], t.ninv);
		}
	}
}

/* The forward transform of length t.n by decimation in frequency, natural
 * order in and bit-reversed order out, with no permutation pass: a[c] ends
 * as the input polynomial at w^rev(c). Gentleman-Sande butterflies. Only
 * a[0, len) may be nonzero, len > n / 2: in the first stage a butterfly whose
 * lower input is zero is a single product. The stage of half-length h reads
 * the tables at h - 1, as aex_ntt_tw does. */
static void aex_ntt_dif(aex_w * a, const aex_tw_t & t, size_t len) {
	const size_t n = t.n;

	for (size_t h = n >> 1; h >= 1; h >>= 1) {
		const aex_w *W = t.sw + h - 1;
		for (size_t i = 0; i < n; i += 2 * h) {
			aex_w *x = a + i, *y = a + i + h;
			/* The first stage's butterflies past len - h see y = 0. */
			const size_t full = (2 * h == n) ? len - h : h;
			size_t k = 0;
			for (; k < full; k++) {
				const aex_w d = aex_sub(x[k], y[k]);
				x[k] = aex_add(x[k], y[k]);
				y[k] = aex_mul(d, W[k]);
			}
			for (; k < h; k++) {
				y[k] = aex_mul(x[k], W[k]);
			}
		}
	}
}

/* --- Reed-Solomon encoding over Z_q ------------------------------------- */

/* The code evaluates a message polynomial of length 2N + ETA at the
 * AEX_COLS-th roots of unity mod q, by aex_ntt_dif: column c is the message
 * at w^rev(c), rev reversing log2(AEX_COLS) bits. Any AEX_COLS distinct
 * points, in any order, give a Reed-Solomon code of the same length and
 * distance, which is all Lemma 2 uses; these make the transform a cyclic
 * one, with no twist and no permutation. aex_buf holds the message; past
 * 2N + ETA it is never read. */
static aex_w *aex_buf;
static aex_tw_t aex_tw;

static inline void aex_unpack(fmpz_t x, const aex_code_t * c, size_t i) {
	fmpz_set_ui_array(x, c->w + 2 * i, 2);
}


static void aex_ntt_setup(const fmpz_mod_ctx_t ctx) {
	/* The symbols are reduced mod q by the context and read as values of
	 * Z_q by aex_load; the two must be the same q. */
	fmpz_t Q;
	fmpz_init(Q);
	fmpz_set_mpz(Q, params::poly_big::moduli_product());
	if (!fmpz_equal(Q, fmpz_mod_ctx_modulus(ctx))) {
		fprintf(stderr, "aex: the code's modulus is not q\n");
		abort();
	}
	fmpz_clear(Q);
	static_assert((zq::MODULUS - 1) % AEX_COLS == 0, "no AEX_COLS-th roots of unity mod q");
	aex_buf = new aex_w[AEX_COLS];
	aex_tw_init(aex_tw, AEX_COLS, aex_root(AEX_COLS));
}

static void aex_ntt_clear(void) {
	delete[] aex_buf;
	aex_tw_clear(aex_tw);
}

/* A symbol of Z_q, reduced, into the message. */
static inline void aex_load(size_t i, const fmpz_t x) {
	aex_buf[i] = aex_from_fmpz(x);
}

/* The transform that turns aex_buf into a codeword, each symbol written low
 * limb, then high. */
static void aex_finish(aex_code_t & out) {
	const size_t len = 2 * params::poly_q::degree + ETA;

	static_assert(2 * params::poly_q::degree + ETA > AEX_COLS / 2,
			"aex_ntt_dif takes a message past half the code length");
	static_assert(2 * params::poly_q::degree + ETA <= AEX_COLS,
			"the message fits the code");
	aex_ntt_dif(aex_buf, aex_tw, len);
	for (size_t i = 0; i < AEX_COLS; i++) {
		out.w[2 * i] = (uint64_t) aex_buf[i];
		out.w[2 * i + 1] = (uint64_t) (aex_buf[i] >> 64);
	}
}

/* Encode(in0, in1, r): pack the two message blocks and the randomness into the
 * low coefficients, then evaluate at the AEX_COLS roots of unity. */
static void aex_encode(aex_code_t & out, fmpz_mod_poly_t in0,
		fmpz_mod_poly_t in1, const fmpz * in, const fmpz_mod_ctx_t ctx) {
	const size_t N = params::poly_q::degree;
	const slong l0 = fmpz_mod_poly_length(in0, ctx), l1 = fmpz_mod_poly_length(in1, ctx);
	fmpz_t zero;
	size_t i;

	/* The coefficients are reduced mod q; past a polynomial's length they are
	 * zero. */
	fmpz_init(zero);
	for (i = 0; i < N; i++) {
		aex_load(i, ((slong) i < l0) ? in0->coeffs + i : zero);
	}
	for (; i < 2 * N; i++) {
		aex_load(i, ((slong) (i - N) < l1) ? in1->coeffs + (i - N) : zero);
	}
	for (; i < 2 * N + ETA; i++) {
		aex_load(i, in + (i - 2 * N));
	}
	fmpz_clear(zero);
	aex_finish(out);
}

/* A polynomial over Z_q as its coefficients, l at r[l]: the layout of a
 * poly_q's data() in the coefficient domain. The prover keeps its sums in
 * this form, rather than in fmpz_mod_poly, and converts once. */
typedef struct {
	aex_w r[params::poly_q::degree];
} aex_rpoly;

/* Encode as aex_encode does, from coefficients: in0 and in1 are in
 * aex_rpoly's layout, or NULL for zero. */
static void aex_encode_res(aex_code_t & out, const aex_w *in0,
		const aex_w *in1, const fmpz * in) {
	const size_t N = params::poly_q::degree;
	size_t i;

	for (i = 0; i < N; i++) {
		aex_buf[i] = in0 ? in0[i] : 0;
		aex_buf[N + i] = in1 ? in1[i] : 0;
	}
	for (i = 2 * N; i < 2 * N + ETA; i++) {
		aex_load(i, in + (i - 2 * N));
	}
	aex_finish(out);
}

/* p's coefficients, p being in the NTT domain: from a copy, which spares
 * transforming p back afterwards. */
static void rp_from_nfl(aex_rpoly & out, const params::poly_q & p) {
	static params::poly_q t;

	t = p;
	t.invntt_pow_invphi();
	memcpy(out.r, t.data(), sizeof(out.r));
}

/* A scalar of Z_q. */
typedef struct {
	aex_w s;
} aex_rscalar;

static void rs_from_fmpz(aex_rscalar & out, const fmpz_t x) {
	out.s = aex_from_fmpz(x) % zq::MODULUS;
}

/* acc += x s. */
static void rp_addmul(aex_rpoly & acc, const aex_w *x, const aex_rscalar & s) {
	for (size_t l = 0; l < params::poly_q::degree; l++) {
		acc.r[l] = aex_add(acc.r[l], aex_mul(s.s, x[l]));
	}
}

/* out = the polynomial a holds. */
static void rp_to_fmpz(fmpz_mod_poly_t out, const aex_rpoly & a,
		const fmpz_mod_ctx_t ctx) {
	const size_t N = params::poly_q::degree;

	fmpz_mod_poly_fit_length(out, N, ctx);
	for (size_t l = 0; l < N; l++) {
		aex_to_fmpz(out->coeffs + l, a.r[l]);
	}
	_fmpz_mod_poly_set_length(out, N);
	_fmpz_mod_poly_normalise(out);
}

/* a = in, whose coefficients are reduced mod q. */
static void rp_from_fmpz(aex_rpoly & a, const fmpz_mod_poly_t in,
		const fmpz_mod_ctx_t ctx) {
	const slong len = fmpz_mod_poly_length(in, ctx);

	for (size_t l = 0; l < params::poly_q::degree; l++) {
		a.r[l] = ((slong) l < len) ? aex_from_fmpz(in->coeffs + l) : 0;
	}
}

/* p = the polynomial a holds, in the coefficient domain. */
static void rp_to_nfl(params::poly_q & p, const aex_rpoly & a) {
	memcpy(p.data(), a.r, sizeof(a.r));
}

/* acc -= x. */
static void rp_sub(aex_rpoly & acc, const aex_w *x) {
	for (size_t l = 0; l < params::poly_q::degree; l++) {
		acc.r[l] = aex_sub(acc.r[l], x[l]);
	}
}

static bool rp_is_zero(const aex_rpoly & a) {
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		if (a.r[i] != 0) {
			return false;
		}
	}
	return true;
}

/* Rows of E, as RowsToMatrix lists them: H, H_0, then H_{i,j} for each k. */
#define AEX_ROWS    (V * (2 + 3 * TAU))
/* How many times the whole proof is run. The algebraic part of Lemma 2 is
 * 18 TAU / p_min^AEX_DEG, since the ring is split and an adversary works modulo
 * one prime: at AEX_DEG = 2 that is 2^-74, so two passes were needed, and
 * Fiat-Shamir then had to bind them to each other, which it did not -- see
 * SOUNDNESS.md 5.5. At AEX_DEG = 4 it is 2^-162, one pass carries the proof,
 * and there is nothing left to bind. */
#define AEX_REPS    1

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

/* Columns are gathered AEX_TREE_BLOCK at a time: each row's symbols for the
 * block are contiguous in its codeword, so a block costs one sequential read
 * a row, where gathering column by column read 16 bytes from each of
 * AEX_ROWS codewords 256 KiB apart, a cache and TLB miss apiece. The bytes
 * are aex_column's: a symbol's two limbs, low first, each little-endian,
 * which on a little-endian machine is the limbs' memory as it stands. */
#define AEX_TREE_BLOCK 32
static_assert(AEX_COLS % AEX_TREE_BLOCK == 0, "columns come in whole blocks");
static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
		"the block gather copies limbs in memory order");

static void aex_tree_build(aex_tree_t & t) {
	uint8_t *blk = new uint8_t[AEX_TREE_BLOCK * AEX_COLBYTES];
	t.node = new uint8_t[aex_tree_nodes() * BLAKE3_OUT_LEN];
	for (size_t c0 = 0; c0 < AEX_COLS; c0 += AEX_TREE_BLOCK) {
		for (size_t r = 0; r < AEX_ROWS; r++) {
			const uint64_t *d = aex_row(r).w + 2 * c0;
			for (size_t b = 0; b < AEX_TREE_BLOCK; b++) {
				memcpy(blk + b * AEX_COLBYTES + r * 16, d + 2 * b, 16);
			}
		}
		for (size_t b = 0; b < AEX_TREE_BLOCK; b++) {
			blake3_hasher h;
			blake3_hasher_init(&h);
			blake3_hasher_update(&h, blk + b * AEX_COLBYTES, AEX_COLBYTES);
			blake3_hasher_finalize(&h, t.node + (c0 + b) * BLAKE3_OUT_LEN, BLAKE3_OUT_LEN);
		}
	}
	delete[]blk;
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
		fmpz_mod_poly_t f[V][AEX_DEG], gr_t rf[ETA], fmpz_mod_poly_t h[2][V][AEX_DEG],
		gr_t rh[ETA], const fmpz_mod_ctx_t ctx) {
	blake3_hasher hasher;
	fmpz_t c;
	uint8_t *out = new uint8_t[ETA * 8];

	fmpz_init(c);
	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, root, BLAKE3_OUT_LEN);
	for (int cc = 0; cc < AEX_DEG; cc++) {
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
		for (int c = 0; c < AEX_DEG; c++) {
			aex_absorb(&hasher, rf[i].c[c]);
			aex_absorb(&hasher, rh[i].c[c]);
		}
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

/* A primitive TAU-th root of unity modulo q, the one the prover's transforms
 * of length TAU use. TAU must be a power of two dividing q - 1. */
static void aex_root_tau(fmpz_t w, const fmpz_mod_ctx_t ctx) {
	static_assert((zq::MODULUS - 1) % TAU == 0, "no TAU-th roots of unity mod q");
	fmpz_t t;

	fmpz_init(t);
	aex_to_fmpz(t, aex_root(TAU));
	fmpz_mod_set_fmpz(w, t, ctx);
	fmpz_clear(t);
}

/* l_i(x) for i = 0..TAU in closed form. With the nodes at the TAU-th roots of
 * unity, l_0 = X^TAU - 1 and l_i(X) = w^{i-1}(X^TAU - 1)/(TAU (X - w^{i-1})),
 * so the whole vector costs O(TAU) multiplies and a single inversion instead of
 * evaluating TAU + 1 dense polynomials. */
static void gr_comp(fmpz * out, gr_t in[ETA], int c) {
	for (size_t i = 0; i < ETA; i++) {
		fmpz_set(out + i, in[i].c[c]);
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
	fmpz_mod_sub_ui(xt.c[0], xt.c[0], 1, ctx);
	gr_set(lev[0], xt);

	/* TAU is a power of two and q is odd, so TAU stays invertible in Z_q and
	 * needs no extension arithmetic; the same goes for the nodes w^i. */
	fmpz_set_ui(wi, TAU);
	fmpz_mod_inv(tauinv, wi, ctx);

	fmpz_one(wi);
	for (size_t i = 0; i < TAU; i++) {
		fmpz_mod_sub(den[i].c[0], x.c[0], wi, ctx);
		for (int c = 1; c < AEX_DEG; c++) {
			fmpz_set(den[i].c[c], x.c[c]);
		}
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
/* Symbol r of an opened column, and symbol i of a codeword. */
static inline aex_w aex_col_sym(const uint8_t *col, size_t r) {
	uint64_t w[2];

	memcpy(w, col + r * 16, 16);
	return (aex_w) w[0] | ((aex_w) w[1] << 64);
}

static inline aex_w aex_code_sym(const aex_code_t *c, size_t i) {
	return (aex_w) c->w[2 * i] | ((aex_w) c->w[2 * i + 1] << 64);
}

static inline aex_w rs_mul(const aex_rscalar & s, aex_w y) {
	return aex_mul(s.s, y);
}

/* r = a b in GR(q, AEX_DEG), in the tower basis (1, Z, Y, ZY): each product
 * of basis elements lands where aex_basis_idx says, times AEX_NR where
 * aex_basis_nr says. r may be a or b. */
static void grq_mul(aex_w r[AEX_DEG], const aex_w a[AEX_DEG],
		const aex_w b[AEX_DEG]) {
	aex_w t[AEX_DEG] = { 0 };

	for (int i = 0; i < AEX_DEG; i++) {
		for (int j = 0; j < AEX_DEG; j++) {
			aex_w x = aex_mul(a[i], b[j]);

			if (aex_basis_nr(i, j)) {
				x = aex_mul(x, AEX_NR);
			}
			t[aex_basis_idx(i, j)] = aex_add(t[aex_basis_idx(i, j)], x);
		}
	}
	for (int i = 0; i < AEX_DEG; i++) {
		r[i] = t[i];
	}
}

static int aex_identities(const aex_open_t & o, fmpz_mod_poly_t f[V][AEX_DEG],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][AEX_DEG], gr_t rh[ETA],
		const gr_t & x, const gr_t & beta0, gr_t beta[TAU][3],
		fmpz_mod_poly_t lag[TAU + 1], const fmpz_mod_ctx_t ctx) {
	fmpz *rc = _fmpz_vec_init(ETA);
	gr_t l0, l0inv;
	gr_t lpow[3];
	gr_t *lev = new gr_t[TAU + 1];
	/* l_i(x) l_0(x)^j does not depend on the column or the component, but used
	 * to be recomputed inside both loops; hoisting it out pays for most of the
	 * extra work the extension costs here. */
	gr_t (*wt)[3] = new gr_t[TAU][3];
	aex_code_t *lhs_f = new aex_code_t[AEX_DEG * V];
	aex_code_t *lhs_h = new aex_code_t[AEX_DEG * V];
	int ok = 1;

	gr_init(l0); gr_init(l0inv);
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

		/* Left-hand sides, one codeword per component and per k, on
		 * values of Z_q: f's once per polynomial, the identity polynomial per
		 * coefficient by grq_mul, then encoded. The same arithmetic as gr_mul
		 * in fmpz, and a test checks the two. */
		const size_t N = params::poly_q::degree;
		aex_rpoly *fr = new aex_rpoly[AEX_DEG], *gres = new aex_rpoly[AEX_DEG];
		aex_w li[AEX_DEG];
		aex_rscalar sl;

		for (int c = 0; c < AEX_DEG; c++) {
			rs_from_fmpz(sl, l0inv.c[c]);
			li[c] = sl.s;
		}
		for (size_t k = 0; k < V; k++) {
			for (int c = 0; c < AEX_DEG; c++) {
				rp_from_fmpz(fr[c], f[k][c], ctx);
			}
			for (size_t l = 0; l < N; l++) {
				const aex_set_t set = aex_set_at(k, l);
				aex_w fv[AEX_DEG], cub[AEX_DEG], t[AEX_DEG];

				for (int i = 0; i < AEX_DEG; i++) {
					fv[i] = fr[i].r[l];
				}
				if (set == AEX_FREE) {
					/* 0 */
					for (int i = 0; i < AEX_DEG; i++) cub[i] = 0;
				} else if (set == AEX_ZERO) {
					/* f */
					for (int i = 0; i < AEX_DEG; i++) cub[i] = fv[i];
				} else if (set == AEX_SGN) {
					/* (f - 1)(f + 1) */
					for (int i = 0; i < AEX_DEG; i++) cub[i] = fv[i], t[i] = fv[i];
					cub[0] = aex_sub(cub[0], 1);
					t[0] = aex_add(t[0], 1);
					grq_mul(cub, cub, t);
				} else {
					/* f (f - 1), and one more factor for the ternary set */
					for (int i = 0; i < AEX_DEG; i++) cub[i] = fv[i];
					cub[0] = aex_sub(cub[0], 1);
					grq_mul(cub, cub, fv);
					if (set == AEX_TER) {
						for (int i = 0; i < AEX_DEG; i++) t[i] = fv[i];
						t[0] = aex_add(t[0], 1);
						grq_mul(cub, cub, t);
					}
				}
				grq_mul(cub, cub, li);
				for (int i = 0; i < AEX_DEG; i++) {
					gres[i].r[l] = cub[i];
				}
			}
			for (int c = 0; c < AEX_DEG; c++) {
				gr_comp(rc, rf, c);
				aex_encode_res(lhs_f[k * AEX_DEG + c], fr[c].r, gres[c].r, rc);
				gr_comp(rc, rh, c);
				aex_encode(lhs_h[k * AEX_DEG + c], h[0][k][c], h[1][k][c], rc, ctx);
			}
		}
		delete[] fr;
		delete[] gres;
	}

	/* The column checks: every scalar below is fixed for the whole check, so
	 * each becomes an aex_w once, and each symbol of a column one too. 550
	 * columns times V (3 TAU + 1) symbols times 8 products was as many
	 * fmpz_mod_mul and fmpz_mod_add, which at TAU = 1000 is 66 million of
	 * each. */
	if (ok) {
		aex_rscalar sl0[AEX_DEG], sb0[AEX_DEG];
		aex_rscalar (*swt)[3][AEX_DEG] = new aex_rscalar[TAU][3][AEX_DEG];
		aex_rscalar (*sbe)[3][AEX_DEG] = new aex_rscalar[TAU][3][AEX_DEG];

		for (int c = 0; c < AEX_DEG; c++) {
			rs_from_fmpz(sl0[c], l0.c[c]);
			rs_from_fmpz(sb0[c], beta0.c[c]);
		}
		for (size_t i = 0; i < TAU; i++) {
			for (size_t j = 0; j < 3; j++) {
				for (int c = 0; c < AEX_DEG; c++) {
					rs_from_fmpz(swt[i][j][c], wt[i][j].c[c]);
					rs_from_fmpz(sbe[i][j][c], beta[i][j].c[c]);
				}
			}
		}
		for (size_t n = 0; n < ETA && ok; n++) {
			const uint8_t *col = o.col + n * AEX_COLBYTES;
			for (size_t k = 0; k < V && ok; k++) {
				aex_w af[AEX_DEG], ah[AEX_DEG], y;

				/* H carries the mask, a Z_q value, so it lands in the first
				 * coordinate and the others start empty. Both identities and
				 * all components read each symbol once. */
				y = aex_col_sym(col, AEX_ROW_H(k));
				for (int c = 0; c < AEX_DEG; c++) {
					ah[c] = (c == 0) ? y : 0;
				}
				y = aex_col_sym(col, AEX_ROW_H0(k));
				for (int c = 0; c < AEX_DEG; c++) {
					af[c] = rs_mul(sl0[c], y);
					ah[c] = aex_add(ah[c], rs_mul(sb0[c], y));
				}
				for (size_t i = 0; i < TAU; i++) {
					for (size_t j = 0; j < 3; j++) {
						y = aex_col_sym(col, AEX_ROW_HIJ(i, j, k));
						for (int c = 0; c < AEX_DEG; c++) {
							af[c] = aex_add(af[c], rs_mul(swt[i][j][c], y));
							ah[c] = aex_add(ah[c], rs_mul(sbe[i][j][c], y));
						}
					}
				}
				for (int c = 0; c < AEX_DEG; c++) {
					ok &= af[c] == aex_code_sym(lhs_f + k * AEX_DEG + c, o.I[n]);
					ok &= ah[c] == aex_code_sym(lhs_h + k * AEX_DEG + c, o.I[n]);
				}
			}
		}
		delete[] swt;
		delete[] sbe;
	}

	gr_clear(l0); gr_clear(l0inv);
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
 * the nodes is a length-TAU NTT and interpolating is its inverse. The
 * decomposition is unique, so any way of computing it gives the same v_{i,j};
 * no closed form in s_i alone exists, since v_{i,0} involves g'(a_i) and so
 * depends on every s_m, but one in the derivatives of g at the nodes does.
 */
static_assert((TAU & (TAU - 1)) == 0, "TAU must be a power of two");

/* Extract v[j][i] for one coefficient position: out[j][i] is
 * G_j at w^i, where P(f) / l_0 = G_0 + l_0 G_1 + l_0^2 G_2 with deg G_j < TAU
 * and f = a l_0 + g, g the interpolant of b. The top level is a constant, the
 * leading coefficient a^deg P. The others come from derivatives at the nodes,
 * with D = X d/dX, which at a node w^i, where X^TAU = 1, has D l_0 = TAU and
 * D^2 l_0 = TAU^2. From H = P(f) = l_0 F and P(g) vanishing at the nodes:
 *   F  = DH / TAU,                    DH  = P'(b) Df,  Df = Dg + a TAU,
 *   DF = (D^2 H - TAU^2 F) / 2 TAU,   D^2 H = P''(b) (Df)^2 + P'(b) D^2 f,
 *                                     D^2 f = D^2 g + a TAU^2,
 * and G_0 = F, G_1 = (DF - DG_0) / TAU at the nodes, the latter since
 * F - G_0 = l_0 (G_1 + l_0 G_2). Dg and D^2 g are transforms of k g_k and
 * k^2 g_k, DG_0 of k times G_0's coefficients: five transforms of length
 * TAU for the cubic set, two for the quadratic ones, instead of a product on
 * 4 TAU points and three rounds of division. buf holds 3 TAU elements. For
 * AEX_ZERO, P(f) = f with g = 0 is the constant a. */
static void aex_extract(aex_w a, const aex_w * b, aex_w out[3][TAU],
		const aex_tw_t & TT, aex_w * buf, aex_set_t set) {
	const aex_w T = TAU, T2 = aex_mul(T, T);
	const aex_w Ti = zq::inv(T), T2i = zq::inv(aex_add(T, T));
	aex_w *g = buf, *dg = buf + TAU, *d2g = buf + 2 * TAU;

	if (set == AEX_FREE || set == AEX_ZERO) {
		for (size_t i = 0; i < TAU; i++) {
			out[0][i] = (set == AEX_ZERO) ? a : 0;
			out[1][i] = 0;
			out[2][i] = 0;
		}
		return;
	}
	/* g's coefficients, then Dg at the nodes, and D^2 g for the cubic set. */
	for (size_t i = 0; i < TAU; i++) {
		g[i] = b[i];
	}
	aex_ntt_tw(g, TT, 1);
	for (size_t k = 0; k < TAU; k++) {
		dg[k] = aex_mul(g[k], k);
		d2g[k] = aex_mul(dg[k], k);
	}
	aex_ntt_tw(dg, TT, 0);
	const aex_w aT = aex_mul(a, T), a2 = aex_mul(a, a);
	if (set != AEX_TER) {
		/* P'(b) = 2b - 1 for {0, 1}, 2b for {-1, 1}; G_1 = a^2, G_2 = 0. */
		for (size_t i = 0; i < TAU; i++) {
			aex_w dp = aex_add(b[i], b[i]);
			if (set == AEX_BIN) {
				dp = aex_sub(dp, 1);
			}
			out[0][i] = aex_mul(aex_mul(dp, aex_add(dg[i], aT)), Ti);
			out[1][i] = a2;
			out[2][i] = 0;
		}
		return;
	}
	aex_ntt_tw(d2g, TT, 0);
	const aex_w aT2 = aex_mul(a, T2), a3 = aex_mul(a2, a);
	/* P = X^3 - X: P'(b) = 3b^2 - 1, P''(b) = 6b. g is spent; its space takes
	 * G_0's coefficients, and dg's DF. */
	for (size_t i = 0; i < TAU; i++) {
		const aex_w bb = aex_mul(b[i], b[i]);
		const aex_w p1 = aex_sub(aex_add(aex_add(bb, bb), bb), 1);
		const aex_w b2 = aex_add(b[i], b[i]);
		const aex_w p2 = aex_add(aex_add(b2, b2), b2);
		const aex_w df = aex_add(dg[i], aT);
		const aex_w d2f = aex_add(d2g[i], aT2);
		const aex_w F = aex_mul(aex_mul(p1, df), Ti);
		const aex_w d2h = aex_add(aex_mul(p2, aex_mul(df, df)),
				aex_mul(p1, d2f));

		out[0][i] = F;
		g[i] = F;
		dg[i] = aex_mul(aex_sub(d2h, aex_mul(T2, F)), T2i);
		out[2][i] = a3;
	}
	aex_ntt_tw(g, TT, 1);
	for (size_t k = 0; k < TAU; k++) {
		g[k] = aex_mul(g[k], k);
	}
	aex_ntt_tw(g, TT, 0);
	for (size_t i = 0; i < TAU; i++) {
		out[1][i] = aex_mul(aex_sub(dg[i], g[i]), Ti);
	}
}

/* Build the rows of the relation proving that the message committed in each
 * P_i is a ring constant. It is the commitment equation itself, so the witness
 * the proof binds is an opening of P_i and no link between two commitment
 * schemes is needed:
 *
 *   row 0    P_i.c1 = r_0 + sum_j A1[0][j] r_{j+1}
 *   row 1    P_i.c2 = sum_j A2[0][j] r_j + sigma_i
 *
 * with r ternary and sigma_i declared AEX_SCALAR: R = HEIGHT + 1 rows and
 * V = WIDTH + 1 components. There is no third row. Where a monomial encoding
 * would need a companion Y = w sigma to pin the Hamming weight, "is a
 * constant" is already coefficient-wise, and exactly so over Z_q.
 */
static void aex_scalar_matrix(comkey_t & key) {
	params::poly_q one = 1;

	one.ntt_pow_phi();
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < V; j++) {
			A[i][j] = 0;
		}
	}
	A[0][0] = one;
	for (int j = 0; j < WIDTH - HEIGHT; j++) {
		A[0][j + HEIGHT] = key.A1[0][j];
	}
	for (int j = 0; j < WIDTH; j++) {
		A[1][j] = key.A2[0][j];
	}
	A[1][WIDTH] = one;

	for (int j = 0; j < V; j++) {
		aex_sets[j] = AEX_TER;
	}
	aex_sets[WIDTH] = AEX_SCALAR;
}

/* The public part of the relation, which is the commitment itself. TAU is a
 * power of two and the caller may have fewer commitments, so the spare
 * relations repeat the first one. */
static void aex_scalar_stmt(const commit_t * P, size_t n) {
	for (size_t i = 0; i < TAU; i++) {
		const commit_t & p = P[i < n ? i : 0];

		t[i][0] = p.c1;
		t[i][1] = p.c2[0];
		for (int j = 2; j < R; j++) {
			t[i][j] = 0;
		}
	}
}

/* The witness: the opening of P_i. */
static void aex_scalar_wit(const vector < params::poly_q > *r,
		const params::poly_q * sigma, size_t n) {
	params::poly_q sg;

	for (size_t i = 0; i < TAU; i++) {
		size_t k = (i < n ? i : 0);

		sg = sigma[k];
		sg.ntt_pow_phi();
		for (int j = 0; j < WIDTH; j++) {
			s[i][j] = r[k][j];
		}
		s[i][WIDTH] = sg;
		for (int j = WIDTH + 1; j < V; j++) {
			s[i][j] = 0;
		}
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
	/* Every coordinate of every challenge comes from Z_q, so each is uniform
	 * over the whole extension. */
	for (int c = 0; c < AEX_DEG; c++) {
		fmpz_randm(x.c[c], rand, q);
		fmpz_randm(beta0.c[c], rand, q);
	}
	for (size_t i = 0; i < TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			for (int c = 0; c < AEX_DEG; c++) {
				fmpz_randm(beta[i][j].c[c], rand, q);
			}
		}
	}

	flint_rand_clear(rand);
}

/* out = in * x mod q, as fmpz_mod_poly_scalar_mul_fmpz, on aex_w values and
 * zq's reduction, where FLINT does a two-limb multiplication and a general
 * reduction a coefficient. Other moduli, and a scalar outside [0, q), go to
 * FLINT. out may be in. */
static void scalar_mul(fmpz_mod_poly_t out, const fmpz_mod_poly_t in,
		const fmpz_t x, const fmpz_mod_ctx_t ctx) {
	const slong len = fmpz_mod_poly_length(in, ctx);
	fmpz_t Q;

	fmpz_init(Q);
	fmpz_set_mpz(Q, params::poly_q::moduli_product());
	const int ours = fmpz_equal(Q, fmpz_mod_ctx_modulus(ctx)) &&
			fmpz_sgn(x) >= 0 && fmpz_cmp(x, Q) < 0;
	fmpz_clear(Q);
	if (!ours) {
		fmpz_mod_poly_scalar_mul_fmpz(out, in, x, ctx);
		return;
	}
	const aex_w s = aex_from_fmpz(x);
	fmpz_mod_poly_fit_length(out, len, ctx);
	for (slong i = 0; i < len; i++) {
		aex_to_fmpz(out->coeffs + i, aex_mul(s, aex_from_fmpz(in->coeffs + i)));
	}
	_fmpz_mod_poly_set_length(out, len);
	_fmpz_mod_poly_normalise(out);
}

static void poly_to(params::poly_q & out, fmpz_mod_poly_t & in,
		const fmpz_mod_ctx_t ctx) {
	/* in's coefficients are reduced mod q, so each is one aex_w; past in's
	 * length they are zero. */
	const slong len = fmpz_mod_poly_length(in, ctx);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		out(0, i) = ((slong) i < len) ? aex_from_fmpz(in->coeffs + i) : 0;
	}
	out.ntt_pow_phi();
}

#ifdef MAIN
/* Only the tests convert this way now: the prover and the verifier keep
 * their sums as aex_rpoly. */
static void poly_from(fmpz_mod_poly_t & out, params::poly_q & in,
		const fmpz_mod_ctx_t ctx) {
	/* No centring: out's modulus is q, so centring is a no-op modulo it.
	 * Write the coefficient array directly: the values are already reduced,
	 * so fmpz_mod_poly_set_coeff_fmpz's bounds check, length update and
	 * redundant reduction are all wasted work at 4096 coefficients. */
	const size_t N = params::poly_q::degree;

	in.invntt_pow_invphi();
	fmpz_mod_poly_fit_length(out, N, ctx);
	for (size_t l = 0; l < N; l++) {
		aex_to_fmpz(out->coeffs + l, in(0, l));
	}
	_fmpz_mod_poly_set_length(out, N);
	_fmpz_mod_poly_normalise(out);
	in.ntt_pow_phi();
}
#endif

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
		scalar_mul(lag[i], lag[i], u, ctx);
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

static int pismall_prover(commit_t & com, gr_t & x, fmpz_mod_poly_t f[V][AEX_DEG],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][AEX_DEG], gr_t rh[ETA],
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
		/* the masks are Z_q values, so they live in the first coordinate and
		 * the others start empty */
		fmpz_randm(rh[i].c[0], prng, q);
		for (int c = 1; c < AEX_DEG; c++) {
			fmpz_zero(rh[i].c[c]);
		}
	}
	for (size_t i = 0; i < V; i++) {
		/* The masks are Z_q values: they live in the first coordinate of the
		 * extension and the others start empty. */
		fmpz_mod_poly_randtest(h[0][i][0], prng, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(h[1][i][0], prng, params::poly_q::degree, ctx);
		for (int c = 1; c < AEX_DEG; c++) {
			fmpz_mod_poly_zero(h[0][i][c], ctx);
			fmpz_mod_poly_zero(h[1][i][c], ctx);
		}
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
	 * position at a time. */
	{
		const size_t N = params::poly_q::degree;
		aex_tw_t TT;
		aex_tw_init(TT, TAU, aex_root(TAU));

		aex_w *sres = new aex_w[N * TAU];
		aex_w *s0res = new aex_w[N];
		aex_w *buf = new aex_w[3 * TAU];
		static aex_w out[3][TAU];

		for (size_t k = 0; k < V; k++) {
			/* data()[l] is already coefficient l, so the values can be read
			 * straight out without going through mpz. */
			s0[k].invntt_pow_invphi();
			memcpy(s0res, s0[k].data(), N * sizeof(aex_w));
			s0[k].ntt_pow_phi();
			for (size_t i = 0; i < TAU; i++) {
				s[i][k].invntt_pow_invphi();
				const aex_w *d = s[i][k].data();
				for (size_t l = 0; l < N; l++) {
					sres[l * TAU + i] = d[l];
				}
				s[i][k].ntt_pow_phi();
			}
			for (size_t l = 0; l < N; l++) {
				aex_extract(s0res[l], sres + l * TAU, out, TT, buf,
						aex_set_at(k, l));
				for (size_t jj = 0; jj < 3; jj++) {
					for (size_t i = 0; i < TAU; i++) {
						v[jj][i][k][l] = out[jj][i];
					}
				}
			}
		}
		aex_tw_clear(TT);
		delete[]sres;
		delete[]s0res;
		delete[]buf;
	}

	/* Encode H's as larger NTT. H_{i,j} has one codeword per component k of
	 * s_i, so it is indexed by k as well; delta_j is 1 only for j = 0. */
	aex_rpoly *rs = new aex_rpoly;
	for (size_t k = 0; k < V; k++) {
		rp_from_nfl(*rs, s0[k]);
		aex_encode_res(H0[k], rs->r, NULL, (const fmpz *) r0);
		gr_comp(rc, rh, 0);
		aex_encode(_H[k], h[0][k][0], h[1][k][0], rc, ctx);
		for (size_t i = 0; i < TAU; i++) {
			rp_from_nfl(*rs, s[i][k]);
			for (size_t j = 0; j < 3; j++) {
				aex_encode_res(H[i][j][k], (j == 0) ? rs->r : NULL, v[j][i][k],
						(const fmpz *) prover_r[i][j]);
			}
		}
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
	/* f = f(x) = s_0 l_0(x) + \Sum s_i l_i(x), summed as residues and
	 * converted once. */
	aex_rpoly (*acc)[AEX_DEG] = new aex_rpoly[V][AEX_DEG];
	aex_rscalar sc[AEX_DEG];
	memset(acc, 0, sizeof(aex_rpoly) * V * AEX_DEG);
	for (size_t i = 0; i <= TAU; i++) {
		for (int c = 0; c < AEX_DEG; c++) {
			rs_from_fmpz(sc[c], prover_y[i].c[c]);
		}
		for (int j = 0; j < V; j++) {
			rp_from_nfl(*rs, (i == 0) ? s0[j] : s[i - 1][j]);
			for (int c = 0; c < AEX_DEG; c++) {
				rp_addmul(acc[j][c], rs->r, sc[c]);
			}
		}
	}
	for (int j = 0; j < V; j++) {
		for (int c = 0; c < AEX_DEG; c++) {
			rp_to_fmpz(f[j][c], acc[j][c], ctx_q);
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

	/* _h = h + s_0 beta_0 + \sum beta_i,j (\delta_j s_i, v_i,j), the s parts
	 * into h[0] and the v parts into h[1], summed as residues and added to
	 * the masks once. */
	aex_rpoly (*acc1)[AEX_DEG] = new aex_rpoly[V][AEX_DEG];
	memset(acc, 0, sizeof(aex_rpoly) * V * AEX_DEG);
	memset(acc1, 0, sizeof(aex_rpoly) * V * AEX_DEG);
	for (int c = 0; c < AEX_DEG; c++) {
		rs_from_fmpz(sc[c], beta0.c[c]);
	}
	for (size_t k = 0; k < V; k++) {
		rp_from_nfl(*rs, s0[k]);
		for (int c = 0; c < AEX_DEG; c++) {
			rp_addmul(acc[k][c], rs->r, sc[c]);
		}
	}
	for (size_t i = 1; i <= TAU; i++) {
		for (size_t j = 0; j < 3; j++) {
			const gr_t & b = prover_beta[i - 1][j];

			for (int c = 0; c < AEX_DEG; c++) {
				rs_from_fmpz(sc[c], b.c[c]);
			}
			for (size_t k = 0; k < V; k++) {
				if (j == 0) {
					rp_from_nfl(*rs, s[i - 1][k]);
					for (int c = 0; c < AEX_DEG; c++) {
						rp_addmul(acc[k][c], rs->r, sc[c]);
					}
				}
				for (int c = 0; c < AEX_DEG; c++) {
					rp_addmul(acc1[k][c], v[j][i - 1][k], sc[c]);
				}
			}
		}
	}
	for (size_t k = 0; k < V; k++) {
		for (int c = 0; c < AEX_DEG; c++) {
			rp_to_fmpz(poly, acc[k][c], ctx);
			fmpz_mod_poly_add(h[0][k][c], h[0][k][c], poly, ctx);
			rp_to_fmpz(poly, acc1[k][c], ctx);
			fmpz_mod_poly_add(h[1][k][c], h[1][k][c], poly, ctx);
		}
	}
	delete[] acc;
	delete[] acc1;
	delete rs;

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

static int pismall_verifier(commit_t & com, fmpz_mod_poly_t f[V][AEX_DEG],
		gr_t rf[ETA], fmpz_mod_poly_t h[2][V][AEX_DEG], gr_t rh[ETA],
		vector < params::poly_q > rd, comkey_t & key,
		fmpz_mod_poly_t lag[TAU + 1], flint_rand_t prng,
		const fmpz_mod_ctx_t ctx, const aex_open_t & o) {
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

	/* The linear check, in residues as the prover's sums are: r = \sum_i
	 * t_i l_i(x) - A f, then m = r / l_0(x) through the basis table, whose
	 * coordinates but the first must vanish. */
	aex_rpoly (*rr)[AEX_DEG] = new aex_rpoly[R][AEX_DEG];
	aex_rpoly *ru = new aex_rpoly[AEX_DEG];
	aex_rpoly *rx = new aex_rpoly;
	aex_rscalar sc[AEX_DEG];
	params::poly_q pf, pa;

	memset(rr, 0, sizeof(aex_rpoly) * R * AEX_DEG);
	result = aex_lagrange(vlev, x, ctx_q);
	if (result) {
		for (int i = 1; i <= TAU; i++) {
			for (int c = 0; c < AEX_DEG; c++) {
				rs_from_fmpz(sc[c], vlev[i].c[c]);
			}
			for (int j = 0; j < R; j++) {
				rp_from_nfl(*rx, t[i - 1][j]);
				for (int c = 0; c < AEX_DEG; c++) {
					rp_addmul(rr[j][c], rx->r, sc[c]);
				}
			}
		}

		/* d = A * _f, in the NTT domain as before. */
		for (int j = 0; j < V; j++) {
			for (int c = 0; c < AEX_DEG; c++) {
				rp_from_fmpz(*rx, f[j][c], ctx_q);
				rp_to_nfl(pf, *rx);
				pf.ntt_pow_phi();
				for (int i = 0; i < R; i++) {
					pa = pf * A[i][j];
					rp_from_nfl(*rx, pa);
					rp_sub(rr[i][c], rx->r);
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
		/* m = r / l_0(x), a multiplication of an extension-valued polynomial by
		 * a scalar of the extension, coordinate by coordinate through the basis
		 * table above. The committed value is a Z_q element, so every
		 * coordinate of the quotient but the first has to come out zero. */
		for (int i = 0; i < R; i++) {
			memset(ru, 0, sizeof(aex_rpoly) * AEX_DEG);
			for (int a = 0; a < AEX_DEG; a++) {
				for (int b = 0; b < AEX_DEG; b++) {
					if (aex_basis_nr(a, b)) {
						gr_mul_nr(nrb, l0i.c[b], ctx_q);
					} else {
						fmpz_set(nrb, l0i.c[b]);
					}
					rs_from_fmpz(sc[0], nrb);
					rp_addmul(ru[aex_basis_idx(a, b)], rr[i][a].r, sc[0]);
				}
			}
			for (int c = 1; c < AEX_DEG; c++) {
				result &= rp_is_zero(ru[c]);
			}
			/* The quotient's first coordinate, in the coefficient domain the
			 * commitment opens in. */
			rp_to_nfl(m[i], ru[0]);
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
	fmpz_mod_ctx_clear(ctx_q);
	delete[] rr;
	delete[] ru;
	delete rx;
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

/* --- The membership sub-proof used by the proof of shuffle --------------- */

/* Setup shared by every membership proof: the interpolation nodes and the
 * Lagrange basis depend on TAU alone, so they are built once. */
/* One pass of the proof. With the challenge in GR(q, AEX_DEG) the algebraic
 * term is 18 TAU / p_min^AEX_DEG, which at degree 4 is 2^-162, so AEX_REPS is 1
 * and what the proof answers to is the column test alone. The verifier requires
 * every pass, as the test of this file runs it. */
struct pismall_pass {
	commit_t com;
	vector < params::poly_q > rd;
	fmpz_mod_poly_t f[V][AEX_DEG], h[2][V][AEX_DEG];
	gr_t rf[ETA], rh[ETA];
	aex_open_t o;
};

struct pismall_const {
	pismall_pass pass[AEX_REPS];
};

/* Initialise a generator for the prover's masking witness. s_0, the witness
 * that masks the real one in the published f, comes out of this, and
 * flint_rand_init() seeds deterministically: left at that, every run of the
 * binary produces the same mask and anyone can recompute it, so the proof stops
 * being zero-knowledge. The generator inside pismall_hash() is a different
 * matter and is seeded from the transcript on purpose, that being Fiat-Shamir.
 */
static void aex_rand_init(flint_rand_t r) {
	ulong seed[2];

	flint_rand_init(r);
	if (getrandom(seed, sizeof(seed), 0) != (ssize_t) sizeof(seed)) {
		fprintf(stderr, "ERROR: could not read entropy for the AEx mask\n");
		abort();
	}
	flint_rand_set_seed(r, seed[0], seed[1]);
}

static int mono_ready;
static flint_rand_t mono_rand;
static fmpz_mod_ctx_t mono_ctx;
static fmpz_t mono_q, mono_a[TAU];
static fmpz_mod_poly_t mono_lag[TAU + 1];

static void pismall_const_init(void) {
	fmpz_t w;

	if (mono_ready) {
		return;
	}
	pismall_alloc();
	aex_rand_init(mono_rand);
	fmpz_init(mono_q);
	fmpz_set_mpz(mono_q, params::poly_q::moduli_product());
	fmpz_mod_ctx_init(mono_ctx, mono_q);
	aex_ntt_setup(mono_ctx);
	for (size_t i = 0; i <= TAU; i++) {
		fmpz_mod_poly_init(mono_lag[i], mono_ctx);
	}
	fmpz_init(w);
	aex_root_tau(w, mono_ctx);
	for (size_t i = 0; i < TAU; i++) {
		fmpz_init(mono_a[i]);
		fmpz_mod_pow_ui(mono_a[i], w, i, mono_ctx);
	}
	fmpz_clear(w);
	pismall_setup(mono_lag, mono_a, mono_q, mono_rand, mono_ctx);
	mono_ready = 1;
}

void pismall_const_clear(void) {
	if (!mono_ready) {
		return;
	}
	for (size_t i = 0; i <= TAU; i++) {
		fmpz_mod_poly_clear(mono_lag[i], mono_ctx);
	}
	for (size_t i = 0; i < TAU; i++) {
		fmpz_clear(mono_a[i]);
	}
	aex_ntt_clear();
	fmpz_mod_ctx_clear(mono_ctx);
	fmpz_clear(mono_q);
	flint_rand_clear(mono_rand);
	pismall_free();
	mono_ready = 0;
}

pismall_const_t *pismall_const_prove(comkey_t & key, commit_t * P,
		vector < params::poly_q > *r, params::poly_q * sigma, size_t n) {
	pismall_const_t *pi = new pismall_const_t;
	gr_t x;

	assert(n >= 1 && n <= TAU);
	pismall_const_init();
	aex_scalar_matrix(key);
	aex_scalar_stmt(P, n);
	aex_scalar_wit(r, sigma, n);

	gr_init(x);
	for (int rep = 0; rep < AEX_REPS; rep++) {
		pismall_pass & ps = pi->pass[rep];

		for (int i = 0; i < V; i++) {
			for (int c = 0; c < AEX_DEG; c++) {
				fmpz_mod_poly_init(ps.f[i][c], mono_ctx);
				fmpz_mod_poly_init(ps.h[0][i][c], mono_ctx);
				fmpz_mod_poly_init(ps.h[1][i][c], mono_ctx);
			}
		}
		for (size_t i = 0; i < ETA; i++) {
			gr_init(ps.rf[i]);
			gr_init(ps.rh[i]);
		}
		ps.rd.resize(WIDTH);
		bdlop_sample_rand(ps.rd);
		pismall_prover(ps.com, x, ps.f, ps.rf, ps.h, ps.rh, ps.rd, key,
				mono_lag, mono_rand, mono_ctx, ps.o);
	}
	gr_clear(x);

	return pi;
}

int pismall_const_verify(pismall_const_t * pi, comkey_t & key, commit_t * P,
		size_t n) {
	if (pi == NULL || n < 1 || n > TAU) {
		return 0;
	}
	pismall_const_init();
	aex_scalar_matrix(key);
	aex_scalar_stmt(P, n);

	int result = 1;
	for (int rep = 0; rep < AEX_REPS; rep++) {
		pismall_pass & ps = pi->pass[rep];

		result &= pismall_verifier(ps.com, ps.f, ps.rf, ps.h, ps.rh, ps.rd,
				key, mono_lag, mono_rand, mono_ctx, ps.o);
	}

	return result;
}

size_t pismall_const_bytes(const pismall_const_t * pi) {
	size_t n = 0;

	if (pi == NULL) {
		return 0;
	}
	for (int rep = 0; rep < AEX_REPS; rep++) {
		const pismall_pass & ps = pi->pass[rep];
		size_t coef = (params::poly_q::bits_in_moduli_product() + 7) / 8;

		/* The commitment and its randomness, then f and h, all uniform. */
		n += (1 + ps.com.c2.size()) * params::poly_q::degree * coef;
		n += ps.rd.size() * params::poly_q::degree * coef;
		n += 3 * V * AEX_DEG * params::poly_q::degree * coef;
		/* The Reed-Solomon randomness. */
		n += 2 * ETA * AEX_DEG * coef;
		/* The opening: root, indices, columns, Merkle paths. The columns are
		 * packed symbols already and there is no distribution to exploit. */
		n += BLAKE3_OUT_LEN;
		n += ETA * sizeof(size_t);
		n += ETA * AEX_COLBYTES;
		n += ETA * (ps.o.levels - 1) * BLAKE3_OUT_LEN;
	}
	return n;
}

void pismall_const_free(pismall_const_t * pi) {
	if (pi == NULL) {
		return;
	}
	for (int rep = 0; rep < AEX_REPS; rep++) {
		pismall_pass & ps = pi->pass[rep];

		for (int i = 0; i < V; i++) {
			for (int c = 0; c < AEX_DEG; c++) {
				fmpz_mod_poly_clear(ps.f[i][c], mono_ctx);
				fmpz_mod_poly_clear(ps.h[0][i][c], mono_ctx);
				fmpz_mod_poly_clear(ps.h[1][i][c], mono_ctx);
			}
		}
		for (size_t i = 0; i < ETA; i++) {
			gr_clear(ps.rf[i]);
			gr_clear(ps.rh[i]);
		}
		aex_open_clear(ps.o);
	}
	delete pi;
}

#ifdef MAIN
/* Commit to TAU ring constants sigma_i = i, or, when scalar is false, to
 * elements that are not constants, and build the relation for them. */
static void aex_scalar_test_setup(comkey_t & key, commit_t * P,
		vector < params::poly_q > *r, params::poly_q * sigma, int scalar) {
	array < mpz_t, params::poly_q::degree > c;
	vector < params::poly_q > msg(1);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(c[i], (params::poly_q::bits_in_moduli_product() << 2));
	}
	for (size_t i = 0; i < TAU; i++) {
		for (size_t l = 0; l < params::poly_q::degree; l++) {
			mpz_set_ui(c[l], 0);
		}
		mpz_set_ui(c[0], i);
		if (!scalar) {
			mpz_set_ui(c[1], 1);
		}
		sigma[i].mpz2poly(c);
		msg[0] = sigma[i];
		r[i].resize(WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(P[i], msg, key, r[i]);
	}
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(c[i]);
	}
	aex_scalar_matrix(key);
	aex_scalar_stmt(P, TAU);
	aex_scalar_wit(r, sigma, TAU);
}

#define AEX_N4  (4 * TAU)

/* Exact division by X^TAU - 1 into a separate buffer: Q_{m-TAU} = c_m + Q_m,
 * taken from the top. src and dst must not alias -- computing it in place
 * silently evaluates a different recurrence. */
static size_t aex_divl0(aex_w * dst, const aex_w * src, size_t len) {
	for (size_t i = 0; i < len; i++) {
		dst[i] = 0;
	}
	for (size_t m = len; m-- > TAU;) {
		dst[m - TAU] = aex_add(src[m], dst[m]);
	}
	return len > TAU ? len - TAU : 1;
}

/* The extraction aex_extract replaced, through P(f) on 4 TAU points and the
 * division by X^TAU - 1 level by level, for the tests. */
static void aex_extract_ref(aex_w a, const aex_w * b, aex_w out[3][TAU],
		const aex_tw_t & TT, const aex_tw_t & T4, aex_w * bufA,
		aex_w * bufB, aex_w * buft, aex_set_t set) {
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
	bufA[0] = aex_sub(bufA[0], a);
	bufA[TAU] = aex_add(bufA[TAU], a);
	for (size_t i = 0; i <= TAU; i++) {
		bufB[i] = bufA[i];
	}
	/* The pointwise polynomial on 4 TAU points: f^3 - f for the ternary set,
	 * f^2 - f for the binary one, f^2 - 1 for the signs. The two linear cases
	 * need no evaluation at all: P(f) = f is already in bufA, and P(f) = 0 is
	 * the empty constraint. */
	if (set == AEX_FREE) {
		for (size_t i = 0; i < AEX_N4; i++) {
			bufA[i] = 0;
		}
	} else if (set != AEX_ZERO) {
		aex_ntt_tw(bufA, T4, 0);
		for (size_t i = 0; i < AEX_N4; i++) {
			aex_w fi = bufA[i];
			aex_w sq = aex_mul(fi, fi);
			bufA[i] = (set == AEX_TER) ? aex_mul(sq, fi) : sq;
		}
		aex_ntt_tw(bufA, T4, 1);
		if (set == AEX_SGN) {
			bufA[0] = aex_sub(bufA[0], 1);
		} else {
			for (size_t i = 0; i <= TAU; i++) {
				bufA[i] = aex_sub(bufA[i], bufB[i]);
			}
		}
	}
	/* Q = P(f) / (X^TAU - 1) */
	size_t len = aex_divl0(bufB, bufA, AEX_N4);
	aex_w *cur = bufB, *oth = bufA;

	for (int j = 0; j < 3; j++) {
		for (size_t i = 0; i < TAU; i++) {
			buft[i] = 0;
		}
		for (size_t m = 0; m < len; m++) {
			buft[m % TAU] = aex_add(buft[m % TAU], cur[m]);
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
			cur[i] = aex_sub(cur[i], buft[i]);
		}
		len = aex_divl0(oth, cur, len);
		aex_w *sw = cur;
		cur = oth;
		oth = sw;
	}
}


/* A uniform value of Z_q, for the tests. */
static aex_w aex_randq(flint_rand_t rand) {
	fmpz_t x, Q;
	aex_w r;

	fmpz_init(x);
	fmpz_init(Q);
	aex_to_fmpz(Q, zq::MODULUS);
	fmpz_randm(x, rand, Q);
	r = aex_from_fmpz(x);
	fmpz_clear(x);
	fmpz_clear(Q);
	return r;
}

/* The straightforward transform aex_ntt_tw replaced, for the tests. */
static void aex_ntt_tw_ref(aex_w * a, const aex_tw_t & t, int inverse) {
	const size_t n = t.n;
	const aex_w *W = inverse ? t.iw : t.w;

	for (size_t i = 1, j = 0; i < n; i++) {
		size_t bit = n >> 1;
		for (; j & bit; bit >>= 1) {
			j ^= bit;
		}
		j ^= bit;
		if (i < j) {
			aex_w x = a[i]; a[i] = a[j]; a[j] = x;
		}
	}
	for (size_t len = 2; len <= n; len <<= 1) {
		size_t step = n / len;
		for (size_t i = 0; i < n; i += len) {
			for (size_t k = 0; k < len / 2; k++) {
				size_t idx = k * step;
				aex_w u = a[i + k];
				aex_w v = aex_mul(a[i + k + len / 2], W[idx]);
				a[i + k] = aex_add(u, v);
				a[i + k + len / 2] = aex_sub(u, v);
			}
		}
	}
	if (inverse) {
		for (size_t i = 0; i < n; i++) {
			a[i] = aex_mul(a[i], t.ninv);
		}
	}
}

static void test(flint_rand_t rand) {
	fmpz_t q, a[TAU];
	gr_t x, rf[ETA], rh[ETA];
	fmpz_mod_poly_t poly;
	fmpz_mod_ctx_t ctx, ctx_q;
	comkey_t key;
	commit_t com;
	vector < params::poly_q > rd;
	fmpz_mod_poly_t f[V][AEX_DEG], lag[TAU + 1], h[2][V][AEX_DEG];

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
		for (int c = 0; c < AEX_DEG; c++) {
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

	/* Create a total of TAU relations t_i = A * s_i. Two components are given
	 * the sets the proof of shuffle needs, so that those paths are covered
	 * here too and not only where they are used. */
	aex_sets[V - 3] = AEX_SCALAR;
	aex_sets[V - 2] = AEX_BIN;
	aex_sets[V - 1] = AEX_SGN;
	for (int i = 0; i < TAU; i++) {
		fmpz_mod_poly_init(lag[i], ctx);
		for (int j = 0; j < V; j++) {
			if (aex_sets[j] == AEX_TER) {
				s[i][j] = nfl::hwt_dist {
				2 *DEGREE / 3};
				s[i][j].ntt_pow_phi();
			} else {
				aex_sample_set(s[i][j], aex_sets[j]);
			}
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
	TEST_ONCE("aex_mul agrees with FLINT's") {
		/* zq's folding reduction against fmpz, at random operands and at the
		 * extremes. */
		const aex_w ends[4] = { 0, 1, zq::MODULUS - 2, zq::MODULUS - 1 };
		fmpz_t fa, fb, fc;
		int ok = 1;

		fmpz_init(fa); fmpz_init(fb); fmpz_init(fc);
		for (int k = 0; k < 100016; k++) {
			const aex_w a = (k < 16) ? ends[k / 4] : aex_randq(rand);
			const aex_w b = (k < 16) ? ends[k % 4] : aex_randq(rand);

			aex_to_fmpz(fa, a);
			aex_to_fmpz(fb, b);
			fmpz_mod_mul(fc, fa, fb, ctx_q);
			ok &= aex_mul(a, b) == aex_from_fmpz(fc);
		}
		fmpz_clear(fa); fmpz_clear(fb); fmpz_clear(fc);
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("the NTT agrees with the straightforward one") {
		/* Both lengths the extraction uses, both directions, at random inputs
		 * and at all q - 1. */
		int ok = 1;
		aex_w *x = new aex_w[AEX_N4], *y = new aex_w[AEX_N4];

		for (size_t n : { (size_t) TAU, (size_t) AEX_N4 }) {
			aex_tw_t tw;
			aex_tw_init(tw, n, aex_root(n));
			for (int rep = 0; rep < 6 && ok; rep++) {
				for (size_t i = 0; i < n; i++) {
					x[i] = (rep == 0) ? zq::MODULUS - 1 : aex_randq(rand);
					y[i] = x[i];
				}
				aex_ntt_tw(x, tw, rep & 1);
				aex_ntt_tw_ref(y, tw, rep & 1);
				for (size_t i = 0; i < n; i++) ok &= x[i] == y[i];
			}
			aex_tw_clear(tw);
		}
		delete[] x;
		delete[] y;
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("extraction by derivatives agrees with division") {
		/* aex_extract against aex_extract_ref, for every set, at random a and
		 * at a = q - 1, with b in the set as an honest witness has it. */
		aex_w *bufA = new aex_w[AEX_N4], *bufB = new aex_w[AEX_N4];
		aex_w *buft = new aex_w[TAU], *buf = new aex_w[3 * TAU];
		static aex_w o0[3][TAU], o1[3][TAU];
		aex_w b[TAU];
		aex_tw_t TT, T4;
		int ok = 1;

		aex_tw_init(TT, TAU, aex_root(TAU));
		aex_tw_init(T4, AEX_N4, aex_root(AEX_N4));
		for (aex_set_t set : { AEX_TER, AEX_BIN, AEX_SGN, AEX_ZERO, AEX_FREE }) {
			for (int rep = 0; rep < 20; rep++) {
				const aex_w a = (rep == 0) ? zq::MODULUS - 1 : aex_randq(rand);
				for (size_t i = 0; i < TAU; i++) {
					const aex_w v = n_randint(rand, 3);
					b[i] = (set == AEX_TER) ? (v == 2 ? zq::MODULUS - 1 : v) :
							(set == AEX_BIN) ? (v & 1) :
							(set == AEX_SGN) ? ((v & 1) ? zq::MODULUS - 1 : 1) :
							(set == AEX_ZERO) ? 0 : aex_randq(rand);
				}
				aex_extract(a, b, o0, TT, buf, set);
				aex_extract_ref(a, b, o1, TT, T4, bufA, bufB, buft, set);
				for (size_t j = 0; j < 3; j++) {
					for (size_t i = 0; i < TAU; i++) {
						ok &= o0[j][i] == o1[j][i];
					}
				}
			}
		}
		aex_tw_clear(TT);
		aex_tw_clear(T4);
		delete[] bufA;
		delete[] bufB;
		delete[] buft;
		delete[] buf;
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("the pruned DIF transform is the NTT in bit-reversed order") {
		/* aex_ntt_dif on the encoder's tables against the straightforward
		 * transform, with x zero past the message length, at random inputs
		 * and at all q - 1. */
		const size_t len = 2 * params::poly_q::degree + ETA;
		aex_w *x = new aex_w[AEX_COLS], *y = new aex_w[AEX_COLS];
		int ok = 1;

		for (int rep = 0; rep < 2; rep++) {
			for (size_t i = 0; i < AEX_COLS; i++) {
				x[i] = (i >= len) ? 0 : (rep == 0) ? zq::MODULUS - 1 : aex_randq(rand);
				y[i] = x[i];
			}
			aex_ntt_dif(x, aex_tw, len);
			aex_ntt_tw_ref(y, aex_tw, 0);
			for (size_t c = 0; c < AEX_COLS; c++) {
				ok &= x[c] == y[aex_tw.rev[c]];
			}
		}
		delete[] x;
		delete[] y;
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("GR multiplication on aex_w agrees with gr_mul") {
		/* grq_mul against gr_mul over fmpz, at random elements and at ones
		 * whose coordinates are all q - 1. */
		gr_t ga, gb, gc;
		fmpz_t Q;
		aex_rscalar sc;
		int ok = 1;

		gr_init(ga); gr_init(gb); gr_init(gc);
		fmpz_init(Q);
		fmpz_set_mpz(Q, params::poly_q::moduli_product());
		for (int k = 0; k < 200 && ok; k++) {
			aex_w ra[AEX_DEG], rb[AEX_DEG], rc_[AEX_DEG];

			for (int i = 0; i < AEX_DEG; i++) {
				if (k == 0) {
					fmpz_sub_ui(ga.c[i], Q, 1);
					fmpz_sub_ui(gb.c[i], Q, 1);
				} else {
					fmpz_randm(ga.c[i], rand, Q);
					fmpz_randm(gb.c[i], rand, Q);
				}
			}
			gr_mul(gc, ga, gb, ctx_q);
			for (int i = 0; i < AEX_DEG; i++) {
				rs_from_fmpz(sc, ga.c[i]); ra[i] = sc.s;
				rs_from_fmpz(sc, gb.c[i]); rb[i] = sc.s;
			}
			grq_mul(rc_, ra, rb);
			for (int i = 0; i < AEX_DEG; i++) {
				rs_from_fmpz(sc, gc.c[i]);
				ok &= rc_[i] == sc.s;
			}
		}
		gr_clear(ga); gr_clear(gb); gr_clear(gc);
		fmpz_clear(Q);
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("residue-form encoding and sums agree with FLINT's") {
		/* aex_encode_res against aex_encode on the same message, and
		 * rp_addmul summed then rp_to_fmpz against scalar_mul and add. */
		params::poly_q p0 = nfl::uniform(), p1 = nfl::uniform();
		aex_rpoly *x0 = new aex_rpoly, *x1 = new aex_rpoly, *acc = new aex_rpoly;
		fmpz_mod_poly_t a0, a1, u, w;
		fmpz *rr = _fmpz_vec_init(ETA);
		fmpz_t Q, k0, k1;
		aex_rscalar s0, s1;
		aex_code_t *c0 = new aex_code_t, *c1 = new aex_code_t;
		int ok = 1;

		fmpz_init(Q); fmpz_init(k0); fmpz_init(k1);
		fmpz_set_mpz(Q, params::poly_q::moduli_product());
		fmpz_mod_poly_init(a0, ctx_q); fmpz_mod_poly_init(a1, ctx_q);
		fmpz_mod_poly_init(u, ctx_q); fmpz_mod_poly_init(w, ctx_q);
		for (size_t i = 0; i < ETA; i++) fmpz_randm(rr + i, rand, Q);
		rp_from_nfl(*x0, p0);
		rp_from_nfl(*x1, p1);
		poly_from(a0, p0, ctx_q);
		poly_from(a1, p1, ctx_q);
		aex_encode(*c0, a0, a1, rr, ctx_q);
		aex_encode_res(*c1, x0->r, x1->r, rr);
		ok &= memcmp(c0->w, c1->w, sizeof(c0->w)) == 0;
		fmpz_mod_poly_zero(u, ctx_q);
		aex_encode(*c0, u, a1, rr, ctx_q);
		aex_encode_res(*c1, NULL, x1->r, rr);
		ok &= memcmp(c0->w, c1->w, sizeof(c0->w)) == 0;
		/* k0 a0 + k1 a1, at a random scalar and at q - 1. */
		for (int t = 0; t < 2; t++) {
			fmpz_randm(k0, rand, Q);
			if (t) fmpz_sub_ui(k1, Q, 1); else fmpz_randm(k1, rand, Q);
			rs_from_fmpz(s0, k0);
			rs_from_fmpz(s1, k1);
			memset(acc, 0, sizeof(*acc));
			rp_addmul(*acc, x0->r, s0);
			rp_addmul(*acc, x1->r, s1);
			rp_to_fmpz(w, *acc, ctx_q);
			fmpz_mod_poly_scalar_mul_fmpz(u, a0, k0, ctx_q);
			fmpz_mod_poly_scalar_addmul_fmpz(u, a1, k1, ctx_q);
			ok &= fmpz_mod_poly_equal(u, w, ctx_q);
		}
		delete x0; delete x1; delete acc; delete c0; delete c1;
		_fmpz_vec_clear(rr, ETA);
		fmpz_clear(Q); fmpz_clear(k0); fmpz_clear(k1);
		fmpz_mod_poly_clear(a0, ctx_q); fmpz_mod_poly_clear(a1, ctx_q);
		fmpz_mod_poly_clear(u, ctx_q); fmpz_mod_poly_clear(w, ctx_q);
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_ONCE("scalar multiplication agrees with FLINT's") {
		fmpz_mod_poly_t u, w, pp;
		fmpz_t x, Q;
		int ok = 1;

		fmpz_init(x);
		fmpz_init(Q);
		fmpz_set_mpz(Q, params::poly_q::moduli_product());
		fmpz_mod_poly_init(u, ctx_q);
		fmpz_mod_poly_init(w, ctx_q);
		fmpz_mod_poly_init(pp, ctx_q);
		for (int k = 0; k < 6 && ok; k++) {
			fmpz_mod_poly_randtest(pp, rand, params::poly_q::degree, ctx_q);
			/* Random, 0, 1, q - 1, then one past q, which goes to FLINT. */
			if (k == 0 || k == 5) fmpz_randm(x, rand, Q);
			if (k == 1) fmpz_zero(x);
			if (k == 2) fmpz_one(x);
			if (k == 3) fmpz_sub_ui(x, Q, 1);
			if (k == 4) fmpz_add_ui(x, Q, 5);
			fmpz_mod_poly_scalar_mul_fmpz(u, pp, x, ctx_q);
			scalar_mul(w, pp, x, ctx_q);
			ok &= fmpz_mod_poly_equal(u, w, ctx_q);
			scalar_mul(pp, pp, x, ctx_q); /* in place */
			ok &= fmpz_mod_poly_equal(u, pp, ctx_q);
		}
		fmpz_mod_poly_clear(u, ctx_q);
		fmpz_mod_poly_clear(w, ctx_q);
		fmpz_mod_poly_clear(pp, ctx_q);
		fmpz_clear(x);
		fmpz_clear(Q);
		TEST_ASSERT(ok, end);
	} TEST_END;

	TEST_BEGIN("conversion is correct") {
		for (int i = 0; i < R; i++) {
			for (int j = 0; j < V; j++) {
				poly_from(f[j][0], A[i][j], ctx);
				poly_to(rd[0], f[j][0], ctx);
				TEST_ASSERT(util::equal(rd[0], A[i][j]), end);
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
				TEST_ASSERT(util::equal(rd[0], rd[1]), end);
			}
		}
	} TEST_END;

	pismall_setup(lag, a, q, rand, ctx);

	bdlop_keygen(key);
	bdlop_sample_rand(rd);

	TEST_ONCE("a codeword is the message evaluated at the roots of unity") {
		/* Symbol c of Encode(m0, m1, r) is the message
		 * polynomial (m0, m1, r, then zeros) evaluated at w^rev(c), with w the
		 * primitive AEX_COLS-th root aex_ntt_setup took: checked by Horner
		 * at a few columns, the first and the last among them. */
		aex_code_t *cw = new aex_code_t;
		fmpz_mod_poly_t m0, m1;
		fmpz_t r[ETA], cf;
		int ok = 1;

		fmpz_mod_poly_init(m0, ctx); fmpz_mod_poly_init(m1, ctx);
		fmpz_init(cf);
		fmpz_mod_poly_randtest(m0, rand, params::poly_q::degree, ctx);
		fmpz_mod_poly_randtest(m1, rand, params::poly_q::degree, ctx);
		for (size_t i = 0; i < ETA; i++) {
			fmpz_init(r[i]);
			fmpz_randm(r[i], rand, q);
		}
		aex_encode(*cw, m0, m1, (const fmpz *) r, ctx);
		const size_t N = params::poly_q::degree, cols[4] = { 0, 1, 5000, AEX_COLS - 1 };
		const aex_w w = aex_tw.w[1];
		for (size_t t = 0; t < 4; t++) {
			const aex_w x = aex_pow(w, aex_tw.rev[cols[t]]);
			aex_w acc = 0;
			/* Horner from the top coefficient, 2N + ETA - 1, down. */
			for (size_t i = 2 * N + ETA; i-- > 0;) {
				if (i < N) fmpz_mod_poly_get_coeff_fmpz(cf, m0, i, ctx);
				else if (i < 2 * N) fmpz_mod_poly_get_coeff_fmpz(cf, m1, i - N, ctx);
				else fmpz_set(cf, r[i - 2 * N]);
				acc = aex_add(aex_mul(acc, x), aex_from_fmpz(cf));
			}
			ok &= aex_code_sym(cw, cols[t]) == acc;
		}
		for (size_t i = 0; i < ETA; i++) fmpz_clear(r[i]);
		fmpz_clear(cf);
		fmpz_mod_poly_clear(m0, ctx); fmpz_mod_poly_clear(m1, ctx);
		delete cw;
		TEST_ASSERT(ok, end);
	} TEST_END;

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

	TEST_ONCE("the blocked tree hashes the columns aex_column gives") {
		/* After a proof, the leaves of a rebuilt tree are the hashes of
		 * aex_column's bytes, column by column. */
		aex_tree_t tt;
		uint8_t *scratch = new uint8_t[AEX_COLBYTES], hc[BLAKE3_OUT_LEN];
		int ok = 1;

		aex_tree_build(tt);
		for (size_t c = 0; c < AEX_COLS && ok; c += 97) {
			aex_hash_column(hc, c, scratch);
			ok &= memcmp(hc, tt.node + c * BLAKE3_OUT_LEN, BLAKE3_OUT_LEN) == 0;
		}
		aex_hash_column(hc, AEX_COLS - 1, scratch);
		ok &= memcmp(hc, tt.node + (AEX_COLS - 1) * BLAKE3_OUT_LEN, BLAKE3_OUT_LEN) == 0;
		aex_tree_clear(tt);
		delete[] scratch;
		TEST_ASSERT(ok, end);
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
		/* X^AEX_DEG - AEX_NR is only irreducible while AEX_NR is a non-residue
		 * modulo q. If that ever stops holding the extension silently
		 * collapses and the soundness claim with it. At degree 4 the criterion
		 * also asks that AEX_NR not lie in -4 (Z_q)^4, which follows: q = 1
		 * mod 4, so -1 is a square, and -AEX_NR/4 is then a non-square and
		 * cannot be a fourth power. Both halves are checked below. */
		live = 1;
		{
			fmpz_t pi, e, w;
			fmpz_init(pi);
			aex_to_fmpz(pi, zq::MODULUS);
			fmpz_init(e);
			fmpz_init(w);
			fmpz_sub_ui(e, pi, 1);
			fmpz_fdiv_q_2exp(e, e, 1);
			fmpz_set_ui(w, AEX_NR);
			fmpz_powm(w, w, e, pi);          /* Euler: -1 iff a non-residue */
			fmpz_sub_ui(e, pi, 1);
			live &= fmpz_equal(w, e);
			/* q = 1 mod 4, the other half of the degree-4 criterion. */
			live &= (zq::MODULUS % 4 == 1);
			fmpz_clear(pi);
			fmpz_clear(e);
			fmpz_clear(w);
		}
		for (int c = 1; c < AEX_DEG; c++) {
			live &= !fmpz_is_zero(x.c[c]);
			for (int k = 0; k < V; k++) {
				live &= !fmpz_mod_poly_is_zero(f[k][c], ctx);
				live &= !fmpz_mod_poly_is_zero(h[0][k][c], ctx);
				live &= !fmpz_mod_poly_is_zero(h[1][k][c], ctx);
			}
			for (size_t i = 0; i < ETA; i++) {
				any |= !fmpz_is_zero(rf[i].c[c]);
				any |= !fmpz_is_zero(rh[i].c[c]);
			}
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

	TEST_ONCE("AEX proof does not repeat its mask") {
		/* Two proofs of the same statement must differ, because s_0 is drawn
		 * afresh. They would be identical if the generator producing it were
		 * left at flint_rand_init()'s fixed seed, which is exactly what makes
		 * the published f stop hiding the witness. Nothing else in this suite
		 * would notice: every other test asks only whether the verifier
		 * accepts, and a proof with a predictable mask verifies perfectly. */
		flint_rand_t r1, r2;
		aex_open_t o1, o2;
		int differ;

		/* Fresh generators, as two runs of the binary would have. Drawing twice
		 * from one generator proves nothing: the stream advances either way,
		 * so the proofs differ even when the seed is fixed. */
		aex_rand_init(r1);
		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, r1, ctx, o1);
		aex_rand_init(r2);
		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, r2, ctx, o2);
		differ = memcmp(o1.root, o2.root, BLAKE3_OUT_LEN) != 0;
		flint_rand_clear(r1);
		flint_rand_clear(r2);
		aex_open_clear(o1);
		aex_open_clear(o2);
		TEST_ASSERT(differ == 1, end);
	} TEST_END;

	TEST_ONCE("AEX proof rejects a witness that is not a constant") {
		/* Component V - 3 is declared AEX_SCALAR, so every coefficient above
		 * the constant one must be zero. Unlike the sets of the KNOWN GAP
		 * below, this constraint is exact over Z_q: f = 0 has a single root
		 * however q factors. That is what makes it usable as the algebraic
		 * half of the membership proof of the shuffle. */
		array < mpz_t, params::poly_q::degree > c;
		params::poly_q keep = s[0][V - 3];
		aex_open_t o;
		int ok;

		for (size_t l = 0; l < params::poly_q::degree; l++) {
			mpz_init2(c[l], (params::poly_q::bits_in_moduli_product() << 2));
			mpz_set_ui(c[l], 0);
		}
		mpz_set_ui(c[0], 7);
		mpz_set_ui(c[1], 1);            /* no longer a constant */
		s[0][V - 3].mpz2poly(c);
		s[0][V - 3].ntt_pow_phi();
		for (size_t l = 0; l < params::poly_q::degree; l++) {
			mpz_clear(c[l]);
		}
		for (int j = 0; j < R; j++) {
			t[0][j] = 0;
			for (int k = 0; k < V; k++) {
				t[0][j] = t[0][j] + A[j][k] * s[0][k];
			}
		}
		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		ok = pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		aex_open_clear(o);
		/* put the honest witness back for the tests below */
		s[0][V - 3] = keep;
		for (int j = 0; j < R; j++) {
			t[0][j] = 0;
			for (int k = 0; k < V; k++) {
				t[0][j] = t[0][j] + A[j][k] * s[0][k];
			}
		}
		TEST_ASSERT(ok == 0, end);
	} TEST_END;

	TEST_ONCE("AEX proof rejects a coefficient outside its set") {
		/* With two primes this was a known gap: f^3 - f had 27 roots in Z_q,
		 * and a witness +1 modulo one prime and -1 modulo the other in every
		 * coefficient passed as ternary. q is prime now, so the roots are
		 * -1, 0, 1 and nothing else, and the sets are exact over Z_q. The
		 * witness below has every coefficient 2. See SOUNDNESS.md, sections
		 * 5.1 and 5.2. */
		aex_open_t o = { };
		params::poly_q z, s00 = s[0][0];
		vector < params::poly_q > t0(t[0], t[0] + R);
		int ok;

		z = 0;
		for (size_t l = 0; l < params::poly_q::degree; l++) {
			z(0, l) = 2;
		}
		z.ntt_pow_phi();
		s[0][0] = z;
		for (int j = 0; j < R; j++) {
			t[0][j] = 0;
			for (int k = 0; k < V; k++) {
				t[0][j] = t[0][j] + A[j][k] * s[0][k];
			}
		}
		ok = pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		ok = ok && pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		aex_open_clear(o);
		/* The benchmarks below prove the honest witness again. */
		s[0][0] = s00;
		for (int j = 0; j < R; j++) {
			t[0][j] = t0[j];
		}
		TEST_ASSERT(ok == 0, end);
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

	TEST_ONCE("constant membership proof is consistent") {
		commit_t *P = new commit_t[TAU];
		vector < params::poly_q > *pr = new vector < params::poly_q >[TAU];
		params::poly_q *sigma = new params::poly_q[TAU];
		int ok = 1;

		aex_scalar_test_setup(key, P, pr, sigma, 1);
		/* Through the API the proof of shuffle calls, rather than by repeating
		 * its steps here: pismall_const_prove carries its own one-time setup,
		 * and nothing else exercises it. */
		for (int rep = 0; rep < AEX_REPS; rep++) {
			pismall_const_t *pc = pismall_const_prove(key, P, pr, sigma, TAU);
			ok &= pismall_const_verify(pc, key, P, TAU);
			pismall_const_free(pc);
		}
		delete[]sigma;
		delete[]pr;
		delete[]P;
		TEST_ASSERT(ok == 1, end);
	} TEST_END;

	TEST_ONCE("constant membership rejects a non-constant") {
		/* The declaration is exact over Z_q, so unlike the binary and ternary
		 * sets this rejection needs no help from a norm bound: a witness with
		 * any non-zero coefficient above the constant one fails outright. */
		commit_t *P = new commit_t[TAU];
		vector < params::poly_q > *pr = new vector < params::poly_q >[TAU];
		params::poly_q *sigma = new params::poly_q[TAU];
		aex_open_t o;
		int ok;

		aex_scalar_test_setup(key, P, pr, sigma, 0);
		pismall_prover(com, x, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		ok = pismall_verifier(com, f, rf, h, rh, rd, key, lag, rand, ctx, o);
		aex_open_clear(o);
		delete[]sigma;
		delete[]pr;
		delete[]P;
		TEST_ASSERT(ok == 0, end);
	} TEST_END;

  end:
	for (int i = 0; i < V; i++) {
		for (int c = 0; c < AEX_DEG; c++) {
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

	aex_rand_init(rand);
	pismall_alloc();

	printf("\n** Tests for lattice-based AEX proof:\n\n");
	test(rand);

	pismall_free();
	flint_rand_clear(rand);

	return test_failures() != 0;
}
#endif
