#include <cmath>

#include "blake3.h"
#include "test.h"
#include "bench.h"
#include "common.h"
#include "pibnd.h"
#include "sample_z_small.h"
#include "sample_z_large.h"

/**
 * Stores a 128-bit signed integer in an mpz_t. GMP only offers mpz_set_si for
 * long, which is too narrow for the coefficients of the last row.
 */
static void mpz_set_int128(mpz_t rop, __int128 op) {
	int negative = (op < 0);
	__uint128_t abs = negative ? -((__uint128_t) op) : (__uint128_t) op;

	mpz_set_ui(rop, (uint64_t) (abs >> 64));
	mpz_mul_2exp(rop, rop, 64);
	mpz_add_ui(rop, rop, (uint64_t) abs);
	if (negative) {
		mpz_neg(rop, rop);
	}
}

#define R       (HEIGHT+1)
/* Number of witness components. The mix-net's own instance of this proof has
 * V = HEIGHT + 3; the proof of shuffle links this file with V = WIDTH + 1, the
 * shape of a BDLOP commitment equation, to bound the norm of the openings of
 * its commitments to the sigma_i. */
#ifndef PIBND_V
#define PIBND_V (HEIGHT+3)
#endif
#define V       PIBND_V
/* Number of relations and of parallel repetitions. These drive every large
 * buffer below, so they can be overridden (e.g. make CONFIG="-DTAU=10 -DNTI=8")
 * to test on a small machine; the paper's benchmarks use the defaults. */
#ifndef TAU
#define TAU     1000
#endif
/* Columns of the response matrix Z, which is what the soundness of the
 * amortized proof is bought with: a prover succeeding with probability
 * 2^-(LEVEL) is extractable, and the challenge column of one statement has
 * NTI bits of entropy, so Lemma 3 of Baum et al. needs NTI >= LEVEL + 2. */
#ifndef NTI
#define NTI     130
#endif

/* Number of rows of S' handled by the first of the two rejection-sampling
 * checks; the last row is handled by the second. */
#define ANEX_K      (V - 1)

/* How many times the prover retries rejection sampling before giving up and
 * emitting the masked opening it has. An honest prover passes both checks with
 * probability about 1/3, so giving up is a 3^-64 event; a prover whose witness
 * is not short never passes, and emitting the opening lets the verifier reject
 * it on the norm test instead of looping here forever. */
#define PIBND_TRIES 64

/* Infinity-norm bound on the last witness row (the decryption noise E in the
 * mix-net; ternary like the others in the test below). */
#ifndef ANEX_E_INF
#define ANEX_E_INF  BETA
#endif

/*
 * sigma_ANEx. Appendix B of the paper bounds
 *     B_Bnd = sqrt(2N) sigma_Bnd <= 1.35 sqrt(k) N sqrt(N) B_Com,
 * i.e. sigma_Bnd = 0.954 sqrt(k) N B_Com, which carries no factor for the tau
 * statements the product S'C' sums over, nor for the NTI columns the rejection
 * sampling below tests as one vector. Both are needed: sigma has to track
 * ||S'C'||, which measurement puts at 0.49 B_Com sqrt(k N tau NTI) and so
 * above the paper's sigma from tau NTI = 2^13.9 on -- an eighth of the real
 * parameters -- and past that point the honest prover exhausts PIBND_TRIES.
 * The factor below tracks the measured growth, which leaves sigma about 86
 * times ||S'C'||. The rejection sampling below runs Figure 2 of the paper with
 * b = 1 -- it rejects on <Z, S'C'> < 0 first -- and takes its M from ||S'C'||,
 * so no value of sigma is invalid: a small one only costs restarts, at
 * 1 / 2 exp(||S'C'||^2 / 2 sigma^2) each. The 0.954 above is what that trade
 * settles at for a fixed M of sqrt(3), and 86 times it is about six bits more
 * than the norm bound needs. See SOUNDNESS.md section 9 for where they can be
 * spent: the decryption phase, whose q answers to this bound alone, rather
 * than the shuffle, whose q is pinned from below by the pass count of its
 * product argument.
 */
static const double SIGMA_ANEX =
		0.954 * BETA * DEGREE * sqrt(ANEX_K * (double) NTI * TAU / 2.0);

/*
 * sigma-hat_ANEx, for the last row: same derivation, one row instead of k.
 */
static const double SIGMA_ANEX_HAT =
		0.954 * ANEX_E_INF * DEGREE * sqrt((double) NTI * TAU / 2.0);

/* Whether the last row needs the quad-precision sampler. sigma-hat_ANEx runs
 * past 2^64 when the last witness row is the mix-net's decryption noise, whose
 * infinity norm is far above BETA, and then it does. When the row is as short
 * as the others -- the proof of shuffle bounds a committed constant with it --
 * sigma-hat is a few thousand and the double sampler covers it, at two orders
 * of magnitude less time. Both sides of the branch are compile-time constant.
 */
static const bool ANEX_HAT_LARGE = SIGMA_ANEX_HAT > 1e15;

/* A params::poly_q is 64 KiB, so the matrices dimensioned by TAU or NTI are far
 * too large to be locals: s and t alone are 600 MiB at the default
 * parameters. They are allocated on the heap once at start-up, and the pointers
 * below index exactly like the two-dimensional arrays they replace. The prover
 * and the verifier each rederive W and C from the transcript, so one copy of
 * each is enough for both.
 *
 * NOTE: with TAU = 1000 and NTI = 130 this binary needs roughly 700 MiB, nearly
 * all of it s and t. It was 9 GiB before the challenge matrix was streamed. */
static params::poly_q A[R][V];
static params::poly_q (*s)[V], (*t)[V];
static params::poly_q (*Z)[NTI], (*W)[NTI], (*SC)[NTI];
/* One row of the challenge matrix. Both sides derive C from the transcript
 * hash and each consumes it once, row by row, so a row at a time is enough and
 * the matrix itself is never stored: at TAU = 1000 it would be 8 GiB. */
static params::poly_q *Crow;

static void pibnd_alloc(void) {
	s = new params::poly_q[TAU][V];
	t = new params::poly_q[TAU][V];
	Z = new params::poly_q[V][NTI];
	W = new params::poly_q[R][NTI];
	Crow = new params::poly_q[NTI];
	SC = new params::poly_q[V][NTI];
}

static void pibnd_free(void) {
	delete[]s;
	delete[]t;
	delete[]Z;
	delete[]W;
	delete[]Crow;
	delete[]SC;
}

static void pibnd_hash(uint8_t h[BLAKE3_OUT_LEN], params::poly_q A[R][V],
		params::poly_q t[TAU][V], params::poly_q W[R][NTI]) {
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);
	/* Hash public key. */
	for (size_t i = 0; i < R; i++) {
		for (int j = 0; j < V; j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)A[i][j].data(),
					16 * DEGREE);
		}
	}
	for (size_t i = 0; i < TAU; i++) {
		for (int j = 0; j < V; j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)t[i][j].data(),
					16 * DEGREE);
		}
	}
	for (size_t i = 0; i < R; i++) {
		for (int j = 0; j < NTI; j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)W[i][j].data(),
					16 * DEGREE);
		}
	}

	blake3_hasher_finalize(&hasher, h, BLAKE3_OUT_LEN);
}

static int pibnd_rej_sampling(params::poly_q Z[V][NTI],
		params::poly_q SC[V][NTI], int lo, int hi, double s2) {
	array < mpz_t, params::poly_q::degree > coeffs0, coeffs1;
	params::poly_q t;
	mpz_t dot, norm, qDivBy2, tmp;
	double r, M;
	int64_t seed;
	mpf_t u;
	uint8_t buf[8];
	gmp_randstate_t state;
	int result;

	/// Constructors
	mpf_init(u);
	gmp_randinit_mt(state);
	mpz_inits(dot, norm, qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs0[i], (params::poly_q::bits_in_moduli_product() << 2));
		mpz_init2(coeffs1[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
	mpz_set_ui(norm, 0);
	mpz_set_ui(dot, 0);
	for (int i = lo; i < hi; i++) {
		for (int j = 0; j < NTI; j++) {
			t = Z[i][j];
			t.invntt_pow_invphi();
			t.poly2mpz(coeffs0);
			t = SC[i][j];
			t.invntt_pow_invphi();
			t.poly2mpz(coeffs1);
			for (size_t l = 0; l < params::poly_q::degree; l++) {
				util::center(coeffs0[l], coeffs0[l],
						params::poly_q::moduli_product(), qDivBy2);
				util::center(coeffs1[l], coeffs1[l],
						params::poly_q::moduli_product(), qDivBy2);
				mpz_mul(tmp, coeffs0[l], coeffs1[l]);
				mpz_add(dot, dot, tmp);
				mpz_mul(tmp, coeffs1[l], coeffs1[l]);
				mpz_add(norm, norm, tmp);
			}
		}
	}

	if (getrandom(buf, sizeof(buf), 0) != sizeof(buf)) {
		fprintf(stderr, "ERROR: could not read entropy for rejection sampling\n");
		abort();
	}
	memcpy(&seed, buf, sizeof(buf));
	gmp_randseed_ui(state, seed);
	mpf_urandomb(u, state, mpf_get_default_prec());

	/* Reject when <z, sc> < 0, then accept with probability min(1, r) for
	 * r = exp((-2<z, sc> + ||sc||^2) / 2s2) / M. Inside that halfspace the
	 * ratio to dominate is at most exp(||sc||^2 / 2s2), which is what M is:
	 * the sqrt(3) this used to divide by is what the constant would have to be
	 * if sigma were the 0.954 ||S'C'|| the paper sizes for, and sigma is 86
	 * times that, so the fixed constant was costing restarts and nothing else.
	 * See SOUNDNESS.md section 9. */
	M = exp(mpz_get_d(norm) / (2.0 * s2));
	result = mpz_get_d(dot) < 0;
	r = -2.0 * mpz_get_d(dot) + mpz_get_d(norm);
	r = r / (2.0 * s2);
	r = exp(r) / M;
	result |= mpf_get_d(u) > r;

	mpf_clear(u);
	gmp_randclear(state);
	mpz_clears(dot, norm, qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs0[i]);
		mpz_clear(coeffs1[i]);
	}
	return result;
}

/**
 * Test if the l2-norm of r is within B = sigma * sqrt(2N).
 *
 * @param[in] r 			- the polynomial to test.
 * @param[in] sigma			- the Gaussian parameter the row was sampled with.
 */
static bool pibnd_test_norm(params::poly_q r, double sigma) {
	array < mpz_t, params::poly_q::degree > coeffs;
	mpz_t norm, qDivBy2, tmp, bound;

	/// Constructors
	mpz_inits(norm, qDivBy2, tmp, bound, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	r.poly2mpz(coeffs);
	mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
	mpz_set_ui(norm, 0);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		util::center(coeffs[i], coeffs[i],
				params::poly_q::moduli_product(), qDivBy2);
		mpz_mul(tmp, coeffs[i], coeffs[i]);
		mpz_add(norm, norm, tmp);
	}

	/* Compare to (sigma * sqrt(2N))^2 = 2 * sigma^2 * N, in mpz because
	 * sigma-hat squared overflows 64 bits at the mix-net's parameters. */
	mpz_set_d(bound, sigma);
	mpz_mul(bound, bound, bound);
	mpz_mul_ui(bound, bound, 2 * params::poly_q::degree);
	int result = mpz_cmp(norm, bound) <= 0;

	mpz_clears(norm, qDivBy2, tmp, bound, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}

	return result;
}

// Sample a challenge.
void pibnd_sample_chall(params::poly_q & f) {
	f = nfl::ZO_dist();
	f.ntt_pow_phi();
}

/* One entry of the challenge matrix: a uniform bit, as a ring constant. That is
 * the challenge set C_Bnd = {0,1} of the amortized proof, and the extractor
 * needs it: it subtracts two transcripts differing in one entry and divides by
 * the difference, which here is +-1. A ternary polynomial, which this used to
 * draw, need not be invertible in a ring splitting into 2N factors -- see
 * SOUNDNESS.md section 8 -- so the proof ran outside the argument it cites. */
static void pibnd_sample_c(params::poly_q & c) {
	uint8_t b;

	nfl::fastrandombytes(&b, sizeof(b));
	c = (uint64_t) (b & 1);
	c.ntt_pow_phi();
}

static int pibnd_prover(uint8_t h[BLAKE3_OUT_LEN], params::poly_q Z[V][NTI],
		params::poly_q A[R][V], params::poly_q t[TAU][V],
		params::poly_q s[TAU][V]) {
	std::array < mpz_t, params::poly_q::degree > coeffs;
	mpz_t qDivBy2;
	__int128 coeff;
	int rej0, rej1, tries = 0;

	mpz_init(qDivBy2);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}
	mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);

	do {
		/* Prover samples Y from Gaussian. */
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < NTI; j++) {
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					if (i < V - 1) {
						coeff = sample_z(0.0, SIGMA_ANEX);
					} else if (!ANEX_HAT_LARGE) {
						coeff = sample_z(0.0, SIGMA_ANEX_HAT);
					} else {
						coeff = sample_z((__float128) 0.0,
								(__float128) SIGMA_ANEX_HAT);
					}
					mpz_set_int128(coeffs[k], coeff);
				}
				Z[i][j].mpz2poly(coeffs);
				Z[i][j].ntt_pow_phi();
			}
		}

		/* Prover computes W = AY. */
		for (int i = 0; i < R; i++) {
			for (int j = 0; j < NTI; j++) {
				W[i][j] = 0;
				for (int k = 0; k < V; k++) {
					W[i][j] = W[i][j] + A[i][k] * Z[k][j];
				}
			}
		}

		pibnd_hash(h, A, t, W);

		/* Sample challenge from RNG seeded with hash. */
		nfl::fastrandombytes_seed(h);

		/* Verifier samples challenge matrix C, one row at a time, each row
		 * folded into SC before the next is drawn. The draws happen in the
		 * same order as the matrix is indexed, so this is the same C. */
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < NTI; j++) {
				SC[i][j] = 0;
			}
		}
		for (int k = 0; k < TAU; k++) {
			for (int j = 0; j < NTI; j++) {
				pibnd_sample_c(Crow[j]);
			}
			for (int i = 0; i < V; i++) {
				for (int j = 0; j < NTI; j++) {
					SC[i][j] = SC[i][j] + s[k][i] * Crow[j];
				}
			}
		}

		nfl::fastrandombytes_reseed();

		/* Prover computes Z = Y + SC and performs rejection sampling. */
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < NTI; j++) {
				Z[i][j] = Z[i][j] + SC[i][j];
			}
		}
		/* Two checks: rows 1..k against sigma_ANEx, the last against
		 * sigma-hat_ANEx. Each succeeds with probability 1/sqrt(3). */
		rej0 = pibnd_rej_sampling(Z, SC, 0, ANEX_K,
				SIGMA_ANEX * SIGMA_ANEX);
		rej1 = pibnd_rej_sampling(Z, SC, ANEX_K, V,
				SIGMA_ANEX_HAT * SIGMA_ANEX_HAT);
	} while ((rej0 || rej1) && ++tries < PIBND_TRIES);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(qDivBy2);

	return !(rej0 || rej1);
}

int pibnd_verifier(uint8_t h1[BLAKE3_OUT_LEN], params::poly_q Z[V][NTI],
		params::poly_q A[R][V], params::poly_q t[TAU][V]) {
	uint8_t h2[BLAKE3_OUT_LEN];
	int result;

	/* Verifier checks that W = AZ - TC. The A Z half needs no challenge, so it
	 * comes first and the rows of C are drawn and consumed after it; nothing
	 * in between touches the PRNG. */
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < NTI; j++) {
			W[i][j] = 0;
			for (int k = 0; k < V; k++) {
				W[i][j] = W[i][j] + A[i][k] * Z[k][j];
			}
		}
	}

	/* Sample challenge from RNG seeded with hash, a row of C at a time. */
	nfl::fastrandombytes_seed(h1);
	for (int k = 0; k < TAU; k++) {
		for (int j = 0; j < NTI; j++) {
			pibnd_sample_c(Crow[j]);
		}
		for (int i = 0; i < R; i++) {
			for (int j = 0; j < NTI; j++) {
				W[i][j] = W[i][j] - t[k][i] * Crow[j];
			}
		}
	}

	/* Restore the global PRNG, which is still seeded with the public hash. */
	nfl::fastrandombytes_reseed();

	pibnd_hash(h2, A, t, W);

	result = memcmp(h1, h2, BLAKE3_OUT_LEN) == 0;
	for (int i = 0; i < V; i++) {
		for (int j = 0; j < NTI; j++) {
			Z[i][j].invntt_pow_invphi();
			result &= pibnd_test_norm(Z[i][j],
					i < ANEX_K ? SIGMA_ANEX : SIGMA_ANEX_HAT);
		}
	}
	return result;
}

/* --- The norm bound used by the proof of shuffle ------------------------- */

struct pibnd_short {
	uint8_t h[BLAKE3_OUT_LEN];
	params::poly_q (*Z)[NTI];
	int complete;                   /* rejection sampling succeeded */
};

static int short_ready;
static params::poly_q (*short_scratch)[NTI];

static void pibnd_short_init(void) {
	if (short_ready) {
		return;
	}
	pibnd_alloc();
	/* pibnd_verifier() takes Z out of the NTT domain to measure it, so it is
	 * given a copy and the proof stays verifiable more than once. */
	short_scratch = new params::poly_q[V][NTI];
	short_ready = 1;
}

void pibnd_short_clear(void) {
	if (!short_ready) {
		return;
	}
	delete[]short_scratch;
	pibnd_free();
	short_ready = 0;
}

/* The relation is the BDLOP commitment equation, with the committed message as
 * the last witness component:
 *
 *   row 0    P_i.c1 = r_0 + sum_j A1[0][j] r_{j+HEIGHT}
 *   row 1    P_i.c2 = sum_j A2[0][j] r_j + sigma_i
 *
 * that is R = HEIGHT + 1 rows and V = WIDTH + 1 components. It is the relation
 * the membership proof of pismall.cpp uses as well, minus the row carrying
 * Y = w sigma, which the norm bound has no use for: Y is determined by sigma
 * over the integers once sigma is known to be binary. Both prover and verifier
 * build it from the commitment key alone.
 */
static void pibnd_commit_matrix(comkey_t & key) {
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
}

/* The public part, which is the commitment itself. The columns past the R
 * rows of the relation are unused, but pibnd_hash() reads all V of them, so
 * they are zeroed rather than left to whatever the allocator returned. */
static void pibnd_commit_stmt(const commit_t * P) {
	for (size_t i = 0; i < TAU; i++) {
		t[i][0] = P[i].c1;
		t[i][1] = P[i].c2[0];
		for (int j = R; j < V; j++) {
			t[i][j] = 0;
		}
	}
}

static void pibnd_commit_wit(const vector < params::poly_q > *r,
		const params::poly_q * sigma) {
	params::poly_q sg;

	for (size_t i = 0; i < TAU; i++) {
		for (int j = 0; j < WIDTH; j++) {
			s[i][j] = r[i][j];
		}
		sg = sigma[i];
		sg.ntt_pow_phi();
		s[i][WIDTH] = sg;
	}
}

pibnd_short_t *pibnd_short_prove(comkey_t & key, commit_t * P,
		vector < params::poly_q > *r, params::poly_q * sigma, size_t n) {
	pibnd_short_t *pi = new pibnd_short_t;

	assert(n == TAU);
	pibnd_short_init();
	pibnd_commit_matrix(key);
	pibnd_commit_stmt(P);
	pibnd_commit_wit(r, sigma);

	pi->Z = new params::poly_q[V][NTI];
	pi->complete = pibnd_prover(pi->h, pi->Z, A, t, s);

	return pi;
}

int pibnd_short_verify(pibnd_short_t * pi, comkey_t & key, commit_t * P,
		size_t n) {
	if (pi == NULL || !pi->complete || n != TAU) {
		return 0;
	}
	pibnd_short_init();
	pibnd_commit_matrix(key);
	pibnd_commit_stmt(P);
	for (int i = 0; i < V; i++) {
		for (int j = 0; j < NTI; j++) {
			short_scratch[i][j] = pi->Z[i][j];
		}
	}

	return pibnd_verifier(pi->h, short_scratch, A, t);
}

double pibnd_short_bound(void) {
	double sigma = SIGMA_ANEX > SIGMA_ANEX_HAT ? SIGMA_ANEX : SIGMA_ANEX_HAT;

	return sigma * sqrt(2.0 * params::poly_q::degree);
}

void pibnd_short_free(pibnd_short_t * pi) {
	if (pi == NULL) {
		return;
	}
	delete[]pi->Z;
	delete pi;
}

#ifdef MAIN
static void test() {
	uint8_t h1[BLAKE3_OUT_LEN];
	std::array < mpz_t, params::poly_q::degree > coeffs;
	gmp_randstate_t prng;
	mpz_t q;

	mpz_init(q);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	/* Create instances. */
	gmp_randinit_default(prng);
	mpz_set(q, params::poly_q::moduli_product());
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < V; j++) {
			for (size_t k = 0; k < params::poly_q::degree; k++) {
				mpz_urandomb(coeffs[k], prng, LEVEL);
				mpz_mod(coeffs[k], coeffs[k], q);
			}
			A[i][j].mpz2poly(coeffs);
			A[i][j].ntt_pow_phi();
		}
	}

	/* Create a total of TAU relations t_i = A * s_i */
	for (int i = 0; i < TAU; i++) {
		for (int j = 0; j < V; j++) {
			pibnd_sample_chall(s[i][j]);
		}
		for (int j = 0; j < R; j++) {
			t[i][j] = 0;
			for (int k = 0; k < V; k++) {
				t[i][j] = t[i][j] + A[j][k] * s[i][k];
			}
		}
	}

	TEST_ONCE("BND proof is consistent") {
		/* The prover's return value matters: giving up on rejection sampling
		 * still leaves a masked opening that passes the norm test, so a test
		 * that only checked the verifier would report success while the
		 * transcript leaked the witness. */
		TEST_ASSERT(pibnd_prover(h1, Z, A, t, s) == 1, end);
		TEST_ASSERT(pibnd_verifier(h1, Z, A, t) == 1, end);
	} TEST_END;

  end:

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(q);
	gmp_randclear(prng);
	return;
}

static void bench() {
	uint8_t h1[BLAKE3_OUT_LEN];
	std::array < mpz_t, params::poly_q::degree > coeffs;
	gmp_randstate_t prng;
	mpz_t q;

	mpz_init(q);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	/* Create instances. */
	gmp_randinit_default(prng);
	mpz_set(q, params::poly_q::moduli_product());
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < V; j++) {
			for (size_t k = 0; k < params::poly_q::degree; k++) {
				mpz_urandomb(coeffs[k], prng, LEVEL);
				mpz_mod(coeffs[k], coeffs[k], q);
			}
			A[i][j].mpz2poly(coeffs);
			A[i][j].ntt_pow_phi();
		}
	}

	/* Create a total of TAU relations t_i = A * s_i */
	for (int i = 0; i < TAU; i++) {
		for (int j = 0; j < V; j++) {
			pibnd_sample_chall(s[i][j]);
		}
		for (int j = 0; j < R; j++) {
			t[i][j] = 0;
			for (int k = 0; k < V; k++) {
				t[i][j] = t[i][j] + A[j][k] * s[i][k];
			}
		}
	}

	BENCH_SMALL("BND prover (N relations)", pibnd_prover(h1, Z, A, t, s));
	BENCH_SMALL("BND verifier (N relations)", pibnd_verifier(h1, Z, A, t));

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(q);
	gmp_randclear(prng);
	return;
}

int main(int argc, char *argv[]) {
	pibnd_alloc();

	printf("\n** Tests for lattice-based BND proof:\n\n");
	test();

	printf("\n** Benchmarks for lattice-based BND proof:\n\n");
	bench();

	pibnd_free();
	return test_failures() != 0;
}
#endif
