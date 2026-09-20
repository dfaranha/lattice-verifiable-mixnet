#include <cmath>

#include "blake3.h"
#include "test.h"
#include "bench.h"
#include "common.h"
#include "sample_z_small.h"
#include "sample_z_large.h"

/* sqrt(3), the per-check rejection-sampling constant. */
#define M_SQRT3     1.7320508075688772

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
#define V       (HEIGHT+3)
/* Number of relations and of parallel repetitions. These drive every large
 * buffer below, so they can be overridden (e.g. make CONFIG="-DTAU=10 -DNTI=8")
 * to test on a small machine; the paper's benchmarks use the defaults. */
#ifndef TAU
#define TAU     1000
#endif
#ifndef NTI
#define NTI     130
#endif

/* Number of rows of S' handled by the first of the two rejection-sampling
 * checks; the last row is handled by the second. */
#define ANEX_K      (V - 1)

/* Infinity-norm bound on the last witness row (the decryption noise E in the
 * mix-net; ternary like the others in the test below). */
#ifndef ANEX_E_INF
#define ANEX_E_INF  BETA
#endif

/*
 * sigma_ANEx: derive here instead of using the paper's.
 */
static const double SIGMA_ANEX =
		0.954 * BETA * DEGREE * sqrt(ANEX_K * (double) NTI * TAU / 2.0);

/*
 * sigma-hat_ANEx, for the last row: same derivation, one row instead of k.
 */
static const double SIGMA_ANEX_HAT =
		0.954 * ANEX_E_INF * DEGREE * sqrt((double) NTI * TAU / 2.0);

/* A params::poly_q is 64 KiB, so the matrices dimensioned by TAU or NTI are far
 * too large to be locals: C[TAU][NTI] alone is about 8.5 GiB at the default
 * parameters. They are allocated on the heap once at start-up, and the pointers
 * below index exactly like the two-dimensional arrays they replace. The prover
 * and the verifier each rederive W and C from the transcript, so one copy of
 * each is enough for both.
 *
 * NOTE: with TAU = 1000 and NTI = 130 this binary needs roughly 9 GiB of RAM.
 * Pass e.g. CONFIG="-DTAU=8 -DNTI=8" to make to try it on a smaller machine. */
static params::poly_q A[R][V];
static params::poly_q (*s)[V], (*t)[V];
static params::poly_q (*Z)[NTI], (*W)[NTI], (*C)[NTI], (*SC)[NTI];

static void pibnd_alloc(void) {
	s = new params::poly_q[TAU][V];
	t = new params::poly_q[TAU][V];
	Z = new params::poly_q[V][NTI];
	W = new params::poly_q[R][NTI];
	C = new params::poly_q[TAU][NTI];
	SC = new params::poly_q[V][NTI];
}

static void pibnd_free(void) {
	delete[]s;
	delete[]t;
	delete[]Z;
	delete[]W;
	delete[]C;
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
	double r, M = M_SQRT3;
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
	 * r = exp((-2<z, sc> + ||sc||^2) / 2s2) / M. */
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

static void pibnd_prover(uint8_t h[BLAKE3_OUT_LEN], params::poly_q Z[V][NTI],
		params::poly_q A[R][V], params::poly_q t[TAU][V],
		params::poly_q s[TAU][V]) {
	std::array < mpz_t, params::poly_q::degree > coeffs;
	mpz_t qDivBy2;
	__int128 coeff;
	int rej0, rej1;

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

		/* Verifier samples challenge matrix C. */
		for (int i = 0; i < TAU; i++) {
			for (int j = 0; j < NTI; j++) {
				C[i][j] = nfl::ZO_dist();
				C[i][j].ntt_pow_phi();
			}
		}

		nfl::fastrandombytes_reseed();

		/* Prover computes Z = Y + SC and performs rejection sampling. */
		for (int i = 0; i < V; i++) {
			for (int j = 0; j < NTI; j++) {
				SC[i][j] = 0;
				for (int k = 0; k < TAU; k++) {
					SC[i][j] = SC[i][j] + s[k][i] * C[k][j];
				}
				Z[i][j] = Z[i][j] + SC[i][j];
			}
		}
		/* Two checks: rows 1..k against sigma_ANEx, the last against
		 * sigma-hat_ANEx. Each succeeds with probability 1/sqrt(3). */
		rej0 = pibnd_rej_sampling(Z, SC, 0, ANEX_K,
				SIGMA_ANEX * SIGMA_ANEX);
		rej1 = pibnd_rej_sampling(Z, SC, ANEX_K, V,
				SIGMA_ANEX_HAT * SIGMA_ANEX_HAT);
	} while (rej0 || rej1);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(qDivBy2);
}

int pibnd_verifier(uint8_t h1[BLAKE3_OUT_LEN], params::poly_q Z[V][NTI],
		params::poly_q A[R][V], params::poly_q t[TAU][V]) {
	uint8_t h2[BLAKE3_OUT_LEN];
	int result;

	/* Sample challenge from RNG seeded with hash. */
	nfl::fastrandombytes_seed(h1);

	/* Verifier samples challenge matrix C. */
	for (int i = 0; i < TAU; i++) {
		for (int j = 0; j < NTI; j++) {
			C[i][j] = nfl::ZO_dist();
			C[i][j].ntt_pow_phi();
		}
	}

	/* Restore the global PRNG, which is still seeded with the public hash. */
	nfl::fastrandombytes_reseed();

	/* Verifier checks that W = AZ - TC. */
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < NTI; j++) {
			W[i][j] = 0;
			for (int k = 0; k < V; k++) {
				W[i][j] = W[i][j] + A[i][k] * Z[k][j];
			}
		}
	}
	for (int i = 0; i < R; i++) {
		for (int j = 0; j < NTI; j++) {
			for (int k = 0; k < TAU; k++) {
				W[i][j] = W[i][j] - t[k][i] * C[k][j];
			}
		}
	}

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
		pibnd_prover(h1, Z, A, t, s);
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
