#include "test.h"
#include "bench.h"
#include "common.h"
#include <sys/random.h>
#include <array>
#include <cassert>

/*============================================================================*/
/* Public definitions                                                         */
/*============================================================================*/

using namespace std;

/**
 * Test if the l2-norm is within bounds (4 * sigma * sqrt(N)).
 *
 * @param[in] r 			- the polynomial to compute the l2-norm.
 * @return the computed norm.
 */
bool bdlop_test_norm(params::poly_q r, uint64_t sigma_sqr) {
	array < mpz_t, params::poly_q::degree > coeffs;
	mpz_t norm, qDivBy2, tmp;

	/// Constructors
	mpz_inits(norm, qDivBy2, tmp, nullptr);
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

	// Compare to (4 * sigma * sqrt(N))^2 = 16 * sigma^2 * N.
	uint64_t bound = 16 * sigma_sqr * params::poly_q::degree;
	int result = mpz_cmp_ui(norm, bound) < 0;

	mpz_clears(norm, qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}

	return result;
}

void bdlop_sample_rand(vector<params::poly_q> &r) {
	for (size_t i = 0; i < r.size(); i++) {
		r[i] = nfl::ZO_dist();
		r[i].ntt_pow_phi();
	}
}

void bdlop_sample_uniform(params::poly_q &f) {
	std::array<mpz_t, params::poly_q::degree> coeffs;
	gmp_randstate_t prng;
	unsigned long int seed;
	mpz_t q;

	gmp_randinit_default(prng);
	if (getrandom(&seed, sizeof(seed), 0) != sizeof(seed)) {
		fprintf(stderr, "ERROR: could not read entropy for uniform sampling\n");
		abort();
	}
	gmp_randseed_ui(prng, seed);

	mpz_init(q);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	mpz_set(q, params::poly_q::moduli_product());
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_urandomm(coeffs[i], prng, q);
	}
	f.mpz2poly(coeffs);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(q);
	gmp_randclear(prng);
}

void bdlop_reduce(params::poly_q &f) {
	std::array<mpz_t, params::poly_q::degree> coeffs;
	mpz_t q;

	mpz_init(q);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	f.invntt_pow_invphi();
	f.poly2mpz(coeffs);
	mpz_set(q, params::poly_q::moduli_product());
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_mod(coeffs[i], coeffs[i], q);
	}
	f.mpz2poly(coeffs);
	f.ntt_pow_phi();

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
	mpz_clear(q);
}

void bdlop_print(params::poly_q &f) {
	std::array<mpz_t, params::poly_q::degree> coeffs;
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	f.poly2mpz(coeffs);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		gmp_printf("%Zd ", coeffs[i]);
	}

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
}

// Sample a challenge.
void bdlop_sample_chal(params::poly_q &f) {
	params::poly_q c0, c1;

	c0 = nfl::hwt_dist {NONZERO};
	c1 = nfl::hwt_dist {NONZERO};

	f = c0 - c1;
	f.ntt_pow_phi();
}

// Generate a key pair.
void bdlop_keygen(comkey_t & key) {
	params::poly_q one = 1;
	one.ntt_pow_phi();
	for (size_t i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH - HEIGHT; j++) {
			bdlop_sample_uniform(key.A1[i][j]);
			key.A1[i][j].ntt_pow_phi();
		}
	}
	for (size_t i = 0; i < SIZE; i++) {
		for (size_t j = 0; j < HEIGHT + SIZE; j++) {
			key.A2[i][j] = 0;
		}
		key.A2[i][i + HEIGHT] = one;
		for (size_t j = SIZE + HEIGHT; j < WIDTH; j++) {
			bdlop_sample_uniform(key.A2[i][j]);
			key.A2[i][j].ntt_pow_phi();
		}
	}
}

// Commit to a message.
void bdlop_commit(commit_t & com, vector<params::poly_q> m, comkey_t & key,
		vector<params::poly_q> r) {
	params::poly_q _m;

	/* m indexes the SIZE rows of key.A2 (and, in bdlop_open, the SIZE entries
	 * of c2/_c2); r indexes the WIDTH columns of key.A2. Note that r.size() is
	 * unsigned, so a vector shorter than HEIGHT would make r.size() - HEIGHT
	 * wrap around and walk far off the end of key.A1. */
	assert(m.size() <= SIZE);
	assert(r.size() >= HEIGHT && r.size() <= WIDTH);

	com.c1 = r[0];
	for (size_t i = 0; i < HEIGHT; i++) {
		for (size_t j = 0; j < r.size() - HEIGHT; j++) {
			com.c1 = com.c1 + key.A1[i][j] * r[j + HEIGHT];
		}
	}

	com.c2.resize(m.size());
	for (size_t i = 0; i < m.size(); i++) {
		com.c2[i] = 0;
		for (size_t j = 0; j < r.size(); j++) {
			com.c2[i] = com.c2[i] + key.A2[i][j] * r[j];
		}
		_m = m[i];
		_m.ntt_pow_phi();
		com.c2[i] = com.c2[i] + _m;
	}
}

// Open a commitment on a message, randomness, factor.
int bdlop_open(commit_t & com, vector<params::poly_q> m, comkey_t & key,
		vector<params::poly_q> r, params::poly_q &f) {
	params::poly_q c1, _c1, c2[SIZE], _c2[SIZE], _m;
	int result = true;

	/* m indexes the SIZE rows of key.A2 (and, in bdlop_open, the SIZE entries
	 * of c2/_c2); r indexes the WIDTH columns of key.A2. Note that r.size() is
	 * unsigned, so a vector shorter than HEIGHT would make r.size() - HEIGHT
	 * wrap around and walk far off the end of key.A1. */
	assert(m.size() <= SIZE);
	assert(r.size() >= HEIGHT && r.size() <= WIDTH);

	c1 = r[0];
	for (size_t i = 0; i < HEIGHT; i++) {
		for (size_t j = 0; j < r.size() - HEIGHT; j++) {
			c1 = c1 + key.A1[i][j] * r[j + HEIGHT];
		}
	}

	for (size_t i = 0; i < m.size(); i++) {
		c2[i] = 0;
		for (size_t j = 0; j < r.size(); j++) {
			c2[i] = c2[i] + key.A2[i][j] * r[j];
		}
		_m = m[i];
		_m.ntt_pow_phi();
		c2[i] = c2[i] + f * _m;
	}

	_c1 = f * com.c1;
	if (_c1 != c1 || com.c2.size() != m.size()) {
		result = false;
		cout << "ERROR: Commit opening failed test for c1" << endl;
	} else {
		for (size_t i = 0; i < m.size(); i++) {
			_c2[i] = f * com.c2[i];
			if (_c2[i] != c2[i]) {
				cout << "ERROR: Commit opening failed test for c2 (postition "
						<< i << ")" << endl;
				result = false;
			}
		}

		// Compute sigma^2 = (0.954 * v * beta * sqrt(k * N))^2.
		for (size_t i = 0; i < r.size(); i++) {
			c1 = r[i];
			c1.invntt_pow_invphi();
			if (!bdlop_test_norm(c1, 16 * SIGMA_C)) {
				cout << "ERROR: Commit opening failed norm test" << endl;
				result = false;
				break;
			}
		}
	}

	return result;
}

#ifdef MAIN
static void test1() {
	comkey_t key;
	commit_t com, _com;

	bdlop_keygen(key);
	vector<params::poly_q> r(WIDTH), s(WIDTH);
	params::poly_q f;
	vector<params::poly_q> m(1);
	bdlop_sample_uniform(m[0]);

	TEST_BEGIN("commitment for single messages can be generated and opened") {
		bdlop_sample_rand(r);
		bdlop_commit(com, m, key, r);
		f = 1;
		f.ntt_pow_phi();
		TEST_ASSERT(bdlop_open(com, m, key, r, f) == 1, end);
		bdlop_sample_chal(f);
		for (size_t j = 0; j < r.size(); j++) {
			s[j] = f * r[j];
		}
		TEST_ASSERT(bdlop_open(com, m, key, s, f) == 1, end);
	} TEST_END;

	TEST_BEGIN("commitments for single messages are linearly homomorphic") {
		/* Test linearity. */
		vector<params::poly_q> rho(1);
		bdlop_sample_uniform(rho[0]);
		for (size_t j = 0; j < r.size(); j++) {
			r[j] = 0;
		}
		bdlop_commit(_com, rho, key, r);
		com.c1 = com.c1 - _com.c1;
		com.c2[0] = com.c2[0] - _com.c2[0];
		m[0] = m[0] - rho[0];
		TEST_ASSERT(bdlop_open(com, m, key, s, f) == 1, end);
	} TEST_END;

  end:
	return;
}

static void test2() {
	comkey_t key, _key;
	commit_t c, com, _com;

	bdlop_keygen(key);
	vector<params::poly_q> r(WIDTH), s(WIDTH);
	params::poly_q t, f, one;
	vector<params::poly_q> _m(1), m(2);
	bdlop_sample_uniform(_m[0]);
	bdlop_sample_uniform(m[0]);
	bdlop_sample_uniform(m[1]);

	TEST_BEGIN("commitment for multiple messages can be generated and opened") {
		bdlop_sample_rand(r);
		bdlop_commit(com, m, key, r);
		f = 1;
		f.ntt_pow_phi();
		TEST_ASSERT(bdlop_open(com, m, key, r, f) == 1, end);
		bdlop_sample_chal(f);
		for (size_t j = 0; j < r.size(); j++) {
			s[j] = f * r[j];
		}
		TEST_ASSERT(bdlop_open(com, m, key, s, f) == 1, end);
	} TEST_END;

	TEST_ONCE("commitments do not open for the wrong keys") {
		bdlop_sample_rand(r);
		bdlop_commit(com, m, key, r);
		bdlop_sample_chal(f);
		for (size_t j = 0; j < r.size(); j++) {
			s[j] = f * r[j];
		}
		bdlop_keygen(key);
		TEST_ASSERT(bdlop_open(com, m, key, s, f) == 0, end);
	} TEST_END;

	TEST_BEGIN("commitments for multiple messages are linearly homomorphic") {
		/* Test linearity. */
		vector<params::poly_q> rho(2);
		bdlop_sample_uniform(rho[0]);
		bdlop_sample_uniform(rho[1]);
		bdlop_sample_rand(r);
		bdlop_commit(com, m, key, r);
		bdlop_sample_chal(f);
		for (size_t j = 0; j < r.size(); j++) {
			s[j] = f * r[j];
			r[j] = 0;
		}
		bdlop_commit(_com, rho, key, r);
		m[0] = m[0] - rho[0];
		m[1] = m[1] - rho[1];
		com.c1 = com.c1 - _com.c1;
		com.c2[0] = com.c2[0] - _com.c2[0];
		com.c2[1] = com.c2[1] - _com.c2[1];
		TEST_ASSERT(bdlop_open(com, m, key, s, f) == 1, end);
		// Restore messages and commitments
		m[0] = m[0] + rho[0];
		m[1] = m[1] + rho[1];
		com.c1 = com.c1 + _com.c1;
		com.c2[0] = com.c2[0] + _com.c2[0];
		com.c2[1] = com.c2[1] + _com.c2[1];
		// Now try again
		rho[0] = 1;
		rho[0].ntt_pow_phi();
		bdlop_sample_uniform(rho[1]);
		_m[0] = m[0];
		t = m[1];
		_m[0].ntt_pow_phi();
		t.ntt_pow_phi();
		_m[0] = _m[0] * rho[0] + t * rho[1];
		_m[0].invntt_pow_invphi();
		c.c1 = com.c1;
		c.c2.resize(1);
		c.c2[0] = com.c2[0] * rho[0] + com.c2[1] * rho[1];
		for (size_t i = 0; i < HEIGHT; i++) {
			for (size_t j = 0; j < WIDTH - HEIGHT; j++) {
				_key.A1[i][j] = key.A1[i][j];
			}
		}
		for (size_t j = 0; j < WIDTH; j++) {
			_key.A2[0][j] = key.A2[0][j];
		}
		for (size_t i = 1; i < SIZE; i++) {
			_key.A2[0][i + HEIGHT] = rho[i];
			for (size_t j = SIZE + HEIGHT; j < WIDTH; j++) {
				_key.A2[0][j] = _key.A2[0][j] + rho[i] * key.A2[i][j];
			}
		}
		TEST_ASSERT(bdlop_open(c, _m, _key, s, f) == 1, end);
	} TEST_END;

  end:
	return;
}

static void bench() {
	comkey_t key;
	commit_t com;
	params::poly_q f;
	vector<params::poly_q> r(WIDTH), s(WIDTH);
	vector<params::poly_q> m(SIZE);
	params::poly_p _m;

	bgvkey_t pk;
	params::poly_q sk;
	bgvenc_t c;

	BENCH_SMALL("bdlp_keygen", bdlop_keygen(key));

	BENCH_BEGIN("bdlop_sample_chal") {
		BENCH_ADD(bdlop_sample_chal(f));
	} BENCH_END;

	BENCH_BEGIN("bdlop_sample_rand") {
		BENCH_ADD(bdlop_sample_rand(r));
	} BENCH_END;

	BENCH_BEGIN("bdlop_reduce") {
		m[0] = nfl::uniform();
		BENCH_ADD(bdlop_reduce(m[0]));
	} BENCH_END;

	BENCH_BEGIN("bdlop_commit") {
		bdlop_sample_uniform(m[0]);
		bdlop_sample_uniform(m[1]);
		BENCH_ADD(bdlop_commit(com, m, key, r));
	} BENCH_END;

	BENCH_BEGIN("bdlop_open") {
		bdlop_sample_uniform(m[0]);
		bdlop_sample_uniform(m[1]);
		bdlop_commit(com, m, key, r);
		for (size_t j = 0; j < r.size(); j++) {
			s[j] = f * r[j];
		}
		BENCH_ADD(bdlop_open(com, m, key, s, f));
	} BENCH_END;

	bgv_keygen(pk, sk);
	bgv_sample_message(_m);
}

int main(void) {
	printf("\n** Tests for lattice-based commitments:\n\n");
	test1();
	test2();

	printf("\n** Benchmarks for lattice-based commitments:\n\n");
	bench();

	return test_failures() != 0;
}
#endif
