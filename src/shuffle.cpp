#include <math.h>
#include <stdlib.h>

#include "blake3.h"
#include "common.h"
#include "test.h"
#include "bench.h"
#include <assert.h>
#include "sample_z_small.h"

/*============================================================================*/
/* Private definitions                                                        */
/*============================================================================*/

/* Number of messages being shuffled. This drives every large buffer below, so
 * it can be overridden (e.g. make CONFIG=-DMSGS=16) to test on a small machine;
 * the paper's benchmarks use 1000. */
#ifndef MSGS
#define MSGS        2
#endif

/* A params::poly_q is 64 KiB, so anything dimensioned by MSGS is far too large
 * to be a local variable: at MSGS = 1000 the buffers below add up to well over
 * a gigabyte. They are allocated on the heap once at start-up, and the pointers
 * index exactly like the arrays they replace. theta/inv and inv_tmp are the
 * prover's and simul_inverse's scratch space, which are equally oversized. */
static commit_t *com, *d, *cs;
static vector < params::poly_q > *r;
static params::poly_q *ms, *_ms, *s;
static params::poly_q (*y)[WIDTH], (*_y)[WIDTH];
static params::poly_q *t, *_t, *u;
static params::poly_q *theta, *inv, *inv_tmp;

static void shuffle_alloc(void) {
	com = new commit_t[MSGS];
	d = new commit_t[MSGS];
	cs = new commit_t[MSGS];
	r = new vector < params::poly_q >[MSGS];
	ms = new params::poly_q[MSGS];
	_ms = new params::poly_q[MSGS];
	s = new params::poly_q[MSGS];
	y = new params::poly_q[MSGS][WIDTH];
	_y = new params::poly_q[MSGS][WIDTH];
	t = new params::poly_q[MSGS];
	_t = new params::poly_q[MSGS];
	u = new params::poly_q[MSGS];
	theta = new params::poly_q[MSGS];
	inv = new params::poly_q[MSGS];
	inv_tmp = new params::poly_q[MSGS];
}

static void shuffle_free(void) {
	delete[]com;
	delete[]d;
	delete[]cs;
	delete[]r;
	delete[]ms;
	delete[]_ms;
	delete[]s;
	delete[]y;
	delete[]_y;
	delete[]t;
	delete[]_t;
	delete[]u;
	delete[]theta;
	delete[]inv;
	delete[]inv_tmp;
}

static void lin_hash(params::poly_q & beta, comkey_t & key, commit_t x,
		commit_t y, params::poly_q alpha[2], params::poly_q & u,
		params::poly_q t, params::poly_q _t) {
	uint8_t hash[BLAKE3_OUT_LEN];
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);

	/* Hash public key. */
	for (size_t i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH - HEIGHT; j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)key.A1[i][j].data(),
					16 * DEGREE);
		}
	}
	for (size_t j = 0; j < WIDTH; j++) {
		blake3_hasher_update(&hasher, (const uint8_t *)key.A2[0][j].data(),
				16 * DEGREE);
	}

	/* Hash alpha, beta from linear relation. */
	for (size_t i = 0; i < 2; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)alpha[i].data(),
				16 * DEGREE);
	}

	blake3_hasher_update(&hasher, (const uint8_t *)x.c1.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)y.c1.data(), 16 * DEGREE);
	/* Both commitments must have the same number of components, otherwise
	 * hashing y.c2 with x.c2's length reads past the end of y.c2. */
	assert(x.c2.size() == y.c2.size());
	for (size_t i = 0; i < x.c2.size(); i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)x.c2[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)y.c2[i].data(),
				16 * DEGREE);
	}

	blake3_hasher_update(&hasher, (const uint8_t *)u.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)t.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)_t.data(), 16 * DEGREE);

	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	/* Sample challenge from RNG seeded with hash. */
	nfl::fastrandombytes_seed(hash);
	bdlop_sample_chal(beta);
	nfl::fastrandombytes_reseed();
}

/* a^-1 mod pm, by the extended Euclidean algorithm. Every modulus of the basis
 * is 39 bits, so the Bezout coefficients stay well inside int64_t. */
static uint64_t residue_inverse(uint64_t a, uint64_t pm) {
	int64_t t = 0, t1 = 1, r = (int64_t) pm, r1 = (int64_t) a, quo, tmp;

	while (r1 != 0) {
		quo = r / r1;
		tmp = t - quo * t1;
		t = t1;
		t1 = tmp;
		tmp = r - quo * r1;
		r = r1;
		r1 = tmp;
	}
	return (uint64_t) (t < 0 ? t + (int64_t) pm : t);
}

/* Inverse in R_q. In the NTT domain R_q is a product of N * nmoduli copies of
 * Z_{p_cm}, so this is just a residue-wise inversion. Both arguments are in
 * that domain and may alias. Each p_cm is prime, so p is invertible exactly
 * when no residue is zero; otherwise return 0 and leave inv alone. */
static int poly_inverse(params::poly_q & inv, const params::poly_q & p) {
	for (size_t cm = 0; cm < params::poly_q::nmoduli; cm++) {
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			if (p(cm, i) == 0) {
				return 0;
			}
		}
	}

	for (size_t cm = 0; cm < params::poly_q::nmoduli; cm++) {
		uint64_t pm = nfl::params < uint64_t >::P[cm];
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			inv(cm, i) = residue_inverse(p(cm, i), pm);
		}
	}
	return 1;
}

static void simul_inverse(params::poly_q inv[MSGS], params::poly_q m[MSGS]) {
	params::poly_q w;
	int ok;

	inv[0] = m[0];
	inv_tmp[0] = m[0];

	for (size_t i = 1; i < MSGS; i++) {
		inv_tmp[i] = m[i];
		inv[i] = inv[i - 1] * m[i];
	}

	w = inv[MSGS - 1];
	/* The product of the shuffled messages behaves like a uniform element of
	 * R_q, so the only way this fails -- one of its 2N NTT residues being zero
	 * -- has probability about 2N/p_min, which is around 2^-26. */
	ok = poly_inverse(w, w);
	assert(ok == 1);
	(void) ok;

	for (size_t i = MSGS - 1; i > 0; i--) {
		inv[i] = w * inv[i - 1];
		w = w * inv_tmp[i];
	}
	inv[0] = w;
}

static int rej_sampling(params::poly_q z[WIDTH], params::poly_q v[WIDTH],
		uint64_t s2) {
	array < mpz_t, params::poly_q::degree > coeffs0, coeffs1;
	params::poly_q t;
	mpz_t dot, norm, qDivBy2, tmp;
	double r, M = 1.75;
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
	for (int i = 0; i < WIDTH; i++) {
		t = z[i];
		t.invntt_pow_invphi();
		t.poly2mpz(coeffs0);
		t = v[i];
		t.invntt_pow_invphi();
		t.poly2mpz(coeffs1);
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			util::center(coeffs0[i], coeffs0[i],
					params::poly_q::moduli_product(), qDivBy2);
			util::center(coeffs1[i], coeffs1[i],
					params::poly_q::moduli_product(), qDivBy2);
			mpz_mul(tmp, coeffs0[i], coeffs1[i]);
			mpz_add(dot, dot, tmp);
			mpz_mul(tmp, coeffs1[i], coeffs1[i]);
			mpz_add(norm, norm, tmp);
		}
	}

	if (getrandom(buf, sizeof(buf), 0) != sizeof(buf)) {
		fprintf(stderr, "ERROR: could not read entropy for rejection sampling\n");
		abort();
	}
	memcpy(&seed, buf, sizeof(buf));
	gmp_randseed_ui(state, seed);
	mpf_urandomb(u, state, mpf_get_default_prec());

	r = -2.0 * mpz_get_d(dot) + mpz_get_d(norm);
	r = r / (2.0 * s2);
	r = exp(r) / M;
	result = mpf_get_d(u) > r;

	mpf_clear(u);
	gmp_randclear(state);
	mpz_clears(dot, norm, qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs0[i]);
		mpz_clear(coeffs1[i]);
	}
	return result;
}

static void lin_prover(params::poly_q y[WIDTH], params::poly_q _y[WIDTH],
		params::poly_q & t, params::poly_q & _t, params::poly_q & u,
		commit_t x, commit_t _x, params::poly_q alpha[2],
		comkey_t & key, vector < params::poly_q > r,
		vector < params::poly_q > _r) {
	params::poly_q beta, tmp[WIDTH], _tmp[WIDTH];
	array < mpz_t, params::poly_q::degree > coeffs;
	int rej0, rej1;

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	do {
		/* Prover samples y,y' from Gaussian. */
		for (int i = 0; i < WIDTH; i++) {
			for (size_t k = 0; k < params::poly_q::degree; k++) {
				int64_t coeff = sample_z(0.0, SIGMA_C);
				mpz_set_si(coeffs[k], coeff);
			}
			y[i].mpz2poly(coeffs);
			y[i].ntt_pow_phi();
			for (size_t k = 0; k < params::poly_q::degree; k++) {
				int64_t coeff = sample_z(0.0, SIGMA_C);
				mpz_set_si(coeffs[k], coeff);
			}
			_y[i].mpz2poly(coeffs);
			_y[i].ntt_pow_phi();
		}

		t = y[0];
		_t = _y[0];
		for (int i = 0; i < HEIGHT; i++) {
			for (int j = 0; j < WIDTH - HEIGHT; j++) {
				t = t + key.A1[i][j] * y[j + HEIGHT];
				_t = _t + key.A1[i][j] * _y[j + HEIGHT];
			}
		}

		u = 0;
		for (int i = 0; i < WIDTH; i++) {
			u = u + alpha[0] * (key.A2[0][i] * y[i]) - (key.A2[0][i] * _y[i]);
		}

		/* Sample challenge. */
		lin_hash(beta, key, x, _x, alpha, u, t, _t);

		/* Prover */
		for (int i = 0; i < WIDTH; i++) {
			tmp[i] = beta * r[i];
			_tmp[i] = beta * _r[i];
			y[i] = y[i] + tmp[i];
			_y[i] = _y[i] + _tmp[i];
		}
		rej0 = rej_sampling(y, tmp, SIGMA_C * SIGMA_C);
		rej1 = rej_sampling(_y, _tmp, SIGMA_C * SIGMA_C);
	} while (rej0 || rej1);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
}

static int lin_verifier(params::poly_q z[WIDTH], params::poly_q _z[WIDTH],
		params::poly_q t, params::poly_q _t, params::poly_q u,
		commit_t x, commit_t _x, params::poly_q alpha[2], comkey_t & key) {
	params::poly_q beta, v, _v, tmp, zero = 0;
	int result = 1;

	/* Sample challenge. */
	lin_hash(beta, key, x, _x, alpha, u, t, _t);

	/* Verifier checks norm, reconstruct from NTT representation. */
	for (int i = 0; i < WIDTH; i++) {
		v = z[i];
		v.invntt_pow_invphi();
		result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
		v = _z[i];
		v.invntt_pow_invphi();
		result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
	}

	/* Verifier computes A1z and A1z'. */
	v = z[0];
	_v = _z[0];
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH - HEIGHT; j++) {
			v = v + key.A1[i][j] * z[j + HEIGHT];
			_v = _v + key.A1[i][j] * _z[j + HEIGHT];
		}
	}

	tmp = t + beta * x.c1 - v;
	tmp.invntt_pow_invphi();
	result &= (tmp == zero);
	tmp = _t + beta * _x.c1 - _v;
	tmp.invntt_pow_invphi();
	result &= (tmp == zero);

	v = 0;
	for (int i = 0; i < WIDTH; i++) {
		v = v + alpha[0] * (key.A2[0][i] * z[i]) - (key.A2[0][i] * _z[i]);
	}
	t = (alpha[0] * x.c2[0] + alpha[1] - _x.c2[0]) * beta + u;

	t.invntt_pow_invphi();
	v.invntt_pow_invphi();

	result &= ((t - v) == 0);
	return result;
}

void shuffle_hash(params::poly_q & beta, commit_t c[MSGS], commit_t d[MSGS],
		params::poly_q _ms[MSGS], params::poly_q rho[SIZE]) {
	uint8_t hash[BLAKE3_OUT_LEN];
	blake3_hasher hasher;
	blake3_hasher_init(&hasher);

	blake3_hasher_init(&hasher);

	for (int i = 0; i < MSGS; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)_ms[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)c[i].c1.data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)d[i].c1.data(),
				16 * DEGREE);
		for (size_t j = 0; j < c[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)c[i].c2[j].data(),
					16 * DEGREE);
			blake3_hasher_update(&hasher, (const uint8_t *)d[i].c2[j].data(),
					16 * DEGREE);
		}
	}

	for (int i = 0; i < SIZE; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)rho[i].data(),
				16 * DEGREE);
	}
	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	/* Sample challenge from RNG seeded with hash. */
	nfl::fastrandombytes_seed(hash);
	beta = nfl::uniform();
	nfl::fastrandombytes_reseed();
}

static void shuffle_prover(params::poly_q y[MSGS][WIDTH],
		params::poly_q _y[MSGS][WIDTH], params::poly_q t[MSGS],
		params::poly_q _t[MSGS], params::poly_q u[MSGS], commit_t d[MSGS],
		params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q ms[MSGS],
		params::poly_q _ms[MSGS], vector < params::poly_q > r[MSGS],
		params::poly_q rho[SIZE], comkey_t & key) {
	vector < params::poly_q > t0(1);
	vector < params::poly_q > _r[MSGS];
	params::poly_q alpha[2], beta;

	/* Prover samples theta_i and computes commitments D_i. */
	for (size_t i = 0; i < MSGS - 1; i++) {
		theta[i] = nfl::ZO_dist();
		theta[i].ntt_pow_phi();
		if (i == 0) {
			t0[0] = theta[0] * _ms[0];
		} else {
			t0[0] = theta[i - 1] * ms[i] + theta[i] * _ms[i];
		}
		t0[0].invntt_pow_invphi();
		_r[i].resize(WIDTH);
		bdlop_sample_rand(_r[i]);
		bdlop_commit(d[i], t0, key, _r[i]);
	}
	t0[0] = theta[MSGS - 2] * ms[MSGS - 1];
	t0[0].invntt_pow_invphi();
	_r[MSGS - 1].resize(WIDTH);
	bdlop_sample_rand(_r[MSGS - 1]);
	bdlop_commit(d[MSGS - 1], t0, key, _r[MSGS - 1]);

	shuffle_hash(beta, c, d, _ms, rho);

	//Check relationship here
	simul_inverse(inv, _ms);
	for (size_t i = 0; i < MSGS - 1; i++) {
		if (i == 0) {
			s[0] = theta[0] * _ms[0] - beta * ms[0];
		} else {
			s[i] = theta[i - 1] * ms[i] + theta[i] * _ms[i] - s[i - 1] * ms[i];
		}
		s[i] = s[i] * inv[i];
	}

	/* Now run \Prod_LIN instances, one for each commitment. */
	for (size_t l = 0; l < MSGS; l++) {
		if (l < MSGS - 1) {
			t0[0] = s[l] * _ms[l];
		} else {
			if (MSGS & 1) {
				params::poly_q zero = 0;
				t0[0] = zero - beta * _ms[l];
			} else {
				t0[0] = beta * _ms[l];
			}
		}

		if (l == 0) {
			alpha[0] = beta;
		} else {
			alpha[0] = s[l - 1];
		}
		alpha[1] = t0[0];
		lin_prover(y[l], _y[l], t[l], _t[l], u[l], c[l], d[l], alpha, key, r[l],
				_r[l]);
	}
}

static int shuffle_verifier(params::poly_q y[MSGS][WIDTH],
		params::poly_q _y[MSGS][WIDTH], params::poly_q t[MSGS],
		params::poly_q _t[MSGS], params::poly_q u[MSGS], commit_t d[MSGS],
		params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q _ms[MSGS],
		params::poly_q rho[SIZE], comkey_t & key) {
	params::poly_q alpha[2], beta;
	vector < params::poly_q > t0(1);
	int result = 1;

	shuffle_hash(beta, c, d, _ms, rho);
	for (size_t l = 0; l < MSGS; l++) {
		if (l < MSGS - 1) {
			t0[0] = s[l] * _ms[l];
		} else {
			if (MSGS & 1) {
				params::poly_q zero = 0;
				t0[0] = zero - beta * _ms[l];
			} else {
				t0[0] = beta * _ms[l];
			}
		}

		if (l == 0) {
			alpha[0] = beta;
		} else {
			alpha[0] = s[l - 1];
		}
		alpha[1] = t0[0];
		result &=
				lin_verifier(y[l], _y[l], t[l], _t[l], u[l], c[l], d[l], alpha,
				key);
	}

	return result;
}

static int run(vector < vector < params::poly_q >> m,
		vector < vector < params::poly_q >> _m, comkey_t & key) {
	vector < params::poly_q > t0(1);
	params::poly_q one, t1, rho[SIZE];
	comkey_t _key;

	/* Extend commitments and adjust key. */
	rho[0] = 1;
	rho[0].ntt_pow_phi();
	for (size_t j = 1; j < SIZE; j++) {
		rho[j] = nfl::uniform();
	}
	for (size_t i = 0; i < MSGS; i++) {
		ms[i] = m[i][0];
		ms[i].ntt_pow_phi();
		_ms[i] = _m[i][0];
		_ms[i].ntt_pow_phi();
		cs[i].c1 = com[i].c1;
		cs[i].c2.resize(1);
		cs[i].c2[0] = com[i].c2[0] * rho[0];
		for (size_t j = 1; j < SIZE; j++) {
			cs[i].c2[0] = cs[i].c2[0] + com[i].c2[j] * rho[j];
			t1 = m[i][j];
			t1.ntt_pow_phi();
			ms[i] = ms[i] + t1 * rho[j];
			t1 = _m[i][j];
			t1.ntt_pow_phi();
			_ms[i] = _ms[i] + t1 * rho[j];
		}
	}

	for (size_t i = 0; i < HEIGHT; i++) {
		for (size_t j = HEIGHT; j < WIDTH; j++) {
			_key.A1[i][j - HEIGHT] = key.A1[i][j - HEIGHT];
		}
	}
	_key.A2[0][0] = 0;
	_key.A2[0][1] = rho[0];
	for (size_t j = 2; j < WIDTH; j++) {
		_key.A2[0][j] = key.A2[0][j];
	}
	for (size_t i = 1; i < SIZE; i++) {
		for (size_t j = 2; j < WIDTH; j++) {
			_key.A2[0][j] = _key.A2[0][j] + rho[i] * key.A2[i][j];
		}
	}

	shuffle_prover(y, _y, t, _t, u, d, s, cs, ms, _ms, r, rho, _key);

	return shuffle_verifier(y, _y, t, _t, u, d, s, cs, _ms, rho, _key);
}

#ifdef MAIN
static void test() {
	comkey_t key;
	vector < vector < params::poly_q >> m(MSGS), _m(MSGS);

	/* Generate commitment key. */
	bdlop_keygen(key);
	for (int i = 0; i < MSGS; i++) {
		m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			m[i][j] = nfl::ZO_dist();
		}
		r[i].resize(WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(com[i], m[i], key, r[i]);
	}

	/* Prover shuffles messages (only a circular shift for simplicity). */
	for (int i = 0; i < MSGS; i++) {
		_m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			_m[i][j] = m[(i + 1) % MSGS][j];
		}
	}

	TEST_ONCE("polynomial inverse is correct") {
		/* nfl::uniform() fills the residues directly, so alpha[0] is already a
		 * uniform element of the NTT domain, which is where poly_inverse works.
		 * Multiplying twice by the inverse gives the inverse back, which avoids
		 * having to build the constant 1 to compare against. */
		params::poly_q alpha[2] = { nfl::uniform(), nfl::uniform() };

		TEST_ASSERT(poly_inverse(alpha[1], alpha[0]) == 1, end);
		alpha[0] = alpha[0] * alpha[1];
		alpha[0] = alpha[0] * alpha[1];
		TEST_ASSERT(alpha[0] == alpha[1], end);
	} TEST_END;

	TEST_ONCE("polynomial inverse reports a zero divisor") {
		/* A single zero residue makes the element a zero divisor. This used to
		 * pass silently, leaving a zero polynomial to flow into the proof. */
		params::poly_q alpha[2] = { nfl::uniform(), nfl::uniform() };

		alpha[0](0, 0) = 0;
		TEST_ASSERT(poly_inverse(alpha[1], alpha[0]) == 0, end);
	} TEST_END;

	TEST_ONCE("shuffle proof is consistent") {
		TEST_ASSERT(run(m, _m, key) == 1, end);
	} TEST_END;

  end:
	return;
}

static void microbench() {
	params::poly_q alpha[2] = { nfl::uniform(), nfl::uniform() };

	alpha[0].ntt_pow_phi();
	alpha[1].ntt_pow_phi();

	BENCH_BEGIN("Polynomial addition") {
		BENCH_ADD(alpha[0] = alpha[0] + alpha[1]);
	} BENCH_END;

	BENCH_BEGIN("Polynomial multiplication") {
		BENCH_ADD(alpha[0] = alpha[0] * alpha[1]);
	} BENCH_END;

	BENCH_BEGIN("Polynomial inverse") {
		BENCH_ADD(poly_inverse(alpha[1], alpha[0]));
	} BENCH_END;
}

static void bench() {
	comkey_t key;
	vector < vector < params::poly_q >> m(MSGS), _m(MSGS);
	params::poly_q by[WIDTH], _by[WIDTH], bt, _bt, bu, alpha[2], beta;

	/* Generate commitment key. */
	bdlop_keygen(key);
	for (int i = 0; i < MSGS; i++) {
		m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			m[i][j] = nfl::ZO_dist();
		}
		r[i].resize(WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(com[i], m[i], key, r[i]);
	}

	/* Prover shuffles messages (only a circular shift for simplicity). */
	for (int i = 0; i < MSGS; i++) {
		_m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			_m[i][j] = m[(i + 1) % MSGS][j];
		}
	}

	alpha[0] = nfl::ZO_dist();
	alpha[1] = nfl::ZO_dist();
	alpha[0].ntt_pow_phi();
	alpha[1].ntt_pow_phi();
	bdlop_sample_chal(beta);

	BENCH_BEGIN("linear hash") {
		BENCH_ADD(lin_hash(beta, key, com[0], com[1], alpha, bu, bt, _bt));
	} BENCH_END;

	BENCH_BEGIN("linear proof") {
		BENCH_ADD(lin_prover(by, _by, bt, _bt, bu, com[0], com[1], alpha, key,
						r[0], r[0]));
	} BENCH_END;

	BENCH_BEGIN("linear verifier") {
		BENCH_ADD(lin_verifier(by, _by, bt, _bt, bu, com[0], com[1], alpha,
						key));
	} BENCH_END;

	BENCH_SMALL("shuffle-proof (N messages)", run(m, _m, key));
}

int main(int argc, char *argv[]) {
	shuffle_alloc();

	printf("\n** Tests for lattice-based shuffle proof:\n\n");
	test();

	printf("\n** Microbenchmarks for polynomial arithmetic:\n\n");
	microbench();

	printf("\n** Benchmarks for lattice-based shuffle proof:\n\n");
	bench();

	shuffle_free();
	return test_failures() != 0;
}
#endif
