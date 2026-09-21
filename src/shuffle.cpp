#include <math.h>
#include <stdlib.h>

#include "blake3.h"
#include "common.h"
#include "test.h"
#include "bench.h"
#include <assert.h>
#include "sample_z_small.h"
#include "pismall.h"
#include "pibnd.h"

/*============================================================================*/
/* Private definitions                                                        */
/*============================================================================*/

/*
 * The proof of shuffle below follows Neff's paradigm, but it does *not* use the
 * plain product identity
 *
 *     \prod (a_i - X) = \prod (b_i - X)                                    (*)
 *
 * that the published version of this code used. Over R_q = Z_q[x]/(x^N + 1) the
 * polynomial x^N + 1 factors, so R_q is not a field and (*) does not imply that
 * the two lists are related by a permutation: it only implies that they are
 * permuted inside each CRT component, possibly by *different* permutations.
 * Bootle, Lyubashevsky and Merino-Gallardo, "Efficient Verifiable Mixnets from
 * Lattices, Revisited" (ePrint 2025/658), exploit exactly that gap to break the
 * soundness of the proof of shuffle of CT-RSA 2021 that this work extends. The
 * gap is wide open here: NFLlib needs an NTT-friendly modulus, so every prime
 * of the RNS basis is 1 mod 2N and R_q splits all the way into 2N linear
 * factors, 8192 of them at these parameters.
 *
 * We therefore use the product from their Lemma 5, which ties every message to
 * its index and forces the per-component permutations to agree:
 *
 *     \prod (a_i + g(i) * X1 - X2) = \prod (b_i + sigma_i * X1 - X2),
 *
 * where g : [N] -> D is injective, D is a set whose pairwise differences are
 * invertible, and sigma_i \in D is committed by the prover before the
 * challenges X1, X2 are drawn. An honest prover sets sigma_i = g(pi(i)) for the
 * secret permutation pi. Note that the identity above also reinstates the
 * evaluation point X2 that the published protocol had dropped: what it proved
 * was \prod a_i = \prod b_i, which does not imply a permutation even over a
 * field.
 *
 * We take D to be the monomials x^i and g(i) = x^i. In this ring that is the
 * natural choice, and one of very few available: x^a - x^b = x^b (x^{a-b} - 1),
 * every NTT slot is a primitive 2N-th root of unity, and so x^k - 1 vanishes in
 * no slot for 0 < k < N. Neither of the two sets used elsewhere works here. The
 * binary polynomials of Protocol 1 of ePrint 2025/658 and the small-norm ball
 * used on the `fix-pkc` branch of the CT-RSA 2021 code are both justified by
 * [42, Corollary 1.2], which bounds norms by q^(1/k) for a ring splitting into
 * k factors; at k = 2 that is roughly q^(1/2), but at k = 2N it is vacuous. The
 * test "a short polynomial can be a zero divisor" below exhibits a 0/1
 * polynomial of Hamming weight 22 that is a zero divisor in this ring, so no
 * norm bound can place an element in D.
 *
 * Lemma 5 also requires the committed sigma_i to lie in D. That is discharged
 * here by pismall_mono_prove(), which runs the amortized exact proof of
 * src/pismall.cpp over all MSGS commitments to the sigma_i and shows that each
 * committed element has binary coefficients and that multiplying it by the
 * public 2 - sum_j x^j leaves every coefficient in {-1, 1}, the two
 * coefficient-wise conditions that together say "monomial".
 *
 * That sub-proof is coefficient-wise but not exact on its own, because q is
 * composite: the identity it checks for the binary set is c (c - 1) = 0, which
 * over Z_q = Z_{p_1} x Z_{p_2} has four roots and not two, namely 0, 1 and the
 * two CRT idempotents. By itself it would therefore say only that sigma_i is a
 * monomial *in each CRT component*, and a prover who CRT-mixes the committed
 * sigma_i the way it mixes the messages would still be accepted. No algebraic
 * identity can do better over a composite modulus: the solution set of a
 * polynomial system over Z_q is the product of the per-component solution sets,
 * while D is the diagonal of such a product.
 *
 * What rules the idempotents out is a norm bound, and pibnd_short_prove() adds
 * one: Pi_BND over the same MSGS commitments, bounding the openings. The
 * idempotents are non-zero multiples of p_2 and of p_1, so their centred
 * representatives exceed 2^38, while the bound proven is below 2^28 at any
 * supported parameters. Binary in each component plus short therefore means
 * binary over the integers, the Y row then pins the Hamming weight to one over
 * the integers as well, and sigma_i in D follows.
 *
 * The two sub-proofs are separate proofs about the same commitments, the
 * membership one extracting an exact opening and the norm one a relaxed
 * opening, so reading them as statements about a single opening takes an
 * argument. It is made modulo each prime of the basis rather than over Z_q,
 * where the exact opening is short in the ordinary sense -- that is what 6.2
 * says, read the other way round -- and it costs one extra assumption, MSIS
 * modulo each p_j and not only modulo their product. See SOUNDNESS.md,
 * section 6.4.
 */

/* Monomials are distinct only up to the degree of the ring, and g must be
 * injective on [MSGS]. */
static_assert((size_t) MSGS <= params::poly_q::degree,
		"MSGS exceeds the degree of the ring, so x^i cannot index the messages");

/* One pass of the product argument has soundness error at most MSGS / p_min.
 * The challenges are uniform over R_q, which in a ring this split has to be
 * analysed slot by slot: if the identity fails in some slot, the check passes
 * only if the challenge hits a root of a degree-MSGS polynomial in that slot.
 * That is about 2^-29 at MSGS = 1000, far short of the LEVEL bits the
 * parameters are otherwise chosen for, so the argument is repeated with
 * independent challenges and the verifier requires every pass. Repetition is
 * sound here because the slot in which the identity fails is fixed by the
 * commitments before any challenge is drawn, so the passes are independent.
 *
 * Nothing else is repeated: the commitments, the linear proofs and the two
 * sub-proofs that establish sigma_i in D are already at or beyond LEVEL. */
static constexpr int shuffle_ilog2(unsigned long long x) {
	return x <= 1 ? 0 : 1 + shuffle_ilog2(x >> 1);
}

/* Bits gained per pass, floor(log2(p_min)) - ceil(log2(MSGS)). */
static constexpr int SHUFFLE_BITS =
		shuffle_ilog2(nfl::params < uint64_t >::P[0] <
				nfl::params < uint64_t >::P[1] ?
				nfl::params < uint64_t >::P[0] :
				nfl::params < uint64_t >::P[1]) -
		shuffle_ilog2(2 * (unsigned long long) MSGS - 1);
static_assert(SHUFFLE_BITS > 0, "MSGS is too large for the RNS basis");
static constexpr int SHUFFLE_REPS = (LEVEL + SHUFFLE_BITS - 1) / SHUFFLE_BITS;

/* A params::poly_q is 64 KiB, so anything dimensioned by MSGS is far too large
 * to be a local variable: at MSGS = 1000 the buffers below add up to several
 * gigabytes. They are allocated on the heap once at start-up, and the pointers
 * index exactly like the arrays they replace. theta/inv and inv_tmp are the
 * prover's and simul_inverse's scratch space, which are equally oversized, and
 * so are sg, fa and fb.
 *
 * pcom, pr, w and tp are the commitments to the sigma_i of Lemma 5, their
 * randomness, and the responses and first messages of the third opening that
 * the linear proof now carries for them. */
static commit_t *com, *d, *cs, *pcom;
static vector < params::poly_q > *r, *pr;
static params::poly_q *ms, *_ms, *s;
static params::poly_q (*y)[WIDTH], (*w)[WIDTH], (*_y)[WIDTH];
static params::poly_q *t, *tp, *_t, *u;
static params::poly_q *theta, *inv, *inv_tmp;
static params::poly_q *sg, *fa, *fb;

/* The proof that every committed sigma_i is a monomial, which is the
 * membership sigma_i in D that Lemma 5 requires. It is produced by the prover
 * along with the P_i and consumed by the verifier; it is kept here rather than
 * threaded through the already long argument lists of the two. */
static pismall_mono_t *mono;

/* The proof that every committed sigma_i is short, which is what makes the
 * coefficient sets of the membership proof exact; see the header comment. */
static pibnd_short_t *bnd;

static void shuffle_alloc(void) {
	com = new commit_t[MSGS];
	d = new commit_t[MSGS];
	cs = new commit_t[MSGS];
	pcom = new commit_t[MSGS];
	r = new vector < params::poly_q >[MSGS];
	pr = new vector < params::poly_q >[MSGS];
	ms = new params::poly_q[MSGS];
	_ms = new params::poly_q[MSGS];
	s = new params::poly_q[MSGS];
	y = new params::poly_q[MSGS][WIDTH];
	w = new params::poly_q[MSGS][WIDTH];
	_y = new params::poly_q[MSGS][WIDTH];
	t = new params::poly_q[MSGS];
	tp = new params::poly_q[MSGS];
	_t = new params::poly_q[MSGS];
	u = new params::poly_q[MSGS];
	theta = new params::poly_q[MSGS];
	inv = new params::poly_q[MSGS];
	inv_tmp = new params::poly_q[MSGS];
	sg = new params::poly_q[MSGS];
	fa = new params::poly_q[MSGS];
	fb = new params::poly_q[MSGS];
}

static void shuffle_free(void) {
	delete[]com;
	delete[]d;
	delete[]cs;
	delete[]pcom;
	delete[]r;
	delete[]pr;
	delete[]ms;
	delete[]_ms;
	delete[]s;
	delete[]y;
	delete[]w;
	delete[]_y;
	delete[]t;
	delete[]tp;
	delete[]_t;
	delete[]u;
	delete[]theta;
	delete[]inv;
	delete[]inv_tmp;
	delete[]sg;
	delete[]fa;
	delete[]fb;
	pismall_mono_free(mono);
	mono = NULL;
	pismall_mono_clear();
	pibnd_short_free(bnd);
	bnd = NULL;
	pibnd_short_clear();
}

/**
 * The map g : [N] -> D of Lemma 5, instantiated as the monomial map i -> x^i.
 *
 * The result is in the coefficient domain, which is what bdlop_commit expects;
 * callers doing arithmetic with it have to convert.
 *
 * @param[out] out			- the resulting ring element.
 * @param[in] i				- the index to encode, below the degree of the ring.
 */
static void index_monomial(params::poly_q & out, size_t i) {
	array < mpz_t, params::poly_q::degree > coeffs;

	assert(i < params::poly_q::degree);
	for (size_t k = 0; k < params::poly_q::degree; k++) {
		mpz_init2(coeffs[k], (params::poly_q::bits_in_moduli_product() << 2));
		mpz_set_ui(coeffs[k], k == i ? 1 : 0);
	}
	out.mpz2poly(coeffs);
	for (size_t k = 0; k < params::poly_q::degree; k++) {
		mpz_clear(coeffs[k]);
	}
}

/*
 * The linear proof relates *three* commitments instead of two. It proves
 * knowledge of openings of x, p and _x such that
 *
 *     coef[0] * <msg of x> + coef[1] * <msg of p> + coef[2] = <msg of _x>,
 *
 * for public coef[0] (alpha), coef[1] (gamma) and coef[2] (the additive term,
 * which the two-commitment version called beta). The extra commitment p is what
 * carries the committed permutation element sigma_i of Lemma 5: in the shuffle
 * the factor b_i = _m_i + sigma_i * tau - mu is no longer public, and splits
 * into the public part (_m_i - mu), folded into coef[2], and the committed part
 * sigma_i scaled by the public tau, folded into coef[1].
 */
static void lin_hash(params::poly_q & beta, comkey_t & key, commit_t x,
		commit_t p, commit_t y, params::poly_q coef[3], params::poly_q & u,
		params::poly_q t, params::poly_q tp, params::poly_q _t) {
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

	/* Hash the coefficients of the linear relation. */
	for (size_t i = 0; i < 3; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)coef[i].data(),
				16 * DEGREE);
	}

	blake3_hasher_update(&hasher, (const uint8_t *)x.c1.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)p.c1.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)y.c1.data(), 16 * DEGREE);
	/* All three commitments must have the same number of components, otherwise
	 * hashing y.c2 with x.c2's length reads past the end of y.c2. */
	assert(x.c2.size() == y.c2.size());
	assert(x.c2.size() == p.c2.size());
	for (size_t i = 0; i < x.c2.size(); i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)x.c2[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)p.c2[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)y.c2[i].data(),
				16 * DEGREE);
	}

	blake3_hasher_update(&hasher, (const uint8_t *)u.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)t.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)tp.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)_t.data(), 16 * DEGREE);

	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	/* Sample challenge from RNG seeded with hash. The challenge set is not free
	 * of zero divisors in this ring -- the test "KNOWN GAP: a challenge
	 * difference can be a zero divisor" exhibits one -- so this proof is worth
	 * only about 1 / p_min on its own and is carried by the repetitions of
	 * shuffle_prover. See SOUNDNESS.md, sections 7 and 8. */
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

static void lin_prover(params::poly_q y[WIDTH], params::poly_q w[WIDTH],
		params::poly_q _y[WIDTH], params::poly_q & t, params::poly_q & tp,
		params::poly_q & _t, params::poly_q & u, commit_t x, commit_t p,
		commit_t _x, params::poly_q coef[3], comkey_t & key,
		vector < params::poly_q > r, vector < params::poly_q > pr,
		vector < params::poly_q > _r) {
	params::poly_q beta, tmp[WIDTH], ptmp[WIDTH], _tmp[WIDTH];
	array < mpz_t, params::poly_q::degree > coeffs;
	int rej0, rej1, rej2;

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	do {
		/* Prover samples y, y_p and y' from Gaussian. */
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
			w[i].mpz2poly(coeffs);
			w[i].ntt_pow_phi();
			for (size_t k = 0; k < params::poly_q::degree; k++) {
				int64_t coeff = sample_z(0.0, SIGMA_C);
				mpz_set_si(coeffs[k], coeff);
			}
			_y[i].mpz2poly(coeffs);
			_y[i].ntt_pow_phi();
		}

		t = y[0];
		tp = w[0];
		_t = _y[0];
		for (int i = 0; i < HEIGHT; i++) {
			for (int j = 0; j < WIDTH - HEIGHT; j++) {
				t = t + key.A1[i][j] * y[j + HEIGHT];
				tp = tp + key.A1[i][j] * w[j + HEIGHT];
				_t = _t + key.A1[i][j] * _y[j + HEIGHT];
			}
		}

		u = 0;
		for (int i = 0; i < WIDTH; i++) {
			u = u + coef[0] * (key.A2[0][i] * y[i]);
			u = u + coef[1] * (key.A2[0][i] * w[i]);
			u = u - (key.A2[0][i] * _y[i]);
		}

		/* Sample challenge. */
		lin_hash(beta, key, x, p, _x, coef, u, t, tp, _t);

		/* Prover */
		for (int i = 0; i < WIDTH; i++) {
			tmp[i] = beta * r[i];
			ptmp[i] = beta * pr[i];
			_tmp[i] = beta * _r[i];
			y[i] = y[i] + tmp[i];
			w[i] = w[i] + ptmp[i];
			_y[i] = _y[i] + _tmp[i];
		}
		rej0 = rej_sampling(y, tmp, SIGMA_C * SIGMA_C);
		rej1 = rej_sampling(w, ptmp, SIGMA_C * SIGMA_C);
		rej2 = rej_sampling(_y, _tmp, SIGMA_C * SIGMA_C);
	} while (rej0 || rej1 || rej2);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}
}

static int lin_verifier(params::poly_q z[WIDTH], params::poly_q zp[WIDTH],
		params::poly_q _z[WIDTH], params::poly_q t, params::poly_q tp,
		params::poly_q _t, params::poly_q u, commit_t x, commit_t p,
		commit_t _x, params::poly_q coef[3], comkey_t & key) {
	params::poly_q beta, v, pv, _v, tmp;
	int result = 1;

	/* Sample challenge. */
	lin_hash(beta, key, x, p, _x, coef, u, t, tp, _t);

	/* Verifier checks norm, reconstruct from NTT representation. */
	for (int i = 0; i < WIDTH; i++) {
		v = z[i];
		v.invntt_pow_invphi();
		result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
		v = zp[i];
		v.invntt_pow_invphi();
		result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
		v = _z[i];
		v.invntt_pow_invphi();
		result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
	}

	/* Verifier computes A1z, A1z_p and A1z'. */
	v = z[0];
	pv = zp[0];
	_v = _z[0];
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH - HEIGHT; j++) {
			v = v + key.A1[i][j] * z[j + HEIGHT];
			pv = pv + key.A1[i][j] * zp[j + HEIGHT];
			_v = _v + key.A1[i][j] * _z[j + HEIGHT];
		}
	}

	/* Being zero is preserved by the inverse transform, so these compare in
	 * the NTT domain and skip it. */
	tmp = t + beta * x.c1 - v;
	result &= util::is_zero(tmp);
	tmp = tp + beta * p.c1 - pv;
	result &= util::is_zero(tmp);
	tmp = _t + beta * _x.c1 - _v;
	result &= util::is_zero(tmp);

	v = 0;
	for (int i = 0; i < WIDTH; i++) {
		v = v + coef[0] * (key.A2[0][i] * z[i]);
		v = v + coef[1] * (key.A2[0][i] * zp[i]);
		v = v - (key.A2[0][i] * _z[i]);
	}
	t = coef[0] * x.c2[0] + coef[1] * p.c2[0] + coef[2] - _x.c2[0];
	t = t * beta + u;

	result &= util::equal(t, v);
	return result;
}

/**
 * Derive the challenges X1 = tau and X2 = mu of Lemma 5.
 *
 * They are drawn after the commitments P_i to the permutation elements, and
 * bind them: the soundness argument needs the sigma_i to be fixed before the
 * two challenges, or the prover could pick them to fit.
 *
 * @param[out] tau			- the challenge X1.
 * @param[out] mu			- the challenge X2.
 * @param[in] c				- the commitments to the input messages.
 * @param[in] p				- the commitments to the permutation elements.
 * @param[in] _ms			- the public output list of messages.
 * @param[in] rho			- the challenges compressing the SIZE components.
 */
static void shuffle_chal_hash(params::poly_q & tau, params::poly_q & mu,
		commit_t c[MSGS], commit_t p[MSGS], params::poly_q _ms[MSGS],
		params::poly_q rho[SIZE], int rep) {
	uint8_t hash[BLAKE3_OUT_LEN];
	uint8_t sep = (uint8_t) rep;
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);
	/* The passes differ only in this byte, which is what makes their
	 * challenges independent. */
	blake3_hasher_update(&hasher, &sep, 1);

	for (int i = 0; i < MSGS; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)_ms[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)c[i].c1.data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)p[i].c1.data(),
				16 * DEGREE);
		for (size_t j = 0; j < c[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)c[i].c2[j].data(),
					16 * DEGREE);
		}
		for (size_t j = 0; j < p[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)p[i].c2[j].data(),
					16 * DEGREE);
		}
	}

	for (int i = 0; i < SIZE; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)rho[i].data(),
				16 * DEGREE);
	}
	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	/* Sample challenges from RNG seeded with hash. */
	nfl::fastrandombytes_seed(hash);
	tau = nfl::uniform();
	mu = nfl::uniform();
	nfl::fastrandombytes_reseed();
}

void shuffle_hash(params::poly_q & beta, commit_t c[MSGS], commit_t p[MSGS],
		commit_t d[MSGS], params::poly_q _ms[MSGS], params::poly_q & tau,
		params::poly_q & mu, params::poly_q rho[SIZE], int rep) {
	uint8_t hash[BLAKE3_OUT_LEN];
	uint8_t sep = (uint8_t) rep;
	blake3_hasher hasher;
	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, &sep, 1);

	for (int i = 0; i < MSGS; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)_ms[i].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)c[i].c1.data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)p[i].c1.data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)d[i].c1.data(),
				16 * DEGREE);
		for (size_t j = 0; j < c[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)c[i].c2[j].data(),
					16 * DEGREE);
			blake3_hasher_update(&hasher, (const uint8_t *)d[i].c2[j].data(),
					16 * DEGREE);
		}
		for (size_t j = 0; j < p[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)p[i].c2[j].data(),
					16 * DEGREE);
		}
	}

	blake3_hasher_update(&hasher, (const uint8_t *)tau.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)mu.data(), 16 * DEGREE);
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

/**
 * Compute the public coefficients of the l-th linear relation of the product
 * argument, namely
 *
 *     coef[0] * a_l + raw * b_l = <message committed in D_l>,
 *
 * with a_l = m_l + g(l) * tau - mu and b_l = _m_l + sigma_l * tau - mu. Only
 * m_l (inside cs[l]) and sigma_l (inside P[l]) are secret, so the relation
 * handed to the linear proof is
 *
 *     coef[0] * m_l + coef[1] * sigma_l + coef[2] = <message of D_l>,
 *     coef[1] = raw * tau,
 *     coef[2] = coef[0] * (g(l) * tau - mu) + raw * (_m_l - mu).
 *
 * The (-1)^N sign of the last equation is folded into raw, so that prover and
 * verifier treat every index uniformly.
 *
 * @param[out] coef			- the three coefficients of the linear relation.
 * @param[in] l				- the index of the relation.
 * @param[in] s				- the values s_i sent by the prover.
 * @param[in] _ms			- the public output list of messages.
 * @param[in] beta			- the challenge of the product argument.
 * @param[in] tau			- the challenge X1 of Lemma 5.
 * @param[in] mu			- the challenge X2 of Lemma 5.
 */
static void shuffle_coeffs(params::poly_q coef[3], size_t l,
		params::poly_q s[MSGS], params::poly_q _ms[MSGS],
		params::poly_q & beta, params::poly_q & tau, params::poly_q & mu) {
	params::poly_q raw, gl, zero = 0;

	if (l == 0) {
		coef[0] = beta;
	} else {
		coef[0] = s[l - 1];
	}

	if (l < MSGS - 1) {
		raw = s[l];
	} else {
		/* Coefficient (-1)^N of b_{N-1} in the last equation. */
		if (MSGS & 1) {
			raw = zero - beta;
		} else {
			raw = beta;
		}
	}

	index_monomial(gl, l);
	gl.ntt_pow_phi();
	gl = gl * tau - mu;
	coef[2] = coef[0] * gl + raw * (_ms[l] - mu);
	coef[1] = raw * tau;
}


/* The prover's first message, sent once and shared by every pass: commit to
 * the permutation elements sigma_i of Lemma 5 and prove that they lie in D. An
 * honest prover has sigma_i = g(pi(i)) = x^pi(i), in the coefficient domain as
 * bdlop_commit expects. It has to precede the challenges tau and mu, which is
 * exactly why it cannot be inside a pass.
 *
 * Membership needs two sub-proofs because a product identity alone cannot give
 * it -- a prover who CRT-mixes the sigma_i the way it mixes the messages
 * balances the product again. pismall shows, coefficient by coefficient, that
 * the element opened by each P_i is binary and that multiplying it by the
 * public 2 - sum_j x^j leaves every coefficient in {-1, 1}, which pins the
 * Hamming weight to one; pibnd bounds the norm of the openings, which is what
 * makes those coefficient sets exact over Z_q. See SOUNDNESS.md, section 6.
 */
static void shuffle_commit_sigma(commit_t p[MSGS],
		vector < params::poly_q > pr[MSGS], params::poly_q sigma[MSGS],
		comkey_t & key) {
	vector < params::poly_q > t0(1);

	for (size_t i = 0; i < MSGS; i++) {
		pr[i].resize(WIDTH);
		bdlop_sample_rand(pr[i]);
		t0[0] = sigma[i];
		bdlop_commit(p[i], t0, key, pr[i]);
		sg[i] = sigma[i];
		sg[i].ntt_pow_phi();
	}

	pismall_mono_free(mono);
	mono = pismall_mono_prove(key, p, pr, sigma, MSGS);
	pibnd_short_free(bnd);
	bnd = pibnd_short_prove(key, p, pr, sigma, MSGS);
}

static void shuffle_prover(params::poly_q y[MSGS][WIDTH],
		params::poly_q w[MSGS][WIDTH], params::poly_q _y[MSGS][WIDTH],
		params::poly_q t[MSGS], params::poly_q tp[MSGS],
		params::poly_q _t[MSGS], params::poly_q u[MSGS], commit_t d[MSGS],
		commit_t p[MSGS], vector < params::poly_q > pr[MSGS],
		params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q ms[MSGS],
		params::poly_q _ms[MSGS], params::poly_q sigma[MSGS],
		vector < params::poly_q > r[MSGS], params::poly_q rho[SIZE],
		comkey_t & key, int rep) {
	vector < params::poly_q > t0(1);
	vector < params::poly_q > _r[MSGS];
	params::poly_q coef[3], beta, tau, mu, gl;

	shuffle_chal_hash(tau, mu, c, p, _ms, rho, rep);

	/* Build the factors of the product of Lemma 5:
	 *     a_i = m_i + g(i) * tau - mu,
	 *     b_i = _m_i + sigma_i * tau - mu.
	 * Tying the index to every message is what forces the permutations of the
	 * CRT components to coincide, and is what the published product lacked. */
	for (size_t i = 0; i < MSGS; i++) {
		index_monomial(gl, i);
		gl.ntt_pow_phi();
		fa[i] = ms[i] + gl * tau - mu;
		fb[i] = _ms[i] + sg[i] * tau - mu;
	}

	/* Prover samples theta_i and computes commitments D_i. */
	for (size_t i = 0; i < MSGS - 1; i++) {
		/* Uniform, not short: theta_i is the only mask on the s_i the prover
		 * publishes, and nfl::uniform already fills the NTT domain. */
		theta[i] = nfl::uniform();
		if (i == 0) {
			t0[0] = theta[0] * fb[0];
		} else {
			t0[0] = theta[i - 1] * fa[i] + theta[i] * fb[i];
		}
		t0[0].invntt_pow_invphi();
		_r[i].resize(WIDTH);
		bdlop_sample_rand(_r[i]);
		bdlop_commit(d[i], t0, key, _r[i]);
	}
	t0[0] = theta[MSGS - 2] * fa[MSGS - 1];
	t0[0].invntt_pow_invphi();
	_r[MSGS - 1].resize(WIDTH);
	bdlop_sample_rand(_r[MSGS - 1]);
	bdlop_commit(d[MSGS - 1], t0, key, _r[MSGS - 1]);

	shuffle_hash(beta, c, p, d, _ms, tau, mu, rho, rep);

	//Check relationship here
	simul_inverse(inv, fb);
	for (size_t i = 0; i < MSGS - 1; i++) {
		if (i == 0) {
			s[0] = theta[0] * fb[0] - beta * fa[0];
		} else {
			s[i] = theta[i - 1] * fa[i] + theta[i] * fb[i] - s[i - 1] * fa[i];
		}
		s[i] = s[i] * inv[i];
	}

	/* Now run \Prod_LIN instances, one for each commitment. */
	for (size_t l = 0; l < MSGS; l++) {
		shuffle_coeffs(coef, l, s, _ms, beta, tau, mu);
		lin_prover(y[l], w[l], _y[l], t[l], tp[l], _t[l], u[l], c[l], p[l],
				d[l], coef, key, r[l], pr[l], _r[l]);
	}
}

static int shuffle_verifier(params::poly_q y[MSGS][WIDTH],
		params::poly_q w[MSGS][WIDTH], params::poly_q _y[MSGS][WIDTH],
		params::poly_q t[MSGS], params::poly_q tp[MSGS],
		params::poly_q _t[MSGS], params::poly_q u[MSGS], commit_t d[MSGS],
		commit_t p[MSGS], params::poly_q s[MSGS], commit_t c[MSGS],
		params::poly_q _ms[MSGS], params::poly_q rho[SIZE], comkey_t & key,
		int rep) {
	params::poly_q coef[3], beta, tau, mu;
	int result = 1;

	/* The first message is shared by every pass, so its sub-proofs are checked
	 * with the first one. */
	if (rep == 0) {
		result &= pismall_mono_verify(mono, key, p, MSGS);
		result &= pibnd_short_verify(bnd, key, p, MSGS);
	}

	shuffle_chal_hash(tau, mu, c, p, _ms, rho, rep);
	shuffle_hash(beta, c, p, d, _ms, tau, mu, rho, rep);
	for (size_t l = 0; l < MSGS; l++) {
		shuffle_coeffs(coef, l, s, _ms, beta, tau, mu);
		result &=
				lin_verifier(y[l], w[l], _y[l], t[l], tp[l], _t[l], u[l], c[l],
				p[l], d[l], coef, key);
	}

	return result;
}

/**
 * Run a full proof of shuffle.
 *
 * @param[in] m				- the input messages, as committed in com.
 * @param[in] _m			- the public output (shuffled) messages.
 * @param[in] sigma			- the permutation elements claimed by the prover, in
 *							  the coefficient domain. An honest prover sets
 *							  sigma[i] = g(pi(i)) = x^pi(i) for the permutation
 *							  with _m[i] = m[pi(i)].
 * @param[in] key			- the commitment key.
 * @return 1 if the proof verifies, 0 otherwise.
 */
static int run(vector < vector < params::poly_q >> m,
		vector < vector < params::poly_q >> _m,
		vector < params::poly_q > &sigma, comkey_t & key) {
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

	shuffle_commit_sigma(pcom, pr, sigma.data(), _key);

	/* The passes share the first message and reuse these buffers, which is
	 * why each one is verified as it is produced rather than at the end. */
	int result = 1;
	for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
		shuffle_prover(y, w, _y, t, tp, _t, u, d, pcom, pr, s, cs, ms, _ms,
				sigma.data(), r, rho, _key, rep);
		result &= shuffle_verifier(y, w, _y, t, tp, _t, u, d, pcom, s, cs, _ms,
				rho, _key, rep);
	}

	return result;
}

#ifdef MAIN
/**
 * Swap the residues of the first RNS modulus of two ring elements, leaving the
 * residues of the second untouched. Both elements are in the NTT domain.
 *
 * @param[in,out] a			- the first element.
 * @param[in,out] b			- the second element.
 */
static void crt_swap(params::poly_q & a, params::poly_q & b) {
	uint64_t t;

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		t = a(0, i);
		a(0, i) = b(0, i);
		b(0, i) = t;
	}
}

/**
 * Mix two ring elements given in the coefficient domain, by swapping the CRT
 * components belonging to the first RNS modulus. This is the manipulation of
 * Section 4.1 of ePrint 2025/658: the outputs are a permutation of the inputs
 * inside each of the fields the ring splits into, but not over the ring.
 *
 * @param[in,out] a			- the first element.
 * @param[in,out] b			- the second element.
 */
static void crt_mix(params::poly_q & a, params::poly_q & b) {
	a.ntt_pow_phi();
	b.ntt_pow_phi();
	crt_swap(a, b);
	a.invntt_pow_invphi();
	b.invntt_pow_invphi();
}

/**
 * Compute the product \prod (v_i - chi) that the published proof of shuffle
 * relied on, used by the tests to exhibit the attack. Everything is in the NTT
 * domain.
 *
 * @param[out] out			- the resulting product.
 * @param[in] v				- the list of messages.
 * @param[in] chi			- the evaluation point.
 */
static void neff_product(params::poly_q & out, vector < params::poly_q > &v,
		params::poly_q & chi) {
	params::poly_q acc = 1;

	acc.ntt_pow_phi();
	for (size_t i = 0; i < v.size(); i++) {
		acc = acc * (v[i] - chi);
	}
	out = acc;
}

static void test() {
	comkey_t key;
	vector < vector < params::poly_q >> m(MSGS), _m(MSGS), am(MSGS);
	vector < params::poly_q > sigma(MSGS), asigma(MSGS);
	size_t pi;

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

	/* Prover shuffles messages (only a circular shift for simplicity), and
	 * commits to the matching permutation elements sigma_i = g(pi(i)). */
	for (int i = 0; i < MSGS; i++) {
		pi = (i + 1) % MSGS;
		_m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			_m[i][j] = m[pi][j];
		}
		index_monomial(sigma[i], pi);
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
		TEST_ASSERT(util::equal(alpha[0], alpha[1]), end);
	} TEST_END;

	TEST_ONCE("polynomial inverse reports a zero divisor") {
		/* A single zero residue makes the element a zero divisor. This used to
		 * pass silently, leaving a zero polynomial to flow into the proof. */
		params::poly_q alpha[2] = { nfl::uniform(), nfl::uniform() };

		alpha[0](0, 0) = 0;
		TEST_ASSERT(poly_inverse(alpha[1], alpha[0]) == 0, end);
	} TEST_END;

	TEST_ONCE("monomial differences are invertible") {
		/* This is what makes the monomials a legal choice of D for Lemma 5:
		 * x^a - x^b = x^b (x^{a-b} - 1), and every NTT slot is a primitive
		 * 2N-th root of unity, so x^k - 1 vanishes in no slot for 0 < k < N. */
		params::poly_q ga, gb, t0;

		for (size_t k = 1; k < 8; k++) {
			index_monomial(ga, 0);
			index_monomial(gb, k);
			ga.ntt_pow_phi();
			gb.ntt_pow_phi();
			ga = ga - gb;
			TEST_ASSERT(poly_inverse(t0, ga) == 1, end);
		}
		index_monomial(ga, params::poly_q::degree - 1);
		index_monomial(gb, 1);
		ga.ntt_pow_phi();
		gb.ntt_pow_phi();
		ga = ga - gb;
		TEST_ASSERT(poly_inverse(t0, ga) == 1, end);
	} TEST_END;

	TEST_ONCE("a short polynomial can be a zero divisor") {
		/* The reason D cannot be a ball of small norm here, unlike in a ring
		 * splitting into few factors. The pattern below is a 0/1 polynomial of
		 * Hamming weight 22 whose value in one of the 8192 NTT slots is zero;
		 * it was found by meet-in-the-middle over subset sums of the powers of
		 * one primitive 2N-th root of unity modulo the first RNS prime, which
		 * costs seconds. Its l_infinity norm is 1, so no norm bound can tell it
		 * apart from a monomial, yet it is a zero divisor and multiplying by it
		 * loses information in that slot. */
		const char *bits = "11001001010001101110011101110010111000010100";
		array < mpz_t, params::poly_q::degree > coeffs;
		params::poly_q e, t0;
		size_t weight = 0;

		for (size_t i = 0; i < params::poly_q::degree; i++) {
			mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
			mpz_set_ui(coeffs[i], 0);
		}
		for (size_t i = 0; bits[i] != '\0'; i++) {
			if (bits[i] == '1') {
				mpz_set_ui(coeffs[i], 1);
				weight++;
			}
		}
		e.mpz2poly(coeffs);
		e.ntt_pow_phi();
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			mpz_clear(coeffs[i]);
		}
		TEST_ASSERT(weight == 22, end);
		TEST_ASSERT(poly_inverse(t0, e) == 0, end);
	} TEST_END;

	TEST_ONCE("the norm bound leaves room for the CRT argument") {
		/* Section 6.4 of SOUNDNESS.md concludes that sigma_i is the same
		 * monomial in both CRT components by reading two congruences, one
		 * modulo each prime of the basis, as equalities over the integers.
		 * That step needs every quantity in them to stay below p_min / 2:
		 * twice the norm bound, because extraction compares two transcripts,
		 * plus the slack of a challenge difference times a monomial. */
		double slack = 2.0 * pibnd_short_bound() + 2.0 * DEGREE;
		double pmin = nfl::params < uint64_t >::P[0]
				< nfl::params < uint64_t >::P[1]
				? nfl::params < uint64_t >::P[0]
				: nfl::params < uint64_t >::P[1];

		TEST_ASSERT(slack < pmin / 2.0, end);
	} TEST_END;

	TEST_ONCE("KNOWN GAP: a challenge difference can be a zero divisor") {
		/* The linear proof draws beta with bdlop_sample_chal, the difference of
		 * two weight-NONZERO ternary vectors, and every argument about it --
		 * the 2-special-soundness extraction, and the final check, which passes
		 * exactly when beta times the relation residual vanishes -- wants such
		 * differences to be invertible. The justification is [42, Corollary
		 * 1.2] once more, vacuous at k = 2N as Section 2 explains.
		 *
		 * The pattern below has 8 coefficients +1 and 6 coefficients -1, so it
		 * is one of those differences: put 7 of its support positions on each
		 * side and add 29 shared positions that cancel, and both sides have
		 * Hamming weight exactly NONZERO. It vanishes in one of the 8192 NTT
		 * slots. Found by meet-in-the-middle over subset sums of the powers of
		 * one primitive 2N-th root modulo the first RNS prime, in seconds, the
		 * same way as the short zero divisor above. Asserting the bug. */
		const char *pat = "+0+00+0+00++0000000++000000000000--0000---000-";
		array < mpz_t, params::poly_q::degree > coeffs;
		params::poly_q e, t0;
		size_t pos = 0, neg = 0;

		for (size_t i = 0; i < params::poly_q::degree; i++) {
			mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
			mpz_set_ui(coeffs[i], 0);
		}
		for (size_t i = 0; pat[i] != '\0'; i++) {
			if (pat[i] == '+') {
				mpz_set_ui(coeffs[i], 1);
				pos++;
			} else if (pat[i] == '-') {
				mpz_set(coeffs[i], params::poly_q::moduli_product());
				mpz_sub_ui(coeffs[i], coeffs[i], 1);
				neg++;
			}
		}
		e.mpz2poly(coeffs);
		e.ntt_pow_phi();
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			mpz_clear(coeffs[i]);
		}
		/* a legal difference of two weight-NONZERO vectors */
		TEST_ASSERT(pos == 8 && neg == 6, end);
		TEST_ASSERT((pos + neg) % 2 == 0 && (pos + neg) / 2 <= NONZERO, end);
		TEST_ASSERT(poly_inverse(t0, e) == 0, end);
	} TEST_END;

	TEST_ONCE("shuffle proof is consistent") {
		TEST_ASSERT(run(m, _m, sigma, key) == 1, end);
	} TEST_END;

	/* Mount the attack of Section 4.1: the output list is obtained from the
	 * honest one by swapping the CRT components of two messages that belong to
	 * the first RNS modulus. It is therefore *not* a permutation of the input
	 * over R_q, yet the product identity that the published proof checked is
	 * still satisfied. */
	for (int i = 0; i < MSGS; i++) {
		am[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			am[i][j] = _m[i][j];
		}
	}
	for (int j = 0; j < SIZE; j++) {
		crt_mix(am[0][j], am[1][j]);
	}

	TEST_ONCE("CRT-mixed list is not a permutation but passes Neff's product") {
		vector < params::poly_q > v(MSGS), av(MSGS);
		params::poly_q chi = nfl::uniform(), p0, p1;

		/* One component of the messages is enough to make the point, and the
		 * compression by rho that the protocol applies is slot-wise, so it
		 * preserves the mixing. */
		for (int i = 0; i < MSGS; i++) {
			v[i] = _m[i][0];
			v[i].ntt_pow_phi();
			av[i] = am[i][0];
			av[i].ntt_pow_phi();
		}
		TEST_ASSERT(!util::equal(am[0][0], _m[0][0]), end);
		TEST_ASSERT(!util::equal(am[0][0], _m[1][0]), end);
		neff_product(p0, v, chi);
		neff_product(p1, av, chi);
		TEST_ASSERT(util::equal(p0, p1), end);
	} TEST_END;

	TEST_ONCE("shuffle proof rejects the CRT-mixing attack") {
		TEST_ASSERT(run(m, am, sigma, key) == 0, end);
	} TEST_END;

	/* Second-order attack, targeting the membership requirement of Lemma 5:
	 * the cheating prover applies to the permutation elements the very same CRT
	 * swap it applied to the messages. Then sigma_0 = g(pi(1)) and
	 * sigma_1 = g(pi(0)) in the first CRT component, while sigma_i = g(pi(i))
	 * in the second, so the product of Lemma 5 balances in both components
	 * again. Those sigma_i are monomials in each CRT component, which is all
	 * the membership sub-proof checks, but their coefficients are CRT
	 * idempotents, which is what the norm bound rejects. */
	for (int i = 0; i < MSGS; i++) {
		asigma[i] = sigma[i];
	}
	crt_mix(asigma[0], asigma[1]);

	TEST_ONCE("shuffle proof rejects CRT-mixed sigma") {
		/* The membership sub-proof accepts these sigma_i, because they are
		 * monomials in each CRT component and its coefficient sets are
		 * per-component too. It is the norm bound that rejects them: their
		 * coefficients are CRT idempotents, far too large for the masked
		 * opening to stay inside the bound the verifier checks. */
		TEST_ASSERT(run(m, am, asigma, key) == 0, end);
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
	vector < params::poly_q > sigma(MSGS);
	params::poly_q by[WIDTH], bw[WIDTH], _by[WIDTH];
	params::poly_q bt, btp, _bt, bu, coef[3], beta;
	size_t pi;

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
		pi = (i + 1) % MSGS;
		_m[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			_m[i][j] = m[pi][j];
		}
		index_monomial(sigma[i], pi);
	}

	for (size_t i = 0; i < 3; i++) {
		coef[i] = nfl::ZO_dist();
		coef[i].ntt_pow_phi();
	}
	bdlop_sample_chal(beta);

	BENCH_BEGIN("linear hash") {
		BENCH_ADD(lin_hash(beta, key, com[0], com[1], com[1], coef, bu, bt,
						btp, _bt));
	} BENCH_END;

	BENCH_BEGIN("linear proof") {
		BENCH_ADD(lin_prover(by, bw, _by, bt, btp, _bt, bu, com[0], com[1],
						com[1], coef, key, r[0], r[1], r[1]));
	} BENCH_END;

	BENCH_BEGIN("linear verifier") {
		BENCH_ADD(lin_verifier(by, bw, _by, bt, btp, _bt, bu, com[0], com[1],
						com[1], coef, key));
	} BENCH_END;

	BENCH_SMALL("shuffle-proof (N messages)", run(m, _m, sigma, key));
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
