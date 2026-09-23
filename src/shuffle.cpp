#include <math.h>
#include <stdlib.h>

#include "blake3.h"
#include "common.h"
#include "test.h"
#include "bench.h"
#include <assert.h>
#include "sample_z_small.h"
#include "pismall.h"
#include "serial.h"
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
 * We take g(i) = i, the ring constant with that value, and D the set of
 * constants the prover can be held to. Differences of distinct g(i) are
 * non-zero integers below MSGS, hence coprime to q and units, which is all
 * Lemma 5 asks of them. The two sets used elsewhere do not work here: the
 * binary polynomials of Protocol 1 of ePrint 2025/658 and the small-norm ball
 * of the `fix-pkc` branch of the CT-RSA 2021 code are both justified by [42,
 * Corollary 1.2], which bounds norms by q^(1/k) for a ring splitting into k
 * factors; at k = 2 that is roughly q^(1/2), at k = 2N it is vacuous. The test
 * "a short polynomial can be a zero divisor" below exhibits a 0/1 polynomial of
 * Hamming weight 19 that is a zero divisor here, so shortness alone certifies
 * nothing about a general ring element. It does certify something about a
 * constant, which is why this encoding works and those do not.
 *
 * Lemma 5 also requires the committed sigma_i to lie in D, and two sub-proofs
 * over the same commitments discharge it between them.
 *
 * pismall_const_prove() is the algebraic half: the amortized exact proof of
 * src/pismall.cpp over all MSGS commitments, showing that every coefficient of
 * sigma_i above the constant one is zero. That constraint is exact over Z_q,
 * unlike every other coefficient set in that file -- f = 0 has a single root
 * however q factors -- so nothing here needs repairing afterwards. It leaves
 * sigma_i an arbitrary constant c_i.
 *
 * pibnd_short_prove() is the size half: Pi_BND over the same commitments,
 * bounding the openings. Together with the argument of SOUNDNESS.md section
 * 6.4 it gives sigma'_i = c c_i mod q for a short sigma'_i and the challenge
 * difference c. Now suppose some difference d = c_i - c_j were a zero divisor,
 * say p_1 | d. Then c d is short and divisible by p_1, so being smaller than
 * p_1 it is zero over the integers; c d = 0 with d a scalar not divisible by
 * p_2 forces c = 0 modulo p_2, and c short forces c = 0, contradiction. The
 * same argument covers c_i - g(j). So every pairwise difference is a unit,
 * which is what Lemma 5 needs -- proven directly, without naming D.
 *
 * The two sub-proofs are separate proofs about the same commitments, the
 * algebraic one extracting an exact opening and the norm one a relaxed
 * opening, so reading them as statements about a single opening takes an
 * argument. It is made modulo each prime of the basis, and costs one extra
 * assumption, MSIS modulo each p_j and not only modulo their product. See
 * SOUNDNESS.md, section 5.4.
 */

/* Differences of distinct g(i) are non-zero integers below MSGS, and they have
 * to stay coprime to q for Lemma 5, so MSGS must not reach the smaller prime of
 * the basis. That is a far weaker bound than the ring degree, which is what the
 * monomial encoding was limited by. */
static_assert((unsigned long long) MSGS <
		(nfl::params < uint64_t >::P[0] < nfl::params < uint64_t >::P[1] ?
		 nfl::params < uint64_t >::P[0] : nfl::params < uint64_t >::P[1]),
		"MSGS reaches the smallest prime of the basis, so g(i) - g(j) can be a zero divisor");

/* One pass of the product argument has soundness error at most MSGS / p_min.
 * The challenges are uniform over R_q, which in a ring this split has to be
 * analysed slot by slot: if the identity fails in some slot, the check passes
 * only if the challenge hits a root of a degree-MSGS polynomial in that slot.
 * That is about 2^-34 at MSGS = 1000, far short of the LEVEL bits the
 * parameters are otherwise chosen for, so the argument is repeated with
 * independent challenges and the verifier requires every pass.
 *
 * Those errors multiply only if a prover who fails a pass has to start over.
 * tau and mu are hashed from the P_i, which run() sends once for every pass,
 * and beta from every pass's D_i at once, so re-rolling either re-rolls every
 * pass and these do multiply. The challenges inside Pi_LIN do not; see
 * SOUNDNESS.md section 6.1. */
static constexpr int shuffle_ilog2(unsigned long long x) {
	return x <= 1 ? 0 : 1 + shuffle_ilog2(x >> 1);
}

/* The smaller prime of the RNS basis. A challenge is a uniform element of R_q
 * and the ring is fully split, so what a false statement needs is a challenge
 * vanishing in one slot, which is 1 / p_min. */
static constexpr unsigned long long P_MIN =
		nfl::params < uint64_t >::P[0] < nfl::params < uint64_t >::P[1] ?
		nfl::params < uint64_t >::P[0] : nfl::params < uint64_t >::P[1];

/* Bits gained per pass, floor(log2(p_min)) - ceil(log2(MSGS)). */
static constexpr int SHUFFLE_BITS =
		shuffle_ilog2(P_MIN) - shuffle_ilog2(2 * (unsigned long long) MSGS - 1);
static_assert(SHUFFLE_BITS > 0, "MSGS is too large for the RNS basis");
static constexpr int SHUFFLE_REPS = (LEVEL + SHUFFLE_BITS - 1) / SHUFFLE_BITS;

/* How many times each linear proof is run. Its challenge beta is uniform over
 * R_q and its final check reduces to beta L = 0 for the residual L of the
 * relation, so a prover whose committed messages violate it passes exactly when
 * beta vanishes in a slot where L does not: 1 / p_min, and no more, because the
 * challenge set has zero divisors -- see SOUNDNESS.md section 7. The LIN_REPS
 * challenges come from one hash of all LIN_REPS first messages, so re-rolling
 * any of them re-rolls all, and a forged relation has to survive every one of
 * them at once: (1 / p_min)^LIN_REPS, which is what makes the repetitions
 * multiply where those of the pass do not. See section 8.1. */
static constexpr int LIN_REPS =
		(LEVEL + shuffle_ilog2(P_MIN) - 1) / shuffle_ilog2(P_MIN);
static_assert(LIN_REPS > 1, "one linear proof cannot reach LEVEL on its own");

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
static vector < params::poly_q > *r, *pr, *_r;
static params::poly_q *ms, *_ms, *s;
static params::poly_q (*y)[LIN_REPS][WIDTH], (*w)[LIN_REPS][WIDTH],
		(*_y)[LIN_REPS][WIDTH];
/* What a linear proof publishes besides its responses: the hash its challenges
 * come from. The first messages are rebuilt by the verifier. */
static uint8_t (*lh)[BLAKE3_OUT_LEN];
static params::poly_q *theta, *inv, *inv_tmp;
static params::poly_q *sg, *fa, *fb;

/* The proof that every committed sigma_i is a ring constant, the algebraic
 * half of the membership Lemma 5 requires. It is produced by the prover along
 * with the P_i and consumed by the verifier; it is kept here rather than
 * threaded through the already long argument lists of the two. */
static pismall_const_t *cst;

/* The proof that every committed sigma_i is short, which is what makes the
 * coefficient sets of the membership proof exact; see the header comment. */
static pibnd_short_t *bnd;

static void shuffle_alloc(void) {
	com = new commit_t[MSGS];
	/* d, _r and theta are the part of a pass that outlives it: every pass's
	 * D_i has to exist before any beta is drawn, so they are dimensioned by
	 * SHUFFLE_REPS as well and indexed d[rep * MSGS + i]. See SOUNDNESS.md
	 * section 6.1. */
	d = new commit_t[SHUFFLE_REPS * MSGS];
	_r = new vector < params::poly_q >[SHUFFLE_REPS * MSGS];
	cs = new commit_t[MSGS];
	pcom = new commit_t[MSGS];
	r = new vector < params::poly_q >[MSGS];
	pr = new vector < params::poly_q >[MSGS];
	ms = new params::poly_q[MSGS];
	_ms = new params::poly_q[MSGS];
	s = new params::poly_q[MSGS];
	y = new params::poly_q[MSGS][LIN_REPS][WIDTH];
	w = new params::poly_q[MSGS][LIN_REPS][WIDTH];
	_y = new params::poly_q[MSGS][LIN_REPS][WIDTH];
	lh = new uint8_t[MSGS][BLAKE3_OUT_LEN];
	theta = new params::poly_q[SHUFFLE_REPS * MSGS];
	inv = new params::poly_q[MSGS];
	inv_tmp = new params::poly_q[MSGS];
	sg = new params::poly_q[MSGS];
	fa = new params::poly_q[MSGS];
	fb = new params::poly_q[MSGS];
}

static void shuffle_free(void) {
	delete[]com;
	delete[]d;
	delete[]_r;
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
	delete[]lh;
	delete[]theta;
	delete[]inv;
	delete[]inv_tmp;
	delete[]sg;
	delete[]fa;
	delete[]fb;
	pismall_const_free(cst);
	cst = NULL;
	pismall_const_clear();
	pibnd_short_free(bnd);
	bnd = NULL;
	pibnd_short_clear();
}

/**
 * The map g : [N] -> D of Lemma 5, instantiated as g(i) = i, the ring constant
 * with that value.
 *
 * The result is in the coefficient domain, which is what bdlop_commit expects;
 * callers doing arithmetic with it have to convert.
 *
 * @param[out] out			- the resulting ring element.
 * @param[in] i				- the index to encode, below the degree of the ring.
 */
static void index_scalar(params::poly_q & out, size_t i) {
	array < mpz_t, params::poly_q::degree > coeffs;

	for (size_t k = 0; k < params::poly_q::degree; k++) {
		mpz_init2(coeffs[k], (params::poly_q::bits_in_moduli_product() << 2));
		mpz_set_ui(coeffs[k], k == 0 ? i : 0);
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
/* The transcript hash of one linear proof: the statement, and the first messages
 * of all LIN_REPS repetitions together. Binding them is what makes the
 * repetitions multiply, since re-rolling any one of them moves every challenge.
 *
 * The middle commitment of the relation, the one to sigma_l, lives under a key
 * of its own: it is committed once and shared by every pass, while x and _x are
 * under the rho-compressed key of this pass. The two share A1 and differ only in
 * the A2 row. See SOUNDNESS.md sections 6.1 and 7.1. */
static void lin_hash(uint8_t hash[BLAKE3_OUT_LEN], comkey_t & key,
		comkey_t & pkey, commit_t x, commit_t p, commit_t y,
		params::poly_q coef[3], params::poly_q u[LIN_REPS],
		params::poly_q t[LIN_REPS], params::poly_q tp[LIN_REPS],
		params::poly_q _t[LIN_REPS]) {
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
		blake3_hasher_update(&hasher, (const uint8_t *)pkey.A2[0][j].data(),
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

	for (int j = 0; j < LIN_REPS; j++) {
		blake3_hasher_update(&hasher, (const uint8_t *)u[j].data(), 16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)t[j].data(), 16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)tp[j].data(), 16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)_t[j].data(), 16 * DEGREE);
	}

	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);
}

/* The LIN_REPS challenges the hash above commits to. The challenge set is not
 * free of zero divisors in this ring -- the test "KNOWN GAP: a challenge
 * difference can be a zero divisor" exhibits one -- so one of them is worth
 * only about 1 / p_min, and it is the repetitions that carry the proof to
 * LEVEL. See SOUNDNESS.md, sections 7 and 7.1. */
static void lin_chal(params::poly_q beta[LIN_REPS],
		const uint8_t hash[BLAKE3_OUT_LEN]) {
	nfl::fastrandombytes_seed(hash);
	for (int j = 0; j < LIN_REPS; j++) {
		bdlop_sample_chal(beta[j]);
	}
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

static int simul_inverse(params::poly_q inv[MSGS], params::poly_q m[MSGS]) {
	params::poly_q w;
	int ok;

	inv[0] = m[0];
	inv_tmp[0] = m[0];

	for (size_t i = 1; i < MSGS; i++) {
		inv_tmp[i] = m[i];
		inv[i] = inv[i - 1] * m[i];
	}

	w = inv[MSGS - 1];
	/* The b_i behave like uniform elements of R_q, so this fails when one of
	 * the 2N NTT residues of their product is zero: about 2N MSGS / p_min,
	 * which is 2^-21 a pass at MSGS = 1000 and 2^-19 a shuffle. The event
	 * depends on the sigma_i, so stopping on it would tell an observer
	 * something about the permutation. The caller restarts instead, which moves
	 * tau and mu and so moves the event. See SOUNDNESS.md section 4.2. */
	ok = poly_inverse(w, w);
	if (!ok) {
		return 0;
	}

	for (size_t i = MSGS - 1; i > 0; i--) {
		inv[i] = w * inv[i - 1];
		w = w * inv_tmp[i];
	}
	inv[0] = w;
	return 1;
}

/* Accumulate <z, v> and ||v||^2 over one masked opening, centred. A proof has
 * three of them and they are folded into one pair: the rejection sampling
 * below is then Figure 2 run on the concatenation, which is the standard
 * procedure, pays the halfspace test once instead of three times and leaks one
 * bit rather than three. See SOUNDNESS.md section 8.1. */
static void rej_accum(params::poly_q z[WIDTH], params::poly_q v[WIDTH],
		mpz_t dot, mpz_t norm) {
	array < mpz_t, params::poly_q::degree > coeffs0, coeffs1;
	params::poly_q t;
	mpz_t qDivBy2, tmp;

	mpz_inits(qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs0[i], (params::poly_q::bits_in_moduli_product() << 2));
		mpz_init2(coeffs1[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
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

	mpz_clears(qDivBy2, tmp, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs0[i]);
		mpz_clear(coeffs1[i]);
	}
}

/* Reject when <z, v> < 0, then accept with probability min(1, r) for
 * r = exp((-2<z, v> + ||v||^2) / 2 s2) / M. The first step is what SIGMA_C is
 * chosen for: inside the halfspace the ratio to dominate is at most
 * exp(||v||^2 / 2 s2), which is M. */
static int rej_decide(mpz_t dot, mpz_t norm, uint64_t s2) {
	double r, M;
	int64_t seed;
	mpf_t u;
	uint8_t buf[8];
	gmp_randstate_t state;
	int result;

	mpf_init(u);
	gmp_randinit_mt(state);
	if (getrandom(buf, sizeof(buf), 0) != sizeof(buf)) {
		fprintf(stderr, "ERROR: could not read entropy for rejection sampling\n");
		abort();
	}
	memcpy(&seed, buf, sizeof(buf));
	gmp_randseed_ui(state, seed);
	mpf_urandomb(u, state, mpf_get_default_prec());

	M = exp(mpz_get_d(norm) / (2.0 * s2));
	result = mpz_get_d(dot) < 0;
	r = -2.0 * mpz_get_d(dot) + mpz_get_d(norm);
	r = r / (2.0 * s2);
	r = exp(r) / M;
	result |= mpf_get_d(u) > r;

	mpf_clear(u);
	gmp_randclear(state);
	return result;
}

/* How many times the prover retries rejection sampling before giving up. The
 * openings of all LIN_REPS repetitions are tested as one, which measurement
 * puts at 0.43 of attempts, so a proof usually passes in one or two; a prover whose witness is not
 * short never succeeds, and without a bound it would spin here forever. The
 * budget is far past what that rate needs, and costs nothing, since it is only
 * reached when the witness is long.
 *
 * Returning whether it succeeded matters as much as the bound. Rejection
 * sampling is what makes the masked opening independent of the witness, not
 * what keeps it inside the norm bound, so the opening left behind by a prover
 * that gave up may well verify while leaking. It must not be published, which
 * is why the status is threaded back to run(). */
#define LIN_TRIES   256

/* How many times the prover rebuilds its first message when a pass turns out
 * unusable, which is the singular case of simul_inverse at about 2^-19 a
 * shuffle. Eight of them leave 2^-152, and each costs the two sub-proofs. */
#define SHUFFLE_TRIES 8

/* One linear proof, run LIN_REPS times against challenges drawn from a single
 * hash of all LIN_REPS first messages. What it publishes is that hash and the
 * responses: the verifier rebuilds t, tp, t' and u from the responses and the
 * challenges, which is the transcript the paper describes, and saves four ring
 * elements a repetition over sending them. */
static int lin_prover(params::poly_q y[LIN_REPS][WIDTH],
		params::poly_q w[LIN_REPS][WIDTH], params::poly_q _y[LIN_REPS][WIDTH],
		uint8_t h[BLAKE3_OUT_LEN], commit_t x, commit_t p, commit_t _x,
		params::poly_q coef[3], comkey_t & key, comkey_t & pkey,
		vector < params::poly_q > r, vector < params::poly_q > pr,
		vector < params::poly_q > _r) {
	params::poly_q beta[LIN_REPS], t[LIN_REPS], tp[LIN_REPS], _t[LIN_REPS];
	params::poly_q u[LIN_REPS];
	params::poly_q tmp[WIDTH], ptmp[WIDTH], _tmp[WIDTH];
	array < mpz_t, params::poly_q::degree > coeffs;
	mpz_t dot, norm;
	int rej, tries = 0;

	mpz_inits(dot, norm, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(coeffs[i], (params::poly_q::bits_in_moduli_product() << 2));
	}

	do {
		/* Prover samples y, y_p and y' from Gaussian, once per repetition. */
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < WIDTH; i++) {
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					int64_t coeff = sample_z(0.0, SIGMA_C);
					mpz_set_si(coeffs[k], coeff);
				}
				y[j][i].mpz2poly(coeffs);
				y[j][i].ntt_pow_phi();
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					int64_t coeff = sample_z(0.0, SIGMA_C);
					mpz_set_si(coeffs[k], coeff);
				}
				w[j][i].mpz2poly(coeffs);
				w[j][i].ntt_pow_phi();
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					int64_t coeff = sample_z(0.0, SIGMA_C);
					mpz_set_si(coeffs[k], coeff);
				}
				_y[j][i].mpz2poly(coeffs);
				_y[j][i].ntt_pow_phi();
			}

			t[j] = y[j][0];
			tp[j] = w[j][0];
			_t[j] = _y[j][0];
			for (int i = 0; i < HEIGHT; i++) {
				for (int k = 0; k < WIDTH - HEIGHT; k++) {
					t[j] = t[j] + key.A1[i][k] * y[j][k + HEIGHT];
					tp[j] = tp[j] + pkey.A1[i][k] * w[j][k + HEIGHT];
					_t[j] = _t[j] + key.A1[i][k] * _y[j][k + HEIGHT];
				}
			}

			u[j] = 0;
			for (int i = 0; i < WIDTH; i++) {
				u[j] = u[j] + coef[0] * (key.A2[0][i] * y[j][i]);
				u[j] = u[j] + coef[1] * (pkey.A2[0][i] * w[j][i]);
				u[j] = u[j] - (key.A2[0][i] * _y[j][i]);
			}
		}

		/* Sample every challenge from one hash of every first message. */
		lin_hash(h, key, pkey, x, p, _x, coef, u, t, tp, _t);
		lin_chal(beta, h);

		/* Prover, and one rejection test over all of the openings: they stand
		 * or fall together, since a fresh first message anywhere moves every
		 * challenge. */
		mpz_set_ui(dot, 0);
		mpz_set_ui(norm, 0);
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < WIDTH; i++) {
				tmp[i] = beta[j] * r[i];
				ptmp[i] = beta[j] * pr[i];
				_tmp[i] = beta[j] * _r[i];
				y[j][i] = y[j][i] + tmp[i];
				w[j][i] = w[j][i] + ptmp[i];
				_y[j][i] = _y[j][i] + _tmp[i];
			}
			rej_accum(y[j], tmp, dot, norm);
			rej_accum(w[j], ptmp, dot, norm);
			rej_accum(_y[j], _tmp, dot, norm);
		}
		rej = rej_decide(dot, norm, SIGMA_C * SIGMA_C);
	} while (rej && ++tries < LIN_TRIES);

	mpz_clears(dot, norm, nullptr);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(coeffs[i]);
	}

	return !rej;
}

static int lin_verifier(params::poly_q z[LIN_REPS][WIDTH],
		params::poly_q zp[LIN_REPS][WIDTH], params::poly_q _z[LIN_REPS][WIDTH],
		uint8_t h[BLAKE3_OUT_LEN], commit_t x, commit_t p, commit_t _x,
		params::poly_q coef[3], comkey_t & key, comkey_t & pkey) {
	params::poly_q beta[LIN_REPS], t[LIN_REPS], tp[LIN_REPS], _t[LIN_REPS];
	params::poly_q u[LIN_REPS], v, tmp;
	uint8_t h2[BLAKE3_OUT_LEN];
	int result = 1;

	lin_chal(beta, h);

	for (int j = 0; j < LIN_REPS; j++) {
		/* Verifier checks norm, reconstruct from NTT representation. */
		for (int i = 0; i < WIDTH; i++) {
			v = z[j][i];
			v.invntt_pow_invphi();
			result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
			v = zp[j][i];
			v.invntt_pow_invphi();
			result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
			v = _z[j][i];
			v.invntt_pow_invphi();
			result &= bdlop_test_norm(v, 4 * SIGMA_C * SIGMA_C);
		}

		/* The first messages are not sent: they are what the checks say they
		 * are, A1 z - beta c1 and the A2 combination less beta times the
		 * statement, and their hash is what has to come out right. */
		t[j] = z[j][0];
		tp[j] = zp[j][0];
		_t[j] = _z[j][0];
		for (int i = 0; i < HEIGHT; i++) {
			for (int k = 0; k < WIDTH - HEIGHT; k++) {
				t[j] = t[j] + key.A1[i][k] * z[j][k + HEIGHT];
				tp[j] = tp[j] + pkey.A1[i][k] * zp[j][k + HEIGHT];
				_t[j] = _t[j] + key.A1[i][k] * _z[j][k + HEIGHT];
			}
		}
		t[j] = t[j] - beta[j] * x.c1;
		tp[j] = tp[j] - beta[j] * p.c1;
		_t[j] = _t[j] - beta[j] * _x.c1;

		u[j] = 0;
		for (int i = 0; i < WIDTH; i++) {
			u[j] = u[j] + coef[0] * (key.A2[0][i] * z[j][i]);
			u[j] = u[j] + coef[1] * (pkey.A2[0][i] * zp[j][i]);
			u[j] = u[j] - (key.A2[0][i] * _z[j][i]);
		}
		tmp = coef[0] * x.c2[0] + coef[1] * p.c2[0] + coef[2] - _x.c2[0];
		u[j] = u[j] - tmp * beta[j];
	}

	lin_hash(h2, key, pkey, x, p, _x, coef, u, t, tp, _t);
	result &= (memcmp(h, h2, BLAKE3_OUT_LEN) == 0);

	return result;
}

static void shuffle_rho_hash(params::poly_q rho[SIZE], commit_t c[MSGS],
		vector < vector < params::poly_q >> &_m, int rep) {
	uint8_t hash[BLAKE3_OUT_LEN];
	uint8_t sep = (uint8_t) rep;
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, &sep, 1);
	for (int i = 0; i < MSGS; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)c[i].c1.data(),
				16 * DEGREE);
		for (size_t j = 0; j < c[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)c[i].c2[j].data(),
					16 * DEGREE);
		}
		for (size_t j = 0; j < _m[i].size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)_m[i][j].data(),
					16 * DEGREE);
		}
	}
	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	nfl::fastrandombytes_seed(hash);
	rho[0] = 1;
	rho[0].ntt_pow_phi();
	for (size_t j = 1; j < SIZE; j++) {
		rho[j] = nfl::uniform();
	}
	nfl::fastrandombytes_reseed();
}

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

/* The challenge beta of every pass at once, from a hash of every pass's D_i.
 * Drawing them separately, from one pass's messages each, is what let a prover
 * settle the passes one at a time; see SOUNDNESS.md section 6.1. The statement
 * is hashed uncompressed -- the input commitments and the output list rather
 * than their rho-compressions -- since rho is hashed with them and the
 * compression follows from the two. */
static void shuffle_beta_hash(params::poly_q beta[SHUFFLE_REPS],
		commit_t com[MSGS], vector < vector < params::poly_q >> &_m,
		commit_t p[MSGS], commit_t d[], params::poly_q tau[SHUFFLE_REPS],
		params::poly_q mu[SHUFFLE_REPS], params::poly_q rho[][SIZE]) {
	uint8_t hash[BLAKE3_OUT_LEN];
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);

	for (int i = 0; i < MSGS; i++) {
		blake3_hasher_update(&hasher, (const uint8_t *)com[i].c1.data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)p[i].c1.data(),
				16 * DEGREE);
		for (size_t j = 0; j < com[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)com[i].c2[j].data(),
					16 * DEGREE);
		}
		for (size_t j = 0; j < p[i].c2.size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)p[i].c2[j].data(),
					16 * DEGREE);
		}
		for (size_t j = 0; j < _m[i].size(); j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)_m[i][j].data(),
					16 * DEGREE);
		}
	}

	for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
		for (int j = 0; j < SIZE; j++) {
			blake3_hasher_update(&hasher, (const uint8_t *)rho[rep][j].data(),
					16 * DEGREE);
		}
		blake3_hasher_update(&hasher, (const uint8_t *)tau[rep].data(),
				16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)mu[rep].data(),
				16 * DEGREE);
		for (int i = 0; i < MSGS; i++) {
			commit_t *di = &d[rep * MSGS + i];
			blake3_hasher_update(&hasher, (const uint8_t *)di->c1.data(),
					16 * DEGREE);
			for (size_t j = 0; j < di->c2.size(); j++) {
				blake3_hasher_update(&hasher, (const uint8_t *)di->c2[j].data(),
						16 * DEGREE);
			}
		}
	}

	blake3_hasher_finalize(&hasher, hash, BLAKE3_OUT_LEN);

	/* One seed, one stream: the passes take their challenges from it in order,
	 * so each of them depends on all of the D_i. */
	nfl::fastrandombytes_seed(hash);
	for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
		beta[rep] = nfl::uniform();
	}
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

	index_scalar(gl, l);
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
 * makes those coefficient sets exact over Z_q. See SOUNDNESS.md, section 5.
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

	pismall_const_free(cst);
	cst = pismall_const_prove(key, p, pr, sigma, MSGS);
	pibnd_short_free(bnd);
	bnd = pibnd_short_prove(key, p, pr, sigma, MSGS);
}

/* The factors of the product of Lemma 5:
 *     a_i = m_i + g(i) * tau - mu,
 *     b_i = _m_i + sigma_i * tau - mu.
 * Tying the index to every message is what forces the permutations of the CRT
 * components to coincide, and is what the published product lacked. Both halves
 * of the prover need them and neither keeps them: they follow from the pass's
 * compression and its tau and mu, and recomputing is cheaper than holding a
 * copy per pass. */
static void shuffle_factors(params::poly_q ms[MSGS], params::poly_q _ms[MSGS],
		params::poly_q & tau, params::poly_q & mu) {
	params::poly_q gl;

	for (size_t i = 0; i < MSGS; i++) {
		index_scalar(gl, i);
		gl.ntt_pow_phi();
		fa[i] = ms[i] + gl * tau - mu;
		fb[i] = _ms[i] + sg[i] * tau - mu;
	}
}

/* The half of a pass the prover can send before beta: its tau and mu, and the
 * commitments D_i under them. Every pass reaches this point before any beta is
 * drawn, which is what binds them to each other. */
static int shuffle_prover_commit(params::poly_q & tau, params::poly_q & mu,
		commit_t d[MSGS], vector < params::poly_q > _r[MSGS],
		params::poly_q theta[MSGS], commit_t p[MSGS], commit_t c[MSGS],
		params::poly_q ms[MSGS], params::poly_q _ms[MSGS],
		params::poly_q rho[SIZE], comkey_t & key, int rep) {
	vector < params::poly_q > t0(1);

	shuffle_chal_hash(tau, mu, c, p, _ms, rho, rep);
	shuffle_factors(ms, _ms, tau, mu);

	/* The s_i of the second half divide by the b_i, so this pass is only usable
	 * if their product inverts. Testing it here costs one inversion and saves
	 * discovering it after the linear proofs have been built. */
	if (!simul_inverse(inv, fb)) {
		return 0;
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

	return 1;
}

/* The other half, once beta is known for every pass: the published s_i and the
 * MSGS linear proofs. */
static int shuffle_prover_respond(params::poly_q y[MSGS][LIN_REPS][WIDTH],
		params::poly_q w[MSGS][LIN_REPS][WIDTH],
		params::poly_q _y[MSGS][LIN_REPS][WIDTH],
		uint8_t lh[MSGS][BLAKE3_OUT_LEN], commit_t d[MSGS],
		commit_t p[MSGS], vector < params::poly_q > pr[MSGS],
		vector < params::poly_q > _r[MSGS], params::poly_q theta[MSGS],
		params::poly_q s[MSGS], commit_t c[MSGS], params::poly_q ms[MSGS],
		params::poly_q _ms[MSGS], vector < params::poly_q > r[MSGS],
		params::poly_q & beta, params::poly_q & tau, params::poly_q & mu,
		comkey_t & key, comkey_t & pkey) {
	params::poly_q coef[3];
	int complete = 1;

	shuffle_factors(ms, _ms, tau, mu);
	if (!simul_inverse(inv, fb)) {
		return 0;
	}
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
		complete &= lin_prover(y[l], w[l], _y[l], lh[l], c[l], p[l], d[l], coef,
				key, pkey, r[l], pr[l], _r[l]);
	}

	return complete;
}

static int shuffle_verifier(params::poly_q y[MSGS][LIN_REPS][WIDTH],
		params::poly_q w[MSGS][LIN_REPS][WIDTH],
		params::poly_q _y[MSGS][LIN_REPS][WIDTH],
		uint8_t lh[MSGS][BLAKE3_OUT_LEN], commit_t d[MSGS],
		commit_t p[MSGS], params::poly_q s[MSGS], commit_t c[MSGS],
		params::poly_q _ms[MSGS], params::poly_q rho[SIZE],
		params::poly_q & beta, comkey_t & key, comkey_t & pkey, int rep) {
	params::poly_q coef[3], tau, mu;
	int result = 1;

	/* The sub-proofs about the P_i are not checked here: the P_i are the first
	 * message, sent once for every pass, and run() checks them once. beta is
	 * not derived here either, being a function of every pass's D_i; run()
	 * derives all of them from the transcript before this is called. */
	shuffle_chal_hash(tau, mu, c, p, _ms, rho, rep);
	for (size_t l = 0; l < MSGS; l++) {
		shuffle_coeffs(coef, l, s, _ms, beta, tau, mu);
		result &= lin_verifier(y[l], w[l], _y[l], lh[l], c[l], p[l], d[l], coef,
				key, pkey);
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
/* The rho-compression of one pass: the messages, the commitments and the key it
 * induces. Both halves of the pass need them and neither keeps them, since one
 * copy per pass would be MSGS commitments and 2 MSGS ring elements each. */
static void shuffle_compress(comkey_t & _key, commit_t cs[MSGS],
		params::poly_q ms[MSGS], params::poly_q _ms[MSGS],
		vector < vector < params::poly_q >> &m,
		vector < vector < params::poly_q >> &_m, commit_t com[MSGS],
		comkey_t & key, params::poly_q rho[SIZE]) {
	params::poly_q t1;

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
}

static int run(vector < vector < params::poly_q >> m,
		vector < vector < params::poly_q >> _m,
		vector < params::poly_q > &sigma, comkey_t & key) {
	static params::poly_q rho[SHUFFLE_REPS][SIZE];
	static params::poly_q tau[SHUFFLE_REPS], mu[SHUFFLE_REPS];
	static params::poly_q beta[SHUFFLE_REPS], vbeta[SHUFFLE_REPS];
	comkey_t _key;
	int result = 1, ready, tries = 0;

	/* The commitments to the sigma_i and the two sub-proofs that place them in D
	 * are the prover's first message, and they are sent once. Every pass's
	 * challenges are a hash of them, so re-rolling them re-rolls every pass at
	 * once, which is what makes the errors of the passes multiply; a first
	 * message per pass would let a prover settle the passes one at a time. They
	 * can be shared because they are committed under the original key rather
	 * than the rho-compressed one of the pass. See SOUNDNESS.md section 6.1. */
	/* Every pass commits its D_i before any of them has a beta, for the same
	 * reason: beta is a hash of all of them together. The compression and the
	 * key it induces depend on rho and so stay inside the pass, recomputed in
	 * the second half rather than held.
	 *
	 * The whole of it is a retry, because a pass is unusable when the product
	 * of its b_i does not invert, and that event depends on the sigma_i: giving
	 * up on it would tell an observer which permutations could have caused it.
	 * What moves it is fresh randomness in the P_i, which moves every pass's
	 * tau and mu, so the restart reaches back that far and takes the two
	 * sub-proofs with it. It happens about once in 2^19 shuffles at
	 * MSGS = 1000; SHUFFLE_TRIES of them leave 2^-152. See SOUNDNESS.md 4.2. */
	do {
		ready = 1;
		shuffle_commit_sigma(pcom, pr, sigma.data(), key);
		for (int rep = 0; rep < SHUFFLE_REPS && ready; rep++) {
			shuffle_rho_hash(rho[rep], com, _m, rep);
			shuffle_compress(_key, cs, ms, _ms, m, _m, com, key, rho[rep]);
			ready = shuffle_prover_commit(tau[rep], mu[rep], &d[rep * MSGS],
					&_r[rep * MSGS], &theta[rep * MSGS], pcom, cs, ms, _ms,
					rho[rep], _key, rep);
		}
	} while (!ready && ++tries < SHUFFLE_TRIES);
	result &= ready;
	result &= pismall_const_verify(cst, key, pcom, MSGS);
	result &= pibnd_short_verify(bnd, key, pcom, MSGS);

	/* Twice, because the verifier derives its challenges from the transcript
	 * rather than taking the prover's word for them; the two must agree. */
	shuffle_beta_hash(beta, com, _m, pcom, d, tau, mu, rho);
	shuffle_beta_hash(vbeta, com, _m, pcom, d, tau, mu, rho);

	for (int rep = 0; rep < SHUFFLE_REPS; rep++) {
		shuffle_compress(_key, cs, ms, _ms, m, _m, com, key, rho[rep]);
		result &= shuffle_prover_respond(y, w, _y, lh, &d[rep * MSGS], pcom, pr,
				&_r[rep * MSGS], &theta[rep * MSGS], s, cs, ms, _ms, r,
				beta[rep], tau[rep], mu[rep], _key, key);
		result &= shuffle_verifier(y, w, _y, lh, &d[rep * MSGS], pcom, s, cs,
				_ms, rho[rep], vbeta[rep], _key, key, rep);
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
	vector < vector < params::poly_q >> m(MSGS), _m(MSGS), am(MSGS), bm(MSGS);
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
		index_scalar(sigma[i], pi);
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

	TEST_ONCE("scalar differences are invertible") {
		/* This is what makes the constants a legal choice for Lemma 5: a
		 * difference of distinct g(i) is a non-zero integer below MSGS, and
		 * every such integer is coprime to q because it is smaller than either
		 * prime of the basis. Note this holds however far the ring splits,
		 * which is exactly what fails for the short ring elements below. */
		params::poly_q ga, gb, t0;

		for (size_t k = 1; k < 8; k++) {
			index_scalar(ga, 0);
			index_scalar(gb, k);
			ga.ntt_pow_phi();
			gb.ntt_pow_phi();
			ga = ga - gb;
			TEST_ASSERT(poly_inverse(t0, ga) == 1, end);
		}
		index_scalar(ga, MSGS - 1);
		index_scalar(gb, 0);
		ga.ntt_pow_phi();
		gb.ntt_pow_phi();
		ga = ga - gb;
		TEST_ASSERT(poly_inverse(t0, ga) == 1, end);
	} TEST_END;

	TEST_ONCE("a short polynomial can be a zero divisor") {
		/* The reason D cannot be a ball of small norm here, unlike in a ring
		 * splitting into few factors. The pattern below is a 0/1 polynomial of
		 * Hamming weight 19 whose value in one of the NTT slots is zero;
		 * it was found by meet-in-the-middle over subset sums of the powers of
		 * one primitive 2N-th root of unity modulo the first RNS prime, which
		 * costs seconds. Its l_infinity norm is 1, so no norm bound separates
		 * it from the short elements a ball of small norm would contain, yet it
		 * is a zero divisor and multiplying by it loses information in that
		 * slot. A constant of the same norm is a small integer and cannot do
		 * this, which is what makes g(i) = i work where a ball does not. */
		const char *bits = "010011110110000101000001110000110001100100010001";
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
		TEST_ASSERT(weight == 19, end);
		TEST_ASSERT(poly_inverse(t0, e) == 0, end);
	} TEST_END;

	TEST_ONCE("the norm bound leaves room for the CRT argument") {
		/* Section 6.4 of SOUNDNESS.md concludes that sigma_i is the same
		 * constant in both CRT components by reading two congruences, one
		 * modulo each prime of the basis, as equalities over the integers.
		 * That step needs every quantity in them to stay below p_min / 2:
		 * twice the norm bound, because extraction compares two transcripts
		 * whose challenges differ by one, plus the slack of a challenge
		 * difference times an index g(j). */
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
		 * The pattern below has 9 coefficients +1 and 9 coefficients -1, so it
		 * is one of those differences: the +1 positions are one side and the
		 * -1 positions the other, each of Hamming weight exactly NONZERO, with
		 * no shared positions needed. It vanishes in one of the NTT
		 * slots. Found by meet-in-the-middle over subset sums of the powers of
		 * one primitive 2N-th root modulo the first RNS prime, in seconds, the
		 * same way as the short zero divisor above. Asserting the bug. */
		const char *pat = "000+++++0+00+000+00000+00000--0-00-000-0-00--00-";
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
		TEST_ASSERT(pos == 9 && neg == 9, end);
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
	 * again. A CRT mix of two constants is still a constant, so the algebraic
	 * half of the membership proof accepts these sigma_i; what rules them out
	 * is that the constant is a CRT idempotent, far too large for the norm
	 * bound. */
	for (int i = 0; i < MSGS; i++) {
		asigma[i] = sigma[i];
	}
	crt_mix(asigma[0], asigma[1]);

	TEST_ONCE("shuffle proof rejects CRT-mixed sigma") {
		/* pismall_const_prove() accepts these sigma_i: a CRT mix of two
		 * constants is a constant, so the exact half of the membership proof
		 * has nothing to object to. It is the norm bound that rejects them,
		 * their value being a CRT idempotent and far too large for the masked
		 * opening to stay inside the bound the verifier checks. */
		TEST_ASSERT(run(m, am, asigma, key) == 0, end);
	} TEST_END;

	/* Third attack, on the compression rather than on the product. The SIZE
	 * components of each message are folded into one with rho before the proof
	 * ever sees them, so a prover who alters the output list by any Delta with
	 * sum_j rho_j Delta_j = 0 changes nothing the proof looks at. The Delta
	 * below is that collision, built against the rho the honest list induces --
	 * which is the best a prover can do, and is not enough, because rho is
	 * derived from the list it compresses: altering the list moves rho, and the
	 * collision is a collision for the old one only. */
	for (int i = 0; i < MSGS; i++) {
		bm[i].resize(SIZE);
		for (int j = 0; j < SIZE; j++) {
			bm[i][j] = _m[i][j];
		}
	}
	{
		params::poly_q delta = 0, d0, zero = 0, rho[SIZE];

		shuffle_rho_hash(rho, com, _m, 0);
		delta(0, 0) = 1;                /* one slot of the first prime */
		d0 = zero - rho[1] * delta;     /* so that d0 + rho_1 delta = 0 */
		delta.invntt_pow_invphi();
		d0.invntt_pow_invphi();
		bm[0][0] = bm[0][0] + d0;
		bm[0][1] = bm[0][1] + delta;
	}

	TEST_ONCE("shuffle proof rejects a compression collision") {
		TEST_ASSERT(!util::equal(bm[0][1], _m[0][1]), end);
		TEST_ASSERT(run(m, bm, sigma, key) == 0, end);
	} TEST_END;

  end:
	return;
}

/* The size of the transcript the last run() produced. The pass-local buffers
 * are reused across passes, so one pass is measured and multiplied; everything
 * else is measured as it stands. */
static void proof_size(void) {
	serial::bits pass, once;
	params::poly_q t0;

	for (size_t i = 0; i < MSGS; i++) {
		serial::put_uniform(pass, d[i].c1);
		for (size_t j = 0; j < d[i].c2.size(); j++) {
			serial::put_uniform(pass, d[i].c2[j]);
		}
		serial::put_uniform(pass, s[i]);
		for (int j = 0; j < LIN_REPS; j++) {
			for (int k = 0; k < WIDTH; k++) {
				t0 = y[i][j][k];
				t0.invntt_pow_invphi();
				serial::put_gauss(pass, t0, SIGMA_C);
				t0 = w[i][j][k];
				t0.invntt_pow_invphi();
				serial::put_gauss(pass, t0, SIGMA_C);
				t0 = _y[i][j][k];
				t0.invntt_pow_invphi();
				serial::put_gauss(pass, t0, SIGMA_C);
			}
		}
		pass.put(0, 8 * BLAKE3_OUT_LEN);        /* the linear proof's hash */
		serial::put_uniform(once, pcom[i].c1);
		for (size_t j = 0; j < pcom[i].c2.size(); j++) {
			serial::put_uniform(once, pcom[i].c2[j]);
		}
	}

	size_t per_pass = pass.bytes();
	size_t small = pismall_const_bytes(cst);
	size_t bound = pibnd_short_bytes(bnd);
	size_t first = once.bytes() + small + bound;
	size_t total = SHUFFLE_REPS * per_pass + first;

	printf("\n** Proof size, measured, at MSGS = %d:\n\n", (int)MSGS);
	printf("  a pass                                = %8.1f KB/vote\n",
			per_pass / 1024.0 / MSGS);
	printf("  %d passes                              = %8.1f KB/vote\n",
			SHUFFLE_REPS, SHUFFLE_REPS * per_pass / 1024.0 / MSGS);
	printf("  P_i, Pi_SMALL and Pi_BND, sent once   = %8.1f KB/vote\n",
			first / 1024.0 / MSGS);
	printf("    of which Pi_SMALL                   = %8.1f KB/vote\n",
			small / 1024.0 / MSGS);
	printf("    of which Pi_BND                     = %8.1f KB/vote\n",
			bound / 1024.0 / MSGS);
	printf("  TOTAL                                 = %8.1f KB/vote\n",
			total / 1024.0 / MSGS);
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
	/* Heap, not stack: LIN_REPS * WIDTH ring elements three times over is
	 * megabytes, and the frame limit this file builds with is 4 MiB. */
	auto by = new params::poly_q[LIN_REPS][WIDTH];
	auto bw = new params::poly_q[LIN_REPS][WIDTH];
	auto _by = new params::poly_q[LIN_REPS][WIDTH];
	uint8_t bh[BLAKE3_OUT_LEN];
	params::poly_q coef[3];
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
		index_scalar(sigma[i], pi);
	}

	for (size_t i = 0; i < 3; i++) {
		coef[i] = nfl::ZO_dist();
		coef[i].ntt_pow_phi();
	}

	BENCH_BEGIN("linear proof") {
		BENCH_ADD(lin_prover(by, bw, _by, bh, com[0], com[1], com[1], coef, key,
						key, r[0], r[1], r[1]));
	} BENCH_END;

	BENCH_BEGIN("linear verifier") {
		BENCH_ADD(lin_verifier(by, bw, _by, bh, com[0], com[1], com[1], coef,
						key, key));
	} BENCH_END;

	BENCH_SMALL("shuffle-proof (N messages)", run(m, _m, sigma, key));

	delete[]by;
	delete[]bw;
	delete[]_by;
}

int main(int argc, char *argv[]) {
	shuffle_alloc();

	printf("\n** Tests for lattice-based shuffle proof:\n\n");
	test();

	proof_size();

	printf("\n** Microbenchmarks for polynomial arithmetic:\n\n");
	microbench();

	printf("\n** Benchmarks for lattice-based shuffle proof:\n\n");
	bench();

	shuffle_free();
	return test_failures() != 0;
}
#endif
