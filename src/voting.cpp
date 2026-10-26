/**
 * @file
 *
 * The mix-net end to end, with MSGS voters, MIXERS mix servers and PARTIES
 * trustees, as the paper puts the pieces together:
 *
 *   1. Key generation: a BGV key pair, its secret key additively shared among
 *      the PARTIES trustees (bgv_keyshare, a dealer, as the repository does).
 *   2. Voting: each voter encrypts its vote, X^j for one of NCAND candidates.
 *   3. Mixing, by each server in turn: re-encrypt every ciphertext c_i as
 *      c_i + E_i with E_i a fresh encryption of zero, commit to E_i, and add
 *      c_i into that commitment, which makes it a commitment to the
 *      re-encryption under the same randomness; then publish the
 *      re-encryptions permuted, with a proof of shuffle of known values over
 *      those commitments. The next server takes the published list as input.
 *   4. Decryption: each trustee publishes its partial decryption of every
 *      ciphertext of the last list (with noise drowning), and anyone combines
 *      them into the plaintexts and tallies.
 *
 * Then the mixing is attacked: a server that changes an output, or replaces a
 * ballot with one of its own, must not get its proof of shuffle accepted.
 *
 * What the repository does not implement is left out, and so is not tested:
 * the voters' ballot proofs, the proof that each E_i is an encryption of zero
 * with short randomness (the mix-net's own instance of Pi_SMALL), and the
 * trustees' proofs of correct decryption (Pi_BND on the decryption noise).
 * Without the second, the commitments to the E_i are not tied to encryptions
 * of zero; the proof of shuffle checked here is about the commitments.
 *
 * The proof of shuffle is internal to shuffle.cpp, so this file includes it;
 * shuffle.cpp's own tests are behind MAIN, which is left undefined here. Its
 * prover and verifier run together, in run(), on the commitments and their
 * randomness in shuffle.cpp's com[] and r[].
 */

#include "shuffle.cpp"

/* The distributed BGV of src/bgv.cpp, which common.h does not declare. */
void bgv_keyshare(params::poly_q s[], size_t shares, params::poly_q & sk);
void bgv_add(bgvenc_t & c, bgvenc_t & d, bgvenc_t & e);
void bgv_distdec(params::poly_q & tj, bgvenc_t & c, params::poly_q & sj);
void bgv_comb(params::poly_p & m, bgvenc_t & c, params::poly_q t[],
		size_t shares);

/* Mix servers. */
#ifndef MIXERS
#define MIXERS 		4
#endif
/* Candidates: a vote for candidate j is X^j. */
#define NCAND 		8

/* A uniform integer in [0, n), from the operating system. */
static uint32_t uniform_below(uint32_t n) {
	uint32_t x, lim = UINT32_MAX - UINT32_MAX % n;
	do {
		if (getrandom(&x, sizeof(x), 0) != sizeof(x)) {
			fprintf(stderr, "ERROR: could not read entropy\n");
			abort();
		}
	} while (x >= lim);
	return x % n;
}

/* The vote X^j, in the coefficient domain as bgv_encrypt takes it. */
static void make_vote(params::poly_p & m, int j) {
	std::array < mpz_t, DEGREE > c;

	for (size_t i = 0; i < DEGREE; i++) {
		mpz_init_set_ui(c[i], (int) i == j);
	}
	m.mpz2poly(c);
	for (size_t i = 0; i < DEGREE; i++) {
		mpz_clear(c[i]);
	}
}

/* The candidate a plaintext votes for, or -1 if it is not X^j, j < NCAND. */
static int candidate(params::poly_p & m) {
	std::array < mpz_t, DEGREE > c;
	int j = -1, ok = 1;

	for (size_t i = 0; i < DEGREE; i++) {
		mpz_init(c[i]);
	}
	m.poly2mpz(c);
	for (size_t i = 0; i < DEGREE && ok; i++) {
		if (mpz_cmp_ui(c[i], 1) == 0 && (int) i < NCAND && j < 0) {
			j = i;
		} else if (mpz_sgn(c[i]) != 0) {
			ok = 0;
		}
	}
	for (size_t i = 0; i < DEGREE; i++) {
		mpz_clear(c[i]);
	}
	return ok ? j : -1;
}

/* A ciphertext's two components in the coefficient domain, the form the
 * commitments and the proof of shuffle take messages in. */
static vector < params::poly_q > as_message(bgvenc_t & c) {
	vector < params::poly_q > m(SIZE);

	m[0] = c.u;
	m[0].invntt_pow_invphi();
	m[1] = c.v;
	m[1].invntt_pow_invphi();
	return m;
}

/* One mix server: from the list in, compute the re-encryptions, commit to
 * them through the commitments to the encryptions of zero, and leave in out
 * the re-encryptions permuted by pi, out[i] = c_pi(i) + E_pi(i). The
 * commitments and their randomness go to shuffle.cpp's com[] and r[], the
 * messages and the permutation elements to m and sigma, ready for run().
 * Returns 0 if a commitment built homomorphically differs from a direct one. */
static int mix(bgvenc_t out[MSGS], bgvenc_t in[MSGS],
		vector < vector < params::poly_q >> &m,
		vector < vector < params::poly_q >> &_m,
		vector < params::poly_q > &sigma, bgvkey_t & pk, comkey_t & key) {
	static bgvenc_t re[MSGS];
	params::poly_p zero = 0;
	int pi[MSGS], ok = 1;

	for (int i = 0; i < MSGS; i++) {
		bgvenc_t e;
		commit_t direct;

		/* E_i, the re-encryption, and the commitment to E_i. */
		bgv_encrypt(e, pk, zero);
		bgv_add(re[i], in[i], e);
		r[i].resize(WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(com[i], as_message(e), key, r[i]);
		/* + c_i: a commitment to c_i + E_i under the same randomness. */
		com[i].c2[0] = com[i].c2[0] + in[i].u;
		com[i].c2[1] = com[i].c2[1] + in[i].v;
		m[i] = as_message(re[i]);

		bdlop_commit(direct, m[i], key, r[i]);
		ok &= util::equal(direct.c1, com[i].c1);
		ok &= util::equal(direct.c2[0], com[i].c2[0]);
		ok &= util::equal(direct.c2[1], com[i].c2[1]);
	}

	/* A uniform permutation, and sigma_i = g(pi(i)). */
	for (int i = 0; i < MSGS; i++) {
		pi[i] = i;
	}
	for (int i = MSGS - 1; i > 0; i--) {
		int j = uniform_below(i + 1), x = pi[i];
		pi[i] = pi[j];
		pi[j] = x;
	}
	for (int i = 0; i < MSGS; i++) {
		out[i] = re[pi[i]];
		_m[i] = m[pi[i]];
		index_scalar(sigma[i], pi[i]);
	}
	return ok;
}

static int cmp_int(const void *a, const void *b) {
	return *(const int *) a - *(const int *) b;
}

static void test() {
	static comkey_t key;
	static bgvkey_t pk;
	static params::poly_q sk, share[PARTIES], t[PARTIES];
	static bgvenc_t list[MIXERS + 1][MSGS];
	static params::poly_p vote[MSGS], plain[MSGS];
	vector < vector < params::poly_q >> m(MSGS), _m(MSGS);
	vector < params::poly_q > sigma(MSGS);
	int votes[MSGS], tally[MSGS], count[NCAND] = { };
	int commit_ok = 1, shuffle_ok = 1, valid = 1;

	bdlop_keygen(key);
	bgv_keygen(pk, sk);
	bgv_keyshare(share, PARTIES, sk);

	/* Voting. The votes are the test oracle, kept apart from what the mix
	 * servers and the trustees use. */
	for (int i = 0; i < MSGS; i++) {
		votes[i] = uniform_below(NCAND);
		make_vote(vote[i], votes[i]);
		bgv_encrypt(list[0][i], pk, vote[i]);
	}

	/* Mixing: server s takes list[s] and publishes list[s + 1]. */
	for (int s = 0; s < MIXERS; s++) {
		commit_ok &= mix(list[s + 1], list[s], m, _m, sigma, pk, key);
		shuffle_ok &= run(m, _m, sigma, key);
	}

	TEST_ONCE("every commitment to a re-encryption is the homomorphic one") {
		TEST_ASSERT(commit_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of shuffle verifies") {
		TEST_ASSERT(shuffle_ok, end);
	} TEST_END;

	/* Decryption: the trustees' partial decryptions, combined. */
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < PARTIES; j++) {
			bgv_distdec(t[j], list[MIXERS][i], share[j]);
		}
		bgv_comb(plain[i], list[MIXERS][i], t, PARTIES);
		tally[i] = candidate(plain[i]);
		valid &= tally[i] >= 0;
	}

	TEST_ONCE("the decrypted ballots are valid votes") {
		TEST_ASSERT(valid, end);
	} TEST_END;

	TEST_ONCE("the tally is the votes cast") {
		qsort(tally, MSGS, sizeof(int), cmp_int);
		qsort(votes, MSGS, sizeof(int), cmp_int);
		TEST_ASSERT(memcmp(tally, votes, sizeof(votes)) == 0, end);
	} TEST_END;

	TEST_ONCE("a mix server that changes an output is rejected") {
		/* Mix the first list again and add 1 to an output component: the
		 * outputs are no longer the committed re-encryptions permuted. */
		params::poly_q one = 1;
		static bgvenc_t out[MSGS];

		mix(out, list[0], m, _m, sigma, pk, key);
		_m[0][1] = _m[0][1] + one;
		TEST_ASSERT(run(m, _m, sigma, key) == 0, end);
	} TEST_END;

	TEST_ONCE("a mix server that replaces a ballot is rejected") {
		/* Publish, in place of one output, a fresh encryption of a vote of
		 * the server's choosing. */
		static bgvenc_t out[MSGS];
		bgvenc_t own;
		params::poly_p v;

		mix(out, list[0], m, _m, sigma, pk, key);
		make_vote(v, NCAND - 1);
		bgv_encrypt(own, pk, v);
		_m[0] = as_message(own);
		TEST_ASSERT(run(m, _m, sigma, key) == 0, end);
	} TEST_END;

	for (int i = 0; i < MSGS; i++) {
		int j = candidate(plain[i]);
		if (j >= 0) {
			count[j]++;
		}
	}
	printf("\n    %d voters, %d mix servers, %d trustees; tally:", MSGS,
			MIXERS, PARTIES);
	for (int j = 0; j < NCAND; j++) {
		printf(" %d", count[j]);
	}
	printf("\n");

  end:
	return;
}

int main(void) {
	setvbuf(stdout, NULL, _IONBF, 0);
	shuffle_alloc();

	printf("\n** End-to-end test of the mix-net:\n\n");
	test();

	shuffle_free();
	return test_failures() != 0;
}
