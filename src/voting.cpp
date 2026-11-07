/**
 * @file
 *
 * The mix-net end to end, with MSGS voters, MIXERS mix servers and PARTIES
 * trustees, as the paper puts the pieces together:
 *
 *   1. Key generation: a BGV key pair, its secret key additively shared among
 *      the PARTIES trustees (bgv_keyshare, a dealer, as the repository does),
 *      and each share s_j committed to and published as [[s_j]].
 *   2. Voting: each voter encrypts its vote, X^j for one of NCAND candidates,
 *      and proves the ballot well formed (src/ballot_proof.c, on LaZer): an
 *      encryption with short randomness of X^j or of 0, bound to the election
 *      and the voter. The board checks every proof.
 *   3. Mixing, by each server in turn: re-encrypt every ciphertext c_i as
 *      c_i + E_i with E_i a fresh encryption of zero, publish a commitment to
 *      E_i and prove, with one amortized Pi_SMALL over all of them, that each
 *      opens to an encryption of zero with ternary randomness (pismall.h,
 *      pismall_mix_*). The verifier adds each input c_i into the commitment to
 *      E_i itself, which makes it a commitment to the re-encryption; the
 *      server publishes the re-encryptions permuted, with a proof of shuffle
 *      of known values over those commitments. The next server takes the
 *      published list as input.
 *   4. Decryption: each trustee publishes its partial decryption
 *      t_ij = s_j u_i + p E_ij of every ciphertext of the last list, with noise
 *      drowning, a commitment to each E_ij, a linear proof per ciphertext that
 *      the openings of [[s_j]] and [[E_ij]] satisfy that equation, and one
 *      amortized Pi_BND that every E_ij is bounded (pibnd.h, pibnd_dec_*):
 *      Pi_DDec of the paper. Anyone checks the proofs, combines the shares
 *      into the plaintexts and tallies.
 *
 * Then the ballots, the mixing and the decryption are attacked: a ballot proof
 * moved to another voter or kept for a changed ciphertext, a ballot for two
 * candidates and one for a candidate past the last, must be refused; a server
 * that changes an output, replaces a ballot with one of its own, or commits to
 * something other than an encryption of zero must not get its proofs accepted;
 * and a trustee whose partial decryption is wrong must not get its proof of
 * decryption accepted.
 *
 * The proof of shuffle is internal to shuffle.cpp, so this file includes it;
 * shuffle.cpp's own tests are behind MAIN, which is left undefined here. Its
 * prover and verifier run together, in run(), on the commitments and their
 * randomness in shuffle.cpp's com[] and r[].
 */

#include "shuffle.cpp"
#include "ballot_proof.h"

static_assert(BALLOT_DEG == DEGREE, "the ballot proof is for this ring");
static_assert((zq::u128) BALLOT_Q == zq::MODULUS, "the ballot proof is for this q");

/* The distributed BGV of src/bgv.cpp, which common.h does not declare. */
void bgv_keyshare(params::poly_q s[], size_t shares, params::poly_q & sk);
void bgv_add(bgvenc_t & c, bgvenc_t & d, bgvenc_t & e);
void bgv_distdec(params::poly_q & tj, bgvenc_t & c, params::poly_q & sj);
void bgv_distdec_noise(params::poly_q & tj, params::poly_q & Ej,
		bgvenc_t & c, params::poly_q & sj);
void bgv_comb(params::poly_p & m, bgvenc_t & c, params::poly_q t[],
		size_t shares);

/* Mix servers. The decryption budget q is sized against was set for the noise
 * of 4 servers' re-encryptions, so fewer are fine and more need it
 * recomputed. */
#ifndef MIXERS
#define MIXERS 		4
#endif
#if MIXERS < 1 || MIXERS > 4
#error "lattice-verifiable-mixnet: the decryption budget allows 1 to 4 mix servers (MIXERS)"
#endif
/* Candidates: a vote for candidate j is X^j. */
#ifndef NCAND
#define NCAND 	8
#endif

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

/* The coefficients of a, centred mod q, as the ballot proof takes them; ntt
 * says whether a is in the NTT domain. q has 88 bits, so a coefficient is read
 * from the two low limbs of its absolute value. */
static void to_i128(__int128 out[DEGREE], const params::poly_q & a, bool ntt) {
	params::poly_q b = a;
	std::array < mpz_t, DEGREE > c;
	mpz_t half, abs;

	if (ntt) {
		b.invntt_pow_invphi();
	}
	for (size_t i = 0; i < DEGREE; i++) {
		mpz_init2(c[i], params::poly_q::bits_in_moduli_product() << 2);
	}
	mpz_inits(half, abs, nullptr);
	mpz_fdiv_q_2exp(half, params::poly_q::moduli_product(), 1);
	b.poly2mpz(c);
	for (size_t i = 0; i < DEGREE; i++) {
		util::center(c[i], c[i], params::poly_q::moduli_product(), half);
		mpz_abs(abs, c[i]);
		unsigned __int128 v = (unsigned __int128) mpz_getlimbn(abs, 0)
				| (unsigned __int128) mpz_getlimbn(abs, 1) << 64;
		out[i] = mpz_sgn(c[i]) < 0 ? -(__int128) v : (__int128) v;
		mpz_clear(c[i]);
	}
	mpz_clears(half, abs, nullptr);
}

/* The same for a short element, as int64_t. */
static void to_i64(int64_t out[DEGREE], const params::poly_q & a, bool ntt) {
	static __int128 t[DEGREE];

	to_i128(t, a, ntt);
	for (size_t i = 0; i < DEGREE; i++) {
		out[i] = (int64_t) t[i];
	}
}

/* The context a ballot proof is bound to: the election and the voter. */
#define CTX_BYTES 	(16 + 16 + 4)
static void ballot_ctx(uint8_t ctx[CTX_BYTES], const uint8_t eid[16], int voter) {
	memcpy(ctx, "lvm_voting/vote/", 16);
	memcpy(ctx + 16, eid, 16);
	for (int b = 0; b < 4; b++) {
		ctx[32 + b] = (uint8_t) ((uint32_t) voter >> (8 * b));
	}
}

/* The plaintext X^0 + X^1, in the coefficient domain: binary, but two votes. */
static void make_two_votes(params::poly_p & m) {
	std::array < mpz_t, DEGREE > c;

	for (size_t i = 0; i < DEGREE; i++) {
		mpz_init_set_ui(c[i], i < 2);
	}
	m.mpz2poly(c);
	for (size_t i = 0; i < DEGREE; i++) {
		mpz_clear(c[i]);
	}
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

/* --- The trustees' proof of correct decryption ----------------------------
 *
 * Trustee j has its key share s_j committed as S_j = [[s_j]] at key
 * generation. For the i-th ciphertext (u_i, v_i) of the last list it publishes
 * its partial decryption t_ij = s_j u_i + p E_ij, a commitment Y_ij = [[E_ij]]
 * to the drowning noise, and the proof below that the openings of S_j and
 * Y_ij satisfy u_i s + p E = t_ij. Its proof that every E_ij is short is one
 * amortized Pi_BND over the Y_ij (pibnd_dec_prove). Both messages sit in the
 * first slot of their commitments, so only c1 and c2[0] are involved.
 *
 * It is the linear proof of the proof of shuffle (lin_prover) with two
 * openings instead of three and this relation, under the same SIGMA_C, the
 * same rejection sampling over all the openings at once, and LIN_REPS
 * repetitions against challenges from one hash, for the reason given there:
 * nothing makes a challenge difference invertible in a fully split ring.
 */
static void dlin_hash(uint8_t h[BLAKE3_OUT_LEN], comkey_t & key, commit_t & X,
		commit_t & Y, params::poly_q & u, params::poly_q & t,
		params::poly_q w[LIN_REPS], params::poly_q _w[LIN_REPS],
		params::poly_q v[LIN_REPS], uint32_t trustee, uint32_t index) {
	static const char label[] = "lvm_voting/ddec/";
	blake3_hasher hasher;

	blake3_hasher_init(&hasher);
	blake3_hasher_update(&hasher, (const uint8_t *)label, sizeof(label) - 1);
	blake3_hasher_update(&hasher, (const uint8_t *)&trustee, sizeof(trustee));
	blake3_hasher_update(&hasher, (const uint8_t *)&index, sizeof(index));
	for (int k = 0; k < WIDTH - HEIGHT; k++) {
		blake3_hasher_update(&hasher, (const uint8_t *)key.A1[0][k].data(),
				16 * DEGREE);
	}
	for (int k = 0; k < WIDTH; k++) {
		blake3_hasher_update(&hasher, (const uint8_t *)key.A2[0][k].data(),
				16 * DEGREE);
	}
	blake3_hasher_update(&hasher, (const uint8_t *)X.c1.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)X.c2[0].data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)Y.c1.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)Y.c2[0].data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)u.data(), 16 * DEGREE);
	blake3_hasher_update(&hasher, (const uint8_t *)t.data(), 16 * DEGREE);
	for (int j = 0; j < LIN_REPS; j++) {
		blake3_hasher_update(&hasher, (const uint8_t *)w[j].data(), 16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)_w[j].data(), 16 * DEGREE);
		blake3_hasher_update(&hasher, (const uint8_t *)v[j].data(), 16 * DEGREE);
	}
	blake3_hasher_finalize(&hasher, h, BLAKE3_OUT_LEN);
}

/* A1 z, the first row of a commitment equation, for a response z. */
static params::poly_q dlin_row0(comkey_t & key, params::poly_q z[WIDTH]) {
	params::poly_q a = z[0];

	for (int k = 0; k < WIDTH - HEIGHT; k++) {
		a = a + key.A1[0][k] * z[k + HEIGHT];
	}
	return a;
}

/* A2[0] z, the second row less the message. */
static params::poly_q dlin_row1(comkey_t & key, params::poly_q z[WIDTH]) {
	params::poly_q a = 0;

	for (int k = 0; k < WIDTH; k++) {
		a = a + key.A2[0][k] * z[k];
	}
	return a;
}

/* Prove that the openings of X = [[s]] (randomness rs) and Y = [[E]]
 * (randomness re) satisfy u s + p E = t. The responses go to z and _z, the
 * hash the challenges come from to h. Returns 0 if rejection sampling did not
 * succeed within LIN_TRIES, in which case nothing may be published. */
static int dlin_prove(params::poly_q z[LIN_REPS][WIDTH],
		params::poly_q _z[LIN_REPS][WIDTH], uint8_t h[BLAKE3_OUT_LEN],
		commit_t & X, commit_t & Y, params::poly_q & u, params::poly_q & t,
		comkey_t & key, vector < params::poly_q > &rs,
		vector < params::poly_q > &re, uint32_t trustee, uint32_t index) {
	params::poly_q beta[LIN_REPS], w[LIN_REPS], _w[LIN_REPS], v[LIN_REPS];
	params::poly_q tmp[WIDTH], _tmp[WIDTH], p = PRIMEP;
	__int128 coeffs[params::poly_q::degree];
	long double dot, norm;
	int rej, tries = 0;

	p.ntt_pow_phi();
	do {
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < WIDTH; i++) {
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					coeffs[k] = sample_z(0.0, SIGMA_C);
				}
				util::set_signed(z[j][i], coeffs);
				z[j][i].ntt_pow_phi();
				for (size_t k = 0; k < params::poly_q::degree; k++) {
					coeffs[k] = sample_z(0.0, SIGMA_C);
				}
				util::set_signed(_z[j][i], coeffs);
				_z[j][i].ntt_pow_phi();
			}
			w[j] = dlin_row0(key, z[j]);
			_w[j] = dlin_row0(key, _z[j]);
			v[j] = u * dlin_row1(key, z[j]) + p * dlin_row1(key, _z[j]);
		}

		dlin_hash(h, key, X, Y, u, t, w, _w, v, trustee, index);
		lin_chal(beta, h);

		dot = 0;
		norm = 0;
		for (int j = 0; j < LIN_REPS; j++) {
			for (int i = 0; i < WIDTH; i++) {
				tmp[i] = beta[j] * rs[i];
				_tmp[i] = beta[j] * re[i];
				z[j][i] = z[j][i] + tmp[i];
				_z[j][i] = _z[j][i] + _tmp[i];
			}
			rej_accum(z[j], tmp, dot, norm);
			rej_accum(_z[j], _tmp, dot, norm);
		}
		rej = rej_decide(dot, norm, SIGMA_C * SIGMA_C);
	} while (rej && ++tries < LIN_TRIES);

	return !rej;
}

static int dlin_verify(params::poly_q z[LIN_REPS][WIDTH],
		params::poly_q _z[LIN_REPS][WIDTH], uint8_t h[BLAKE3_OUT_LEN],
		commit_t & X, commit_t & Y, params::poly_q & u, params::poly_q & t,
		comkey_t & key, uint32_t trustee, uint32_t index) {
	params::poly_q beta[LIN_REPS], w[LIN_REPS], _w[LIN_REPS], v[LIN_REPS];
	params::poly_q a, p = PRIMEP;
	uint8_t h2[BLAKE3_OUT_LEN];
	int result = 1;

	p.ntt_pow_phi();
	lin_chal(beta, h);
	for (int j = 0; j < LIN_REPS; j++) {
		for (int i = 0; i < WIDTH; i++) {
			a = z[j][i];
			a.invntt_pow_invphi();
			result &= bdlop_test_norm(a, 4 * SIGMA_C * SIGMA_C);
			a = _z[j][i];
			a.invntt_pow_invphi();
			result &= bdlop_test_norm(a, 4 * SIGMA_C * SIGMA_C);
		}
		/* The first messages, as the checks say they are. */
		w[j] = dlin_row0(key, z[j]) - beta[j] * X.c1;
		_w[j] = dlin_row0(key, _z[j]) - beta[j] * Y.c1;
		a = u * X.c2[0] + p * Y.c2[0] - t;
		v[j] = u * dlin_row1(key, z[j]) + p * dlin_row1(key, _z[j])
				- beta[j] * a;
	}
	dlin_hash(h2, key, X, Y, u, t, w, _w, v, trustee, index);
	result &= (memcmp(h, h2, BLAKE3_OUT_LEN) == 0);

	return result;
}

/* Commit to a single message m, in the coefficient domain, under fresh
 * randomness. */
static void commit_one(commit_t & c, vector < params::poly_q > &rc,
		const params::poly_q & m, comkey_t & key) {
	vector < params::poly_q > msg(1, m);

	rc.resize(WIDTH);
	bdlop_sample_rand(rc);
	bdlop_commit(c, msg, key, rc);
}

/* What a mix server publishes besides its output list: the commitments to the
 * encryptions of zero E_i it added, and the proof that each is one. The
 * randomness of the E_i is its witness. */
static commit_t ecom[MSGS];
static params::poly_q erho[MSGS], ee1[MSGS], ee2[MSGS];

/* One mix server: from the list in, compute the re-encryptions, commit to the
 * encryptions of zero E_i into ecom[], and leave in out the re-encryptions
 * permuted by pi, out[i] = c_pi(i) + E_pi(i). The randomness of the
 * commitments goes to shuffle.cpp's r[], the messages and the permutation
 * elements to m and sigma, ready for run(); com[] is left for the verifier to
 * build (verifier_commitments). Returns 0 if a commitment built
 * homomorphically differs from a direct one. */
static int mix(bgvenc_t out[MSGS], bgvenc_t in[MSGS],
		vector < vector < params::poly_q >> &m,
		vector < vector < params::poly_q >> &_m,
		vector < params::poly_q > &sigma, bgvkey_t & pk, comkey_t & key) {
	static bgvenc_t re[MSGS];
	params::poly_p zero = 0;
	int pi[MSGS], ok = 1;

	for (int i = 0; i < MSGS; i++) {
		bgvenc_t e;
		commit_t direct, sum;

		/* E_i, the re-encryption, and the commitment to E_i. */
		bgv_encrypt_rand(e, pk, zero, erho[i], ee1[i], ee2[i]);
		bgv_add(re[i], in[i], e);
		r[i].resize(WIDTH);
		bdlop_sample_rand(r[i]);
		bdlop_commit(ecom[i], as_message(e), key, r[i]);
		m[i] = as_message(re[i]);

		/* + c_i: a commitment to c_i + E_i under the same randomness. */
		sum = ecom[i];
		sum.c2[0] = sum.c2[0] + in[i].u;
		sum.c2[1] = sum.c2[1] + in[i].v;
		bdlop_commit(direct, m[i], key, r[i]);
		ok &= util::equal(direct.c1, sum.c1);
		ok &= util::equal(direct.c2[0], sum.c2[0]);
		ok &= util::equal(direct.c2[1], sum.c2[1]);
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

/* The verifier's side of a mix: from the input list and the published
 * commitments to the E_i, the commitments to the re-encryptions c_i + E_i that
 * the proof of shuffle is about, into shuffle.cpp's com[]. Nothing in it comes
 * from the mix server but ecom[], which the proof of re-encryption covers. */
static void verifier_commitments(bgvenc_t in[MSGS]) {
	for (int i = 0; i < MSGS; i++) {
		com[i] = ecom[i];
		com[i].c2[0] = com[i].c2[0] + in[i].u;
		com[i].c2[1] = com[i].c2[1] + in[i].v;
	}
}

/* One mix server's publication, as bytes: its output list (u and v of each
 * ciphertext, uniform), the commitments to the E_i, the proof of
 * re-encryption, and the proof of shuffle (shuffle_prove_bytes). sz[] gets
 * the bytes of each of the four. */
static double t_remix, t_rr_prove, t_rr_verify;

static int mix_publish(serial::bits & out, size_t sz[4], bgvenc_t in[MSGS],
		vector < vector < params::poly_q >> &m,
		vector < vector < params::poly_q >> &_m,
		vector < params::poly_q > &sigma, bgvkey_t & pk, comkey_t & key,
		int &commit_ok) {
	static bgvenc_t *list_out = new bgvenc_t[MSGS];
	pismall_mix_t *pr;
	size_t at = out.bytes();
	double t0;
	int ok;

	t0 = shuffle_now();
	commit_ok &= mix(list_out, in, m, _m, sigma, pk, key);
	t_remix += shuffle_now() - t0;
	for (int i = 0; i < MSGS; i++) {
		serial::put_uniform(out, list_out[i].u);
		serial::put_uniform(out, list_out[i].v);
	}
	sz[0] += out.bytes() - at;
	at = out.bytes();
	for (int i = 0; i < MSGS; i++) {
		serial::put_commit(out, ecom[i]);
	}
	sz[1] += out.bytes() - at;
	at = out.bytes();
	t0 = shuffle_now();
	pr = pismall_mix_prove(key, pk, ecom, r, erho, ee1, ee2, MSGS);
	ok = pismall_mix_write(pr, out);
	pismall_mix_free(pr);
	t_rr_prove += shuffle_now() - t0;
	sz[2] += out.bytes() - at;
	at = out.bytes();
	/* The proof of shuffle is about the commitments to the c_i + E_i, which
	 * the server forms as anyone does. */
	verifier_commitments(in);
	ok &= shuffle_prove_bytes(out, m, _m, sigma, key);
	sz[3] += out.bytes() - at;
	return ok;
}

/* Anyone: a mix server's bytes, against the list in it took. The list it
 * published, as read, goes to out; returns whether every proof verifies and
 * the bytes are exactly an encoding a server writes. */
static int mix_check(serial::bits & pub, bgvenc_t out[MSGS], bgvenc_t in[MSGS],
		bgvkey_t & pk, comkey_t & key, int &rr_ok) {
	static commit_t vecom[MSGS], vcom[MSGS];
	static vector < vector < params::poly_q >> vm(MSGS);
	pismall_mix_t *pr;
	double t0;
	int rr, ok;

	for (int i = 0; i < MSGS; i++) {
		serial::get_uniform(pub, out[i].u);
		serial::get_uniform(pub, out[i].v);
	}
	for (int i = 0; i < MSGS; i++) {
		serial::get_commit(pub, vecom[i], SIZE);
	}
	t0 = shuffle_now();
	pr = pismall_mix_read(pub);
	rr = !pub.bad && pismall_mix_verify(pr, key, pk, vecom, MSGS);
	pismall_mix_free(pr);
	t_rr_verify += shuffle_now() - t0;
	rr_ok &= rr;
	for (int i = 0; i < MSGS; i++) {
		vcom[i] = vecom[i];
		vcom[i].c2[0] = vcom[i].c2[0] + in[i].u;
		vcom[i].c2[1] = vcom[i].c2[1] + in[i].v;
		vm[i] = as_message(out[i]);
	}
	ok = shuffle_verify_bytes(pub, vcom, vm, key);
	return rr && ok && pub.finish();
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
	int commit_ok = 1, shuffle_ok = 1, valid = 1, cast_ok = 1, board_ok = 1;
	int rr_ok = 1, dec_ok = 1, dlin_ok = 1, dbnd_ok = 1, read_ok = 1;
	size_t setup_bytes = 0, ballot_bytes = 0, mix_sz[4] = { }, mix_bytes = 0;
	/* The trustees' commitments to their key shares, and what each publishes
	 * for the decryption: shares T, commitments Y to the noise E, and their
	 * randomness ry. One trustee's E, Y and ry are live at a time. */
	static commit_t scom[PARTIES], Y[MSGS];
	static vector < params::poly_q > srand[PARTIES], ry[MSGS];
	static params::poly_q T[PARTIES][MSGS], E[MSGS];
	/* What the trustees published, as read: the shares and the noise
	 * commitments, which is what the shares are combined from. */
	static params::poly_q (*VT)[MSGS] = new params::poly_q[PARTIES][MSGS];
	static commit_t *vY = new commit_t[MSGS];
	static params::poly_q dz[LIN_REPS][WIDTH], d_z[LIN_REPS][WIDTH];
	uint8_t dh[BLAKE3_OUT_LEN];
	size_t share_bytes = 0, dproof_bytes = 0;
	/* The voters' ballot proofs, and the ring elements they take. */
	static std::vector < uint8_t > proof[MSGS];
	static __int128 a128[DEGREE], b128[DEGREE], u128[DEGREE], v128[DEGREE];
	static int64_t r64[DEGREE], e164[DEGREE], e264[DEGREE], m64[DEGREE];
	params::poly_q rr, re1, re2;
	bgvenc_t two;
	params::poly_p v2;
	uint8_t eid[16], ctx[CTX_BYTES];
	size_t len, proof_bytes = 0;
	/* Wall-clock times of the phases, reported at the end; the attack tests
	 * below run the shuffle again and are not counted. */
	double t0, t_key, t_vote, t_board = 0, t_prove, t_verify, t_shared,
			t_dprove = 0, t_dverify = 0, t_comb;

	t0 = shuffle_now();
	bdlop_keygen(key);
	bgv_keygen(pk, sk);
	bgv_keyshare(share, PARTIES, sk);
	for (int j = 0; j < PARTIES; j++) {
		params::poly_q sj = share[j];

		sj.invntt_pow_invphi();
		commit_one(scom[j], srand[j], sj, key);
	}
	t_key = shuffle_now() - t0;
	{
		/* The trustees publish their key-share commitments; everyone uses
		 * them as read. */
		serial::bits b;
		for (int j = 0; j < PARTIES; j++) {
			serial::put_commit(b, scom[j]);
		}
		setup_bytes = b.bytes();
		serial::bits rd(std::move(b.buf));
		for (int j = 0; j < PARTIES; j++) {
			serial::get_commit(rd, scom[j], 1);
		}
		read_ok &= rd.finish();
	}
	ballot_setup();
	to_i128(a128, pk.a, true);
	to_i128(b128, pk.b, true);
	if (getrandom(eid, sizeof(eid), 0) != sizeof(eid)) {
		fprintf(stderr, "ERROR: could not read entropy\n");
		abort();
	}

	/* Voting. The votes are the test oracle, kept apart from what the mix
	 * servers and the trustees use. Each voter proves its ballot is X^j for
	 * j < NCAND, or 0, under short randomness, bound to this election and to
	 * the voter. */
	t0 = shuffle_now();
	for (int i = 0; i < MSGS; i++) {
		votes[i] = uniform_below(NCAND);
		make_vote(vote[i], votes[i]);
		bgv_encrypt_rand(list[0][i], pk, vote[i], rr, re1, re2);
		to_i128(u128, list[0][i].u, true);
		to_i128(v128, list[0][i].v, true);
		to_i64(r64, rr, false);
		to_i64(e164, re1, false);
		to_i64(e264, re2, false);
		memset(m64, 0, sizeof(m64));
		m64[votes[i]] = 1;
		ballot_ctx(ctx, eid, i);
		proof[i].resize(ballot_proof_len());
		cast_ok &= ballot_prove(proof[i].data(), &len, u128, v128, a128, b128,
				r64, e164, e264, m64, NCAND, ctx, sizeof(ctx));
		proof[i].resize(len);
		proof_bytes += len;
	}
	t_vote = shuffle_now() - t0;

	/* Each ballot's ciphertext goes to the board as bytes, read back in place;
	 * the proof is bytes already. */
	for (int i = 0; i < MSGS; i++) {
		serial::bits b;
		serial::put_uniform(b, list[0][i].u);
		serial::put_uniform(b, list[0][i].v);
		ballot_bytes += b.bytes();
		serial::bits rd(std::move(b.buf));
		serial::get_uniform(rd, list[0][i].u);
		serial::get_uniform(rd, list[0][i].v);
		read_ok &= rd.finish();
	}

	TEST_ONCE("the key-share commitments and the ballots read back from their bytes") {
		TEST_ASSERT(read_ok, end);
	} TEST_END;

	TEST_ONCE("every voter proves its ballot") {
		TEST_ASSERT(cast_ok, end);
	} TEST_END;

	TEST_ONCE("the board accepts every voter's ballot proof") {
		t0 = shuffle_now();
		for (int i = 0; i < MSGS; i++) {
			to_i128(u128, list[0][i].u, true);
			to_i128(v128, list[0][i].v, true);
			ballot_ctx(ctx, eid, i);
			board_ok &= ballot_verify(proof[i].data(), proof[i].size(), u128,
					v128, a128, b128, NCAND, ctx, sizeof(ctx));
		}
		t_board = shuffle_now() - t0;
		TEST_ASSERT(board_ok, end);
	} TEST_END;

	TEST_ONCE("a ballot proof does not verify for another voter") {
		to_i128(u128, list[0][0].u, true);
		to_i128(v128, list[0][0].v, true);
		ballot_ctx(ctx, eid, 1);
		TEST_ASSERT(ballot_verify(proof[0].data(), proof[0].size(), u128, v128,
				a128, b128, NCAND, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	TEST_ONCE("a ballot changed after its proof is rejected") {
		/* v + 2: the same randomness, now an encryption of m + 2. */
		to_i128(u128, list[0][0].u, true);
		to_i128(v128, list[0][0].v, true);
		v128[0] += 2;
		ballot_ctx(ctx, eid, 0);
		TEST_ASSERT(ballot_verify(proof[0].data(), proof[0].size(), u128, v128,
				a128, b128, NCAND, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	TEST_ONCE("a ballot for two candidates cannot be proven") {
		std::vector < uint8_t > pf(ballot_proof_len());

		make_two_votes(v2);
		bgv_encrypt_rand(two, pk, v2, rr, re1, re2);
		to_i128(u128, two.u, true);
		to_i128(v128, two.v, true);
		to_i64(r64, rr, false);
		to_i64(e164, re1, false);
		to_i64(e264, re2, false);
		memset(m64, 0, sizeof(m64));
		m64[0] = m64[1] = 1;
		ballot_ctx(ctx, eid, 0);
		TEST_ASSERT(ballot_prove(pf.data(), &len, u128, v128, a128, b128, r64,
				e164, e264, m64, NCAND, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	TEST_ONCE("a ballot for a candidate past the last is rejected") {
		/* X^NCAND, a vote for no candidate of this election, proven as a
		 * ballot of an election with one candidate more: the proof is a valid
		 * one, of that other statement, and the board must refuse it. */
		std::vector < uint8_t > pf(ballot_proof_len());
		params::poly_p past;
		bgvenc_t c;

		make_vote(past, NCAND);
		bgv_encrypt_rand(c, pk, past, rr, re1, re2);
		to_i128(u128, c.u, true);
		to_i128(v128, c.v, true);
		to_i64(r64, rr, false);
		to_i64(e164, re1, false);
		to_i64(e264, re2, false);
		memset(m64, 0, sizeof(m64));
		m64[NCAND] = 1;
		ballot_ctx(ctx, eid, 0);
		TEST_ASSERT(ballot_prove(pf.data(), &len, u128, v128, a128, b128, r64,
				e164, e264, m64, NCAND, ctx, sizeof(ctx)) == 0, end);
		TEST_ASSERT(ballot_prove(pf.data(), &len, u128, v128, a128, b128, r64,
				e164, e264, m64, NCAND + 1, ctx, sizeof(ctx)) == 1, end);
		pf.resize(len);
		TEST_ASSERT(ballot_verify(pf.data(), pf.size(), u128, v128, a128, b128,
				NCAND + 1, ctx, sizeof(ctx)) == 1, end);
		TEST_ASSERT(ballot_verify(pf.data(), pf.size(), u128, v128, a128, b128,
				NCAND, ctx, sizeof(ctx)) == 0, end);
	} TEST_END;

	/* Mixing: server s takes list[s] and publishes list[s + 1]. */
	for (int srv = 0; srv < MIXERS; srv++) {
		serial::bits pub;

		shuffle_ok &= mix_publish(pub, mix_sz, list[srv], m, _m, sigma, pk, key,
				commit_ok);
		mix_bytes += pub.bytes();
		serial::bits rd(std::move(pub.buf));
		shuffle_ok &= mix_check(rd, list[srv + 1], list[srv], pk, key, rr_ok);
	}
	t_prove = shuffle_t_prove;
	t_verify = shuffle_t_verify;
	t_shared = shuffle_t_shared;

	TEST_ONCE("every commitment to a re-encryption is the homomorphic one") {
		TEST_ASSERT(commit_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of re-encryption verifies") {
		TEST_ASSERT(rr_ok, end);
	} TEST_END;

	TEST_ONCE("every mix server's proof of shuffle verifies") {
		TEST_ASSERT(shuffle_ok, end);
	} TEST_END;

	/* Decryption. Each trustee in turn publishes its partial decryption of
	 * every ciphertext of the last list, a commitment to each drowning noise
	 * and a linear proof per ciphertext, then one Pi_BND over all of its noise.
	 * A linear proof is checked as soon as it is produced, as the proof of
	 * shuffle does with its own, so only one is ever live. */
	for (int j = 0; j < PARTIES; j++) {
		serial::bits pub;
		pibnd_dec_t *bp;
		size_t at;

		/* Trustee j: its shares and, for each, the commitment to the noise
		 * and the linear proof; then Pi_BND over all of its noise. */
		t0 = shuffle_now();
		for (int i = 0; i < MSGS; i++) {
			bgvenc_t & c = list[MIXERS][i];

			bgv_distdec_noise(T[j][i], E[i], c, share[j]);
			commit_one(Y[i], ry[i], E[i], key);
			dec_ok &= dlin_prove(dz, d_z, dh, scom[j], Y[i], c.u, T[j][i], key,
					srand[j], ry[i], j, i);
			at = pub.bytes();
			serial::put_uniform(pub, T[j][i]);
			share_bytes += pub.bytes() - at;
			serial::put_commit(pub, Y[i]);
			serial::put_bytes(pub, dh, BLAKE3_OUT_LEN);
			for (int k = 0; k < LIN_REPS; k++) {
				for (int l = 0; l < WIDTH; l++) {
					serial::put_gauss_ntt(pub, dz[k][l], SIGMA_C);
					serial::put_gauss_ntt(pub, d_z[k][l], SIGMA_C);
				}
			}
		}
		bp = pibnd_dec_prove(key, Y, ry, E, MSGS);
		dec_ok &= pibnd_dec_write(bp, pub);
		pibnd_dec_free(bp);
		t_dprove += shuffle_now() - t0;
		dproof_bytes += pub.bytes();

		/* Anyone: the same, read from trustee j's bytes. */
		t0 = shuffle_now();
		serial::bits rd(std::move(pub.buf));
		for (int i = 0; i < MSGS; i++) {
			serial::get_uniform(rd, VT[j][i]);
			serial::get_commit(rd, vY[i], 1);
			serial::get_bytes(rd, dh, BLAKE3_OUT_LEN);
			for (int k = 0; k < LIN_REPS; k++) {
				for (int l = 0; l < WIDTH; l++) {
					serial::get_gauss_ntt(rd, dz[k][l], SIGMA_C);
					serial::get_gauss_ntt(rd, d_z[k][l], SIGMA_C);
				}
			}
			dlin_ok &= !rd.bad && dlin_verify(dz, d_z, dh, scom[j], vY[i],
					list[MIXERS][i].u, VT[j][i], key, j, i);
		}
		bp = pibnd_dec_read(rd);
		dbnd_ok &= !rd.bad && pibnd_dec_verify(bp, key, vY, MSGS) && rd.finish();
		pibnd_dec_free(bp);
		t_dverify += shuffle_now() - t0;
	}
	dproof_bytes -= share_bytes;

	/* Anyone: combine the shares, once every proof has been checked. */
	t0 = shuffle_now();
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < PARTIES; j++) {
			t[j] = VT[j][i];
		}
		bgv_comb(plain[i], list[MIXERS][i], t, PARTIES);
		tally[i] = candidate(plain[i]);
		valid &= tally[i] >= 0;
	}
	t_comb = shuffle_now() - t0;

	TEST_ONCE("every trustee proves each of its partial decryptions") {
		TEST_ASSERT(dec_ok, end);
	} TEST_END;

	TEST_ONCE("every trustee's linear proofs of decryption verify") {
		TEST_ASSERT(dlin_ok, end);
	} TEST_END;

	TEST_ONCE("every trustee's proof that its noise is bounded verifies") {
		TEST_ASSERT(dbnd_ok, end);
	} TEST_END;

	TEST_ONCE("the decrypted ballots are valid votes") {
		TEST_ASSERT(valid, end);
	} TEST_END;

	TEST_ONCE("the tally is the votes cast") {
		qsort(tally, MSGS, sizeof(int), cmp_int);
		qsort(votes, MSGS, sizeof(int), cmp_int);
		TEST_ASSERT(memcmp(tally, votes, sizeof(votes)) == 0, end);
	} TEST_END;

	{
		/* An honest publication by the first server, then altered. Its time
		 * is not counted. */
		double keep[5] = { t_remix, t_rr_prove, t_rr_verify, shuffle_t_prove,
			shuffle_t_verify };
		serial::bits pub;
		static bgvenc_t *next = new bgvenc_t[MSGS];
		size_t sz[4] = { };
		const size_t elem = params::poly_q::degree * 88 / 8;
		int junk = 1;

		mix_publish(pub, sz, list[0], m, _m, sigma, pk, key, junk);
		std::vector < uint8_t > honest = pub.buf;

		TEST_ONCE("a mix server's publication reads back and verifies") {
			serial::bits rd{std::vector < uint8_t > (honest)};
			TEST_ASSERT(mix_check(rd, next, list[0], pk, key, junk) == 1, end);
		} TEST_END;

		TEST_ONCE("a mix server that changes an output is rejected") {
			/* The low bit of the first coefficient of output 0's v. */
			std::vector < uint8_t > bad = honest;
			bad[elem + 10] ^= 0x01;
			serial::bits rd(std::move(bad));
			TEST_ASSERT(mix_check(rd, next, list[0], pk, key, junk) == 0, end);
		} TEST_END;

		TEST_ONCE("a mix server that replaces a ballot is rejected") {
			/* In place of output 0, a fresh encryption of a vote of the
			 * server's choosing. */
			std::vector < uint8_t > bad = honest;
			bgvenc_t own;
			params::poly_p v;
			serial::bits ob;

			make_vote(v, NCAND - 1);
			bgv_encrypt(own, pk, v);
			serial::put_uniform(ob, own.u);
			serial::put_uniform(ob, own.v);
			memcpy(bad.data(), ob.buf.data(), 2 * elem);
			serial::bits rd(std::move(bad));
			TEST_ASSERT(mix_check(rd, next, list[0], pk, key, junk) == 0, end);
		} TEST_END;

		TEST_ONCE("a mix server's publication with a byte appended is refused") {
			std::vector < uint8_t > bad = honest;
			bad.push_back(0);
			serial::bits rd(std::move(bad));
			TEST_ASSERT(mix_check(rd, next, list[0], pk, key, junk) == 0, end);
		} TEST_END;
		t_remix = keep[0];
		t_rr_prove = keep[1];
		t_rr_verify = keep[2];
		shuffle_t_prove = keep[3];
		shuffle_t_verify = keep[4];
	}

	TEST_ONCE("a mix server that commits to other than a zero is rejected") {
		/* The attack the proof of re-encryption is there for: commit, in
		 * place of E_0, to own - c_0 for an encryption own of a vote of the
		 * server's choosing. The verifier's commitment to c_0 + E_0 is then a
		 * commitment to own, and the proof of shuffle goes through with own
		 * among the outputs; only the proof that E_0 encrypts zero can fail. */
		static bgvenc_t out[MSGS];
		vector < params::poly_q > msg;
		bgvenc_t own;
		params::poly_p v;
		pismall_mix_t *pr;

		mix(out, list[0], m, _m, sigma, pk, key);
		make_vote(v, NCAND - 1);
		bgv_encrypt(own, pk, v);
		msg = as_message(own);
		msg[0] = msg[0] - as_message(list[0][0])[0];
		msg[1] = msg[1] - as_message(list[0][0])[1];
		bdlop_commit(ecom[0], msg, key, r[0]);
		pr = pismall_mix_prove(key, pk, ecom, r, erho, ee1, ee2, MSGS);
		TEST_ASSERT(pismall_mix_verify(pr, key, pk, ecom, MSGS) == 0, end);
		pismall_mix_free(pr);
	} TEST_END;

	TEST_ONCE("a trustee whose partial decryption is wrong is rejected") {
		/* t + 1 for the last trustee's first share, with the proof made for
		 * it from the true witness. */
		params::poly_q one = 1, bad;

		one.ntt_pow_phi();
		bad = T[PARTIES - 1][0] + one;
		dlin_prove(dz, d_z, dh, scom[PARTIES - 1], Y[0], list[MIXERS][0].u,
				bad, key, srand[PARTIES - 1], ry[0], PARTIES - 1, 0);
		TEST_ASSERT(dlin_verify(dz, d_z, dh, scom[PARTIES - 1], Y[0],
				list[MIXERS][0].u, bad, key, PARTIES - 1, 0) == 0, end);
	} TEST_END;

	TEST_ONCE("a trustee whose noise is out of bounds is rejected") {
		/* A share t = s u + p E' whose E' has a coefficient of 2^84, far past
		 * BOUND_D and the slack of the relaxed proof: the linear proof holds,
		 * since the share is consistent with its commitment, and only the
		 * norm bound can fail. */
		__int128 cf[DEGREE] = { };
		params::poly_q big, ent;
		pibnd_dec_t *bp;
		int lin;

		cf[0] = (__int128) 1 << 84;
		util::set_signed(big, cf);
		E[0] = E[0] + big;
		commit_one(Y[0], ry[0], E[0], key);
		ent = E[0];
		ent.ntt_pow_phi();
		T[PARTIES - 1][0] = share[PARTIES - 1] * list[MIXERS][0].u + ent + ent;
		dlin_prove(dz, d_z, dh, scom[PARTIES - 1], Y[0], list[MIXERS][0].u,
				T[PARTIES - 1][0], key, srand[PARTIES - 1], ry[0],
				PARTIES - 1, 0);
		lin = dlin_verify(dz, d_z, dh, scom[PARTIES - 1], Y[0],
				list[MIXERS][0].u, T[PARTIES - 1][0], key, PARTIES - 1, 0);
		bp = pibnd_dec_prove(key, Y, ry, E, MSGS);
		TEST_ASSERT(lin == 1 && pibnd_dec_verify(bp, key, Y, MSGS) == 0, end);
		pibnd_dec_free(bp);
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
	printf("    ballot proof %.1f KB on average\n", proof_bytes / 1024.0 / MSGS);
	printf("    timing, wall clock: key generation %.2f s; voting (encrypt and "
			"prove) %.2f s, %.2f ms per ballot; board check %.2f s, %.2f ms per "
			"ballot\n", t_key, t_vote, 1e3 * t_vote / MSGS, t_board,
			1e3 * t_board / MSGS);
	printf("    timing, per mix server: re-encryption and commitments %.2f s, "
			"prove %.2f s, verify %.2f s, both (compression) %.2f s\n",
			t_remix / MIXERS, t_prove / MIXERS, t_verify / MIXERS,
			t_shared / MIXERS);
	printf("    timing, per mix server: proof of re-encryption, prove %.2f s, "
			"verify %.2f s\n", t_rr_prove / MIXERS, t_rr_verify / MIXERS);
	printf("    sizes, as published: key-share commitments %.1f KB in all; "
			"ballot ciphertext %.1f KB\n", setup_bytes / 1024.0,
			ballot_bytes / 1024.0 / MSGS);
	printf("    sizes, per mix server and ballot: %.1f KB in all = output %.1f "
			"+ commitments to the E_i %.1f + proof of re-encryption %.1f + "
			"proof of shuffle %.1f\n", mix_bytes / 1024.0 / MIXERS / MSGS,
			mix_sz[0] / 1024.0 / MIXERS / MSGS, mix_sz[1] / 1024.0 / MIXERS / MSGS,
			mix_sz[2] / 1024.0 / MIXERS / MSGS, mix_sz[3] / 1024.0 / MIXERS / MSGS);
	printf("    timing, per trustee: partial decryptions and their proofs %.2f "
			"s, %.2f ms per ballot; verify them %.2f s, %.2f ms per ballot\n",
			t_dprove / PARTIES, 1e3 * t_dprove / PARTIES / MSGS,
			t_dverify / PARTIES, 1e3 * t_dverify / PARTIES / MSGS);
	printf("    decryption, per ballot and trustee: share %.1f KB, proof %.1f KB "
			"(commitment to the noise, linear proof, share of Pi_BND)\n",
			share_bytes / 1024.0 / PARTIES / MSGS,
			dproof_bytes / 1024.0 / PARTIES / MSGS);
	printf("    timing: combining the shares %.2f s, %.2f ms per ballot (%d "
			"trustees)\n", t_comb, 1e3 * t_comb / MSGS, PARTIES);

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
