#ifndef PIBND_H
#define PIBND_H

#include <vector>

#include "common.h"

/**
 * The amortized approximate norm proof of src/pibnd.cpp, instantiated on the
 * BDLOP commitment equation: a proof that the n commitments P[i] have openings
 * whose components, the committed message included, are short.
 *
 * The proof of shuffle needs it next to the membership proof of pismall.h.
 * That one is coefficient-wise but not exact, because q is composite: it places
 * each coefficient of sigma_i in the four roots of c (c - 1) = 0 over
 * Z_q = Z_{p_1} x Z_{p_2}, which are 0, 1 and the two CRT idempotents. The
 * idempotents are multiples of p_2 and of p_1 respectively, so their centred
 * representatives exceed 2^38, while the norm proven here is below 2^28 at any
 * supported parameters. The two together therefore say that the coefficients
 * are 0 and 1 as integers, which is what Lemma 5 of ePrint 2025/658 needs and
 * what no algebraic identity over a composite modulus can give on its own.
 */
typedef struct pibnd_short pibnd_short_t;

/**
 * Prove that the openings of the n commitments P[i] are short.
 *
 * @param[in] key			- the commitment key P was committed under.
 * @param[in] P				- the n commitments.
 * @param[in] r				- their randomness, WIDTH ternary polynomials each.
 * @param[in] sigma			- the committed messages, in the coefficient domain.
 * @param[in] n				- the number of commitments, which has to be the
 *							  compile-time TAU of src/pibnd.cpp.
 * @return the proof, to be released with pibnd_short_free(). A prover whose
 *		   witness is not short cannot pass rejection sampling; it gives up
 *		   after a bounded number of attempts and returns a proof that fails
 *		   the verifier's norm test.
 */
pibnd_short_t *pibnd_short_prove(comkey_t & key, commit_t * P,
		std::vector < params::poly_q > *r, params::poly_q * sigma, size_t n);

/**
 * Verify a proof produced by pibnd_short_prove() against the same key and
 * commitments.
 *
 * @return 1 if the proof verifies, 0 otherwise.
 */
int pibnd_short_verify(pibnd_short_t * pi, comkey_t & key, commit_t * P,
		size_t n);

/**
 * The l2-norm bound the verifier enforces on each masked opening. The argument
 * of SOUNDNESS.md section 5.4 reads two congruences modulo the primes of the
 * basis as equalities over the integers, which needs twice this bound, plus
 * the slack of a challenge difference, to stay below p_min / 2.
 */
double pibnd_short_bound(void);

/** Bytes the proof occupies on the wire, its openings entropy-coded. */
size_t pibnd_short_bytes(const pibnd_short_t * pi);

/** Release a proof, and the buffers the proofs share. */
void pibnd_short_free(pibnd_short_t * pi);
void pibnd_short_clear(void);

#endif
