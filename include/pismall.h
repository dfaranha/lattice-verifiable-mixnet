#ifndef PISMALL_H
#define PISMALL_H

#include <vector>

#include "common.h"

/**
 * The amortized exact proof of src/pismall.cpp, specialised to the statement
 * the proof of shuffle needs: the message committed in each of the n BDLOP
 * commitments P[i] is a monomial x^j. That is the membership sigma_i in D
 * required by Lemma 5 of ePrint 2025/658, with D the monomials.
 *
 * The relation proven is the commitment equation itself, so the witness bound
 * is an opening of P[i] and no link between two commitment schemes is needed.
 * Being a monomial is not a coefficient-wise property, but it splits into two
 * that are: sigma has binary coefficients, and sigma * (2 - sum_j x^j) has all
 * of its coefficients in {-1, 1}, which happens exactly when the binary sigma
 * has Hamming weight one.
 */
typedef struct pismall_mono pismall_mono_t;

/** Smallest power of two at least n, for n up to 8192. The proof interpolates
 * over the TAU-th roots of unity, so its amortization parameter has to be a
 * power of two; a caller with a different number of relations pads. */
#define AEX_PAD2(n)	((n) <= 1 ? 1 : (n) <= 2 ? 2 : (n) <= 4 ? 4 :			\
					 (n) <= 8 ? 8 : (n) <= 16 ? 16 : (n) <= 32 ? 32 :		\
					 (n) <= 64 ? 64 : (n) <= 128 ? 128 : (n) <= 256 ? 256 :	\
					 (n) <= 512 ? 512 : (n) <= 1024 ? 1024 :				\
					 (n) <= 2048 ? 2048 : (n) <= 4096 ? 4096 : 8192)

/**
 * Prove that the message committed in each P[i] is a monomial.
 *
 * @param[in] key			- the commitment key P was committed under.
 * @param[in] P				- the n commitments.
 * @param[in] r				- their randomness, WIDTH ternary polynomials each.
 * @param[in] sigma			- the committed monomials, in the coefficient
 *							  domain, as bdlop_commit takes them.
 * @param[in] n				- the number of commitments, at most the
 *							  compile-time TAU of src/pismall.cpp.
 * @return the proof, to be released with pismall_mono_free().
 */
pismall_mono_t *pismall_mono_prove(comkey_t & key, commit_t * P,
		std::vector < params::poly_q > *r, params::poly_q * sigma, size_t n);

/**
 * Verify a proof produced by pismall_mono_prove() against the same key and
 * commitments.
 *
 * @return 1 if the proof verifies, 0 otherwise.
 */
int pismall_mono_verify(pismall_mono_t * pi, comkey_t & key, commit_t * P,
		size_t n);

/** Release a proof and the one-time setup it shares with the other proofs. */
void pismall_mono_free(pismall_mono_t * pi);
void pismall_mono_clear(void);

#endif
