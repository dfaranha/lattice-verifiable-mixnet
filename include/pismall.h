#ifndef PISMALL_H
#define PISMALL_H

#include <vector>

#include "common.h"
#include "serial.h"

/**
 * The amortized exact proof of src/pismall.cpp, specialised to the statement
 * the proof of shuffle needs: the message committed in each of the n BDLOP
 * commitments P[i] is a ring constant. With g(i) = i, that is the algebraic
 * half of the membership required by Lemma 5 of ePrint 2025/658.
 *
 * The relation proven is the commitment equation itself, so the witness bound
 * is an opening of P[i] and no link between two commitment schemes is needed.
 * Unlike every other coefficient set in that file, this one is exact over Z_q:
 * the identity is f = 0 at each coefficient above the constant one, and f = 0
 * has a single root whether or not q is composite. The size half, which is
 * what makes the committed constants pairwise different by a unit, comes from
 * the norm bound of pibnd.h.
 */
typedef struct pismall_const pismall_const_t;

/** Smallest power of two at least n, for n up to 8192. The proof interpolates
 * over the TAU-th roots of unity, so its amortization parameter has to be a
 * power of two; a caller with a different number of relations pads. */
#define AEX_PAD2(n)	((n) <= 1 ? 1 : (n) <= 2 ? 2 : (n) <= 4 ? 4 :			\
					 (n) <= 8 ? 8 : (n) <= 16 ? 16 : (n) <= 32 ? 32 :		\
					 (n) <= 64 ? 64 : (n) <= 128 ? 128 : (n) <= 256 ? 256 :	\
					 (n) <= 512 ? 512 : (n) <= 1024 ? 1024 :				\
					 (n) <= 2048 ? 2048 : (n) <= 4096 ? 4096 : 8192)

/**
 * Prove that the message committed in each P[i] is a ring constant.
 *
 * @param[in] key			- the commitment key P was committed under.
 * @param[in] P				- the n commitments.
 * @param[in] r				- their randomness, WIDTH ternary polynomials each.
 * @param[in] sigma			- the committed constants, in the coefficient
 *							  domain, as bdlop_commit takes them.
 * @param[in] n				- the number of commitments, at most the
 *							  compile-time TAU of src/pismall.cpp.
 * @return the proof, to be released with pismall_const_free().
 */
pismall_const_t *pismall_const_prove(comkey_t & key, commit_t * P,
		std::vector < params::poly_q > *r, params::poly_q * sigma, size_t n);

/**
 * Verify a proof produced by pismall_const_prove() against the same key and
 * commitments.
 *
 * @return 1 if the proof verifies, 0 otherwise.
 */
int pismall_const_verify(pismall_const_t * pi, comkey_t & key, commit_t * P,
		size_t n);

/** Bytes the proof occupies on the wire. */
size_t pismall_const_bytes(const pismall_const_t * pi);

/** Release a proof and the one-time setup it shares with the other proofs. */
void pismall_const_free(pismall_const_t * pi);
/* The proof as published bytes (pismall.cpp): write returns 0 if the proof
 * is not of the form a prover makes; read returns a proof to verify, or one
 * to free if the reader is left bad or unfinished. */
int pismall_const_write(const pismall_const_t * pi, serial::bits & b);
pismall_const_t *pismall_const_read(serial::bits & b);
void pismall_const_clear(void);

/**
 * The same proof at the mix-net's own relation, from a second build of
 * src/pismall.cpp (PISMALL_MIX): each of the n commitments P[i] opens, under
 * ternary randomness r[i], to an encryption of zero E_i = (a rho_i + p e1_i,
 * b rho_i + p e2_i) under the key pk, with rho_i, e1_i and e2_i ternary. It is
 * Pi_SMALL as Pi_Mix of the paper runs it, and what ties a mix server's
 * re-encryptions to its input list: the verifier adds each input c_i to P[i]
 * itself, which gives the commitment to c_i + E_i the proof of shuffle is
 * about.
 */
typedef struct pismall_mix pismall_mix_t;

/**
 * Prove that each P[i] commits to an encryption of zero with short randomness.
 *
 * @param[in] key			- the commitment key P was committed under.
 * @param[in] pk			- the encryption key the E_i are under.
 * @param[in] P				- the n commitments, to E_i in the coefficient
 *							  domain as bdlop_commit takes it.
 * @param[in] r				- their randomness, WIDTH ternary polynomials each,
 *							  in the NTT domain.
 * @param[in] rho, e1, e2	- the encryption randomness of each E_i, in the
 *							  coefficient domain.
 * @param[in] n				- the number of commitments, at most the
 *							  compile-time TAU of the PISMALL_MIX build.
 * @return the proof, to be released with pismall_mix_free().
 */
pismall_mix_t *pismall_mix_prove(comkey_t & key, bgvkey_t & pk, commit_t * P,
		std::vector < params::poly_q > *r, params::poly_q * rho,
		params::poly_q * e1, params::poly_q * e2, size_t n);

/** Verify a proof produced by pismall_mix_prove(). @return 1 if it verifies. */
int pismall_mix_verify(pismall_mix_t * pi, comkey_t & key, bgvkey_t & pk,
		commit_t * P, size_t n);

/** Bytes the proof occupies on the wire. */
size_t pismall_mix_bytes(const pismall_mix_t * pi);

/** Release a proof, and the setup the proofs of this build share. */
void pismall_mix_free(pismall_mix_t * pi);
/* The proof as published bytes (pismall.cpp): write returns 0 if the proof
 * is not of the form a prover makes; read returns a proof to verify, or one
 * to free if the reader is left bad or unfinished. */
int pismall_mix_write(const pismall_mix_t * pi, serial::bits & b);
pismall_mix_t *pismall_mix_read(serial::bits & b);
void pismall_mix_clear(void);

#endif
