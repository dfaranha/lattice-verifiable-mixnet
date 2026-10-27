/**
 * @file
 *
 * The voter's proof that a ballot is well formed, on LaZer's linear proofs: a
 * BGV encryption (u, v) = (a r + 2 e1, b r + 2 e2 + m) of a vote m = X^j (or of
 * 0) with short randomness (r, e1, e2), bound to a context such as the
 * election and the voter.
 *
 * C, so that the C++ code can call it without compiling LaZer's headers:
 * elements of R_q are passed as their BALLOT_DEG coefficients, centred mod
 * q; q has 88 bits, so they are __int128.
 */

#ifndef BALLOT_PROOF_H
#define BALLOT_PROOF_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The ring the ballots live in: DEGREE of common.h, which voting.cpp checks,
 * and the product of params::poly_q's two moduli, given as its factors. */
#define BALLOT_DEG 	4096
#define BALLOT_Q0 	17592167170049ULL
#define BALLOT_Q1 	17592123129857ULL

/* Initialise LaZer; call once before proving or verifying. */
void ballot_setup(void);

/* An upper bound on the size in bytes of a proof; its encoding varies. */
size_t ballot_proof_len(void);

/**
 * Prove that u = a r + 2 e1 and v = b r + 2 e2 + m with r, e1, e2 ternary and
 * short and m = X^j or 0, bound to ctx. Refuses (returns 0, no proof) if the
 * witness is not of that form or the equations do not hold.
 *
 * @param[out] proof		- room for ballot_proof_len() bytes.
 * @param[out] len			- the bytes written, at most that.
 * @return 1 if a proof was made, 0 otherwise.
 */
int ballot_prove(uint8_t *proof, size_t *len, const __int128 u[],
		const __int128 v[], const __int128 a[], const __int128 b[],
		const int64_t r[], const int64_t e1[], const int64_t e2[],
		const int64_t m[], const uint8_t *ctx, size_t ctxlen);

/**
 * Verify a ballot proof for (u, v) under the public key (a, b) and the
 * context ctx.
 *
 * @return 1 if it verifies, 0 otherwise.
 */
int ballot_verify(const uint8_t *proof, size_t len, const __int128 u[],
		const __int128 v[], const __int128 a[], const __int128 b[],
		const uint8_t *ctx, size_t ctxlen);

#ifdef __cplusplus
}
#endif

#endif /* BALLOT_PROOF_H */
