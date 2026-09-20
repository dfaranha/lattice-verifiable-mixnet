/**
 * @file
 *
 * Helpers for moving polynomial coefficients between NFLlib and FLINT.
 *
 * NFLlib converts polynomials through arrays of GMP integers (poly2mpz and
 * mpz2poly), whereas FLINT works in terms of fmpz. FLINT 3.5 removed the
 * fmpz_mod_poly_{get,set}_coeff_mpz functions that used to bridge the two --
 * those names are now macros expanding to `#pragma GCC error`, so they cannot
 * even be mentioned in a translation unit that includes fmpz_mod_poly.h. The
 * wrappers below take their place.
 */

#ifndef FLINT_UTIL_H
#define FLINT_UTIL_H

#include <gmp.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpz_mod.h>
#include <flint/fmpz_mod_poly.h>

/* flint_rand_init(), flint_rand_clear() and flint_rand_set_seed() arrived in
 * FLINT 3.1, replacing the flint_rand{init,clear,seed}() spellings. */
#if !defined(__FLINT_RELEASE) || __FLINT_RELEASE < 30100
#error "This code requires FLINT 3.1 or later."
#endif

/**
 * Reads coefficient @p n of @p poly into the GMP integer @p c.
 */
static inline void flint_poly_get_coeff_mpz(mpz_t c, const fmpz_mod_poly_t poly,
		slong n, const fmpz_mod_ctx_t ctx) {
	fmpz_t t;

	fmpz_init(t);
	fmpz_mod_poly_get_coeff_fmpz(t, poly, n, ctx);
	fmpz_get_mpz(c, t);
	fmpz_clear(t);
}

/**
 * Sets coefficient @p n of @p poly to the GMP integer @p c.
 */
static inline void flint_poly_set_coeff_mpz(fmpz_mod_poly_t poly, slong n,
		const mpz_t c, const fmpz_mod_ctx_t ctx) {
	fmpz_t t;

	fmpz_init(t);
	fmpz_set_mpz(t, c);
	fmpz_mod_poly_set_coeff_fmpz(poly, n, t, ctx);
	fmpz_clear(t);
}

#endif /* FLINT_UTIL_H */
