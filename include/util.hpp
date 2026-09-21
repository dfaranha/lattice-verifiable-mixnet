#pragma once

#include <cstddef>

#include <algorithm>
#include <chrono>
#include <iostream>
#include <memory>
#include <nfl.hpp>

namespace util {
/// Helper functions for messages conversion

/**
 * Center op1 modulo op2
 * @param rop     result
 * @param op1     number op1 already reduced modulo op2, i.e. such that 0 <= op1
 * < op2-1
 * @param op2     modulus
 * @param op2Div2 floor(modulus/2)
 */
inline void center(mpz_t & rop, mpz_t const &op1, mpz_t const &op2,
		mpz_t const &op2Div2) {
	mpz_set(rop, op1);
	if (mpz_cmp(op1, op2Div2) > 0) {
		mpz_sub(rop, rop, op2);
	}
}

/* Exact comparison of ring elements. NFLlib's operator== is element-wise and
 * its operator bool is "some coefficient is non-zero", so `a == b` holds as
 * soon as a and b agree in one of the nmoduli * degree values they store,
 * which is far too weak for a verification equation. Both arguments have to be
 * in the same domain. operator!= is fine as it stands. */
template <class P> inline bool equal(P const &a, P const &b) {
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		for (size_t i = 0; i < P::degree; i++) {
			if (a(cm, i) != b(cm, i)) {
				return false;
			}
		}
	}
	return true;
}

template <class P> inline bool is_zero(P const &a) {
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		for (size_t i = 0; i < P::degree; i++) {
			if (a(cm, i) != 0) {
				return false;
			}
		}
	}
	return true;
}
} // namespace util
