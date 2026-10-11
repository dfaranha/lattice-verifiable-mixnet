#pragma once

#include <cstddef>
#include <cstdint>
#include <cmath>

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

/* Centred coefficients without GMP. A coefficient of R_q is stored as one
 * residue per modulus; with one or two moduli below 2^63 its value mod q fits
 * 128 bits, and the CRT that recombines two residues needs one multiplication
 * by p_0^-1 mod p_1, done with Shoup's precomputed quotient. */
template <class P> struct crt {
	static_assert(P::nmoduli == 1 || P::nmoduli == 2, "one or two moduli");
	uint64_t p0, p1, w, wp;
	__int128 Q, half;

	crt() {
		p0 = P::get_modulus(0);
		p1 = (P::nmoduli == 2) ? P::get_modulus(P::nmoduli - 1) : 1;
		w = 1;
		if (P::nmoduli == 2) {
			/* p_0^-1 mod p_1, by Fermat: p_1 is prime. */
			uint64_t b = p0 % p1, e = p1 - 2, r = 1;
			for (; e; e >>= 1, b = (uint64_t) ((__uint128_t) b * b % p1)) {
				if (e & 1) r = (uint64_t) ((__uint128_t) r * b % p1);
			}
			w = r;
		}
		wp = (uint64_t) (((__uint128_t) w << 64) / p1);
		Q = (__int128) p0 * p1;
		half = Q / 2;
	}
	static const crt &get() {
		static const crt c;
		return c;
	}
};

/* The coefficients of a, read as they are stored (the coefficient domain, for
 * them to mean anything), centred into (-q/2, q/2]. */
template <class P> inline void centred(__int128 out[], P const &a) {
	const crt<P> &c = crt<P>::get();

	for (size_t i = 0; i < P::degree; i++) {
		const uint64_t r0 = a(0, i);
		__int128 x = r0;

		if (P::nmoduli == 2) {
			const uint64_t r1 = a(P::nmoduli - 1, i), p1 = c.p1;
			const uint64_t r0m = r0 % p1;
			const uint64_t d = (r1 >= r0m) ? r1 - r0m : r1 + p1 - r0m;
			/* Shoup: d w mod p_1, in [0, 2 p_1), then reduced. */
			const uint64_t h = (uint64_t) (((__uint128_t) c.wp * d) >> 64);
			uint64_t t = d * c.w - h * p1;
			t -= (t >= p1) ? p1 : 0;
			x += (__int128) c.p0 * t;
		}
		out[i] = (x > c.half) ? x - c.Q : x;
	}
}

/* a = the polynomial with signed coefficients v, in the coefficient domain,
 * each reduced mod every modulus. */
template <class P> inline void set_signed(P &a, const __int128 v[]) {
	for (size_t cm = 0; cm < P::nmoduli; cm++) {
		const uint64_t p = P::get_modulus(cm);

		for (size_t i = 0; i < P::degree; i++) {
			const __int128 x = v[i];
			const __uint128_t m = (x < 0) ? (__uint128_t) 0 - (__uint128_t) x : (__uint128_t) x;
			/* Most coefficients fit 64 bits, where the division is cheap. */
			const uint64_t r = (m >> 64) ? (uint64_t) (m % p) : (uint64_t) m % p;
			a(cm, i) = (x < 0 && r != 0) ? p - r : r;
		}
	}
}

/* dot += sum_k a_k b_k and norm += sum_k b_k^2 over n centred coefficients.
 * Exact in 128 bits when every |a_k| and |b_k| is below 2^57, so that n <= 2^12
 * products stay below 2^126; in long double otherwise. The callers turn both
 * into doubles for a rejection test, as mpz_get_d did. */
inline void dot_norm(long double &dot, long double &norm, const __int128 a[],
		const __int128 b[], size_t n) {
	const __int128 lim = (__int128) 1 << 57;
	bool small = n <= 4096;

	for (size_t k = 0; k < n && small; k++) {
		small = a[k] > -lim && a[k] < lim && b[k] > -lim && b[k] < lim;
	}
	if (small) {
		__int128 d = 0, s = 0;

		for (size_t k = 0; k < n; k++) {
			d += (__int128) (int64_t) a[k] * (int64_t) b[k];
			s += (__int128) (int64_t) b[k] * (int64_t) b[k];
		}
		dot += (long double) d;
		norm += (long double) s;
	} else {
		for (size_t k = 0; k < n; k++) {
			dot += (long double) a[k] * (long double) b[k];
			norm += (long double) b[k] * (long double) b[k];
		}
	}
}

/* out = the exact squared l2-norm of a's centred coefficients, when every one
 * is below 2^57 in absolute value (then 2^12 squares stay below 2^126).
 * Returns false otherwise, for the caller to fall back on GMP: with q of 88
 * bits a coefficient can be far larger, and a verifier's check has to be
 * exact whatever it is given. */
template <class P> inline bool norm2_small(unsigned __int128 &out, P const &a) {
	static_assert(P::degree <= 4096, "2^12 squares below 2^114 fit 128 bits");
	__int128 c[P::degree];
	const __int128 lim = (__int128) 1 << 57;

	centred(c, a);
	out = 0;
	for (size_t i = 0; i < P::degree; i++) {
		if (c[i] <= -lim || c[i] >= lim) {
			return false;
		}
		out += (unsigned __int128) ((__int128) (int64_t) c[i] * (int64_t) c[i]);
	}
	return true;
}
} // namespace util
