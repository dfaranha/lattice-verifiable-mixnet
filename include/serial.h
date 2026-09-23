/**
 * @file
 *
 * Serialisation of a proof, and the only place that says how many bytes one
 * takes. Every size in SOUNDNESS.md used to be computed by hand from the
 * shapes of the structures; this makes the same count come out of the code.
 *
 * Two encodings, because a proof carries two kinds of ring element.
 *
 * A *uniform* element -- a commitment, a published scalar -- is uniform over
 * R_q and costs the width of the modulus, which is the sum of the widths of
 * the primes of the basis. There is nothing to exploit.
 *
 * A *masked opening* is a discrete Gaussian of width sigma_C. Section 10 of
 * SOUNDNESS.md counted it at log2(6 sigma_C) bits a coefficient, which is
 * 13.58 here, and that figure deserves scrutiny: 6 sigma_C is plus or minus
 * three standard deviations, and a discrete Gaussian leaves that interval
 * about once in 370 coefficients. At 4096 coefficients a polynomial has some
 * eleven of them, so *no* flat encoding of that width can carry a response --
 * a safe one needs log2(12 sigma_C), or 14.58 bits.
 *
 * What makes the published figure reachable is coding the distribution rather
 * than its bound. The entropy of a discrete Gaussian is log2(sigma sqrt(2 pi
 * e)), which is 13.05 bits here, and Golomb-Rice on the zigzagged coefficient
 * lands within about half a bit of it. So the number in the document was right
 * all along, but only for an encoder that did not exist; this is that encoder.
 */

#ifndef SERIAL_H
#define SERIAL_H

#include <cmath>
#include <cstdint>
#include <vector>

#include "common.h"
#include "util.hpp"

namespace serial {

/** Bits in one residue of coefficient, per prime of the basis. */
static inline size_t pbits(size_t cm) {
	size_t b = 0;
	uint64_t p = nfl::params < uint64_t >::P[cm];

	while (p != 0) {
		b++;
		p >>= 1;
	}
	return b;
}

/** A growable bit buffer, written and read most-significant bit first. */
class bits {
  public:
	std::vector < uint8_t > buf;
	size_t nbits = 0;
	size_t pos = 0;

	void put(uint64_t v, int n) {
		for (int i = n - 1; i >= 0; i--) {
			if ((nbits & 7) == 0) {
				buf.push_back(0);
			}
			if ((v >> i) & 1) {
				buf[nbits >> 3] |= 0x80 >> (nbits & 7);
			}
			nbits++;
		}
	}

	uint64_t get(int n) {
		uint64_t v = 0;
		for (int i = 0; i < n; i++) {
			v <<= 1;
			v |= (buf[pos >> 3] >> (7 - (pos & 7))) & 1;
			pos++;
		}
		return v;
	}

	size_t bytes(void) const {
		return (nbits + 7) / 8;
	}
};

static inline uint64_t zigzag(int64_t x) {
	return ((uint64_t) x << 1) ^ (uint64_t) (x >> 63);
}

static inline int64_t unzigzag(uint64_t u) {
	return (int64_t) (u >> 1) ^ -(int64_t) (u & 1);
}

/**
 * The Rice parameter for a discrete Gaussian of width sigma: the mean of the
 * zigzagged value is 2 sigma sqrt(2/pi), and the split belongs there.
 */
static inline int rice_k(double sigma) {
	int k = (int) (std::log2(2.0 * sigma * 0.7978845608) + 0.5);
	return k < 0 ? 0 : k;
}

/** Unary runs longer than this escape to a full-width value. */
#define SERIAL_ESCAPE 24

static inline void put_rice(bits & b, int64_t x, int k) {
	uint64_t u = zigzag(x);
	uint64_t q = u >> k;

	if (q >= SERIAL_ESCAPE) {
		b.put(0xffffff, SERIAL_ESCAPE);
		b.put(u, 64);
		return;
	}
	for (uint64_t i = 0; i < q; i++) {
		b.put(1, 1);
	}
	b.put(0, 1);
	if (k > 0) {
		b.put(u & (((uint64_t) 1 << k) - 1), k);
	}
}

static inline int64_t get_rice(bits & b, int k) {
	uint64_t q = 0;

	while (q < SERIAL_ESCAPE && b.get(1) == 1) {
		q++;
	}
	if (q >= SERIAL_ESCAPE) {
		return unzigzag(b.get(64));
	}
	uint64_t u = q << k;
	if (k > 0) {
		u |= b.get(k);
	}
	return unzigzag(u);
}

/** Write a uniform ring element: every residue of every coefficient. */
static inline void put_uniform(bits & b, const params::poly_q & p) {
	for (size_t cm = 0; cm < params::poly_q::nmoduli; cm++) {
		size_t n = pbits(cm);
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			b.put(p(cm, i), n);
		}
	}
}

static inline void get_uniform(bits & b, params::poly_q & p) {
	for (size_t cm = 0; cm < params::poly_q::nmoduli; cm++) {
		size_t n = pbits(cm);
		for (size_t i = 0; i < params::poly_q::degree; i++) {
			p(cm, i) = b.get(n);
		}
	}
}

/**
 * Write a masked opening, Rice-coded about its own width. The residues of a
 * short element are not themselves short, so this reconstructs the integer
 * coefficient and centres it before coding. The element is taken in the
 * coefficient domain, which is how it is transmitted.
 */
static inline void put_gauss(bits & b, params::poly_q p, double sigma) {
	std::array < mpz_t, params::poly_q::degree > c;
	mpz_t qDivBy2;
	int k = rice_k(sigma);

	mpz_init(qDivBy2);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(c[i], (params::poly_q::bits_in_moduli_product() << 2));
	}
	mpz_fdiv_q_2exp(qDivBy2, params::poly_q::moduli_product(), 1);
	p.poly2mpz(c);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		util::center(c[i], c[i], params::poly_q::moduli_product(), qDivBy2);
		/* A response is far inside 64 bits; anything else is a witness that
		 * is not short, and the escape carries it rather than truncating. */
		put_rice(b, mpz_fits_slong_p(c[i]) ? mpz_get_si(c[i]) : INT64_MAX, k);
	}
	mpz_clear(qDivBy2);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(c[i]);
	}
}

static inline void get_gauss(bits & b, params::poly_q & p, double sigma) {
	std::array < mpz_t, params::poly_q::degree > c;
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_init2(c[i], (params::poly_q::bits_in_moduli_product() << 2));
		mpz_set_si(c[i], get_rice(b, k));
		if (mpz_sgn(c[i]) < 0) {
			mpz_add(c[i], c[i], params::poly_q::moduli_product());
		}
	}
	p.mpz2poly(c);
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		mpz_clear(c[i]);
	}
}

}                               /* namespace serial */

#endif                          /* SERIAL_H */
