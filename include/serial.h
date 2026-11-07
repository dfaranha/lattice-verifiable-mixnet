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

/** A growable bit buffer, written and read most-significant bit first. */
class bits {
  public:
	std::vector < uint8_t > buf;
	size_t nbits = 0;
	size_t pos = 0;
	/* Set by a read past the end, or of an encoding no writer produces; a
	 * transcript read with it set is to be rejected. */
	bool bad = false;

	bits() = default;
	/** A reader over len published bytes. */
	bits(const uint8_t *in, size_t len) : buf(in, in + len), nbits(8 * len) {}
	/** A reader over a writer's bytes, which it takes over. */
	explicit bits(std::vector < uint8_t > &&in) : buf(std::move(in)), nbits(8 * buf.size()) {}

	/* The low n bits of v, most significant first; for n > 64, the bits
	 * above v's 64 are zeros, written without shifting a 64-bit value by 64
	 * or more, which is undefined (proof_size puts a 256-bit hash this way). */
	void put(uint64_t v, int n) {
		for (int i = n - 1; i >= 0; i--) {
			if ((nbits & 7) == 0) {
				buf.push_back(0);
			}
			if (i < 64 && ((v >> i) & 1)) {
				buf[nbits >> 3] |= 0x80 >> (nbits & 7);
			}
			nbits++;
		}
	}

	uint64_t get(int n) {
		uint64_t v = 0;
		if (pos + n > 8 * buf.size()) {
			bad = true;
			pos = 8 * buf.size();
			return 0;
		}
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

	/** Whether a reader ended exactly where its writer did: nothing flagged,
	 * no byte left over and the padding bits of the last byte zero. */
	bool finish(void) const {
		return !bad && (pos + 7) / 8 == buf.size()
				&& ((pos & 7) == 0 || (buf[pos >> 3] & (0xff >> (pos & 7))) == 0);
	}

	/** n <= 128 bits of v, most significant first. */
	void put128(zq::u128 v, int n) {
		if (n > 64) {
			put((uint64_t) (v >> 64), n - 64);
			put((uint64_t) v, 64);
		} else {
			put((uint64_t) v, n);
		}
	}

	zq::u128 get128(int n) {
		if (n > 64) {
			zq::u128 hi = get(n - 64);
			return (hi << 64) | get(64);
		}
		return get(n);
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
		uint64_t u = b.get(64);
		/* The writer escapes only what the unary run cannot carry. */
		if ((u >> k) < SERIAL_ESCAPE) {
			b.bad = true;
		}
		return unzigzag(u);
	}
	uint64_t u = q << k;
	if (k > 0) {
		u |= b.get(k);
	}
	return unzigzag(u);
}

/** Write a uniform ring element: every coefficient, in the 88 bits of q. */
static inline void put_uniform(bits & b, const params::poly_q & p) {
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		b.put((uint64_t) (p(0, i) >> 64), 24);
		b.put((uint64_t) p(0, i), 64);
	}
}

static inline void get_uniform(bits & b, params::poly_q & p) {
	const zq::u128 q = params::poly_q::get_modulus(0);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		zq::u128 hi = b.get(24);
		zq::u128 v = (hi << 64) | b.get(64);
		if (v >= q) {
			b.bad = true;
			v = 0;
		}
		p(0, i) = v;
	}
}

/* Zigzag and Golomb-Rice in 128 bits: the widest response here, Pi_BND's
 * row for the decryption noise, is about 2^74, past what 64 bits hold. */
static inline zq::u128 zigzag128(__int128 x) {
	return ((zq::u128) x << 1) ^ (zq::u128) (x >> 127);
}

static inline __int128 unzigzag128(zq::u128 u) {
	return (__int128) (u >> 1) ^ -(__int128) (u & 1);
}

static inline void put_rice128(bits & b, __int128 x, int k) {
	zq::u128 u = zigzag128(x);
	zq::u128 q = u >> k;

	if (q >= SERIAL_ESCAPE) {
		b.put(0xffffff, SERIAL_ESCAPE);
		b.put128(u, 128);
		return;
	}
	for (unsigned i = 0; i < (unsigned) q; i++) {
		b.put(1, 1);
	}
	b.put(0, 1);
	if (k > 0) {
		b.put128(u & ((((zq::u128) 1) << k) - 1), k);
	}
}

static inline __int128 get_rice128(bits & b, int k) {
	unsigned q = 0;
	zq::u128 u;

	while (q < SERIAL_ESCAPE && b.get(1) == 1) {
		q++;
	}
	if (q >= SERIAL_ESCAPE) {
		u = b.get128(128);
		if ((u >> k) < SERIAL_ESCAPE) {
			b.bad = true;
		}
	} else {
		u = ((zq::u128) q << k) | (k > 0 ? b.get128(k) : 0);
	}
	return unzigzag128(u);
}

/**
 * Write a masked opening, Rice-coded about its own width: the centred
 * coefficients of an element in the coefficient domain, which is how it is
 * transmitted. q is one prime, so a coefficient is one residue.
 */
static inline void put_gauss(bits & b, const params::poly_q & p, double sigma) {
	const zq::u128 q = params::poly_q::get_modulus(0);
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		zq::u128 c = p(0, i);
		__int128 x = c > q / 2 ? -(__int128) (q - c) : (__int128) c;
		put_rice128(b, x, k);
	}
}

static inline void get_gauss(bits & b, params::poly_q & p, double sigma) {
	const zq::u128 q = params::poly_q::get_modulus(0);
	int k = rice_k(sigma);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		__int128 x = get_rice128(b, k);
		if (x > (__int128) (q / 2) || x < -(__int128) (q / 2)) {
			b.bad = true;
			x = 0;
		}
		p(0, i) = x < 0 ? q - (zq::u128) (-x) : (zq::u128) x;
	}
}

/** A Gaussian element held in the NTT domain, sent in the coefficient one. */
static inline void put_gauss_ntt(bits & b, const params::poly_q & p, double sigma) {
	params::poly_q t = p;
	t.invntt_pow_invphi();
	put_gauss(b, t, sigma);
}

static inline void get_gauss_ntt(bits & b, params::poly_q & p, double sigma) {
	get_gauss(b, p, sigma);
	p.ntt_pow_phi();
}

/** A ternary element held in the NTT domain: 2 bits a coefficient, 0, 1 or
 * 2 for -1. Returns 0, writing nothing usable, if it is not ternary. */
static inline int put_ternary_ntt(bits & b, const params::poly_q & p) {
	const zq::u128 q = params::poly_q::get_modulus(0);
	params::poly_q t = p;
	int ok = 1;

	t.invntt_pow_invphi();
	for (size_t i = 0; i < params::poly_q::degree; i++) {
		zq::u128 c = t(0, i);
		ok &= c <= 1 || c == q - 1;
		b.put(c <= 1 ? (uint64_t) c : 2, 2);
	}
	return ok;
}

static inline void get_ternary_ntt(bits & b, params::poly_q & p) {
	const zq::u128 q = params::poly_q::get_modulus(0);

	for (size_t i = 0; i < params::poly_q::degree; i++) {
		uint64_t c = b.get(2);
		if (c == 3) {
			b.bad = true;
			c = 0;
		}
		p(0, i) = c == 2 ? q - 1 : (zq::u128) c;
	}
	p.ntt_pow_phi();
}

static inline void put_bytes(bits & b, const uint8_t *v, size_t n) {
	for (size_t i = 0; i < n; i++) {
		b.put(v[i], 8);
	}
}

static inline void get_bytes(bits & b, uint8_t *v, size_t n) {
	for (size_t i = 0; i < n; i++) {
		v[i] = (uint8_t) b.get(8);
	}
}

/** A commitment: c1 and its n message rows, uniform, as held. */
static inline void put_commit(bits & b, const commit_t & c) {
	put_uniform(b, c.c1);
	for (size_t i = 0; i < c.c2.size(); i++) {
		put_uniform(b, c.c2[i]);
	}
}

static inline void get_commit(bits & b, commit_t & c, size_t n) {
	get_uniform(b, c.c1);
	c.c2.resize(n);
	for (size_t i = 0; i < n; i++) {
		get_uniform(b, c.c2[i]);
	}
}

}                               /* namespace serial */

#endif                          /* SERIAL_H */
