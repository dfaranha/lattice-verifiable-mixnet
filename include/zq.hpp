/**
 * @file
 *
 * Polynomials over Z_q[X]/(X^N + 1) for a single prime q, as a drop-in for the
 * part of NFLlib's poly that this code uses.
 *
 * NFLlib keeps a ring element as residues modulo word-sized primes, so the
 * 88-bit modulus the mix-net needs was a product of two 44-bit primes, and
 * R_q split into components whose challenges and openings could disagree (see
 * SOUNDNESS.md). Here q is one prime,
 *
 *   q = 2^88 - 25 * 2^16 + 1 = 309485009821345068723142657,
 *
 * with q = 1 mod 2^16, so that R_q has a negacyclic NTT for every degree up to
 * 2^15. A coefficient is one value below q in an unsigned __int128, 16 bytes,
 * the same size as NFLlib's two 64-bit residues, so the hashes that absorb an
 * element as 16 * N bytes keep absorbing all of it.
 *
 * Multiplication splits each operand into 64 and 24 bits and folds the 176-bit
 * product with 2^88 = 25 * 2^16 - 1 (mod q), twice; no division.
 *
 * As in NFLlib, every operation is coefficient-wise, so * is the ring product
 * only in the NTT domain, and the samplers fill the coefficient domain.
 */

#ifndef ZQ_HPP
#define ZQ_HPP

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <array>
#include <vector>
#include <algorithm>
#include <numeric>
#include <limits>
#include <stdexcept>
#include <gmp.h>
#include <nfl.hpp>

namespace zq {

typedef unsigned __int128 u128;

/* The modulus and its folding constant: 2^88 = C mod q. */
static constexpr u128 MODULUS = ((u128) 1 << 88) - ((u128) 25 << 16) + 1;
static constexpr u128 C = ((u128) 25 << 16) - 1;
static constexpr u128 MASK88 = ((u128) 1 << 88) - 1;

/* Branch-free: on random data a branch here is mispredicted half the time,
 * which costs more than the arithmetic. r < 2^127 unless it wrapped. */
static inline u128 csub(u128 r) {
	r -= MODULUS;
	return r + (MODULUS & -(r >> 127));
}

static inline u128 add(u128 a, u128 b) {
	return csub(a + b);
}

static inline u128 sub(u128 a, u128 b) {
	u128 r = a - b;
	return r + (MODULUS & -(r >> 127));
}

static inline u128 neg(u128 a) {
	return sub(0, a);
}

/* x mod q for x = hi 2^88 + lo with hi < 2^88 and lo < 2^88. */
static inline u128 fold(u128 hi, u128 lo) {
	u128 y = hi * C + lo;					/* < 2^110 */
	y = (y >> 88) * C + (y & MASK88);		/* < 2^88 + 2^44 < 2 q */
	return csub(y);
}

static inline u128 mul(u128 a, u128 b) {
	const uint64_t a0 = (uint64_t) a, a1 = (uint64_t) (a >> 64);
	const uint64_t b0 = (uint64_t) b, b1 = (uint64_t) (b >> 64);
	const u128 p00 = (u128) a0 * b0;
	const u128 mid = (u128) a0 * b1 + (u128) a1 * b0 + (p00 >> 64);
	const u128 top = (u128) a1 * b1 + (mid >> 64);			/* < 2^49 */
	const uint64_t w0 = (uint64_t) p00, w1 = (uint64_t) mid, w2 = (uint64_t) top;
	const u128 lo = (u128) w0 | ((u128) (w1 & ((1ULL << 24) - 1)) << 64);
	const u128 hi = (u128) (w1 >> 24) | ((u128) w2 << 40);
	return fold(hi, lo);
}

static inline u128 pow(u128 a, u128 e) {
	u128 r = 1;
	while (e) {
		if (e & 1) {
			r = mul(r, a);
		}
		a = mul(a, a);
		e >>= 1;
	}
	return r;
}

/* a^-1 mod q, for a != 0. */
static inline u128 inv(u128 a) {
	return pow(a, MODULUS - 2);
}

/* q as an mpz, set once. */
static inline const mpz_t &modulus_mpz() {
	struct holder {
		mpz_t q;
		holder() {
			mpz_init(q);
			mpz_import(q, 2, -1, sizeof(uint64_t), 0, 0, (const uint64_t[]) {
					(uint64_t) MODULUS, (uint64_t) (MODULUS >> 64)});
		}
	};
	static holder h;
	return h.q;
}

/* The tables of the negacyclic NTT of degree N: psi a primitive 2N-th root,
 * its powers in bit-reversed order, and those of its inverse. */
template <size_t D> struct ntt_tables {
	std::vector<u128> fwd, bwd;
	u128 ninv;

	static const ntt_tables &get() {
		static ntt_tables t;
		return t;
	}

  private:
	ntt_tables() : fwd(D), bwd(D) {
		static_assert((D & (D - 1)) == 0 && D >= 2 && D <= (1 << 15),
				"a power of two the NTT supports");
		/* A quadratic non-residue g gives psi = g^((q-1)/2N) of order 2N. */
		u128 g = 2;
		while (pow(g, (MODULUS - 1) / 2) != MODULUS - 1) {
			g++;
		}
		const u128 psi = pow(g, (MODULUS - 1) / (2 * D)), psiinv = inv(psi);
		unsigned logn = 0;
		while (((size_t) 1 << logn) < D) {
			logn++;
		}
		for (size_t i = 0; i < D; i++) {
			size_t r = 0;
			for (unsigned b = 0; b < logn; b++) {
				r |= ((i >> b) & 1) << (logn - 1 - b);
			}
			fwd[i] = pow(psi, r);
			bwd[i] = pow(psiinv, r);
		}
		ninv = zq::inv((u128) D);
	}
};

/* nfl::uniform, nfl::ZO_dist and nfl::hwt_dist are the samplers' tags, as in
 * NFLlib, so that the code that names them is unchanged. */
template <size_t Degree> class poly {
  public:
	typedef u128 value_type;
	static constexpr size_t degree = Degree;
	static constexpr size_t nmoduli = 1;

	poly() {
		std::memset(_data, 0, sizeof(_data));
	}
	/* The constant v (coefficient 0), as NFLlib's poly(v). */
	poly(value_type v) {
		std::memset(_data, 0, sizeof(_data));
		_data[0] = v % MODULUS;
	}
	poly(int v) : poly(v < 0 ? neg((u128) (-(int64_t) v) % MODULUS) : (u128) v) {}
	poly(nfl::uniform const &m) {
		set(m);
	}
	poly(nfl::ZO_dist const &m) {
		set(m);
	}
	poly(nfl::hwt_dist const &m) {
		set(m);
	}

	/* Without these, x = 0 would be ambiguous: the samplers' tags are
	 * implicitly constructible from integers too. */
	poly &operator=(int v) {
		return *this = poly(v);
	}
	poly &operator=(value_type v) {
		return *this = poly(v);
	}
	poly &operator=(nfl::uniform const &m) {
		set(m);
		return *this;
	}
	poly &operator=(nfl::ZO_dist const &m) {
		set(m);
		return *this;
	}
	poly &operator=(nfl::hwt_dist const &m) {
		set(m);
		return *this;
	}

	static value_type get_modulus(size_t) {
		return MODULUS;
	}
	static const mpz_t &moduli_product() {
		return modulus_mpz();
	}
	static constexpr size_t bits_in_moduli_product() {
		return 88;
	}

	value_type &operator()(size_t, size_t i) {
		return _data[i];
	}
	value_type const &operator()(size_t, size_t i) const {
		return _data[i];
	}
	value_type *data() {
		return _data;
	}
	value_type const *data() const {
		return _data;
	}
	value_type *begin() {
		return _data;
	}
	value_type *end() {
		return _data + Degree;
	}
	value_type const *begin() const {
		return _data;
	}
	value_type const *end() const {
		return _data + Degree;
	}

	/* Uniform in [0, q), by rejection on 88-bit words. */
	void set(nfl::uniform const &) {
		u128 buf[64];
		size_t i = 0, k = 64;

		while (i < Degree) {
			if (k == 64) {
				nfl::fastrandombytes((unsigned char *) buf, sizeof(buf));
				k = 0;
			}
			u128 x = buf[k++] & MASK88;
			if (x < MODULUS) {
				_data[i++] = x;
			}
		}
	}

	/* +-1 with probability rho / 256 each half, else 0, as NFLlib's ZO_dist. */
	void set(nfl::ZO_dist const &m) {
		uint8_t rnd[Degree];

		nfl::fastrandombytes(rnd, sizeof(rnd));
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = rnd[i] <= m.rho ? ((rnd[i] & 2) ? MODULUS - 1 : 1) : 0;
		}
	}

	/* hwt coefficients +-1 at uniform positions, the others 0, as NFLlib's
	 * hwt_dist: reservoir sampling of the positions, then a sign each. */
	void set(nfl::hwt_dist const &m) {
		if (m.hwt == 0 || m.hwt > Degree) {
			throw std::runtime_error("zq: hwt_dist weight out of range");
		}
		std::vector<size_t> hit(m.hwt), rnd(m.hwt);
		std::iota(hit.begin(), hit.end(), 0U);
		auto ptr = rnd.end();
		for (size_t k = m.hwt; k < Degree; ++k) {
			size_t pos;
			const size_t lim = std::numeric_limits<size_t>::max() / k;
			for (;;) {
				if (ptr == rnd.end()) {
					nfl::fastrandombytes((unsigned char *) rnd.data(),
							rnd.size() * sizeof(size_t));
					ptr = rnd.begin();
				}
				pos = *ptr++;
				if (pos <= lim * k) {
					pos %= k;
					break;
				}
			}
			if (pos < m.hwt) {
				hit[pos] = k;
			}
		}
		std::memset(_data, 0, sizeof(_data));
		nfl::fastrandombytes((unsigned char *) rnd.data(),
				rnd.size() * sizeof(size_t));
		for (size_t j = 0; j < hit.size(); j++) {
			_data[hit[j]] = (rnd[j] & 2) ? 1 : MODULUS - 1;
		}
	}

	/* Negacyclic NTT, in place: coefficients to evaluations at the odd powers
	 * of psi, in bit-reversed order. */
	void ntt_pow_phi() {
		const ntt_tables<Degree> &t = ntt_tables<Degree>::get();
		size_t k = 1;
		for (size_t len = Degree / 2; len >= 1; len >>= 1) {
			for (size_t start = 0; start < Degree; start += 2 * len) {
				const u128 z = t.fwd[k++];
				for (size_t j = start; j < start + len; j++) {
					const u128 u = _data[j], v = mul(z, _data[j + len]);
					_data[j] = add(u, v);
					_data[j + len] = sub(u, v);
				}
			}
		}
	}

	void invntt_pow_invphi() {
		const ntt_tables<Degree> &t = ntt_tables<Degree>::get();
		for (size_t len = 1; len < Degree; len <<= 1) {
			/* Undo the forward butterflies of this level, block by block. */
			size_t k = Degree / (2 * len);
			for (size_t start = 0; start < Degree; start += 2 * len) {
				const u128 z = t.bwd[k++];
				for (size_t j = start; j < start + len; j++) {
					const u128 u = _data[j], v = _data[j + len];
					_data[j] = add(u, v);
					_data[j + len] = mul(z, sub(u, v));
				}
			}
		}
		for (size_t j = 0; j < Degree; j++) {
			_data[j] = mul(_data[j], t.ninv);
		}
	}

	/* The coefficients as integers in [0, q) (or values, in the NTT domain). */
	template <class A> void poly2mpz(A &out) const {
		for (size_t i = 0; i < Degree; i++) {
			const uint64_t w[2] = { (uint64_t) _data[i], (uint64_t) (_data[i] >> 64) };
			mpz_import(out[i], 2, -1, sizeof(uint64_t), 0, 0, w);
		}
	}

	/* From integers, reduced mod q (negative ones too). */
	template <class A> void mpz2poly(A const &in) {
		mpz_t r;
		mpz_init(r);
		for (size_t i = 0; i < Degree; i++) {
			uint64_t w[2] = { 0, 0 };
			mpz_mod(r, in[i], modulus_mpz());
			mpz_export(w, nullptr, -1, sizeof(uint64_t), 0, 0, r);
			_data[i] = (u128) w[0] | ((u128) w[1] << 64);
		}
		mpz_clear(r);
	}

	poly &operator+=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = add(_data[i], b._data[i]);
		}
		return *this;
	}
	poly &operator-=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = sub(_data[i], b._data[i]);
		}
		return *this;
	}
	poly &operator*=(poly const &b) {
		for (size_t i = 0; i < Degree; i++) {
			_data[i] = mul(_data[i], b._data[i]);
		}
		return *this;
	}
	friend poly operator+(poly a, poly const &b) {
		return a += b;
	}
	friend poly operator-(poly a, poly const &b) {
		return a -= b;
	}
	friend poly operator*(poly a, poly const &b) {
		return a *= b;
	}
	friend poly operator-(poly a) {
		for (size_t i = 0; i < Degree; i++) {
			a._data[i] = neg(a._data[i]);
		}
		return a;
	}
	/* Exact, unlike NFLlib's element-wise operator==. */
	friend bool operator==(poly const &a, poly const &b) {
		return std::memcmp(a._data, b._data, sizeof(a._data)) == 0;
	}
	friend bool operator!=(poly const &a, poly const &b) {
		return !(a == b);
	}

  private:
	alignas(32) value_type _data[Degree];
};

}	/* namespace zq */

#endif /* ZQ_HPP */
