/*
 * What is left of NFLlib: the tags that select a sampler when a polynomial is
 * assigned, and its fast PRNG (src/fastrandombytes.cpp, AES-256 in counter
 * mode). Both keep NFLlib's names so that the callers did not have to change.
 * The tags are NFLlib's own definitions (NFLlib/include/nfl/poly.hpp).
 */
#ifndef NFL_HPP
#define NFL_HPP

#include <cstdint>
#include "fastrandombytes.h"

namespace nfl {

struct uniform {};

struct hwt_dist { // hamming weight distribution.
	uint32_t hwt;
	hwt_dist(uint32_t hwt_) : hwt(hwt_) {}
};

struct ZO_dist { // zero distribution.
	uint8_t rho; // P(1) = P(-1) = (rho/0xFF)/2, P(0) = 1 - P(1) - P(-1)
	ZO_dist(uint8_t rho_ = 0x7F) : rho(rho_) {}
};

}

#endif
