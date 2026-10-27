#include <cstddef>

#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <memory>
#include <nfl.hpp>
#include "zq.hpp"

#include "bench.h"
#include <sys/random.h>

using namespace std;

#ifndef COMMON_H
#define COMMON_H

/* Weight of each of the two ternary vectors a challenge is the difference of.
 * The paper takes 36, which is what its sigma_C is priced from. Nothing here
 * needs it that large: SOUNDNESS.md section 7 shows the linear proof is worth
 * about 1 / q whatever the challenge set is, since nothing makes the
 * differences invertible in a fully split ring, so the set only has to be too
 * big to guess -- at 9 it has more than 2^98 elements against the 2^87 that
 * would matter. What the weight does buy is the size of what the masking has
 * to cover, ||beta r|| growing as its square root, and so SIGMA_C and every
 * published response with it. */
#define NONZERO     9
/* Security level to attain. */
#define LEVEL       128
/* The \infty-norm bound of certain elements. */
#define BETA 	    1
/* Width k of the comming matrix. */
#define WIDTH 	    4
/* Height of the commitment matrix. */
#define HEIGHT 	    1
/* Dimension of the committed messages. */
#ifndef SIZE
#define SIZE        2
#endif
/* Number of messages being shuffled. This drives every large buffer of the
 * proof of shuffle, so it can be overridden (e.g. make CONFIG=-DMSGS=16) to
 * test on a small machine; the paper's benchmarks use 1000. It lives here
 * rather than in shuffle.cpp because pismall.cpp, which carries the membership
 * sub-proof, is amortized over exactly these MSGS relations. */
#ifndef MSGS
#define MSGS        2
#endif
/* Large modulus. Not named here: it is params::poly_q::moduli_product(), the
 * prime q = 2^88 - 25 2^16 + 1 of include/zq.hpp. q = 1 mod 2^16, so it is
 * 1 mod 2N as Table 1 requires and Z_q supports the length-16384 NTT the AEx
 * encoding needs. 5 is a non-residue, which keeps Y^2 - 5 irreducible and so
 * lets pismall draw its challenges from the quadratic extension; see AEX_NR
 * there. */
/* Small modulus. */
#define PRIMEP      2
/* Degree of the irreducible polynomial. */
#define DEGREE      4096
/* Sigma for the commitment gaussian distribution. The rejection sampling of
 * SOUNDNESS.md 8.1 takes its M from the norm it is masking, so no value here is
 * invalid and this is a trade of proof size against restarts: ||beta r|| is
 * about 380 at NONZERO = 9, the batch of 3 LIN_REPS times 3 openings is about
 * 1150, and 2^11 leaves M near 1.2 and acceptance near 0.4, which is where 2^12
 * left it at the old weight of 36. Each published coefficient costs
 * log2(6 SIGMA_C) bits, so this is a bit a coefficient off every response. */
#define SIGMA_C     (1u << 11)
/* Parties that run the distributed decryption protocol. */
#define PARTIES     4
/* Security level for Distributed Decryption. */
#define BGVSEC      40
/* Bound for Distributed Decryption: 2^BGVSEC * (B_Dec / (p * xi)), the paper's
 * smudging bound. It must stay below q/(2p), so it is tied to q and had to be
 * recomputed when the ring moved from 124 to 78 bits. */
#define BOUND_D     "11260098580054016"

namespace params {
    using poly_p = nfl::poly_from_modulus<uint32_t, DEGREE, 30>;
    /* One 88-bit prime, q = 2^88 - 25 * 2^16 + 1 (include/zq.hpp), so R_q
     * has no zero divisors from a split modulus. The paper analyses 78, but
     * its bound on the slack of Pi_BND drops a factor that proof's own
     * correctness analysis requires, and with it restored 2^78 is about five
     * bits short of B_Dec + B_DDec < q/2; see SOUNDNESS.md section 8. A
     * coefficient is 16 bytes, so a ring element is the same 64 KiB it was. */
    using poly_q = zq::poly<DEGREE>;
    using poly_big = zq::poly<4 * DEGREE>;
}

/* The hashes in shuffle.cpp, pismall.cpp and pibnd.cpp absorb a ring element as
 * 16 * DEGREE bytes, at 38 call sites. That is the whole element only while a
 * coefficient is 16 bytes, two 64-bit residues under NFLlib and one
 * unsigned __int128 under zq; with any other layout every challenge would
 * leave part of each element out, which is the bug ntru_voting_impl's
 * SOUNDNESS.md records three times. */
static_assert(16 * DEGREE == sizeof(params::poly_q::value_type) *
              params::poly_q::nmoduli * params::poly_q::degree,
              "the hashes absorb 16 * DEGREE bytes a ring element");

/*============================================================================*/
/* Type definitions                                                           */
/*============================================================================*/

/* Class that represents a commitment key pair. */
class comkey_t {
    public:
       params::poly_q A1[HEIGHT][WIDTH - HEIGHT];
       params::poly_q A2[SIZE][WIDTH];
};

/* Class that represents a commitment in CRT representation. */
class commit_t {
    public:
      params::poly_q c1;
      vector<params::poly_q> c2;
};

/* Class that represents a BGV key pair. */
class bgvkey_t {
    public:
       params::poly_q a;
       params::poly_q b;
};

class bgvenc_t {
    public:
       params::poly_q u;
       params::poly_q v;
};

#include "util.hpp"

void bdlop_sample_rand(vector<params::poly_q>& r);
void bdlop_sample_chal(params::poly_q& f);
bool bdlop_test_norm(params::poly_q r, uint64_t sigma_sqr);
void bdlop_commit(commit_t& com, vector<params::poly_q> m, comkey_t& key, vector<params::poly_q> r);
int  bdlop_open(commit_t& com, vector<params::poly_q> m, comkey_t& key, vector<params::poly_q> r, params::poly_q& f);
void bdlop_keygen(comkey_t& key);

void bgv_sample_message(params::poly_p& r);
void bgv_sample_short(params::poly_q& r);
void bgv_keygen(bgvkey_t& pk, params::poly_q& sk);
void bgv_encrypt(bgvenc_t &c, bgvkey_t& pk, params::poly_p& m);
void bgv_encrypt_rand(bgvenc_t &c, bgvkey_t& pk, params::poly_p& m,
		params::poly_q& r, params::poly_q& e1, params::poly_q& e2);
void bgv_decrypt(params::poly_p& m, bgvenc_t& c, params::poly_q & sk);

#endif
