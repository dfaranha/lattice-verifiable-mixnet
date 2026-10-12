/* ****************************** *
 * Implemented by Raymond K. ZHAO *
 *                                *
 * Integer samplers               *
 * ****************************** */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include "sample_z_small.h"
#include "param.h"
#include "fastrandombytes.h"
#include "poly.h"

#include <x86intrin.h>

using namespace nfl;

/* Box-Muller sampler precision: 53 bits */
#define FP_PRECISION 53
#define FP_FACTOR (1.0 / (1LL << FP_PRECISION))
#define FP_MASK ((1LL << FP_PRECISION) - 1)
#define BOX_MULLER_BYTES (8 * 2)

/* Constants used by COSAC */
static const double pi2 = 2 * M_PI;
static const double sqrt_pi2 = 2 / (M_SQRT1_2 * M_2_SQRTPI);

/* Parameters used by FACCT comparison */
#define COMP_ENTRY_SIZE 13
#define COSAC_EXP_MANTISSA_PRECISION 52
#define COSAC_EXP_MANTISSA_MASK ((1LL << COSAC_EXP_MANTISSA_PRECISION) - 1)
#define COSAC_R_MANTISSA_PRECISION (COSAC_EXP_MANTISSA_PRECISION + 1)
#define COSAC_R_MANTISSA_MASK ((1LL << COSAC_R_MANTISSA_PRECISION) - 1)
#define COSAC_R_EXPONENT_L (8 * COMP_ENTRY_SIZE - COSAC_R_MANTISSA_PRECISION)
#define COSAC_DOUBLE_ONE (0x3ffLL << 52)

#define DISCRETE_BYTES (2 * COMP_ENTRY_SIZE)

/* Constants used by FACCT */
#define CDT_ENTRY_SIZE 16
#define CDT_LOW_MASK 0x7fffffffffffffff
#define CDT_LENGTH 9 /* [0..tau*sigma]=[0..9] */

#define BERNOULLI_ENTRY_SIZE 9 /* 72bit randomness */

/* the closest integer k such that k*sigma_0=sigma */
#define BINARY_SAMPLER_K 125

/* -1/k^2 */
#define BINARY_SAMPLER_K_2_INV (-1.0/(BINARY_SAMPLER_K * BINARY_SAMPLER_K))

#define EXP_MANTISSA_PRECISION 52
#define EXP_MANTISSA_MASK ((1LL << EXP_MANTISSA_PRECISION) - 1)
#define R_MANTISSA_PRECISION (EXP_MANTISSA_PRECISION + 1)
#define R_MANTISSA_MASK ((1LL << R_MANTISSA_PRECISION) - 1)
#define R_EXPONENT_L (8 * BERNOULLI_ENTRY_SIZE - R_MANTISSA_PRECISION)

#define DOUBLE_ONE (1023LL << 52)

#define UNIFORM_SIZE 1
#define UNIFORM_REJ 62
#define BARRETT_BITSHIFT (UNIFORM_SIZE * 8)

#define BARRETT_FACTOR ((1LL << BARRETT_BITSHIFT) / BINARY_SAMPLER_K)
#define UNIFORM_Q (BINARY_SAMPLER_K * BARRETT_FACTOR)

#define BASE_TABLE_SIZE (4 * CDT_ENTRY_SIZE)
#define BERNOULLI_TABLE_SIZE (4 * BERNOULLI_ENTRY_SIZE)

/* CDT table */
static const __m256i V_CDT[][2] = {{{2200310400551559144, 2200310400551559144, 2200310400551559144, 2200310400551559144}, {3327841033070651387, 3327841033070651387, 3327841033070651387, 3327841033070651387}},
{{7912151619254726620, 7912151619254726620, 7912151619254726620, 7912151619254726620}, {380075531178589176, 380075531178589176, 380075531178589176, 380075531178589176}},
{{5167367257772081627, 5167367257772081627, 5167367257772081627, 5167367257772081627}, {11604843442081400, 11604843442081400, 11604843442081400, 11604843442081400}},
{{5081592746475748971, 5081592746475748971, 5081592746475748971, 5081592746475748971}, {90134450315532, 90134450315532, 90134450315532, 90134450315532}},
{{6522074513864805092, 6522074513864805092, 6522074513864805092, 6522074513864805092}, {175786317361, 175786317361, 175786317361, 175786317361}},
{{2579734681240182346, 2579734681240182346, 2579734681240182346, 2579734681240182346}, {85801740, 85801740, 85801740, 85801740}},
{{8175784047440310133, 8175784047440310133, 8175784047440310133, 8175784047440310133}, {10472, 10472, 10472, 10472}},
{{2947787991558061753, 2947787991558061753, 2947787991558061753, 2947787991558061753}, {0, 0, 0, 0}},
{{22489665999543, 22489665999543, 22489665999543, 22489665999543}, {0, 0, 0, 0}}};

static const __m256i V_CDT_LOW_MASK = {CDT_LOW_MASK, CDT_LOW_MASK, CDT_LOW_MASK, CDT_LOW_MASK};

static const __m256i V_K_K_K_K = {BINARY_SAMPLER_K, BINARY_SAMPLER_K, BINARY_SAMPLER_K, BINARY_SAMPLER_K};

/* coefficients of the exp evaluation polynomial */
static const __m256i EXP_COFF[] = {{0x3e833b70ffa2c5d4, 0x3e833b70ffa2c5d4, 0x3e833b70ffa2c5d4, 0x3e833b70ffa2c5d4},
								   {0x3eb4a480fda7e6e1, 0x3eb4a480fda7e6e1, 0x3eb4a480fda7e6e1, 0x3eb4a480fda7e6e1},
								   {0x3ef01b254493363f, 0x3ef01b254493363f, 0x3ef01b254493363f, 0x3ef01b254493363f},
								   {0x3f242e0e0aa273cc, 0x3f242e0e0aa273cc, 0x3f242e0e0aa273cc, 0x3f242e0e0aa273cc},
								   {0x3f55d8a2334ed31b, 0x3f55d8a2334ed31b, 0x3f55d8a2334ed31b, 0x3f55d8a2334ed31b},
								   {0x3f83b2aa56db0f1a, 0x3f83b2aa56db0f1a, 0x3f83b2aa56db0f1a, 0x3f83b2aa56db0f1a},
								   {0x3fac6b08e11fc57e, 0x3fac6b08e11fc57e, 0x3fac6b08e11fc57e, 0x3fac6b08e11fc57e},
								   {0x3fcebfbdff556072, 0x3fcebfbdff556072, 0x3fcebfbdff556072, 0x3fcebfbdff556072},
								   {0x3fe62e42fefa7fe6, 0x3fe62e42fefa7fe6, 0x3fe62e42fefa7fe6, 0x3fe62e42fefa7fe6},
								   {0x3ff0000000000000, 0x3ff0000000000000, 0x3ff0000000000000, 0x3ff0000000000000}};

static const __m256d V_INT64_DOUBLE = {0x0010000000000000, 0x0010000000000000, 0x0010000000000000, 0x0010000000000000};
static const __m256d V_DOUBLE_INT64 = {0x0018000000000000, 0x0018000000000000, 0x0018000000000000, 0x0018000000000000};

static const __m256i V_EXP_MANTISSA_MASK = {EXP_MANTISSA_MASK, EXP_MANTISSA_MASK, EXP_MANTISSA_MASK, EXP_MANTISSA_MASK};
static const __m256i V_RES_MANTISSA = {1LL << EXP_MANTISSA_PRECISION, 1LL << EXP_MANTISSA_PRECISION, 1LL << EXP_MANTISSA_PRECISION, 1LL << EXP_MANTISSA_PRECISION};
static const __m256i V_RES_EXPONENT = {R_EXPONENT_L - 1023 + 1, R_EXPONENT_L - 1023 + 1, R_EXPONENT_L - 1023 + 1, R_EXPONENT_L - 1023 + 1};
static const __m256i V_R_MANTISSA_MASK = {R_MANTISSA_MASK, R_MANTISSA_MASK, R_MANTISSA_MASK, R_MANTISSA_MASK};
static const __m256i V_1 = {1, 1, 1, 1};
static const __m256i V_DOUBLE_ONE = {DOUBLE_ONE, DOUBLE_ONE, DOUBLE_ONE, DOUBLE_ONE};

static const __m256d V_K_2_INV = {BINARY_SAMPLER_K_2_INV, BINARY_SAMPLER_K_2_INV, BINARY_SAMPLER_K_2_INV, BINARY_SAMPLER_K_2_INV};

static inline uint64_t load_40(const unsigned char *x)
{
	return ((uint64_t)(*x)) | (((uint64_t)(*(x + 1))) << 8) | (((uint64_t)(*(x + 2))) << 16) | (((uint64_t)(*(x + 3))) << 24) | (((uint64_t)(*(x + 4))) << 32);
}

static inline int64_t cosac_comp(const unsigned char *r, const double x)
{
	uint64_t res;
	uint64_t res_mantissa;
	uint64_t res_exponent;
	uint64_t r1;
	uint64_t r2;
	uint64_t r_mantissa;
	uint64_t r_exponent;

	/* x's bits; reading them through a uint64_t pointer breaks strict
	 * aliasing, which -O3 is entitled to miscompile. */
	memcpy(&res, &x, sizeof(res));
	res_mantissa = (res & COSAC_EXP_MANTISSA_MASK) | (1LL << COSAC_EXP_MANTISSA_PRECISION);
	res_exponent = COSAC_R_EXPONENT_L - 0x3ff + 1 + (res >> COSAC_EXP_MANTISSA_PRECISION);

	/* The caller passes r + i * COMP_ENTRY_SIZE, and COMP_ENTRY_SIZE is 13,
	 * so this pointer is not 8-byte aligned on every call. Dereferencing it
	 * as a uint64_t is undefined behaviour that UBSan reports; memcpy says
	 * the same thing legally and compiles to the same single load. */
	memcpy(&r1, r, sizeof(r1));
	r2 = load_40(r + 8);

	r_mantissa = r1 & COSAC_R_MANTISSA_MASK;
	r_exponent = (r1 >> COSAC_R_MANTISSA_PRECISION) | (r2 << (64 - COSAC_R_MANTISSA_PRECISION));

	return (res == COSAC_DOUBLE_ONE) || ((r_mantissa < res_mantissa) && (r_exponent < (1ULL << res_exponent)));
}

/* The sampler's randomness, drawn from fastrandombytes() 8 KiB at a time and
 * handed out from there: a sample takes two or three draws of 13 to 42 bytes,
 * and a draw that small costs several times as much a byte as a large one,
 * the AES stream doing a block of work per call however few bytes it returns.
 * The bytes are the same stream's, in the same order. The buffer is refilled
 * only from inside sample_z(), after its check that the stream is not keyed
 * with a public seed, so it never holds public bytes. */
#define SAMPLER_BUF 8192
static unsigned char sampler_buf[SAMPLER_BUF];
static size_t sampler_pos = SAMPLER_BUF;

static inline void sampler_bytes(unsigned char *out, size_t n)
{
	if (n > SAMPLER_BUF - sampler_pos) {
		size_t k = SAMPLER_BUF - sampler_pos;

		memcpy(out, sampler_buf + sampler_pos, k);
		out += k;
		n -= k;
		fastrandombytes(sampler_buf, SAMPLER_BUF);
		sampler_pos = 0;
	}
	memcpy(out, sampler_buf + sampler_pos, n);
	sampler_pos += n;
}

/* New COSAC sampler.
 * This is the sampling algorithm from:
 * Shuo Sun, Yongbin Zhou, Yunfeng Ji, Rui Zhang, & Yang Tao. (2021). Generic, Efficient and Isochronous Gaussian Sampling over the Integers.
 * https://eprint.iacr.org/2021/199 */
int64_t sample_z(const double center, const double sigma)
{
	unsigned char r[DISCRETE_BYTES];

	double c, cr, rc;
	double yr, rej;
	double sigma2;
	double yrc;

	uint64_t i;
	int64_t cmp1;
	uint64_t head = 2;

	unsigned char r_bm[BOX_MULLER_BYTES];

	double r1, r2;
	double norm[2];

	cr = round(center);
	c = center - cr;

	sigma2 = -sigma * sigma * 2;

	rc = exp(c * c / sigma2) / (sigma * sqrt_pi2);

	/* cosac_comp() is exact only for probabilities of at least
	 * 2^-(COSAC_R_EXPONENT_L + 1); below that it shifts by a negative amount,
	 * and this first comparison, which decides whether to return the center,
	 * goes wrong. rc is about 1 / (sigma sqrt(2 pi)), so that happens past
	 * sigma = 2^52 / sqrt(2 pi) = 1.8 * 10^15. The same flaw in a sampler with a 19-bit field made it
	 * return its center for most samples past sigma = 418000. */
	if (rc < ldexp(1.0, -(COSAC_R_EXPONENT_L + 1))) {
		fprintf(stderr, "sample_z: sigma = %g is beyond what the sampler supports\n", sigma);
		abort();
	}

	/* The samples are secret, and the global stream may be keyed with a
	 * public hash between deriving a challenge and reseeding. */
	if (fastrandombytes_is_public()) {
		fprintf(stderr, "sample_z: the stream is keyed with a public seed\n");
		abort();
	}

	sampler_bytes(r, COMP_ENTRY_SIZE);

	if (cosac_comp(r, rc))
	{
		return cr;
	}

	while (1)
	{
		sampler_bytes(r, DISCRETE_BYTES);

		for (i = 0; i < 2; i++, head++)
		{
			if (head >= 2)
			{
				head = 0;

				sampler_bytes((unsigned char *)r_bm, BOX_MULLER_BYTES);

				/* The uniforms come from r_bm, drawn for this purpose. They
				 * used to be read from r, whose bytes are also the coins of
				 * the acceptance tests below, so each deviate was correlated
				 * with its own acceptance: at sigma = 4 the samples came out
				 * 4.6 per cent too wide, with a chi-square of 13061 over 32
				 * bins against the exact distribution, 33 once read from
				 * r_bm. memcpy, since r_bm + 8 need not be aligned. */
				uint64_t u1, u2;
				memcpy(&u1, r_bm, sizeof(u1));
				memcpy(&u2, r_bm + 8, sizeof(u2));
				r1 = ((u1 & FP_MASK) + 1) * FP_FACTOR;
				r2 = ((u2 & FP_MASK) + 1) * FP_FACTOR;

				r1 = sqrt(-2 * log(r1)) * sigma;
				r2 = r2 * pi2;

				norm[0] = r1 * sin(r2);
				norm[1] = r1 * cos(r2);
			}

			yr = norm[head] + c;

			cmp1 = yr >= 0;

			yr = floor(yr) + cmp1;

			yrc = yr - c;
			rej = yrc + norm[head];
			yrc = yrc - norm[head];
			rej = exp(rej * yrc / sigma2);

			if (cosac_comp(r + i * COMP_ENTRY_SIZE, rej))
			{
				return yr + cr;
			}
		}
	}
}
