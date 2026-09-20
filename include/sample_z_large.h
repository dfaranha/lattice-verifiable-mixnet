/* ****************************** *
 * Implemented by Raymond K. ZHAO *
 *                                *
 * Integer samplers               *
 * ****************************** */

#ifndef _SAMPLE_Z_LARGE_H
#define _SAMPLE_Z_LARGE_H

#include "poly.h"

/* Returns __int128, not int64_t: sigma-hat_ANEx runs well past 2^64, whose
 * samples do not fit. The sampler already computes in __float128, so only the
 * conversion on return was truncating. */
__int128 sample_z(const __float128 center, const __float128 sigma);
void sample_e(POLY_64 *out);
void sample_0z(POLY_64 *sample);

#endif
