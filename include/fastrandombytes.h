/*
 * File:   lattisigns512-20130329/fastrandombytes.h
 * Author: Gim Güneysu, Tobias Oder, Thomas Pöppelmann, Peter Schwabe
 * Public Domain
 */

#ifndef FASTRANDOMBYTES_H
#define FASTRANDOMBYTES_H

namespace nfl {
/* Key the global stream with s. Every caller keys it with a public hash, to
 * derive challenges, and calls fastrandombytes_reseed() as soon as they are
 * drawn: until then the stream is predictable, and nothing secret may come
 * from it. */
void fastrandombytes_seed(const unsigned char *s);
/* Make the next draw rekey the stream from the operating system. */
void fastrandombytes_reseed();
/* Whether the stream is keyed with a caller's seed, so public: samplers of
 * secrets check it and refuse. */
int fastrandombytes_is_public();
void fastrandombytes(unsigned char *r, unsigned long long rlen);
}

#endif
