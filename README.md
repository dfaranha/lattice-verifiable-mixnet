# Lattice-based verifiable mix-net

[![CI](https://github.com/dfaranha/lattice-verifiable-mixnet/actions/workflows/ci.yml/badge.svg)](https://github.com/dfaranha/lattice-verifiable-mixnet/actions/workflows/ci.yml)

Code accompanying the paper "Verifiable Mix-Nets and Distributed Decryption for Voting from Lattice-Based Assumptions", accepted for publication at ACM CCS 2023.

Dependencies are the [NFLlib](https://github.com/quarkslab/NFLlib) and [FLINT](https://flintlib.org/doc/) libraries.
NFLlib is already included in this repository, but instructions for installing its dependencies can be found in the link above.
FLINT is usually included in package managers and can be easily installed in most systems out there. FLINT 3.1 or later is required: the code uses the `flint_rand_init()` family introduced in that release, and the `fmpz_mod_poly_{get,set}_coeff_mpz()` functions it used to call were removed in FLINT 3.5.
GMP, MPFR and MPC are also required, all of them available as packages (`libgmp-dev`, `libmpfr-dev` and `libmpc-dev` on Debian-based systems). MPC only provides the `mpc.h` header included by `poly.h`; no MPC symbol is linked.

The code is compiled as `gnu++17`. NFLlib predates C++20 and relies on `std::allocator<void>`, which that standard removed, so the language level is pinned in the `Makefile` rather than left to the compiler default.

### Building dependencies

To build NFLlib, run the following inside a cloned version of this repository:

```
$ mkdir deps
$ cd deps
$ cmake ../NFLlib -DCMAKE_BUILD_TYPE=Release -DNFL_OPTIMIZED=ON
$ make
$ make test
```

### Building and running the code

For building the actual code, run `make` inside the source directory. This will build the binaries for `bdlop`, `bgv`, `pismall`, `pibnd` and `shuffle` to test and benchmark different modules of the code.

The binaries respectively implement the BDLOP commitment scheme, the distributed BGV cryptosystem, the two zero-knowledge proofs and the shuffle itself. Tests and benchmarks are included for each of them, such that they can be used independently. Each binary exits non-zero if any of its tests failed, so a run can be checked without reading the output.

### Memory requirements

A `params::poly_q` occupies 64 KiB, and the proofs are dimensioned by parameters in the thousands, so some of these binaries are very memory-hungry. The large matrices are allocated on the heap at start-up rather than placed on the stack or in static storage: they are far too big for a stack frame, and keeping them out of static storage means the binaries build with the default code model and that AddressSanitizer can bounds-check them.

Peak resident memory at the parameters currently in the sources. Every buffer here is linear in its size parameter, so these come from measuring small instances and extrapolating; the `pibnd` formula reproduces a measured `TAU = 32, NTI = 16` run to within 0.3%.

| binary    | peak resident memory | grows by |
| --------- | -------------------- | -------- |
| `bdlop`   | ~10 MiB | fixed |
| `bgv`     | ~7 MiB | fixed |
| `shuffle` | ~2.6 GiB at `MSGS = 1000` | ~2.6 MiB per message |
| `pismall` | ~10 GiB at `TAU = 1024` | ~10 MiB per relation, mostly the `H[TAU][3][V]` codewords and the `v_{i,j}` coefficient arrays |
| `pibnd`   | ~8.5 GiB at `TAU = 1000`, `NTI = 130` | 64 KiB x (8 TAU + 10 NTI + TAU NTI), dominated by the `C[TAU][NTI]` challenge matrix |

Note that `pismall` defaults to `TAU = 1024` rather than the paper's 1000: its interpolation nodes are the `TAU`-th roots of unity, so `TAU` must be a power of two. The extra 24 relations are padded with zero witnesses and cost nothing in soundness.

Because the large buffers are heap-allocated, raising the stack limit is not needed.

These sizes are set by `MSGS` in `src/shuffle.cpp` and `TAU` (and `NTI`) in `src/pismall.cpp` and `src/pibnd.cpp`. Each can be overridden at build time, which is the easiest way to smoke-test the proofs on a machine that cannot hold the full instance:

```
$ make CONFIG="-DTAU=8 -DNTI=8" pibnd
$ make CONFIG=-DTAU=8 pismall
$ make CONFIG=-DMSGS=16 shuffle
```

Leave `CONFIG` empty to build the sizes used for the paper's benchmarks.

### Continuous integration

`.github/workflows/ci.yml` builds every binary and runs its tests on each push and pull request, at reduced parameters so that a run fits in a runner: `TAU = 8` for the proofs, `MSGS = 4` and `MSGS = 5` for the shuffle, the latter to cover the odd-`MSGS` branch in the prover. A second, non-blocking job repeats the smaller binaries under AddressSanitizer and UBSan.

The workflow builds FLINT from source and caches it, rather than installing it from `apt`: no current runner image ships a new enough version, since Ubuntu 22.04 packages FLINT 2.8.4 and 24.04 packages 3.0.1, both below the 3.1 this code requires.

__WARNING__: This is an academic proof of concept, and in particular has not received code review. This implementation is NOT ready for any type of production use.
