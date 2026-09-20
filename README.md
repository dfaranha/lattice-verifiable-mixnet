# Lattice-based verifiable mix-net

Code accompanying the paper "Verifiable Mix-Nets and Distributed Decryption for Voting from Lattice-Based Assumptions", accepted for publication at ACM CCS 2023.

Dependencies are the [NFLlib](https://github.com/quarkslab/NFLlib) and [FLINT](https://flintlib.org/doc/) libraries.
NFLlib is already included in this repository, but instructions for installing its dependencies can be found in the link above.
FLINT is usually included in package managers and can be easily installed in most systems out there. FLINT 3.1 or later is required: the code uses the `flint_rand_init()` family introduced in that release, and the `fmpz_mod_poly_{get,set}_coeff_mpz()` functions it used to call were removed in FLINT 3.5.

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

The binaries respectively implement the BDLOP commitment scheme, the distributed BGV cryptosystem, the two zero-knowledge proofs and the shuffle itself. Tests and benchmarks are included for each of them, such that they can be used independently.

### Memory requirements

A `params::poly_q` occupies 64 KiB, and the proofs are dimensioned by parameters in the thousands, so some of these binaries are very memory-hungry. The large matrices are allocated on the heap at start-up rather than placed on the stack or in static storage: they are far too big for a stack frame, and keeping them out of static storage means the binaries build with the default code model and that AddressSanitizer can bounds-check them.

Approximate resident memory at the parameters currently in the sources:

| binary    | resident memory | notes                                    |
| --------- | ----------- | -------------------------------------------- |
| `bdlop`   | negligible  |                                               |
| `bgv`     | negligible  |                                               |
| `shuffle` | scales with `MSGS` | ~1 GiB at `MSGS = 1000`               |
| `pismall` | several GiB | `TAU = 1000`                                  |
| `pibnd`   | ~9 GiB      | dominated by the `C[TAU][NTI]` challenge matrix |

Because the large buffers are heap-allocated, raising the stack limit is not needed.

These sizes are set by `MSGS` in `src/shuffle.cpp` and `TAU` (and `NTI`) in `src/pismall.cpp` and `src/pibnd.cpp`. Each can be overridden at build time, which is the easiest way to smoke-test the proofs on a machine that cannot hold the full instance:

```
$ make CONFIG="-DTAU=8 -DNTI=8" pibnd
$ make CONFIG=-DTAU=8 pismall
$ make CONFIG=-DMSGS=16 shuffle
```

Leave `CONFIG` empty to build the sizes used for the paper's benchmarks.

__WARNING__: This is an academic proof of concept, and in particular has not received code review. This implementation is NOT ready for any type of production use.
