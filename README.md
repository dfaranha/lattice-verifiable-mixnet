# Lattice-based verifiable mix-net

[![CI](https://github.com/dfaranha/lattice-verifiable-mixnet/actions/workflows/ci.yml/badge.svg)](https://github.com/dfaranha/lattice-verifiable-mixnet/actions/workflows/ci.yml)

Code accompanying the paper "Verifiable Mix-Nets and Distributed Decryption for Voting from Lattice-Based Assumptions", accepted for publication at ACM CCS 2023.

### Soundness: this branch carries a partial fix

Bootle, Lyubashevsky and Merino-Gallardo, ["Efficient Verifiable Mixnets from
Lattices, Revisited"](https://eprint.iacr.org/2025/658), showed that the proof
of shuffle of Aranha, Baum, Gjøsteen, Silde and Tunge (CT-RSA 2021), which this
mix-net extends, is not sound: Neff's product identity does not imply a
permutation over a ring that is not a field, only a permutation inside each CRT
component, and the components need not agree.

The `fix-pkc` branch replaces that product with the one from Lemma 5 of their
paper, taking the set `D` to be the monomials `x^i`, which is one of the few
legal choices in the fully splitting ring NFLlib gives us. A second, independent hole found along the way — every
equality the verifier checked was NFLlib's element-wise `operator==`, true as
soon as the two sides agree in one of the 8192 NTT slots — was fixed on `main`
and is inherited here.

**The fix is deliberately incomplete.** Lemma 5 also requires the committed
permutation elements to lie in `D`, and proving that needs machinery this
repository does not have. A prover who CRT-mixes the committed `sigma_i`, and
not only the messages, is still accepted; the test named `KNOWN GAP` asserts
that, so it turns red the day a membership sub-proof is added. Read
[SOUNDNESS.md](SOUNDNESS.md) before relying on any of this: it explains what is
fixed, what is not, why the norm-based shortcut used for the CT-RSA 2021 code
cannot be reused here, and the three ways the gap could be closed.

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
| `shuffle` | ~3.7 GiB at `MSGS = 1000` | ~3.75 MiB per message |
| `pismall` | ~10 GiB at `TAU = 1024` | ~10 MiB per relation, mostly the `H[TAU][3][V]` codewords and the `v_{i,j}` coefficient arrays |
| `pibnd`   | ~8.5 GiB at `TAU = 1000`, `NTI = 130` | 64 KiB x (8 TAU + 10 NTI + TAU NTI), dominated by the `C[TAU][NTI]` challenge matrix |

The shuffle grew by about 40% in memory and 90% in prover time when the proof
of shuffle was fixed: the linear proof now relates three commitments instead of
two, so it carries a third masked opening, a third first message and a third
rejection-sampling test. Measured at `MSGS = 4`, the prover went from 578 to
1102 Mcycles and the verifier from 16.7 to 23.2 Mcycles. Most of the prover
cost is the extra rejection sampling, which multiplies the expected number of
restarts rather than adding to the work of one; batching the three tests into a
single one over the concatenated vectors would recover much of it.

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

`.github/workflows/ci.yml` builds every binary and runs its tests on each push and pull request, at reduced parameters so that a run fits in a runner: `TAU = 8` for the proofs, `MSGS = 4` and `MSGS = 5` for the shuffle, the latter to cover the odd-`MSGS` branch in the prover. A second, non-blocking job repeats the smaller binaries and the shuffle under AddressSanitizer and UBSan.

The workflow builds FLINT from source and caches it, rather than installing it from `apt`: no current runner image ships a new enough version, since Ubuntu 22.04 packages FLINT 2.8.4 and 24.04 packages 3.0.1, both below the 3.1 this code requires.

__WARNING__: This is an academic proof of concept, and in particular has not
received code review. This implementation is NOT ready for any type of
production use, in particular because of the soundness gap described above and
in [SOUNDNESS.md](SOUNDNESS.md).
