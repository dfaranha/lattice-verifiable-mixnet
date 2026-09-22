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
paper, taking `g(i) = i`: differences of distinct indices are non-zero integers
smaller than either prime of the basis, hence units, which is what the lemma
asks and which holds however far the ring splits. A second, independent hole found along the way — every
equality the verifier checked was NFLlib's element-wise `operator==`, true as
soon as the two sides agree in one of the 8192 NTT slots — was fixed on `main`
and is inherited here.

Lemma 5 also requires the committed permutation elements to lie in a set whose
differences are units, and the shuffle proves that with two sub-proofs over the
commitments to the `sigma_i`. `\Pi_SMALL` shows that each `sigma_i` is a ring
constant — every coefficient above the constant one is zero. That constraint is
*exact* over `Z_q`, unlike every other coefficient set in that file: `f = 0` has
a single root however `q` factors. `\Pi_BND` then bounds the norm of the
openings, and the two together give that every difference of committed constants
is a unit, by an argument that never has to name the set. A prover who CRT-mixes
the committed `sigma_i` as well as the messages is rejected.

One pass of the product argument is worth only `MSGS / p_min`, about `2^-34` at
`MSGS = 1000`, so it is repeated with independent challenges as many times as
`LEVEL` needs -- four or five at any supported size. The same repetitions cover
two weaknesses found afterwards. The challenge set of the linear proof is not
free of zero divisors in a ring splitting this far, so that proof is worth only
about `2^-44` per pass and has no soundness argument of its own; a `KNOWN GAP`
test exhibits a legal challenge that is a zero divisor. And the `SIZE` components
of each message are compressed into one with a vector `rho` before the proof
sees them, so an output list altered by any `Delta` with
`\sum_j rho_j Delta_j = 0` was accepted outright, `rho` having been sampled
rather than derived. It is now hashed from the commitments and the output
components, and drawn afresh in each pass.

**The modulus has moved from 78 to 88 bits**, because the slack bound feeding
the distributed-decryption budget drops a factor that the amortized proof's own
correctness analysis requires. The lattice estimator puts the BGV instance at `2^158` there and the
commitment's hiding at `2^156`, against `2^180` for the former at the paper's
modulus, so the ring degree stays at 4096. Binding turns out to need no
assumption at all at these dimensions: no two openings that short can differ.
See
[SOUNDNESS.md](SOUNDNESS.md) section 9.

**Read [SOUNDNESS.md](SOUNDNESS.md) before relying on any of this.** Two things
in particular. `\Pi_SMALL`'s *other* coefficient sets are not exact over `Z_q`,
where "ternary" means "ternary in each CRT component"; a `KNOWN GAP` test in
`pismall` exhibits a full-size element it accepts as ternary. That defect is not
in the path above, but it is real, and the argument below in fact relies on it.
And
reading the two sub-proofs as statements about a single opening of `P_i` takes
an argument, made in section 6.4 modulo each prime of the basis, which costs one
assumption the mix-net did not make before: MSIS modulo each `p_j` and not only
modulo their product.

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
| `shuffle` | ~13.8 GiB at `MSGS = 1000` | 13.9 MiB per message, measured at 8, 16, 32 and 64 and linear to within 1%; mostly the `LIN_REPS` responses of each linear proof |
| `pismall` | ~10 GiB at `TAU = 1024` | ~10 MiB per relation, mostly the `H[TAU][3][V]` codewords and the `v_{i,j}` coefficient arrays |
| `pibnd`   | ~700 MiB at `TAU = 1000`, `NTI = 130` | 64 KiB x (2 TAU V + 2 V NTI + R NTI + NTI), dominated by the witness and statement matrices; it was 8.5 GiB before the challenge matrix was streamed a row at a time |

The shuffle grew by about 40% in memory and 90% in prover time when the proof
of shuffle was fixed: the linear proof now relates three commitments instead of
two, so it carries a third masked opening, a third first message and a third
rejection-sampling test. Measured at `MSGS = 4`, the prover went from 578 to
1102 Mcycles and the verifier from 16.7 to 23.2 Mcycles. Most of the prover
cost is the extra rejection sampling, which multiplies the expected number of
restarts rather than adding to the work of one. That has since been recovered:
the three tests are batched into one over the concatenated vectors, which takes
a proof from 4.1 restarts on average to 1.0 and the `linear proof` benchmark
from 277 to 95 Mcycles. See SOUNDNESS.md section 9.1, which is also where the
rejection sampling itself was corrected.

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
