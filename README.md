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
smaller than `q`, hence units, which is what the lemma asks and which holds
however far the ring splits. A second, independent hole found along the way — every
equality the verifier checked was NFLlib's element-wise `operator==`, true as
soon as the two sides agree in one of the 8192 NTT slots — was fixed on `main`
and is inherited here.

**This is the `single-prime` branch**: `q` is the prime
`2^88 - 25 * 2^16 + 1` rather than the product of two 44-bit NFLlib primes,
and [SOUNDNESS.md](SOUNDNESS.md) section 0 says what that changes. NFLlib cannot
hold an 88-bit prime, so `include/zq.hpp` replaces it, with one 128-bit word a
coefficient, and the plaintext ring is a `zq` polynomial as well: this branch no
longer depends on NFLlib. What it kept of it is the sampler tags (`include/nfl.hpp`)
and the AES-256-CTR generator (`src/fastrandombytes.cpp`).

Lemma 5 also requires the committed permutation elements to lie in a set whose
differences are units. `\Pi_SMALL` shows that each `sigma_i` is a ring
constant -- every coefficient above the constant one is zero -- and over a
prime `q` that is enough: two distinct constants differ by a unit, and a
constant is the same value in every NTT slot, so every slot reads off the same
permutation. A prover who mixes the slots of the committed `sigma_i` as well as
the messages is rejected, since the result is not a constant. With a composite
`q` a second sub-proof, `\Pi_BND`, had to bound the norm of the openings as
well; it is kept as `CONFIG=-DSHUFFLE_PIBND=1`.

One pass of the product argument is worth `MSGS / q`, about `2^-77` at
`MSGS = 1000`, so it is run twice with challenges bound across the passes. The
same two passes cover the compression of the `SIZE` components of each message
by a vector `rho`, which is hashed from the commitments and the output
components and drawn afresh in each pass. The linear proof's challenges are
sparse ternary differences, and nothing proves those invertible in a ring that
splits all the way, as an NTT needs; each is taken to be worth about `1 / q`,
which no known zero divisor contradicts, and the proof is repeated twice against
challenges bound to each other.

**The modulus is 88 bits rather than the paper's 78**, because the slack bound
feeding the distributed-decryption budget drops a factor that the amortized
proof's own correctness analysis requires. The lattice estimator puts the BGV
instance at `2^158` there and the commitment's hiding at `2^156`, against
`2^180` for the former at the paper's modulus, so the ring degree stays at
4096. Binding turns out to need no assumption at all at these dimensions: no
two openings that short can differ. See [SOUNDNESS.md](SOUNDNESS.md) section 9.

**Read [SOUNDNESS.md](SOUNDNESS.md) before relying on any of this**, starting
with section 0; sections 1 to 12 were written for the composite modulus.

The only library dependency beyond GMP and MPFR is [FLINT](https://flintlib.org/doc/); unlike the other branches, this one does not use NFLlib.
FLINT is usually included in package managers and can be easily installed in most systems out there. FLINT 3.1 or later is required: the code uses the `flint_rand_init()` family introduced in that release, and the `fmpz_mod_poly_{get,set}_coeff_mpz()` functions it used to call were removed in FLINT 3.5.
GMP, MPFR and MPC are also required, all of them available as packages (`libgmp-dev`, `libmpfr-dev` and `libmpc-dev` on Debian-based systems). MPC only provides the `mpc.h` header included by `poly.h`; no MPC symbol is linked.
The voters' ballot proofs use [LaZer](https://github.com/lazer-crypto/lazer), the submodule `third_party/lazer` (branch `skip-zeros` of [this fork](https://github.com/dfaranha/lazer), with fixes and speed-ups); fetch it with `git submodule update --init third_party/lazer`. The first `make` of `voting` builds it, HEXL included.

The code is compiled as `gnu++17`, pinned in the `Makefile`: the GNU dialect is needed for the `Q` suffix on the `__float128` literals in `param.h`. The generator uses AES-NI, which `-march=native` enables on any x86-64 processor that has it.

### Building and running the code

For building the actual code, run `make` inside the source directory. This will build the binaries for `bdlop`, `bgv`, `pismall`, `pibnd` and `shuffle` to test and benchmark different modules of the code, and `voting`, which runs the mix-net end to end.

The binaries respectively implement the BDLOP commitment scheme, the distributed BGV cryptosystem, the two zero-knowledge proofs and the shuffle itself. Tests and benchmarks are included for each of them, such that they can be used independently. Each binary exits non-zero if any of its tests failed, so a run can be checked without reading the output.

`voting` puts them together, with `MSGS` voters, 4 mix servers and `PARTIES`
trustees: the trustees share a BGV key; each voter encrypts a vote for one of 8
candidates and proves the ballot well formed, which the board checks (below);
each mix server in turn re-encrypts every ciphertext with a fresh
encryption of zero, commits to that encryption of zero and adds the input into
the commitment, which makes it a commitment to the re-encryption, and publishes
the re-encryptions permuted with a proof of shuffle over those commitments; and
the trustees' partial decryptions of the last list are combined and tallied. It
also checks that a ballot proof moved to another voter or kept for a changed
ciphertext is rejected, that a ballot for two candidates cannot be proven, and
that a mix server that changes an output, or replaces a ballot with one of its
own, is rejected. What this branch does not implement is not in it: the proof
that each re-encryption adds an encryption of zero with short randomness, and
the trustees' proofs of correct decryption.
The election size is the build-time `MSGS`: `make CONFIG=-DMSGS=25 voting` runs
the same election as the `voting` of lattice-voting-ctrsa21, 25 voters and 8
candidates, in about four and a half minutes, three of them the ballot proofs,
and half a GiB; at `MSGS = 4` it
takes about a minute. `-DNCAND=<n>` sets the number of candidates and
`-DMIXERS=<n>` the number of mix servers.

The ballot proof (`src/ballot_proof.c`) shows, with LaZer's linear proofs, that
(u, v) = (ar + 2e1, br + 2e2 + m) with r, e1, e2 ternary and short and
m = X^j or 0: one vote or none. It proves m binary and equal to a u' with
||u'|| <= 1, which leaves only those. It is bound to the election and the
voter, so it cannot be copied to another voter's ballot. LaZer lifts the
statement, over R_q of degree 4096 and the 88-bit q, to its ring of degree 64
and a 115-bit proof modulus; `lazer/ballot.py` describes it, and
`lazer/ballot.h` is generated from it, from `third_party/lazer/scripts`, with
`sage lin-codegen.sage ../../../lazer/ballot.py > ../../../lazer/ballot.h`.
LaZer's default target, a root Hermite factor of 1.0044, is about 102 bits
core-SVP under the lattice-estimator, so the file asks for 1.0036: MLWE 134.9
and MSIS 136.1 bits, knowledge error 2^-127. The proof is about 82 KiB, and
takes about 4.4 s to prove and 3.0 s to check on a laptop: the degree and the
width of q make it the slowest of the codebases' ballot proofs.

### Memory requirements

A `params::poly_q` occupies 64 KiB, and the proofs are dimensioned by parameters in the thousands, so some of these binaries are very memory-hungry. The large matrices are allocated on the heap at start-up rather than placed on the stack or in static storage: they are far too big for a stack frame, and keeping them out of static storage means the binaries build with the default code model and that AddressSanitizer can bounds-check them.

Peak resident memory at the parameters currently in the sources. Every buffer here is linear in its size parameter, so these come from measuring small instances and extrapolating; the `pibnd` formula reproduces a measured `TAU = 32, NTI = 16` run to within 0.3%.

| binary    | peak resident memory | grows by |
| --------- | -------------------- | -------- |
| `bdlop`   | ~10 MiB | fixed |
| `bgv`     | ~7 MiB | fixed |
| `shuffle` | ~13.8 GiB at `MSGS = 1000` | 13.9 MiB per message, measured at 8, 16, 32 and 64 and linear to within 1%; mostly the `LIN_REPS` responses of each linear proof |
| `pismall` | ~10 GiB at `TAU = 1024` | ~10 MiB per relation, mostly the `H[TAU][3][V]` codewords and the `v_{i,j}` coefficient arrays |
| `pibnd`   | ~700 MiB at `TAU = 1000`, `NTI = 130` | 64 KiB x (2 TAU V + 2 V NTI + R NTI), dominated by the witness and statement matrices; it was 8.5 GiB before the challenge matrix was streamed a row at a time, and the row itself is now NTI bytes rather than NTI ring elements |

The shuffle grew by about 40% in memory and 90% in prover time when the proof
of shuffle was fixed: the linear proof relates three commitments instead of two,
so it carries a third masked opening. Measured at `MSGS = 4`, the prover went
from 578 to 1102 Mcycles and the verifier from 16.7 to 23.2 Mcycles at that
point.

Most of the prover's cost there is rejection sampling, which multiplies the
expected number of restarts rather than adding to the work of one, and the
structure around it has changed twice since. All of a proof's openings are now
masked and tested as one batch rather than three, and its first messages are not
sent at all -- the verifier rebuilds them -- which is what paid for running each
linear proof `LIN_REPS` times against challenges bound to one another. A proof
now takes about 1.7 restarts, and the benchmarks at `MSGS = 4` read 348 Mcycles
for `linear proof`, 70 for `linear verifier` and 20.9 Gcycles for
`shuffle-proof`. See SOUNDNESS.md sections 7.1 and 8.1.

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

`.github/workflows/ci.yml` builds every binary and runs its tests on each push and pull request, at reduced parameters so that a run fits in a runner: `TAU = 8` for the proofs, `MSGS = 4` and `MSGS = 5` for the shuffle and `voting`, the latter to cover the odd-`MSGS` branch in the prover. A second, non-blocking job repeats the smaller binaries and the shuffle under AddressSanitizer and UBSan.

The workflow builds FLINT from source and caches it, rather than installing it from `apt`: no current runner image ships a new enough version, since Ubuntu 22.04 packages FLINT 2.8.4 and 24.04 packages 3.0.1, both below the 3.1 this code requires.

__WARNING__: This is an academic proof of concept, and in particular has not
received code review. This implementation is NOT ready for any type of
production use, in particular because the linear proof's soundness rests on the
heuristic described above and in [SOUNDNESS.md](SOUNDNESS.md).
