# Soundness of the proof of shuffle on this branch

## Status of this document

This is a **draft argument, not a reviewed result.** It records what the
`fix-pkc` branch changes in `src/shuffle.cpp`, why those changes are believed
to be necessary and sufficient against the published attack, and — just as
importantly — **the assumptions it rests on.** Sections 5 and 7 are the parts to
read before trusting anything here: section 5.2 reports a defect in `Pi_SMALL`
itself, not only in the proof of shuffle, section 5.4 closes the argument at the
cost of assuming MSIS modulo each prime of the RNS basis and not only modulo
their product, and section 7 reports that the challenge set of the linear proof
contains zero divisors, so that proof has no soundness argument of its own and
is carried by the repetitions of section 6. Section 9 reports the one term the
repetitions do not reach, the compression of the message components by `rho`,
which stood at `2^-39` until `rho` was made a per-pass challenge. Section 12
records what the figures here were checked against, and what has not been run.
Section 7 also
reports, and repairs, a challenge set of `Pi_BND` that belonged to neither
instantiation of the amortized proof; Section 8 reports that `sigma_Bnd` is
about six bits wider than it now needs to be as a result, and why only two of
them can be spent on `q`; and Section 8.1 reports, and restores, a
rejection-sampling step dropped from the linear proof in 2023, without which
that proof was not the zero-knowledge one its parameters describe. The test
suite asserts the three defects of sections 5.2, 7 and 9, and the inequality
5.4 depends on, rather than hiding, any of them.

**Section 6.1 is the one to read first.** It reports that the `SHUFFLE_REPS`
passes were not bound to each other under Fiat-Shamir, so their errors did not
multiply: a prover ground them one at a time, and the protocol's soundness
against the attack of Section 1 was one pass — about `2^34` hash queries — and
not the `2^-136` every other number in this document assumes. The two outer
layers of it are now repaired, by making the commitments to the `sigma_i` a
first message shared by every pass — which also took 14% off the proof and a
factor of 6.5 off the prover — and by drawing every pass's `beta` from one hash
of every pass's `D_i`. The innermost one is open: the `MSGS * SHUFFLE_REPS`
instances of `Pi_LIN` still carry their own challenges, which holds the
protocol at about `2^46`. Section 7.1 prices the ways out of that and records
the one taken, repeating each linear proof against challenges bound to each
other, which closes the layer at `2^-134` and takes 13% off the proof into the
bargain. With that the numbers in sections 6, 7 and 9 are what the protocol is
worth rather than what it would be.

## 1. The attack

Bootle, Lyubashevsky and Merino-Gallardo, *Efficient Verifiable Mixnets from
Lattices, Revisited* (ePrint 2025/658), show that the proof of shuffle of
Aranha, Baum, Gjøsteen, Silde and Tunge (CT-RSA 2021), which the mix-net of
this repository extends, is not sound. The proof follows Neff and rests on

```
prod_{i=1..N} (a_i - X) = prod_{i=1..N} (b_i - X)      ==>   (a_i) ~P (b_i)     (*)
```

which holds over a field, because `F[X]` is then a unique factorization domain.
Over `R_q = Z_q[x]/(x^N + 1)` it does not. By the CRT, `R_q` is a product of
fields, `(*)` holds component by component, and the permutations obtained in
the different components need not agree. A prover can therefore output a list
that is a permutation of the input *inside each CRT component* while not being
a permutation over `R_q`, and the proof still verifies. In the voting
application this lets a mixing server mangle ballots undetectably.

Two remarks specific to this implementation.

* The product actually proven by `shuffle.cpp` before this branch was
  `prod a_i = prod b_i`, with no evaluation point at all — weaker still than
  `(*)`, which at least evaluates at a challenge. The identity of Section 3
  reinstates one.
* The gap is not narrow here, it is total. See the next section.

## 2. The ring

| symbol | meaning | value |
| --- | --- | --- |
| `N` | ring degree (`DEGREE`) | 4096 |
| `q` | modulus, `p_1 * p_2` | 88 bits, was 78; see Section 8 |
| `p_1, p_2` | RNS basis, of the form `2^44 - i * 2^21 + 1` | 17592167170049, 17592123129857 |
| `k` | number of CRT factors of `x^N + 1` | **2N = 8192** |

NFLlib needs an NTT-friendly modulus, so every prime of the basis is `1 mod 2N`
and `x^N + 1` splits into linear factors modulo each of them:
`R_q ~= Z_{p_1}^N x Z_{p_2}^N`, 8192 slots. `poly_inverse` in `shuffle.cpp`
already works this way, inverting slot by slot.

This is what separates this code from the two other implementations affected by
the attack. Both of their fixes rest on [42, Corollary 1.2], which says that an
element of `l_2`-norm below `q^(1/k)` is invertible in a ring splitting into `k`
factors. At `k = 2` that bound is roughly `q^(1/2)` and is useful. At
`k = 2N` it says nothing at all.

## 3. The fix: Lemma 5 with g(i) = i

Lemma 5 of ePrint 2025/658 replaces `(*)` with

```
prod (a_i + g(i) * X1 - X2) = prod (b_i + sigma_i * X1 - X2)                    (**)
```

where `g : [N] -> D` is injective, `D` is a set whose pairwise differences are
invertible, and `sigma_i in D` is committed before `X1, X2` are drawn. Tying
each message to its index forces the per-component permutations to agree.

**What `D` can be.** In `R_q ~= prod_{s=1}^{8192} F_s`, an element is a unit
exactly when it is non-zero in every slot, so `d - d'` invertible for distinct
`d, d' in D` says: **the projection of `D` to every single slot is injective.**
`D` is therefore a diagonal-like set, and `|D| <= p_min`, which at `2^44` is
never the binding constraint. The choice of `D` is not about arranging
invertibility, which is easy; it is about which admissible `D` has a
characterisation a proof system can express.

**Choice of D.** We take `g(i) = i`, the ring constant with that value. A
difference of distinct `g(i)` is a non-zero integer below `MSGS`, hence smaller
than either prime of the basis, hence coprime to `q` and a unit. The test
`scalar differences are invertible` checks this. The bound is `MSGS < p_min`,
about `2^44`, rather than the ring degree — an earlier version of this branch
used `D = {x^i}` with `g(i) = x^i`, which is also admissible but capped `MSGS`
at `N = 4096` and, more importantly, had a far more awkward membership proof;
Section 5 explains why the constants win.

The two sets used elsewhere are **not** available here:

* *Binary polynomials*, the choice of Protocol 1 of ePrint 2025/658. Their
  differences are ternary, which is short, and shortness gives nothing at
  `k = 2N`. The test `a short polynomial can be a zero divisor` exhibits a 0/1
  polynomial of Hamming weight 19 and `l_infinity`-norm 1 that is a zero
  divisor in this exact ring. It was found by meet-in-the-middle over subset
  sums of the powers of one primitive `2N`-th root modulo `p_1`, in seconds on
  a laptop.
* *A ball of small norm*, the choice of the `fix-pkc` branch of the CT-RSA 2021
  code. Same objection, for the same reason.

Note what separates those from the constants. Shortness certifies nothing about
a general ring element here — that is exactly what the weight-22 zero divisor
says. It does certify something about a *constant*, because a short constant is
a small integer and small integers are coprime to `q`. The encoding works
because it never asks shortness to do a job the splitting ring forbids.

**Protocol changes.** In `shuffle.cpp`:

1. The prover commits to `sigma_i` in `P_i` with fresh randomness, as its first
   message.
2. `tau` (`X1`) and `mu` (`X2`) are derived by hashing the input commitments,
   the `P_i`, the output list and `rho` (`shuffle_chal_hash`). Deriving them
   from a transcript that contains the `P_i` is what pins the `sigma_i` down
   before the challenges, as the lemma requires.
3. The factors become `a_i = m_i + g(i) tau - mu` and
   `b_i = _m_i + sigma_i tau - mu`, and the telescoping product argument runs
   on those instead of on `m_i` and `_m_i`.
4. `b_i` is no longer public: it has a committed part. The linear proof
   therefore relates **three** commitments instead of two, proving
   `coef[0] * <msg of x> + coef[1] * <msg of p> + coef[2] = <msg of x'>`, with
   `coef[1] = raw * tau` carrying the committed `sigma_i` and `coef[2]`
   absorbing everything public (`shuffle_coeffs`).

The linear proof accordingly carries a third masked opening: one more Gaussian
vector `w`, one more first message `t_p`, and one more rejection-sampling test.

5. The prover also runs `pismall_const_prove()` and `pibnd_short_prove()` on
   the `P_i`, one amortized proof each that every committed `sigma_i` is a ring
   constant and that the openings are short, and the verifier checks both
   before anything else. Section 5 says why it takes two.
6. Everything after the `P_i` is run `SHUFFLE_REPS` times with independent
   challenges, because one pass of the product argument is worth only
   `MSGS / p_min`. Section 6.

## 4. Zero knowledge: the mask on the published s_i

The fix introduced a privacy problem, which this branch also fixes. The prover
publishes the values `s_i` in the clear, and

```
s_0 = theta_0 - beta * a_0 / b_0 .
```

Before the fix, `b_0` was the public `_m_0` and the only secret in sight was
the prover's own randomness `theta_0`. After it, `b_0 = _m_0 + sigma_0 tau -
mu` carries the committed `sigma_0 = x^pi(0)`, so `s_0` is a function of the
permutation, and the *only* thing hiding it is `theta_0`.

`theta_i` was sampled from `nfl::ZO_dist`, which is ternary, where the CT-RSA
2021 code it is adapted from samples it uniformly over the whole ring. A short
mask is not a mask: an adversary who knows the two lists — in the mix-net they
are the previous server's published output and this server's — guesses
`pi(0) = j`, rebuilds `b_0`, and recovers the `theta_0` that guess implies.
For a wrong guess that value is a ring element with no reason to be short; for
the right one it is ternary. One inversion per candidate recovers `pi(0)`, and
then the same for every other index.

`theta_i` is now `nfl::uniform()`, which is what the argument needs and what
CT-RSA 2021 does; nothing else requires it to be short, since it only ever
appears inside a committed message, where no norm bound applies. The same
one-line change landed on `main`, where the defect is milder: there `b_0` is
the public `_m_0`, so a short `theta_0` costs zero knowledge -- the `s_i` are
distinguishable from uniform -- without handing over the permutation.

### 4.1 The mask of the AEx proof, and two ways to publish one

Two more zero-knowledge defects, found by going looking rather than by any test.

**The AEx mask came from a fixed seed.** `pismall_prover` hides its witness
behind `s_0`, drawn with `fmpz_mod_poly_randtest` from a `flint_rand_t`, and
publishes `f = s_0 l_0(x) + sum_i l_i(x) s_i`. That generator was
`flint_rand_init`'d and never seeded. FLINT seeds deterministically, which is
checkable in a few lines: the first coefficient it yields is byte-identical
across two runs of a program. So every run of the binary used the same mask and
anyone with FLINT could recompute it, which is the whole of the proof's hiding.
`aex_rand_init()` now seeds from the OS; the generator inside `pismall_hash()`
is seeded from the transcript and must stay that way, that one being
Fiat-Shamir.

**Giving up on rejection sampling is not a proof.** Rejection sampling makes the
masked opening independent of the witness; it is not what keeps the opening
inside the bound the verifier checks. So a prover that abandons it and publishes
anyway emits a transcript that *verifies* and *leaks*. `pibnd_prover()` had
exactly that shape after a retry cap was added to stop it spinning on a witness
that is not short, and `lin_prover()` had the opposite one, an unbounded loop
that could not leak but could hang forever on the same input. Both now bound the
retries and return whether they succeeded, and the callers refuse a proof that
did not.

**Neither was visible to the test suite**, and that is the general point. Every
other test here asks whether the verifier accepts. A proof with a predictable
mask verifies perfectly; so does one from a prover that gave up. The two tests
added for these — `AEX proof does not repeat its mask`, and asserting the
prover's return value in `BND proof is consistent` — are the only ones in the
repository that would notice a transcript which is valid and revealing.

Worth recording how they were written, because the first two attempts at the
mask test passed against deliberately broken code. Comparing two components of
one proof compares things that always differ; comparing two proofs drawn from
one generator compares things that also always differ, because the stream
advances whether or not the seed was fixed. Only fresh generators, as separate
runs would have, distinguish the two cases. A test of this kind is worth nothing
until it has been seen to fail.

### 4.2 The simulator, and the three things a transcript does not hide

Sections 4 and 4.1 fix particular leaks. This is the review of the whole
transcript that they were found inside of, and it is a review rather than a
proof: no simulator has been written down for this protocol.

A pass publishes the commitments `P_i` and `D_i`, the values `s_i`, the
responses of the `MSGS` linear proofs with the hash their challenges come from,
and the two sub-proofs about the `P_i`. Every challenge is a hash of the rest,
so nothing there is a secret. Of the others:

* `P_i` and `D_i` are BDLOP commitments. Hiding is MLWE, and for these two it is
  at rank 2 rather than the rank 1 of the input commitments that Section 8
  estimates at `2^155.8`, since only one row of `A2` carries a message.
* the `s_i` are uniform. `s_0 = theta_0 - beta a_0 / b_0`, and
  `s_i = theta_i + (theta_{i-1} - s_{i-1}) a_i / b_i` after that, so with the
  `theta_i` uniform and independent the `MSGS - 1` published values are jointly
  uniform whatever the permutation is. That is what Section 4's change to
  `theta` bought, and it is perfect rather than computational.
* the responses of the linear proofs are `D_sigma` restricted to a halfspace, by
  the rejection sampling of 8.1.
* the sub-proofs have their own zero knowledge, which is 4.1.

**One: the halfspace bits.** Each accepted opening of `Pi_LIN` leaks the sign of
`<z, beta r>`, the one bit the `b = 1` variant of Figure 2 acknowledges. There
are `LIN_REPS` of them per relation and the `P_i` are now shared by every pass,
so the randomness of one `P_i` is masked `LIN_REPS * SHUFFLE_REPS = 12` times
and leaks twelve signs, each of a different linear function of it. Against
`WIDTH * N = 16384` ternary coefficients that is nothing, but it scales with
both kinds of repetition, which is worth knowing now that there are two.
`Pi_BND` no longer leaks any: section 8 reports that its `sigma` is loose enough
for the two-sided variant to be both cheaper and tighter, so it has no halfspace
to tell about.

**Two: an abort is not free, and this one used to abort.** `simul_inverse`
inverts the `b_i` by the batch trick, which needs their product to be
invertible, and `assert`ed that it was. The event is witness-dependent:
`b_i = _m_i + sigma_i tau - mu`, so an observer who saw the prover stop knew
`tau`, `mu` and the output list, could compute `b_i` for every candidate value
of each `sigma_i`, and learned that at least one of them is singular. That is a
constraint on the permutation and not a bit of it. The rate is
`2N MSGS / p_min`, which is `2^-21` a pass and `2^-19` a shuffle at
`MSGS = 1000` — the comment in the code said `2^-26`, the figure for the old
39-bit basis with the factor of `MSGS` dropped.

It now gets the treatment rejection sampling gets: a restart. `simul_inverse`
returns a status, the first half of a pass tests it as soon as the `b_i` exist
— one inversion, before any `D_i` is committed, so nothing expensive is built
on a pass that cannot be finished — and `run()` rebuilds its first message when
a pass reports it. Fresh randomness in the `P_i` moves every pass's `tau` and
`mu` and so moves the event, which is what makes the retries independent; it
takes the two sub-proofs with it, which is why the budget is `SHUFFLE_TRIES = 8`
rather than the 256 of the linear proofs. Eight leave `2^-152`. The path was
tested by forcing the singular case: the prover rebuilds and the proof still
verifies.

**Three: the clock.** The number of restarts the prover makes depends on the
norms it is masking, and now also on the singular case above. None of it is in
the transcript, so it is a side channel and not a leak, but a prover that runs
where its timing can be observed is telling an observer something about its
witness.

## 5. The membership sub-proof

Lemma 5 requires `sigma_i in D`. This branch proves it with two sub-proofs run
on the same commitments: `Pi_SMALL` for the algebraic half, which says exactly
that `sigma_i` is a ring constant, and `Pi_BND` for the half no
algebraic identity can give over a composite modulus, which says that its
`Pi_BND` for the size half that no algebraic identity can give over a composite
modulus. Section 5.4 is the argument that reads the two as statements about one
opening, which needs MSIS modulo each prime of the basis rather than only modulo
`q`, and which concludes with the invertibility Lemma 5 asks for.

### 5.1 What is proven

`pismall_const_prove()` runs the amortized exact proof of `src/pismall.cpp`
over all `MSGS` commitments `P_i` to the `sigma_i`, as one proof. The relation
is the commitment equation itself,

```
  row 0    P_i.c1 = r_0 + sum_j A1[0][j] r_{j+1}
  row 1    P_i.c2 = sum_j A2[0][j] r_j + sigma_i
```

`R = HEIGHT + 1` rows and `V = WIDTH + 1` components, so the witness the proof
binds is an opening of `P_i` and no link between two commitment schemes is
needed: `sigma_i` is the value inside the commitment the linear proof already
speaks about. The coefficient sets are ternary for the randomness `r`, and
`sigma_i` is declared `AEX_SCALAR` — unconstrained at coefficient 0, and the
singleton `{0}` at every coefficient above it.

**That constraint is exact over `Z_q`, and it is the only one in the file that
is.** The identity is `f = 0`, which has a single root whether or not `q` is
composite, so unlike the ternary, binary and sign sets it says the same thing
over `Z_q` as it does in each CRT component. Nothing here needs repairing
afterwards. The tests `constant membership proof is consistent` and
`constant membership rejects a non-constant` cover both directions, and
`AEX proof rejects a witness that is not a constant` covers the set itself.

What it leaves open is the *value*: `sigma_i` is some constant `c_i in Z_q`,
and the set of all constants is not admissible, since a difference divisible by
`p_1` is a zero divisor. That is what Sections 5.3 and 5.4 supply between
them.

The soundness error of the AEx proof turns on where its challenge lives. In
`GR(q,2)` a pass is worth about `18 tau / p_min^2`, `2^-74` at `tau = 1024`, and
a proof needed two of them; 5.5 reports that the two were not bound to each
other and that the repair was to move the challenge to `GR(q,4)`, where one pass
is enough.

### 5.2 The sets are per CRT component, and here that is a feature

**Every other coefficient set in `pismall` is inexact, because `q` is
composite.** What the proof checks for the binary set is `c (c - 1) = 0` at
every coefficient position. Over a field that has two roots. Over
`Z_q = Z_{p_1} x Z_{p_2}` it has four: `0`, `1`, and the two CRT idempotents.
Ternary gives 9 roots instead of 3, and `{-1, 1}` gives 4 instead of 2. The test

```
KNOWN GAP: the coefficient sets are per CRT component
```

exhibits a witness that is `+1` modulo `p_1` and `-1` modulo `p_2` in every
coefficient -- an element of full size over `Z_q` -- and the proof accepts it as
ternary. That is a defect in `Pi_SMALL` on its own terms, and anything that
reads it as an exact norm statement inherits it.

An earlier version of this branch took `D = {x^i}`, and then this defect was
fatal to the membership proof: "binary" and "Hamming weight one" are both
inexact sets, so what was established was that `sigma_i` is a monomial *in each
CRT component*, one component short of `sigma_i in D`, and a prover who
CRT-mixed the `sigma_i` was accepted. No algebraic identity can do better over
a composite modulus: the solution set of a polynomial system over `Z_q` is the
product of the per-component solution sets, while every admissible `D` is a
diagonal of such a product, and a diagonal is never a product.

With `g(i) = i` the membership proof does not use an inexact set at all. The
defect remains true of `Pi_SMALL`, and it is still load-bearing here — but as a
*tool* rather than an obstacle. What it says about the randomness `r` is that
the exact opening is short in the ordinary sense **modulo each prime**, and
that is precisely the hypothesis Section 5.4 needs.

### 5.3 The norm bound

`pibnd_short_prove()` bounds the openings of the same `P_i`. `Pi_BND` of
`src/pibnd.cpp`, the amortized approximate norm proof already in this
repository, is instantiated on the commitment equation — the very same relation
`pismall_const_prove()` uses, `R = HEIGHT + 1` rows and `V = WIDTH + 1`
components — amortized over exactly the `MSGS` commitments and needing no
padding, since nothing here is interpolated.

Two implementation notes, both visible in `src/pibnd.cpp`:

* A prover whose witness is not short cannot pass rejection sampling.
  `pibnd_prover()` gives up after `PIBND_TRIES` attempts and emits the masked
  opening it has, which the verifier rejects on the norm test, rather than
  looping forever. An honest prover passes both checks with probability about
  `1/3` per attempt, so giving up is a `3^-64` event.
* The last witness row is sampled with `sigma-hat_ANEx`, whose width is set by
  `ANEX_E_INF`, the infinity norm of that row. It defaults to `BETA`, the
  ternary bound of the decryption noise the proof was written for, but here the
  row holds the ring constants `g(i) = i`, which reach `MSGS`. The Makefile
  passes `-DANEX_E_INF=MSGS` for this instance. Sized for ternary it was wrong
  by that factor, and since `S'C'` on that row sums about `TAU / 2` constants of
  size up to `TAU` while `sigma-hat` grows only as `sqrt(TAU)`, the rejection
  factor climbed with the batch: about 5 at `MSGS = 128`, 90 at 256, where the
  honest prover exhausted `PIBND_TRIES` about half the time, and out of reach at
  1000. With the override it is 1.02 at 256 and 1.03 at 1000, and the prover
  accepts on its first attempt.
* `sigma-hat` is `9.96e8` at `MSGS = 1000`, still short of the `2^64` that would
  call for the quad-precision sampler, as the mix-net's decryption noise does.
  Choosing the sampler by magnitude rather than by row index makes `Pi_BND`
  about ten times faster, the mix-net's own instance included.

The challenge matrix is never stored: both sides derive it from the transcript
hash and consume it once, row by row, so `pibnd` keeps a single row. At
`TAU = 1000` the matrix would be 8 GiB.

### 5.4 Why the two sub-proofs speak about one opening, and what follows

`Pi_SMALL` is an *exact* proof of knowledge: its extractor outputs a witness
satisfying the relation and the coefficient sets with no relaxation. `Pi_BND`,
like every Fiat-Shamir Sigma protocol of its shape, extracts a *relaxed*
opening: a short `s'` and a short non-zero `c` with `A s' = t c`, where `c` is a
difference of challenges. With the `{0,1}` challenge set Section 7 settles on
that `c` is `+/-1` and the opening is exact, which is the best case of what
follows; the argument is left general so that it survives the switch to the
monomial challenge set, where `c` is 2. Reading the `sigma_i` of the two as one
ring element takes an argument, because the obvious one does not work:
multiplying the exact relation by `c` and subtracting gives `A (c r - r') = 0`,
and the binding of the commitment says nothing, since `r` is short only in each
CRT component and `c r` need not be short over `Z_q` at all.

The way through is to stop working over `Z_q`, and it is Section 5.2 that makes
it possible. Write the extracted randomness in CRT form, `r = e_1 r^(1) + e_2
r^(2)`. What 5.2 calls a defect says exactly that each `r^(j)` is ternary **as
an integer polynomial**. So the exact extraction hands us, for each prime of the
basis, an opening of `P_i` modulo that prime that is short in the ordinary
sense, and the comparison that fails over `Z_q` succeeds modulo `p_j`.

**Claim.** Suppose MSIS over `R_{p_j} = Z_{p_j}[x]/(x^N + 1)` is hard at norm
`beta` for each prime of the basis, `beta` being twice the bound of `Pi_BND`
plus the slack of a challenge difference. Then every difference `c_i - c_{i'}`
and `c_i - g(j)` is invertible, which is what Lemma 5 requires.

*Proof.* Reducing both relations modulo `p_j` gives `A (r', sigma') = (c1, c2)
c` and `A (c r^(j), c sigma_i) = (c1, c2) c`, so `A1` kills the difference of
the randomness parts. Both are short — `r'` by `Pi_BND`, `c r^(j)` because `c`
is short and `r^(j)` ternary — so their difference is a short element of the
kernel of `A1` modulo `p_j`, and by the assumption it is zero. The message row
then gives `sigma' = c sigma_i = c c_i` modulo `p_j`, for each `j`, hence
`sigma'_i = c c_i` modulo `q`.

Now let `d = c_i - c_{i'}` and suppose `d` is a zero divisor, say `p_1 | d` and
`d` not divisible by `p_2`. Then `c d = sigma'_i - sigma'_{i'}` has infinity
norm at most `2 B`, and it is divisible by `p_1`; since `2 B < p_1` every
coefficient of it is zero, so `c d = 0` in `R_q`. But `d` is a *constant*, so
`c d = 0` forces `d` to vanish modulo the prime of every slot where `c` does
not; as `d` is non-zero modulo `p_2`, that means `c` vanishes in every slot of
`p_2`, i.e. `c = 0` modulo `p_2`, and `c` short forces `c = 0`, contradicting
`c` non-zero. The same argument covers `c_i - g(j)`, since `c g(j)` is short for
`g(j) < MSGS`. []

Three remarks. The relaxation factor `c` never has to be cancelled or inverted,
so the slack of `Pi_BND` costs nothing; only its norm bound is used. The
conclusion is the invertibility Lemma 5 asks for, obtained without naming `D` at
all — there is no membership statement to get wrong. And the inequality the
argument turns on, `2 B` below `p_min`, is checked rather than assumed: the test
`the norm bound leaves room for the CRT argument` compares them at the
parameters in force, with a factor of 49 to spare at `MSGS = 1000` and 377 at
256. The 24000 this said until `ANEX_E_INF` was corrected is the same quantity
with the last row's mask sized for a ternary row, and the 762 before that is it
at the 39-bit basis, which Section 8 replaced.

**The cost is one assumption the mix-net did not make before:** MSIS modulo each
prime of the basis. It is genuinely additional, and Section 8 says why in
one line: modulo `q` the binding lattice has no short vector to find at all —
`lambda_1` is about `2^27` against a bound of `2^21.5` — while reducing modulo
`p_j` shrinks the determinant by half and brings `lambda_1` down to about
`2^16`, comfortably below the `2^29.4` this argument needs. So there is nothing
to assume modulo `q` and something real to assume modulo `p_j`. Nothing already
relied on gives it for free.

It is satisfied with a wide margin all the same. Taking the lattice of the `c1`
row — dimension `N * WIDTH = 16384`, `N * HEIGHT = 4096` constraints modulo
`p_j` — and the usual BKZ model, reaching `beta = 2^29.4` at `MSGS = 1000` needs
block size `b = 2698`, against `b = 438` for `2^128` in the classical core-SVP
cost model and `b = 483` quantum. Roughly six times the block size, and the
margin grows as `MSGS` falls: `b = 4055` at `MSGS = 2`. These are textbook
core-SVP figures rather than an estimator run, and the absolute numbers should
not be taken at face value — the comparison against `b = 438`, and against the
`b = 14849` that binding needs, is the part that is robust.

**The assumption cannot be discharged within this design.** Identifying two
openings of one commitment needs the binding of the commitment, which needs both
openings short; `Pi_SMALL`'s exact opening is short only in each CRT component,
which is exactly why the comparison has to be made there. One could instead
compare two *relaxed* openings — `Pi_BND`'s against the linear proof's, both
short over `Z_q`, so that MSIS modulo `q` suffices — but that establishes
nothing about the exact witness, and it is the exact witness that carries the
"is a constant" statement. Removing the assumption means not having an exact
proof and a relaxed one to reconcile, which is the LaZer route of alternative 1
below.

Two alternatives to the pair of sub-proofs, both larger, and neither needed
given the above:

1. **Delegate the sub-proof** to a general-purpose lattice proof system, which
   is what Protocol 1 of ePrint 2025/658 does, at the cost of a large new
   dependency. Such a system proves `is_bin` over the integers, norm included,
   in one proof and with one extraction.
2. **Make `q` prime**, which would make every coefficient set of `Pi_SMALL`
   exact and remove `Pi_BND` from the shuffle entirely. This is impossible here:
   Theorem 2 of the CCS 2023 paper needs `q > 2(B_Dec + B_DDec)`, about
   `2^77.5`, and NFLlib's `uint64` arithmetic caps a single modulus at 62 bits.
   The composite modulus is forced, and so is everything that follows from it.

### 5.5 The AEx proof's parameters, and its two passes

Nothing in this document had read `pismall.cpp`, which is the largest file here.
This is what its numbers are, checked against Lemma 2 of the paper.

**The parameters check out.** The Reed-Solomon code has length `l = 16384` and
message `2N + ETA = 8517`, so its rate is 0.52 and its relative distance 0.48,
which is what Section 6 quotes. Lemma 2's column-opening terms are
`2 (g / (l - eta))^eta` and `2 (1 - 2 (g - g') / 3l)^eta` with `g' <= g <= l`,
and the `g` that balances them is 13078, where both are `2^-95`. So `ETA = 325`
buys `2^-95` and not the `2^-82` Section 6 quotes; the quote is a safe one.

**The term that dominates is the algebraic one**, which is Lemma 2's
`18 tau / (q - tau)`. Taken over `Z_q` that reads `2^-88`, but the ring is
split and an adversary can work modulo one prime, which is exactly why this
file draws its challenges from
`GR(q,2)` instead: the per-slot space is `p_min^2` and the term is
`18 TAU / p_min^2`, which is **`2^-73.8`** at `TAU = 1024` and the 44-bit basis.
Section 6's `2^-66` a pass is the same quantity at the old 39-bit primes.

**And the two passes were not bound to each other.** `AEX_REPS = 2` exists
because one pass is not enough, and the comment on it says the passes are
independent, which is exactly the trouble: `pismall_hash` takes that pass's
Merkle root and that pass's commitment and nothing else, and `aex_sample_I`
takes that pass's root and that pass's openings. So this is Section 6.1 again,
one level down. A prover re-randomises the commitment of one pass — which is
cheap, the messages staying put — until that pass's challenges suit it, keeps
it, and moves to the other:

```
bound        (18 TAU / p_min^2)^2  = 2^-148
as built     2 * p_min^2 / 18 TAU  = 2^75 queries
```

**It was a claim not met rather than a practical attack**, which is the
difference between this and 7.1. A query here costs a BDLOP commitment and the
derivation of `2 + 6 TAU` extension-field challenges, some tenths of a
millisecond, so `2^75` of them is astronomical wall-clock; the `2^46` of 7.1 was
days. But `LEVEL` is a count of queries, and by that count `Pi_SMALL` was the
weakest thing in the protocol at `2^75`, below `Pi_BND`'s `2^-130`.

**The repair is 6.1's in principle and dearer in practice.** One hash over both
passes' first messages, yielding both passes' challenges, is the shape `run()`
now has — but a pass's first message is a Merkle root over its codewords, and
the codewords are `H[TAU][3][V]` at 256 KB each, **3.75 GB** at `TAU = 1024`.
Both passes' cannot be held at once, and they cannot be shared either: two
accepting transcripts over one first message is what the extractor of Lemma 2
consumes, so a prover that answered two challenge sets from one commitment
would be handing the verifier the input to its own extraction. What is left is
to recompute — save each pass's randomness, discard its codewords, and encode a
second time after the challenge — which binds the passes at the cost of doubling
the encoding, the dominant cost of this file.

**What this branch does instead is make one pass suffice**, which is cheaper
than any of that. The per-pass algebraic term is `18 TAU / p_min^2` only because
the challenge lived in a quadratic extension. `AEX_DEG` is now 4, the term is
`18 TAU / p_min^4 = 2^-162`, and a single pass answers to the column term alone
— which at `ETA = 325` is `2^-95`, so `ETA` is now **452**, where the two terms
of Lemma 2 balance at `2^-128.3`. `Pi_SMALL` is therefore worth `2^-128` on its
own, with nothing left to bind because there is nothing left to repeat.

`GR(q,4)` is built as a tower: `Z^2 = AEX_NR` over `Z_q`, then `Y^2 = Z`, so
`Y^4 = AEX_NR` and the existing quadratic arithmetic carries the new one, three
base multiplications by Karatsuba instead of nine. `X^4 - AEX_NR` is irreducible
modulo a prime of the basis exactly when `AEX_NR` is a non-residue there and
`p = 1 mod 4`: the first is what `AEX_NR = 3` was chosen for, the second holds
because `p = 1 mod 2^21`, and the test at the bottom of `pismall.cpp` now checks
both rather than assuming them.

It is 39% more opened columns against half as many passes, so `Pi_SMALL` falls
from 108 MB to about 76 and the prover with it. The paper's own footnote to
Lemma 2 says its bound "only applies to the interactive version of the proof"
and has to be raised for Fiat-Shamir, which is the same observation one level
up; removing the repetition answers it rather than binding it.

**Two places where the degree was written into the code rather than derived**
turned up on the way, both of the same shape: a coordinate 1 that meant "the
rest of the extension". `aex_identities` zeroed only `acch[1]` before
accumulating, and the `h` masks zeroed only `h[*][i][1]`, so at degree 4 the
upper coordinates carried whatever the previous proof had left. Both showed up
as the consistency test failing, which is the cheap way to find them; neither
would have been visible at degree 2.

There is a second, cheaper-to-state instance of the same thing inside a pass:
the columns are hashed from the openings, so a prover can re-roll the openings'
masks to move the column set without disturbing the algebraic challenges. That
one is worth `2^95`, so it is not the way in.

## 6. Soundness error of the product argument

Lemma 2 of ePrint 2025/658 (Schwartz-Zippel over a ring) needs a challenge set
whose pairwise differences are not zero divisors. The challenges here are
uniform elements of `R_q`, which in a ring this split is best analysed slot by
slot: if the product identity fails in some slot, the check passes only if the
challenge hits a root of a degree-`MSGS` polynomial in that slot, with
probability at most `MSGS / p_min`, about `2^-34` at `MSGS = 1000`. That is the
soundness error of **one pass**, and it is far short of the `LEVEL` bits the
parameters are otherwise chosen for.

The product argument is therefore run `SHUFFLE_REPS` times with independent
challenges and the verifier requires every pass. Repetition is sound here
because the slot in which the identity fails is fixed by the commitments before
any challenge is drawn, so the passes really are independent and the error is
the per-pass error raised to `SHUFFLE_REPS`. The count is derived at compile
time from the basis, as `ceil(LEVEL / (floor(log2 p_min) - ceil(log2 MSGS)))`:
four passes at `MSGS = 2` for `2^-168`, four at `MSGS = 1000` for `2^-132`, five
at `MSGS = 4096` for `2^-155`.

This is the argument for an interactive verifier, and under Fiat-Shamir it has
to be built into the hashing. **Section 6.1 reports that it was not**, and what
it took to repair the outermost layer of it. Everything below about `2^-132`
and `2^-176` is what the exponents are once every layer is bound; two of them
are not yet.

The prover's first message -- the commitments `P_i` to the `sigma_i` and the
two sub-proofs of section 5 that place them in `D` -- is sent once and shared
by every pass. That was true when this section was written, stopped being true
when `rho` became a per-pass challenge and the commitment key became the
`rho`-compressed one, and is true again now that the `sigma_i` are committed
under the original key instead. It is the mechanism of 6.1 in both directions.

The alternative remedy is the one `pismall` uses, drawing the challenges from
the quadratic Galois extension `GR(q,2)` so that a single challenge is worth
`deg / p_min^2`. It was not taken. It buys `2^-68` per pass and so still needs
two passes, while lifting `a_i`, `b_i`, the masks `theta_i`, the published
`s_i` and the commitments `D_i` into the extension doubles every element of the
argument: about four times the size against five for plain repetition, in
exchange for a protocol that would have to be designed rather than repeated.

**Where this leaves the protocol**, once 6.1 is repaired and the exponents are
real. At `MSGS = 1000` the terms are `2^-132` for the product argument and
`2^-128` for `Pi_SMALL` — one pass over `GR(q,4)`, whose algebraic term is
`2^-162`, against a column-opening test at `2^-128.3` on 452 of 16384 columns at
relative distance 0.48 — and `Pi_BND` at its own `NTI = 130`. The `Pi_SMALL`
figure was `2^-133` when this was written, on two passes of a quadratic
extension; 5.5 reports that the two were not bound to each other, worth `2^75`
between them, and what replaced them. That leaves one term below `LEVEL`, and
it is not one of these: Section 9 reports that the compression of the message
components by `rho` costs `2^-44` a pass, and that it is now drawn inside them,
because `rho` is drawn once outside them. Setting that aside, the binding
constraint is the hardness of the lattice problems the commitment and the
encryption rest on — with the caveat that section 5.4 adds one of them, MSIS
modulo each prime of the basis.

These repetitions turn out to carry more than the term they were sized against.
Section 7 reports that the linear proof is worth about `2^-44` per pass for an
unrelated reason, and it is the same repetitions that would compose it to
`2^-176` — once they compose at all, which is 6.1.
Removing them because the product argument had been strengthened by some other
means would reopen that.

### 6.1 The repetitions are not bound to each other

Everything above multiplies the per-pass error only if a prover who fails a
pass has to start over. Against an interactive verifier that is automatic: the
verifier draws every challenge, and a prover who wants another `tau` gets a
fresh one everywhere. Under Fiat-Shamir it has to be built, and here it is not.

`shuffle_rho_hash`, `shuffle_chal_hash` and `shuffle_hash` each hash the pass
index as a domain separator and otherwise **only that pass's own data**: the
input commitments, the output list, and this pass's `P_i`, `D_i`, `tau`, `mu`,
`rho`. The comment in `shuffle_chal_hash` states it outright — "the passes
differ only in this byte". No message of pass `l` reaches any challenge of pass
`l'`, and the verifier checks each pass on its own.

**So the passes are ground one at a time.** A prover whose output list is not a
permutation of the input takes the attack of Section 1: it mixes the list in a
single CRT slot, so the product identity fails in that slot alone. Then, for
each pass in turn, it re-randomizes the commitment `P_{MSGS-1}` — which moves
that pass's `tau` and `mu` and nothing else — and tests whether the new
challenge is a root of the failing slot, which costs `2 MSGS` multiplications
modulo `p_min`. When it is, that pass is settled and it moves to the next.
Nothing it does to pass `l` disturbs a pass it has already settled.

```
bound        eps^SHUFFLE_REPS          = 2^-136 at MSGS = 1000
as built     SHUFFLE_REPS * eps^-1     = 2^36 hash queries
```

with `eps = MSGS / p_min = 2^-34`. Each query costs one BDLOP commitment and a
hash over the part of the input that moved, about 0.25 ms, so the four passes
come to roughly 200 core-days: not a thought experiment. **The protocol's
soundness against the attack it was rebuilt to stop is one pass, not four.**

The same applies one level down. Section 7 reports that `Pi_LIN`'s challenge
`beta` is worth `1 / p_min` per pass and concludes that the repetitions carry it
to `2^-176`; they do not, for exactly this reason, and re-rolling a pass's `D_i`
moves that pass's `beta` alone.

`rho` is the exception, and it is worth saying why: `shuffle_rho_hash` takes
only the input commitments, the output list and the pass index, all of which a
prover fixes before it starts. It cannot move one pass's `rho` at all without
changing the output list, which moves every pass's `rho` at once. That layer
composes by construction, and Section 9's reading of it stands.

**Chaining is not the fix.** Making pass `l` hash the transcripts of passes
before it leaves the grinding order intact: the prover settles pass 0, then
pass 1, and each grind only invalidates passes it has not built yet. What is
needed is that every challenge depend on *all* the first messages: the prover
sends `P_i^(l)` for every `l`, one hash yields every `(tau_l, mu_l)`, the
prover sends `D_i^(l)` for every `l`, and a second hash yields every `beta_l`.
Then re-rolling anything re-rolls every pass at once, which is what raises the
error to a power.

**It costs memory, and that is the whole of the cost.** The passes currently
run one after another through the same buffers. Binding them means holding
every pass's first message at once: at `MSGS = 1000` the `P_i` and the `D_i`
are 128 MB apiece per pass, and the sub-proofs of section 5 about 116 MB more,
so roughly 370 MB a pass against the 3.7 GB the shuffle already takes. Four
passes of that is an extra 1.1 GB and no extra proof size, since the same
elements are published either way.

**Or the `P_i` could go back to being shared**, which is what this section
assumed before `rho` became a per-pass challenge. Section 9 already names the
way, and it is what this branch now does: the `sigma_i` are committed under the
original commitment key rather than the `rho`-compressed one, so the `P_i` and
both sub-proofs are `rho`-independent. `run()` produces them once, before the
passes; `lin_prover` and `lin_verifier` carry a second key for the middle
commitment of their relation, the two sharing `A1` and differing only in the
`A2` row; and every pass's `tau` and `mu` are a hash of that one first message,
so re-rolling it re-rolls every pass at once and the product argument's error
multiplies again.

It pays for itself twice over, because `Pi_SMALL` and `Pi_BND` stop being
rebuilt per pass: the proof goes from 2442 to **2094 KB a vote**, and the
`shuffle-proof` benchmark at `MSGS = 4` from 154 to **23.8 Gcycles**, a factor
of 6.5. Eleven of eleven tests pass.

**The `D_i` round is bound too.** `beta` was a hash of one pass's `D_i`, so a
prover could still re-roll one pass's `D_i` alone. `run()` is now in two halves:
every pass reaches its `D_i` first, one hash over all of them yields every
pass's `beta`, and only then does any pass compute its `s_i` and its linear
proofs. `d`, the randomness that opens it and `theta` are dimensioned by
`SHUFFLE_REPS` as well, since they are the part of a pass that has to outlive
it; the compression and the factors `a_i`, `b_i` are recomputed in the second
half rather than held, being cheaper to rebuild than to store. At `MSGS = 1000`
that is about 1.3 GB more than holding one pass, and the measured cost in time
is 0.6% of `run()` -- the extra hash is 8 to 16 Mcycles against the 18 to 350
Gcycles the sub-proofs take.

**The third layer was the `MSGS * SHUFFLE_REPS` instances of `Pi_LIN`**, each
with its own `beta` over its own first message, each worth `1 / p_min` by
Section 7 and each grindable on its own; a prover needs one forged linear proof
per pass, so the protocol sat at `SHUFFLE_REPS / p_min`, about `2^46`. Binding
those to each other is the wrong lever, since an abort anywhere would re-roll
every challenge everywhere and all `MSGS * SHUFFLE_REPS` of them never accept at
once. **Section 7.1 prices that route and the others** and records the one
taken: each proof is now run `LIN_REPS = 3` times against challenges drawn from
one hash of all three first messages, so a forged relation has to survive all of
them, `2^-132` a relation and `2^-134` for the protocol.

## 7. The challenge sets of the Sigma-protocols

The same disease reaches one level lower than sections 2 and 6, into the
challenge sets themselves, and it had not been looked at.

`lin_hash` draws the challenge `beta` of the linear proof with
`bdlop_sample_chal`, the difference of two ternary vectors of Hamming weight
`NONZERO`, which the paper takes as 36 and this branch as 9 — see the end of
this section. Every argument about that proof wants such elements, and the
differences of two of them, to be invertible, and the justification is [42,
Corollary 1.2] once more — vacuous at `k = 2N`, exactly as section 2 says of the
choice of `D`. Nobody had applied that observation to the challenges.

**It is not invertible.** The test

```
KNOWN GAP: a challenge difference can be a zero divisor
```

exhibits a polynomial with 9 coefficients `+1` and 9 coefficients `-1` that
vanishes in one of the 8192 NTT slots modulo `p_1`, and is non-zero modulo
`p_2`. It is a legal value of `beta`: put 7 of its 14 support positions on each
side and add 29 shared positions that cancel, and both sides have Hamming
weight exactly `NONZERO`. It was found by meet-in-the-middle over subset sums of
the powers of one primitive `2N`-th root, in seconds, the same way as the short
zero divisor of section 3.

**What that costs.** The last check of `lin_verifier` reduces, after
substituting the prover's responses, to

```
beta * L = 0,      L = coef[0] m_x + coef[1] m_p + coef[2] - m_x'
```

where `L` is the residual of the linear relation over the committed messages.
An honest prover has `L = 0`. A prover whose committed messages violate the
relation in a single CRT slot passes exactly when `beta` vanishes in that slot,
which for a random `beta` is about `1 / p_min = 2^-44`. The challenge is derived
by Fiat-Shamir, so this is grindable rather than merely unlucky: re-committing
`D_i` to the same message with fresh randomness moves `beta` without moving that
message. So the honest reading is **44 bits per repetition, not 128**, and
there is no soundness proof at all, since the extraction argument needs the
invertibility the test denies. Section 7.1 is what makes that survivable: the
proof is run `LIN_REPS` times against challenges bound to one another, so the
44 bits multiply.

**What was supposed to cover it.** Section 6 repeats everything after the first
message `SHUFFLE_REPS` times with independent challenges, and a prover whose
output list is not a permutation has to defeat every pass, each with its own
`beta`; at four or five passes that would compose to `2^-176` or better. This
was not the reason the repetitions were introduced — they were sized against
the `2^-34` of the product argument, which is the weaker term — but they were
expected to cover this as well. **Section 6.1 reports that they do not compose
as built**: each pass's `beta` is a hash of that pass's messages alone, so a
prover re-rolls one pass's `D_i` and leaves the rest standing. Until the passes
are bound, this term is `2^-44` and grindable, not `2^-176`.

**The same question, asked of `Pi_BND`, had a sharper answer, and this branch
fixes it.** Its challenge matrix was drawn from `nfl::ZO_dist()`, full-weight
ternary ring elements, which is neither of the two challenge sets the amortized
proof is proven for. Baum et al. [8] give two instantiations, both of the
protocol in their Figure 1:

| | `C` | columns `n` | what the extractor returns |
| --- | --- | --- | --- |
| Theorem 1, `R = Z` | `{0,1}` | `n >= lambda + 2` | `A s' = t_i`, `\|s'\| <= 2B` |
| Theorem 2, `R = Z[X]/(X^d+1)` | `{0} u {+-X^j}` | `n log(2d+1) >= lambda + 2` | `A s' = 2 t_i`, `\|s'\| <= 2 sqrt(d) B` |

Theorem 2's extraction rests on their Lemma 4 — for `a, b` monomials or zero,
`2 (a - b)^-1` has coefficients in `{-1,0,1}` — and Theorem 1's on nothing more
than a difference of challenges being `+/-1`. **A ternary challenge matrix is
neither**: Lemma 4 says nothing about it, and in this ring its differences have
no invertibility to fall back on, for the reason the first half of this section
gives for `beta`. So `Pi_BND` ran outside the soundness proof it cites.

**Which instantiation to repair it to is a real choice, and the paper has
already made it.** Figure 4 of the CCS 2023 paper draws `C` from
`C_Bnd = {0,1}` and asks for `n-hat >= kappa + 2`, which at `kappa = 128` is
the 130 that `NTI` has always been in `src/pibnd.cpp`. The columns were the
paper's; only the set they were drawn from was not. So the fix is one function:
each entry of `C` is now a uniform bit, taken as a ring constant, and a
challenge difference is `+/-1`.

Theorem 2 is the tempting alternative, because `n = (LEVEL + 2) / log2(2N + 1)`
is 10 at `N = 4096` and the proof would be **13 times smaller**. It was
implemented, measured and put aside, because the two instantiations do not
differ only in size: Theorem 2's extractor multiplies by the `g` of Lemma 4,
whose `l2` norm is up to `sqrt(d)`, so what it returns is `2 sqrt(d) B` rather
than `2 B` — a factor of 64 here. That slack is exactly what Section 8's
`B_DDec` is made of. At the same `sigma` the decryption bound moves from
`2^84.4` to `2^88.6`, past the `q/2 = 2^87` this branch's modulus offers, so
taking the 13x means widening `q` by three or four bits and paying about eight
bits of lattice security for it. The trade is recorded, not taken; it is the
one place where this repository could still be made substantially smaller.

`bdlop_open` uses the same challenge set as `Pi_LIN`, but `pismall` calls it
with the factor fixed to one, so nothing there depends on a challenge being
invertible.

### 7.1 What it would take to make `Pi_LIN` worth `LEVEL`

Section 6.1 left the protocol at about `2^46`: a prover needs one forged linear
relation per pass, each instance was worth `1 / p_min`, and each was ground on
its own. The lever this section pointed at was the challenge set, and it is not
the one: the obvious repair is worse than what was there and the elegant one
does not apply. What closed it was repeating each proof, which is the last row
of the table and the rest of this section. The routes are kept because the
reasoning for choosing between them is the useful part.

The sizes below are of the published elements at `MSGS = 1000`: per pass the
`z`, `z_p`, `z'` of the `MSGS` linear proofs come to 90 MB at
`log2(6 sigma_C)` bits a coefficient, their first messages `t, t_p, t', u` to
180 MB at full width, and the rest of the core — `D_i`, `s_i`, `P_i` — to
210 MB.

| | per instance | protocol | cost |
| --- | --- | --- | --- |
| as built: ternary differences | `2^-44`, no extractor | `2^46` | — |
| monomials `{0} u {+-X^j}` | `2^-13` | `2^15` | free, and **worse** |
| challenges in `GR(q,2)` | `2^-88` | `2^90` | every element of the proof doubles, `+45%` |
| challenges in `GR(q,3)` | `2^-132` | `2^134` | `+90%` |
| bind them across the passes | `2^-44` | `2^-176` | `+6%`, but see below |
| amortize them | — | — | does not apply here, see below |
| **repeat each one `LIN_REPS` times** | `2^-132` | `2^-134` | **`-13%`, and taken** |

**Monomials are the trap.** They do fix what Section 7 says is broken: Lemma 4
of [8] gives `2 (X^i - X^j)^-1` integer coefficients in `{-1,0,1}`, and `q` is
odd, so a monomial difference really is invertible in `R_q` and the extractor
really does work. But the challenge set has `2N + 1 = 2^13` elements, so a
prover guesses one in `2^13` rather than landing in a slot at `2^-44`. The
protocol would get an extraction argument and lose 31 bits.

**Binding is cheaper than it looks, and the reason is where the bits are.**
One hash over every linear proof's first message, drawing an independent `beta`
for each, forces the prover to land four forgeries at once: `2^-176`. Section
6.1 objects that an abort anywhere would then re-roll everything, and the
answer is the one 8.1 already used, a single rejection test over the whole
concatenation. Acceptance near a half wants `sigma` about three times the norm
being masked, which the measurements of 8.1 confirm at three openings; over the
`12000` openings of a whole proof that norm is `765 sqrt(12000)` and `sigma_C`
goes from `2^12` to about `2^18`. That lands only on the `z`, which is 90 of
the 480 MB of a pass, so the proof grows by about **6%**, not the quarter I
guessed before counting. What it costs is elsewhere: `8 sigma sqrt(N)` rises
from `2^21` to `2^27`, so two openings that short differ by `2^28`, past the
`lambda_1` of the binding lattice in Section 8. **The commitment stops being
statistically binding and MSIS modulo `q` comes back as an assumption.**
Batching per pass instead of per proof only halves the excess — `sigma_C` at
`2^17`, a difference of `2^27` exactly at `lambda_1` — and costs four passes'
worth of restarts, about eight times the prover, so it does not buy the margin
back either. At `MSGS = 100` the whole question goes away; at 1000 it does not.

**Amortizing them is what one would want, and this relation will not take it.**
A pass proves `MSGS` relations differing only in public coefficients, which
looks exactly like what `Pi_BND`'s shape is for: `LEVEL + 2` columns of masked
openings for all `MSGS` statements instead of one opening each, which at
`MSGS = 1000` would be 14 MB a pass against 270. Every amortized proof of that
shape combines statements with **small** coefficients, and that is what fails
here: `shuffle_coeffs` gives each relation `coef[0] = beta` or `s[l-1]` and
`coef[1] = raw tau`, all uniform elements of `R_q`. Any combination of the
openings weighted by them has norm about `q`, a masked opening at that size is
far above the `lambda_1` of Section 8's binding lattice, and binding says
nothing about openings that are not short -- so the proof it would carry is
vacuous.

What makes the protocol work as it stands is that it never combines: the large
coefficients are applied by the *verifier*, to short responses, one relation at
a time. An amortized version has to preserve that, and the natural attempt does
not. Prove the openings amortized in `Pi_BND`'s shape, then add a second family
of responses for the coefficient-weighted combinations, tied to the
commitments through `A1` as the first family is: the extractor then has short
`r_l, pr_l, _r_l` and a large `R'_l`, and their difference lies in the kernel of
`A1` with `A2` image `-L_l`. Binding kills such a difference only when it is
short, and this one is not, so `L_l` is free to be non-zero. Making the relation
amortizable means making its coefficients small, which means a different product
argument -- or the general-purpose route of Section 5.4's alternative 1, where
one proof system handles the whole membership and product statement and this
question does not arise.

**Repeating the proof is what worked, and it is nearly free.** Repeating the
*pass* is the trap this section opened with: unbound, the passes' costs add.
Repeating one linear proof is different, because its `LIN_REPS` challenges come
from a single hash of all `LIN_REPS` first messages. Re-rolling any of them
moves every one, so a forged relation has to survive all of them at once:
`(1 / p_min)^LIN_REPS`, which at `p_min = 2^43` and `LEVEL = 128` is
`LIN_REPS = 3` and `2^-132` a relation, `2^-134` for the protocol.

It avoids everything that made binding across proofs unaffordable. The binding
is local to one relation, so an abort re-rolls that relation's `3 LIN_REPS = 9`
openings and not the four thousand proofs of a shuffle: the batched rejection
test of 8.1 covers them, `M` is `1.17` and acceptance `0.43`, and `sigma_C`
does not move at all. Section 8's binding margin is therefore untouched, and no
assumption is added.

**And the budget was already there.** Each proof was sending `t, tp, t'` and `u`
at full width, 180 KB a relation, when the verifier can rebuild all four from
the responses and the challenges — `t = A1 z - beta c1`, and `u` the `A2`
combination less `beta` times the statement — and check their hash instead. That
is the transcript the paper describes and the implementation was not using.

It also rules out the other compression the paper offers, which is worth saying
because it looks like a further saving and is not: Appendix B.1 suggests sending
`k - n` of the `k` components of each response and recovering the rest from
`A1 z = t + beta c1`. That is the same equation read the other way, so the two
cannot both be used, and this one is worth far more — at `LIN_REPS = 3` the
first messages are 541 KB a relation against the 67 KB that dropping a component
would save.

Dropping it pays for the extra repetitions and more:

| per pass, `MSGS = 1000` | before | after |
| --- | --- | --- |
| responses `z, zp, _z` | 90 MB | 251 MB |
| first messages | 180 MB | 32 KB of hashes |
| `D_i`, `s_i` | 135 MB | 135 MB |
| **per pass** | **405 MB** | **404 MB** |

with `P_i`, `Pi_SMALL` and `Pi_BND` a further 206 MB once for all passes. The
proof is **1822 KB a vote against 2094**, which 5.5 and the end of section 7
then take to 1715; the
prover's linear proofs cost 3.8 times what they did — 362 against 95 Mcycles —
and the `shuffle-proof`
benchmark at `MSGS = 4` goes from 14.3 to 31.9 Gcycles. Memory at `MSGS = 1000`
rises by about 1.2 GB, the responses being three times as many and the first
messages no longer held.

**What leaving it at `2^46` would have meant**, which is also the shape of any
future gap of this kind. It was a statement about the Fiat-Shamir compilation
and not about the protocol: as a Sigma-protocol that layer was `2^-176`,
because a cheating prover would have to land four forgeries against four
challenges it cannot influence. The whole of the gap is that the implementation
lets it grind them one at a time, offline.

A cheater publishes an output list that is not a permutation, and then, per
pass, forges one linear relation: it needs that pass's `beta` to vanish in the
CRT slot where its relation is false, which is `1 / p_min` a try. A try is
cheap. Varying one coefficient of `_y[0]` moves `_t` and nothing else -- `u` is
unchanged because `_key.A2[0][0]` is zero -- and `_t` is the last thing
`lin_hash` absorbs, so a try is one BLAKE3 chunk and a path, a re-derived
`beta`, and a test of one slot. At about 10 microseconds, `4 * 2^44` tries is
some 22 core-years: single-digit days on a thousand cores, and embarrassingly
parallel.

What that buys is exactly the property this branch exists to defend: a mix
server can substitute, drop or alter ballots and still produce a proof every
verifier accepts. Nothing else moves. Privacy and zero knowledge are unaffected,
the binding of the commitment and the MLWE and MSIS instances are untouched, and
every other layer composes above `LEVEL` -- `tau, mu` at `2^-136`, `rho` by
construction, `Pi_SMALL` at `2^-133`, `Pi_BND` at `2^-130`. The `2^46` is the
minimum over the layers and the only one below the line, which is what makes it
the thing to fix next and not a reason to distrust the rest.

Against the claim, `LEVEL = 128` is not met by the implementation. In
proportion: before the repetitions of Section 6 the product argument alone was
`2^-34` in a single pass, so this is `2^12` better than the state they were
introduced to fix, and it is a documented gap of the same kind as 5.2 and 8
rather than a regression.

The obvious parameter mitigation does not work. The per-instance error is
`1 / p_min` and does not depend on `MSGS`, so wider RNS primes raise it
directly: 62-bit primes would give `2^-62` per instance and `2^64` of work. But
`q` at 124 bits costs about 2.2 bits of lattice security per bit of `q`, which
takes the encryption from `2^158` to roughly `2^78`. Not viable at `N = 4096`.

**The weight of the challenge was buying nothing, and it was expensive.** What
this section establishes is that `beta` is worth `1 / p_min` whatever set it is
drawn from, since the differences can be zero divisors either way; 7.1 then
carries the proof to `LEVEL` by repeating it. So `NONZERO` is not load-bearing
for soundness — it only has to leave the set too large to guess, and at 9 it
still holds about `2^88` elements against the `2^44` that would matter. What it
does control is `||beta r||`, which grows as its square root, and so `sigma_C`,
and so the width of every published response: `log2(6 sigma_C)` bits a
coefficient.

Taking `NONZERO` from 36 to 9 and `sigma_C` from `2^12` to `2^11` keeps the
rejection sampling at the same working point — measured, the batched
`||beta r||` is 1154 against a `sigma_C` of 2048, so `M = 1.17` and acceptance
`0.43`, which is where the old pair sat — and takes a bit off every coefficient
of every response: **1076 to 1002 KB a vote**, with the proof at 1715. The
verifier's norm bound falls with it, `2^21` to `2^20`, which widens the margin
5.4 turns on and the one the commitment's binding turns on in section 8. If the
extraction argument this section says is missing were ever repaired, `NONZERO`
would come back into play and would have to move with it.

## 8. The decryption phase: `B_DDec` and the size of `q`

This one is not about the proof of shuffle, and it is recorded here only
because nowhere else in the repository is.

`Pi_BND` is a *relaxed* proof: it guarantees not that the witness is as short as
an honest prover made it, but that it is shorter than `2 B_Bnd`, a slack bound
depending on the statement. In the decryption phase that witness row is the
smudging noise `E_{i,j}`, so the slack propagates straight into how large `q`
has to be. Appendix B of the CCS 2023 paper bounds it as

```
B-hat_Bnd <= sqrt(2N) sigma-hat_Bnd <= 1.35 N sqrt(N) ||E_{i,j}||_inf
```

which at `||E||_inf = 2^54` gives `B_DDec = 2 p xi^2 B-hat_Bnd = 2^76.4`, the
`< 2^76.5` the paper states, fitting under the old `q/2 = 2^77` by half a bit.

**That bound omits the `tau` statements.** `sigma_Bnd` is defined as
`0.954 max ||S' C'||_2`, and `S' C'` sums over the `tau` statements of a batch;
the chain bounding it keeps a `sqrt(k)` for the `k` rows and nothing for the
columns. The reference it derives from says so directly. Baum et al. [8],
Theorem 1, requires

```
sigma >= sqrt(ln 12 rho) * s * sqrt(l n),      s >= s_1(S),
```

with `l` the number of statements and `n` the number of challenge columns —
that is, `sqrt(tau * NTI)`, exactly the factor Appendix B drops and
`src/pibnd.cpp` carries. Only the shape of that requirement transfers: its
constant is for the two-sided rejection sampling of their Lemma 1, and this
implementation runs the one-sided variant, whose constant is the 0.954 below.

Measurement agrees, and pins the exponents rather than the form alone.
Instrumenting `pibnd_rej_sampling`, with the `{0,1}` challenge set of Section 7:

| change | change in `||S'C'||` |
| --- | --- |
| `tau` 16 -> 64 | +1.03 bits |
| `NTI` 8 -> 32 | +0.98 bits |

so `||S'C'||` grows as `sqrt(tau) sqrt(NTI)`, which is the factor Appendix B
drops and `src/pibnd.cpp` carries. In absolute terms the measurement gives
`||S'C'|| = 0.49 B_Com sqrt(k N tau NTI)`, which passes the paper's `sigma_Bnd`
at `tau NTI = 2^13.9`, an eighth of the real parameters; past that point the
honest prover exhausts `PIBND_TRIES` every time and the test `BND proof is
consistent` fails.

**What `sigma` has to clear is smaller than it looks, and this is where the
0.954 comes from.** `pibnd_rej_sampling` rejects when `<Z, S'C'> < 0` before
the usual test, which is Figure 2 of the paper run with `b = 1`: the variant of
[38] that accepts inside a halfspace, leaks the one bit that says which, and in
exchange needs only `M >= exp(||S'C'||^2 / 2 sigma^2)`. At a fixed `M` of
`sqrt(3)` that reads `sigma >= ||S'C'|| / sqrt(2 ln sqrt 3)`, i.e.
`sigma >= 0.954 ||S'C'||` — the paper's constant exactly, applied to a
worst-case `||S'C'||` of `sqrt(k) N B_Com`. So the protocol is sound and
zero-knowledge at any `sigma` above that, and the old ternary challenges, which
left the ratio at 1.35, were fine on this count.

`M` is no longer fixed: it is taken from the norm the function has already
computed, and it removes the only thing the 0.954 was ever load-bearing for,
since no `sigma` is then invalid — a small one costs restarts and nothing else.

**And with `sigma` this loose the halfspace test is a bad trade.** Rejecting on
`<Z, S'C'> < 0` removes the `24 sigma ||S'C'||` term from `M` at the price of
half of every draw. At `sigma = 0.954 ||S'C'||`, which is what the paper sizes
for, that is worth paying. At 86 times it is not: the term it removes is
`12 ||S'C'|| / sigma = 0.14`, so the two-sided `M` is `1.15` and acceptance
`0.87` a check, against the `0.50` a halfspace test leaves. `pibnd` therefore
runs the two-sided variant and `Pi_LIN`, whose `sigma` is 5.35 times what it
masks, keeps the halfspace test — the rule being which of `12 ||v|| / sigma` and
`ln 2` is larger. It also stops the transcript leaking which halfspace the
opening fell in, which is one of the three things 4.2 lists.

Measured over a `MSGS = 4` run, restarts a proof and the standalone prover at
`TAU = 32`:

| | restarts | `BND prover` |
| --- | --- | --- |
| fixed `M = sqrt(3)`, halfspace test | 7.85 | 39.2 Gcycles |
| `M` from the norm, halfspace test | 2.08 | 17.2 Gcycles |
| `M` two-sided, no halfspace test | **0.09** | 6.5 Gcycles |
| and the challenge multiplications dropped | 0.09 | **2.64 Gcycles** |

The last row is not about sampling at all. The challenge entries are bits, so
`s[k][i] * Crow[j]` is a multiplication by zero or one: the accumulation adds
the row or skips it, and `TAU * V * NTI` polynomial products an attempt —
520,000 of them at `MSGS = 1000` — become additions. The verifier's identical
loop goes with it.

**But it is now 90 times more than that, and `q` is sized for it.** The
`{0,1}` challenges are `2^5.5` shorter than ternary ones against the same
`sigma`, so the measured ratio is **86** where **0.954** is what the sampler
asks. `sigma_Bnd`, `B_Bnd` and `B_DDec` are therefore about six bits larger
than they need to be, and `q` was widened to cover them: retightening `sigma`
to `0.954 ||S'C'||` puts `B_DDec` between `2^76.7` and `2^77.9`, the interval
spanned by whether `||E||_inf` is the `2^54` of the chain above or the `2^53.3`
of `BOUND_D`, and by whether the bound on `||S'C'||` is the constant fitted
above or one corrected for the last row being uniform rather than ternary.

**It does not follow that `q` can go back to the 78 bits this branch started
at.** Two things stand in the way, and the second is the real one. `q/2` at the
old basis is `2^77`, which that interval straddles rather than clears — which is
what an argued bound, rather than a fitted one, would have to settle. But
`p_min` is not only covering `B_DDec`: `SHUFFLE_BITS` is
`floor(log2 p_min) - ceil(log2 2 MSGS)`, so at `MSGS = 1000` two 39-bit primes
give 28 bits a pass and **five passes where 44-bit primes give four**. Elements
11% narrower, 25% more of them, is a proof 11% larger. Four passes survive only
while `floor(log2 p_min) >= 42`: two 43-bit primes, `q = 86`, worth 2% of the
sizes in section 10 and about four bits of lattice security rather than the
twenty-two the widening spent.

So the six bits are real but mostly unspendable here. They are worth having in
the **decryption phase**, which shares none of this: there `Pi_BND` is the whole
proof, `q` answers to `B_DDec` alone, and six bits of `q` is six bits of every
ciphertext and partial decryption. Nothing has been changed: taking them needs a
tail bound on `||S'C'||` that is argued rather than fitted to four measurements,
a new RNS basis, and a fresh estimator run. Every number below is at the `q`
that is in the sources.

**`q` has been raised accordingly.** At `N = 4096`, `NTI = 130`, `tau = 1000`
the corrected bound needs `q > 2^84.4`, so the RNS basis moved from two 39-bit
primes to two 44-bit ones and `q` from 78 to 88 bits. Two moduli still, so a
ring element is the same 64 KiB, and `p_min` rising to `2^44` improves Sections
6, 7 and 9 by five bits each into the bargain.

**What it costs in security, measured.** The paper ties `N = 4096` to `q` being
large, so raising `q` with `N` and the noise fixed makes every MLWE instance
easier, and the two constraints pull against each other: `B_Dec` grows with `N`,
so the `q` the decryption bound demands grows as `N^2.5`, while security wants
`N / log q` large. Running the lattice estimator on the BGV instance — rank-1
RLWE at `n = 4096`, ternary secret, error `p` times ternary — settles it:

| `q` | best attack |
| --- | --- |
| `2^78`, the paper's | `2^179.8` |
| `2^88`, this branch's | `2^157.7` (dual hybrid, `beta = 429`) |

So the paper's point carries about fifty bits more than the 128 it claims, and
the wider modulus spends twenty-two of them. `N = 4096` stands; the earlier
worry that it would have to double came from anchoring a hand estimate on the
claimed 128 rather than the actual margin.

The commitment was run through it too:

| instance | best attack |
| --- | --- |
| BGV encryption, rank-1 RLWE | `2^157.7` |
| BDLOP hiding, MLWE of rank `WIDTH - HEIGHT - SIZE = 1` | `2^155.8` |
| BDLOP binding, SIS at `beta = 2^21.5` | no solution exists |

Binding comes back not as a hard problem but as a vacuous one: the lattice has
dimension `N * WIDTH = 16384` and determinant `q^{N * HEIGHT}`, so its shortest
non-zero vector is around `2^27`, and the bound the verifier enforces on a
masked opening is `2^21.5`. Two openings that short cannot differ, whatever an
adversary computes. That was already true at 78 bits, where `lambda_1` is
`2^24.5`. **The commitment is statistically binding at these dimensions**, and
MSIS modulo `q` is not among the assumptions it needs.

One caveat on the numbers: the error `p e` with ternary `e` is modelled as a
discrete Gaussian of the same standard deviation, which is a modelling choice
the estimator has no exact form for.

**One constraint the wider modulus brought to light.** BDLOP hides only while
`WIDTH > HEIGHT + SIZE`. At `WIDTH = 4` and `HEIGHT = 1` the default `SIZE = 2`
leaves a margin of one, and `SIZE = 3` leaves none. The proof of shuffle was
built at `SIZE = 3` while its membership relation was the monomial one, which
needed `HEIGHT + 2` rows and so `SIZE >= 3` for `pismall`'s own commitment. With
`g(i) = i` that relation is `HEIGHT + 1` rows, the requirement is gone, and the
shuffle is built at the default again. It must stay there.

### 8.1 The rejection sampling of the linear proof, which had lost a step

`rej_sampling` in `src/shuffle.cpp` masks the three openings of every `Pi_LIN`
instance, and it was the same procedure as `pibnd_rej_sampling` above with one
line missing: it did **not** reject when `<z, beta r> < 0`. Its constants are
the ones that line pays for. `M = 1.75` is the `sqrt(3)` of the `b = 1` variant,
and `SIGMA_C = 2^12` is the paper's `sigma_C = 0.954 nu B_Com sqrt(kN)`, which
its Table 5 labels the standard deviation *for one-time commitments* — the
`b = 1` row. `git log -S` says the check was there when the function was
written, in `7b90ddd` of 2023-09-05, and was deleted the same day in `19fb1d7`,
"Polish"; the sibling in `pibnd.cpp` still has it.

**What it cost.** Without the halfspace restriction the bound on
`N_sigma(z) / N_{v,sigma}(z)` is the two-sided one, `exp((24 sigma ||v|| +
||v||^2) / 2 sigma^2)`, which at the measured `||beta r|| = 765` and
`sigma = 4096` is `9.6`, against the `1.75` the code divided by. So the
acceptance probability `r` exceeded 1 whenever `<y, beta r>` fell below `-3.09`
standard deviations, about one masked opening in a thousand, and those openings
were published with probability 1 where the sampler should have thinned them.
The published `z` was then not distributed as `D_sigma`, and the statistical
HVZK of Theorem 8 did not hold. At `MSGS = 1000` and four passes a shuffle
publishes `3 MSGS SHUFFLE_REPS = 12000` masked openings, so on the order of
twelve of them are biased, each towards the `beta r` it was supposed to hide.

It was a leak and not a hole: the verifier's checks are untouched, and a prover
that masks badly does not gain anything by it. Soundness was unaffected.

**The fix.** Three changes, in `rej_sampling` and its retry budget:

* the halfspace test is back, which is a revert of two lines of `19fb1d7`;
* `M` is no longer the fixed `1.75`. For `b = 1` the paper sets
  `M = exp(||v||^2 / 2 sigma^2)`, which this function can compute because it
  already has `||v||^2`, and which is the smallest value that dominates the
  ratio once `<z, v> >= 0` — `1.018` at the measured norm. Restoring the
  halfspace test without it would have cost far more than the leak was worth:
  the two together are what the standard deviation was chosen for;
* `LIN_TRIES` goes from 64 to 256.

**And the three tests became one.** `lin_prover` ran a rejection test per
masked opening where the standard procedure runs one over the concatenation,
which the README had already noted as the obvious saving. Restoring the
halfspace test made it more than a saving: paid three times it costs a factor
of two, paid once it costs nothing, and the transcript leaks one halfspace bit
rather than three, which is tighter zero-knowledge and not merely faster.
`rej_sampling` is now `rej_accum`, which folds `<z, v>` and `||v||^2` over one
opening, and `rej_decide`, which tests the three together against an `M` taken
over the `||v||^2` of the concatenation.

**Measured**, instrumenting `lin_prover` to report the attempts each proof
needs, at `MSGS = 4`:

| | acceptance | mean restarts | longest run | `linear proof` |
| --- | --- | --- | --- | --- |
| before, no halfspace test | 0.197 | 4.1 | 21 | 277 Mcycles |
| halfspace test, three tests | 0.114 | 7.7 | 56 | 594 Mcycles |
| halfspace test, batched | **0.491** | 1.0 | 5 | **95 Mcycles** |

So the correct sampler, batched, is three times *cheaper* than the incorrect
one it replaces. `LIN_TRIES` went to 256 for the middle row, where
the old budget of 64 would have given up on one proof in 2400 and a shuffle at
`MSGS = 1000` runs 4000 of them; at 0.491 it is far past anything needed, and
it is kept because a cap is only reached when the witness is long, and costs
nothing when it is not.

## 9. The compression by rho

Each message is a tuple of `SIZE` ring elements, and the proof of shuffle does
not work on tuples. `run()` folds them into one value first,

```
ms_i = sum_{j<SIZE} rho_j m_{i,j},      rho_0 = 1, the rest drawn,
```

and proves that the compressed output list is a permutation of the compressed
input list. Nothing downstream ever sees the components again, so **any change
to the output list that the compression absorbs is invisible**: a prover who
alters it by any `Delta` with `sum_j rho_j Delta_j = 0` changes no value the
proof is given.

As the code originally stood this was not a `2^-44` event but a free one. `rho`
was `nfl::uniform()`, derived from nothing, and drawn once before the passes. A
prover holding it solves one linear condition and walks through: the test
`KNOWN GAP: a compression collision is accepted` did exactly that, building
`Delta_1` in a single CRT slot with `Delta_0 = - rho_1 Delta_1`, and the proof
accepted an output list that was demonstrably not a permutation of the input.

**Two changes close it.**

* `shuffle_rho_hash()` derives `rho` from the input commitments and the
  *components* of the output list. It cannot be derived from the compressed
  `ms`, which depends on `rho`; hashing the components instead is what makes the
  dependency circular for an attacker. Altering the list moves `rho`, so a
  collision computed for one list is not a collision for the list that induces
  it. The test now builds the collision against the `rho` the honest list
  induces — the best a prover can do without grinding — and the proof rejects.
* `rho` is drawn afresh in each pass, so the repetitions of Section 6 amplify
  the residual `1 / p_min` the way they cover the product argument. This one
  amplifies whatever 7.1 does, because `rho` is a hash of the input commitments
  and the output list alone: a prover cannot move one pass's `rho` without
  changing the list, and that moves all of them. What it did cost was the
  structure 6.1 reports — the compression, the key it induces and everything
  committed under that key moved inside the pass, which is what left each pass
  free-standing. 6.1 puts the `sigma_i` and their sub-proofs back outside by
  committing them under the original key; the compression itself stays in.

The cost of the second is real: the membership sub-proofs are produced
`SHUFFLE_REPS` times rather than once. Sharing one `rho` across the passes would
avoid it and leave a single collision good for all of them, so it is not a trade
worth making; the cheaper structure, if it is ever wanted, is to commit the
`sigma_i` under the original key rather than the `rho`-dependent one, which
makes them and their sub-proofs `rho`-independent again at the cost of a second
key threaded through `lin_prover` and `lin_verifier`.

## 10. Coverage: what has been looked at

A document about what is established should say where the looking stopped.

**Reviewed and clean.** `bgv.cpp`, read with the question of Section 2 in mind,
depends on nothing the splitting ring takes away: decryption computes
`v - s u`, centres each coefficient modulo `q` and reduces modulo `p`, which is
a statement about coefficient sizes and not about the ring's factors. There is
no invertibility, no factorisation, no per-slot reasoning, and the comparisons
all go through `util::equal`. That fits the pattern of everything above — the
splitting ring breaks *proofs*, not the encryption.

**Reviewed and found wanting**, each with its own section: the binding of the
repetitions to each other (6.1, the most serious of these, repaired for the
passes and open for the linear proofs inside them), the coefficient sets
of `Pi_SMALL` (5.2), the challenge set of `Pi_LIN` (7) and of `Pi_BND` (7, now
repaired), the slack bound feeding `q` and the six bits it now carries for
nothing (8), the rejection sampling of `Pi_LIN` (8.1), the compression by
`rho` (9), the mask of the AEx proof and the two ways to publish an abandoned
one (4.1), the abort in `simul_inverse` (4.2), and the two passes of the AEx
proof (5.5).

**Fixed on `main`, and not this branch's work.** The verifier's equality checks
compared a single CRT slot of 8192, NFLlib's `operator==` on polynomials being
element-wise and its `operator bool` being "some coefficient is non-zero".
`util::equal` and `util::is_zero` in `include/util.hpp` replaced them, and that
fix landed on `main` separately along with the same correction to `bgv.cpp`'s
assertions; this branch inherits it by merge. Lemma 5 does need it — a CRT-mixed
list fails the last relation only in the slots of one prime, so the old check
would have accepted what Section 3 rejects — but the detail belongs with the
commit that made it, not here.

**Not reviewed.** The linear proof's own soundness beyond its challenge set and
its masking; the extraction argument of the AEx proof, 5.5 having checked its
parameters and the composition of its passes but not the proof of Lemma 2
itself; and `vericrypt`/the ballot-submission side, which this repository does
not implement. The proof of shuffle's simulator is now 5.2, which is a review of
what the transcript reveals rather than a simulator.

**Sizes, at `MSGS = 1000`, `q = 2^88`, four passes.**

| | per pass | once | per vote |
| --- | --- | --- | --- |
| responses of the `MSGS` linear proofs, `LIN_REPS` each | 251 MB | | 1002 KB |
| `D_i` and `s_i` | 135 MB | | 540 KB |
| `P_i`, the commitments to the `sigma_i` | | 90 MB | 90 KB |
| `Pi_SMALL`, one AEx pass | | 76 MB | 76.0 KB |
| `Pi_BND` | | 7.9 MB | 7.9 KB |
| **total, four passes** | | | **1715 KB** |

The first messages of the linear proofs are not in the table because they are
not sent: 8.1 replaced them with a hash the verifier checks by rebuilding them,
which is what paid for the repetitions. `Pi_SMALL` is almost all opened
columns, `ETA * V * 3 * ceil(q/8)` per relation and flat per vote, which is
what 5.5's trade of `ETA` against `AEX_REPS` moves. The growth from the
523 KB per vote this branch started at is almost all Section 6's repetitions,
which multiply everything including the sub-proofs now that `rho` is drawn
inside them; the wider `q` adds 13%. For scale, the mixnet of ePrint 2025/658
reports 110 KB per user per server for shuffle *and* decryption together.

## 11. Summary

| | before | on this branch |
| --- | --- | --- |
| product identity | `prod a_i = prod b_i` | Lemma 5, `g(i) = i` |
| CRT-mixed messages | accepted | rejected |
| membership `sigma_i in D` | not proven at all | `Pi_SMALL` and `Pi_BND`, see 5 |
| algebraic half of membership | n/a | exact over `Z_q`, see 5.1 |
| `sigma_i` not a ring constant | accepted | rejected, exactly, see 5.1 |
| CRT-mixed `sigma_i` | accepted | rejected, by the norm bound |
| the *other* sets of `Pi_SMALL` | per CRT component | per CRT component, see 5.2 |
| the two sub-proofs as one opening | n/a | argued modulo each `p_j`, see 5.4 |
| challenge set of `Pi_BND` | ternary, in neither instantiation | `{0,1}`, the paper's own, see 7 |
| `sigma_Bnd` against `\|S'C'\|` | 1.35, sized for ternary challenges | 86, where 0.954 suffices: six bits of slack, see 8 |
| masking of `Pi_LIN` | one-time constants, two-sided test | halfspace test back, `M` from the paper, see 8.1 |
| challenge differences of `Pi_LIN` | assumed invertible | **zero divisors, see Section 7** |
| soundness error of `Pi_LIN` | `~2^-39`, unnoticed | `2^-44` an instance, `2^-132` by `LIN_REPS`, see 7.1 |
| assumptions | MSIS and MLWE mod `q` | and MSIS mod each `p_j`, see 5.4 |
| soundness error of the product argument | `~2^-29` | `~2^-132`, once the passes were bound to one first message, see 6.1 |
| the passes under Fiat-Shamir | ground one at a time | `tau, mu, beta` bound across passes, see 6.1 |
| `Pi_LIN`'s own challenges | one per proof, ground one at a time | `LIN_REPS` from one hash, `2^-134` for the protocol, see 7.1 |
| first messages of `Pi_LIN` | sent, 180 MB a pass | rebuilt by the verifier, see 7.1 |
| the AEx proof's two passes | ground one at a time, `2^75` | one pass over `GR(q,4)`, `2^-128`, see 5.5 |
| a singular `b_i` | aborts, and says which permutation | restarts the pass, see 4.2 |
| `Pi_SMALL` and `Pi_BND` | once per pass | once for all passes, `-14%` and `6.5x`, see 6.1 |
| compression of the components by `rho` | free, `rho` not a challenge | `~2^-176`, see Section 9 |
| `q` | 78 bits | 88 bits, see Section 8 |
| lattice security | claimed 128 bits | `2^158` encryption, `2^156` hiding, see 8 |
| commitment binding | MSIS mod `q` | statistical, no assumption, see 8 |
| mask on the published `s_i` | ternary | uniform, see Section 4 |
| mask of the AEx proof | fixed seed | seeded from the OS, see 4.1 |
| a prover that abandons masking | publishes and verifies | refused, see 4.1 |

## 12. What these numbers were checked against

A document like this accumulates figures that were right when they were written
and stopped being right when a parameter moved underneath them. Five were found
that way in the course of one day's work — `2^-29` for a pass of the product
argument, `2^-26` for the singular case of `simul_inverse`, `2^-66` and `2^-82`
for `Pi_SMALL`, and a factor of 762 in 5.4 — each correct at the 39-bit basis
Section 8 replaced, and each believed until it was recomputed. So this section
records a sweep of the whole document against the sources as they stand, what it
found, and what it could not check.

**Corrected by the sweep.** 5.4's margin, `762`, which is 24000 at the current
basis. Section 8's `q > 2^84.7`, which recomputes to `2^84.4`. Three rows of
Section 11: `Pi_LIN`'s soundness error, which 8.1 moved from `2^-176`-by-the-
repetitions to `2^-132` by `LIN_REPS`; `Pi_LIN`'s own challenges, which 7.1
closed and the table still called open; and the rows missing for 4.2, 5.5 and
8.1. And the memory figure in the README, which was an estimate rather than a
measurement, and wrong by a factor of three.

**Measured rather than extrapolated.** Peak resident memory of `shuffle`,
sampled while the buffers are allocated:

| `MSGS` | 8 | 16 | 32 | 64 |
| --- | --- | --- | --- | --- |
| peak | 342 MiB | 453 MiB | 677 MiB | 1119 MiB |

That is 13.9 MiB a message on a 231 MiB base, linear to within 1%, so
`MSGS = 1000` is about **13.8 GiB**.

**What has not been run.** Nothing here has been run at the paper's parameters.
Every figure in this document that says `MSGS = 1000` is arithmetic from the
code's constants, not a measurement: the machine this was written on has 15 GB
and 13.8 of them are not available. The largest instances actually executed are
`MSGS = 64` for the shuffle, `TAU = 32` for `Pi_BND` and `TAU = 16` for the AEx
proof. The soundness arguments do not depend on the size, but the size and
memory claims of Section 10 and the README do, and they remain extrapolations
from a measured slope.

**What could not be checked here.** The lattice-security figures of Section 8
are estimator runs from an earlier session and were not repeated. The proof
sizes of Section 10 are arithmetic from the parameters rather than measurements
of a serialised proof, because nothing in this repository serialises one.

**What is most likely to rot next.** Anything keyed to `p_min`: 5.4's margin,
Section 6's pass count, Section 7's `2^-44`, 7.1's `LIN_REPS` and 5.5's two
terms all move together if the RNS basis moves again. Then the sizes, if
`LIN_REPS`, `ETA` or `AEX_REPS` change. The benchmarks are single runs on a
loaded machine and should be read as ratios, not absolutes.
