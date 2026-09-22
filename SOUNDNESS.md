# Soundness of the proof of shuffle on this branch

## Status of this document

This is a **draft argument, not a reviewed result.** It records what the
`fix-pkc` branch changes in `src/shuffle.cpp`, why those changes are believed
to be necessary and sufficient against the published attack, and — just as
importantly — **the assumptions it rests on.** Sections 6 and 8 are the parts to
read before trusting anything here: section 6.2 reports a defect in `Pi_SMALL`
itself, not only in the proof of shuffle, section 6.4 closes the argument at the
cost of assuming MSIS modulo each prime of the RNS basis and not only modulo
their product, and section 8 reports that the challenge set of the linear proof
contains zero divisors, so that proof has no soundness argument of its own and
is carried by the repetitions of section 7. Section 10 reports the one term the
repetitions do not reach, the compression of the message components by `rho`,
which stood at `2^-39` until `rho` was made a per-pass challenge. The
test suite asserts all three defects, and the inequality 6.4 depends on, rather
than hiding any of them.

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
| `q` | modulus, `p_1 * p_2` | 88 bits, was 78; see Section 9 |
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
Section 6 explains why the constants win.

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
   before anything else. Section 6 says why it takes two.
6. Everything after the `P_i` is run `SHUFFLE_REPS` times with independent
   challenges, because one pass of the product argument is worth only
   `MSGS / p_min`. Section 7.

## 4. The second bug: element-wise equality

Independently of the above, the verifier's equality checks were not checking
equality. NFLlib overloads `operator==` on polynomials **element-wise**, and
`operator bool` on a polynomial is "some coefficient is non-zero". So

```
tmp == zero
```

is true as soon as *one* of the 8192 slots of `tmp` vanishes, and `a == b` as
soon as `a` and `b` agree in one slot. A prover who satisfies a verification
equation in a single slot and in no other passed.

This is the same slot-by-slot cheating as the attack above, one level lower,
and it is fatal to the fix if left in place: the CRT-mixed list is rejected
because the last relation fails in the slots of `p_1`, but it still holds in
the slots of `p_2`, so the old check would accept. `util::equal` and
`util::is_zero` in `include/util.hpp` compare all residues and are used
instead. Both fixes were verified to matter on their own: with the index
binding in place but the element-wise comparison restored, the attack test
goes back to passing.

That fix is independent of the rest of this branch and landed on `main`
separately, together with the same correction to the assertions in `bgv.cpp`;
this branch inherits it by merge.

Note that `operator!=` is *not* affected in the same way — "some slot differs"
is the right semantics for an inequality — so `bdlop_open`, which uses `!=`,
was always strict.

## 5. Zero knowledge: the mask on the published s_i

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

### 5.1 The mask of the AEx proof, and two ways to publish one

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

## 6. The membership sub-proof

Lemma 5 requires `sigma_i in D`. This branch proves it with two sub-proofs run
on the same commitments: `Pi_SMALL` for the algebraic half, which says exactly
that `sigma_i` is a ring constant, and `Pi_BND` for the half no
algebraic identity can give over a composite modulus, which says that its
`Pi_BND` for the size half that no algebraic identity can give over a composite
modulus. Section 6.4 is the argument that reads the two as statements about one
opening, which needs MSIS modulo each prime of the basis rather than only modulo
`q`, and which concludes with the invertibility Lemma 5 asks for.

### 6.1 What is proven

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
`p_1` is a zero divisor. That is what Sections 6.3 and 6.4 supply between
them.

The soundness error of one pass of the AEx proof is not negligible -- the
challenge lives in `GR(q,2)`, so a pass is worth about `3 tau / p_min^2`, around
`2^-66` at `tau = 1024` -- so a proof is `AEX_REPS` independent passes and the
verifier requires every one of them, which is how the test of `pismall.cpp` runs
it too.

### 6.2 The sets are per CRT component, and here that is a feature

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
that is precisely the hypothesis Section 6.4 needs.

### 6.3 The norm bound

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
* The last witness row is sampled with `sigma-hat_ANEx`, which needs the
  quad-precision sampler only when it runs past `2^64`, as it does when that row
  is the mix-net's decryption noise. Here the row is a committed constant and
  `sigma-hat` is a few thousand, so the double sampler covers it. Choosing the
  sampler by magnitude rather than by row index makes `Pi_BND` about ten times
  faster, the mix-net's own instance included.

The challenge matrix is never stored: both sides derive it from the transcript
hash and consume it once, row by row, so `pibnd` keeps a single row. At
`TAU = 1000` the matrix would be 8 GiB.

### 6.4 Why the two sub-proofs speak about one opening, and what follows

`Pi_SMALL` is an *exact* proof of knowledge: its extractor outputs a witness
satisfying the relation and the coefficient sets with no relaxation. `Pi_BND`,
like every Fiat-Shamir Sigma protocol of its shape, extracts a *relaxed*
opening: a short `s'` and a short non-zero `c` with `A s' = t c`, where `c` is a
difference of challenges. Reading the `sigma_i` of the two as one ring element
takes an argument, because the obvious one does not work: multiplying the exact
relation by `c` and subtracting gives `A (c r - r') = 0`, and the binding of the
commitment says nothing, since `r` is short only in each CRT component and `c r`
need not be short over `Z_q` at all.

The way through is to stop working over `Z_q`, and it is Section 6.2 that makes
it possible. Write the extracted randomness in CRT form, `r = e_1 r^(1) + e_2
r^(2)`. What 6.2 calls a defect says exactly that each `r^(j)` is ternary **as
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
parameters in force, with a factor of 762 to spare at `MSGS = 1000`.

**The cost is one assumption the mix-net did not make before:** MSIS modulo each
prime of the basis. It is genuinely additional, and Section 9 says why in
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

## 7. Soundness error of the product argument

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

Only the product argument repeats. The prover's first message -- the
commitments `P_i` to the `sigma_i` and the two sub-proofs of section 6 that
place them in `D` -- is sent once and shared by every pass, which is also
forced: the `sigma_i` have to be fixed before any challenge, so a pass cannot
re-commit to them.

The alternative remedy is the one `pismall` uses, drawing the challenges from
the quadratic Galois extension `GR(q,2)` so that a single challenge is worth
`deg / p_min^2`. It was not taken. It buys `2^-68` per pass and so still needs
two passes, while lifting `a_i`, `b_i`, the masks `theta_i`, the published
`s_i` and the commitments `D_i` into the extension doubles every element of the
argument: about four times the size against five for plain repetition, in
exchange for a protocol that would have to be designed rather than repeated.

**Where this leaves the protocol.** At `MSGS = 1000` the terms are `2^-132` for
the product argument, about `2^-133` for `Pi_SMALL` — `2^-66` per pass from the
`GR(q,2)` challenge, squared by its two repetitions, with the column-opening
test at `2^-82` or better on 325 of 16384 columns at relative distance 0.48 —
and `Pi_BND` at its own `NTI = 130`. That leaves one term below `LEVEL`, and it
is not one of these: Section 10 reports that the compression of the message
components by `rho` costs `2^-44` a pass, and that it is now drawn inside them,
because `rho` is drawn once outside them. Setting that aside, the binding
constraint is the hardness of the lattice problems the commitment and the
encryption rest on — with the caveat that section 6.4 adds one of them, MSIS
modulo each prime of the basis.

These repetitions turn out to carry more than the term they were sized against.
Section 8 reports that the linear proof is worth about `2^-44` per pass for an
unrelated reason, and it is the same repetitions that compose it to `2^-176`.
Removing them because the product argument had been strengthened by some other
means would reopen that.

## 8. The challenge sets of the Sigma-protocols

The same disease reaches one level lower than sections 2 and 7, into the
challenge sets themselves, and it had not been looked at.

`lin_hash` draws the challenge `beta` of the linear proof with
`bdlop_sample_chal`, the difference of two ternary vectors of Hamming weight
`NONZERO = 36`. Every argument about that proof wants such elements, and the
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
message. So the honest reading is **39 bits per pass, not 128**, and there is no
soundness proof at all, since the extraction argument needs the invertibility
the test denies.

**Why the protocol survives.** Section 7 repeats everything after the first
message `SHUFFLE_REPS` times with independent challenges, and a prover whose
output list is not a permutation has to defeat every pass, each with its own
`beta`. At four or five passes that composes to `2^-176` or better. This was not
the reason the repetitions were introduced — they were sized against the `2^-34`
of the product argument, which is the weaker term — but they cover this as well.
The practical conclusion is that the repetitions carry more weight than their
stated purpose, and removing them on the grounds that the product argument had
been improved by other means would reopen this.

**The same question, asked of `Pi_BND`, has a sharper answer.** Its challenge
matrix is drawn from `nfl::ZO_dist()`, full-weight ternary ring elements. Baum
et al. [8] give two instantiations of the amortized proof: Theorem 1 over
`R = Z` with `C = {0,1}`, and Theorem 2 over `R = Z[X]/(X^d + 1)`, which is the
one that applies here since `A` is a matrix of polynomials. Theorem 2 fixes

```
C = {0} union {+/- X^j},
```

monomials and zero, and its extraction rests on their Lemma 4: for
`a, b` in that set, `2 (a - b)^-1` has coefficients in `{-1, 0, 1}`. That is a
statement about monomials, and it is what makes the extractor work. **A ternary
challenge matrix is not that set**, Lemma 4 says nothing about it, and in this
ring the differences have no invertibility to fall back on — which is Section 8
one level up. So `Pi_BND` as implemented runs outside the soundness proof it
cites.

There is something to gain from fixing it rather than only a debt to pay. With
the intended challenge set, Theorem 2's extractor returns `A S' = 2 T`, a clean
factor of two rather than an arbitrary short `c`, and `Section 6.4` would
simplify accordingly: the argument there carries `c` through only to cancel it
at the end.

`bdlop_open` uses the same challenge set as `Pi_LIN`, but `pismall` calls it
with the factor fixed to one, so nothing there depends on a challenge being
invertible.

## 9. The decryption phase: `B_DDec` and the size of `q`

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
`src/pibnd.cpp` carries.

Measurement agrees, and pins the exponents rather than the form alone.
Instrumenting `pibnd_rej_sampling`:

| change | change in `||S'C'||` |
| --- | --- |
| `tau` 8 -> 32 -> 128 | +1.004, +0.999 bits |
| `NTI` 8 -> 32 | +0.998 bits |

so `||S'C'||` grows as `sqrt(tau) sqrt(NTI)`, and `sigma / ||S'C'|| = 1.35` at
every point — the form *and* the constant in `pibnd.cpp` are right. With the
paper's constant instead, the honest prover exhausts `PIBND_TRIES` every time
and the test `BND proof is consistent` fails.

**`q` has been raised accordingly.** At `N = 4096`, `NTI = 130`, `tau = 1000`
the corrected bound needs `q > 2^84.7`, so the RNS basis moved from two 39-bit
primes to two 44-bit ones and `q` from 78 to 88 bits. Two moduli still, so a
ring element is the same 64 KiB, and `p_min` rising to `2^44` improves Sections
7, 8 and 10 by five bits each into the bargain.

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

## 10. The compression by rho

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
* `rho` is drawn afresh in each pass, so the repetitions of Section 7 amplify
  the residual `1 / p_min` the way they cover the product argument. That is why
  the whole body of `run()` is now the pass: the compression, the key it
  induces, the commitments to the `sigma_i` under that key, and the sub-proofs
  about them all depend on `rho` and all move inside.

The cost of the second is real: the membership sub-proofs are produced
`SHUFFLE_REPS` times rather than once. Sharing one `rho` across the passes would
avoid it and leave a single collision good for all of them, so it is not a trade
worth making; the cheaper structure, if it is ever wanted, is to commit the
`sigma_i` under the original key rather than the `rho`-dependent one, which
makes them and their sub-proofs `rho`-independent again at the cost of a second
key threaded through `lin_prover` and `lin_verifier`.

## 11. Coverage: what has been looked at

A document about what is established should say where the looking stopped.

**Reviewed and clean.** `bgv.cpp`, read with the question of Section 2 in mind,
depends on nothing the splitting ring takes away: decryption computes
`v - s u`, centres each coefficient modulo `q` and reduces modulo `p`, which is
a statement about coefficient sizes and not about the ring's factors. There is
no invertibility, no factorisation, no per-slot reasoning, and the comparisons
all go through `util::equal`. That fits the pattern of everything above — the
splitting ring breaks *proofs*, not the encryption.

**Reviewed and found wanting**, each with its own section: the coefficient sets
of `Pi_SMALL` (6.2), the challenge set of `Pi_LIN` (8) and of `Pi_BND` (8), the
slack bound feeding `q` (9), the compression by `rho` (10), the mask of the AEx
proof and the two ways to publish an abandoned one (5.1).

**Not reviewed.** The linear proof's own soundness beyond its challenge set; the
proof of shuffle's simulator; and `vericrypt`/the ballot-submission side, which
this repository does not implement.

**Sizes, at `MSGS = 1000`, `q = 2^88`, four passes.**

| | per pass | per vote |
| --- | --- | --- |
| shuffle core, `MSGS` linear proofs plus `D_i`, `s_i`, `P_i` | 480.5 MB | 492.0 KB |
| `Pi_SMALL`, two AEx passes | 108.0 MB | 110.5 KB |
| `Pi_BND` | 7.9 MB | 8.1 KB |
| **total, four passes** | | **2442 KB** |

`Pi_SMALL` is 105 of its 108 MB in opened columns, so its cost is
`ETA * V * 3 * ceil(q/8)` per relation and flat per vote. The growth from the
523 KB per vote this branch started at is almost all Section 7's repetitions,
which multiply everything including the sub-proofs now that `rho` is drawn
inside them; the wider `q` adds 13%. For scale, the mixnet of ePrint 2025/658
reports 110 KB per user per server for shuffle *and* decryption together.

## 12. Summary

| | before | on this branch |
| --- | --- | --- |
| product identity | `prod a_i = prod b_i` | Lemma 5, `g(i) = i` |
| CRT-mixed messages | accepted | rejected |
| membership `sigma_i in D` | not proven at all | `Pi_SMALL` and `Pi_BND`, see 6 |
| algebraic half of membership | n/a | exact over `Z_q`, see 6.1 |
| `sigma_i` not a ring constant | accepted | rejected, exactly, see 6.1 |
| CRT-mixed `sigma_i` | accepted | rejected, by the norm bound |
| the *other* sets of `Pi_SMALL` | per CRT component | per CRT component, see 6.2 |
| the two sub-proofs as one opening | n/a | argued modulo each `p_j`, see 6.4 |
| challenge differences of `Pi_LIN` | assumed invertible | **zero divisors, see Section 8** |
| soundness error of `Pi_LIN` | `~2^-39`, unnoticed | `~2^-176` by the repetitions |
| assumptions | MSIS and MLWE mod `q` | and MSIS mod each `p_j`, see 6.4 |
| verifier equality | one slot in 8192 | all slots |
| soundness error of the product argument | `~2^-29` | `~2^-132`, see Section 7 |
| compression of the components by `rho` | free, `rho` not a challenge | `~2^-176`, see Section 10 |
| `q` | 78 bits | 88 bits, see Section 9 |
| lattice security | claimed 128 bits | `2^158` encryption, `2^156` hiding, see 9 |
| commitment binding | MSIS mod `q` | statistical, no assumption, see 9 |
| mask on the published `s_i` | ternary | uniform, see Section 5 |
| mask of the AEx proof | fixed seed | seeded from the OS, see 5.1 |
| a prover that abandons masking | publishes and verifies | refused, see 5.1 |
