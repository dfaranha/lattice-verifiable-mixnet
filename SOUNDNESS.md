# Soundness of the proof of shuffle on this branch

## Status of this document

This is a **draft argument, not a reviewed result.** It records what the
`fix-pkc` branch changes in `src/shuffle.cpp`, why those changes are believed
to be necessary and sufficient against the published attack, and — just as
importantly — **what this branch still does not prove.** Section 6 is the part
to read before trusting anything here: section 6.2 reports a defect in
`Pi_SMALL` itself, not only in the proof of shuffle, and section 6.4 states the
one step of the argument that has not been worked out. The test suite asserts
the defect of 6.2 rather than hiding it.

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
| `q` | modulus, `p_1 * p_2` | 78 bits |
| `p_1, p_2` | RNS basis, of the form `2^39 - i * 2^15 + 1` | 549701287937, 549682413569 |
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

## 3. The fix: Lemma 5 with D the monomials

Lemma 5 of ePrint 2025/658 replaces `(*)` with

```
prod (a_i + g(i) * X1 - X2) = prod (b_i + sigma_i * X1 - X2)                    (**)
```

where `g : [N] -> D` is injective, `D` is a set whose pairwise differences are
invertible, and `sigma_i in D` is committed before `X1, X2` are drawn. Tying
each message to its index forces the per-component permutations to agree.

**Choice of D.** We take `D = {x^i}` and `g(i) = x^i`. Their differences are
invertible in this ring:

```
x^a - x^b = x^b (x^{a-b} - 1),  0 <= b < a < N,
```

`x^b` is a unit, and each NTT slot evaluates `x` at a primitive `2N`-th root of
unity `r`, so `r^{a-b} = 1` would need `2N | a - b`, impossible for
`0 < a - b < N`. The test `monomial differences are invertible` checks this.
`g` is injective for `i < N`, so the encoding supports up to `N = 4096`
messages; `MSGS` is `static_assert`ed against that bound.

The two sets used elsewhere are **not** available here:

* *Binary polynomials*, the choice of Protocol 1 of ePrint 2025/658. Their
  differences are ternary, which is short, and shortness gives nothing at
  `k = 2N`. The test `a short polynomial can be a zero divisor` exhibits a 0/1
  polynomial of Hamming weight 22 and `l_infinity`-norm 1 that is a zero
  divisor in this exact ring. It was found by meet-in-the-middle over subset
  sums of the powers of one primitive `2N`-th root modulo `p_1`, in seconds on
  a laptop.
* *A ball of small norm*, the choice of the `fix-pkc` branch of the CT-RSA 2021
  code. Same objection, for the same reason.

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

5. The prover also runs `pismall_mono_prove()` and `pibnd_short_prove()` on the
   `P_i`, one amortized proof each that every committed `sigma_i` is a monomial
   in each CRT component and that the openings are short, and the verifier
   checks both before anything else. Section 6 says why it takes two.

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

## 6. The membership sub-proof

Lemma 5 requires `sigma_i in D`. This branch proves it with two sub-proofs run
on the same commitments: `Pi_SMALL` for the algebraic half, which says that
`sigma_i` is a monomial in each CRT component, and `Pi_BND` for the half no
algebraic identity can give over a composite modulus, which says that its
coefficients are small enough for the two components to be the same monomial.
What has not been worked out is the step that reads the two as statements about
one opening; that is 6.4.

### 6.1 What is proven

`pismall_mono_prove()` runs the amortized exact proof of `src/pismall.cpp` over
all `MSGS` commitments `P_i` to the `sigma_i`, as one proof. The relation is the
commitment equation itself,

```
  row 0    P_i.c1 = r_0 + sum_j A1[0][j] r_{j+1}
  row 1    P_i.c2 = sum_j A2[0][j] r_j + sigma_i
  row 2    0      = Y_i - w sigma_i,          w = 2 - sum_{j<N} x^j public,
```

so the witness the proof binds is an opening of `P_i` and no link between two
commitment schemes is needed: `sigma_i` is the value inside the commitment the
linear proof already speaks about. The coefficient sets are ternary for the
commitment randomness `r`, binary for `sigma_i` and `{-1, 1}` for `Y_i`.

Being a monomial is not a coefficient-wise property, but it splits into two
that are. For binary `sigma` of Hamming weight `S` with partial sums `A_i`,

```
  (sigma * w)_i = S - 2 A_{i-1},          A_{-1} = 0,
```

because `x^k (sum_j x^j) = sum_{j>=k} x^j - sum_{j<k} x^j` in the negacyclic
ring. Its constant coefficient is `S`, and `0 <= S <= N < q - 1`, so all
coefficients of `sigma w` lie in `{-1, 1}` exactly when `S = 1`, that is when
`sigma` is one of the monomials `x^i`. The two tests
`monomial membership proof is consistent` and
`monomial membership rejects a binary non-monomial` in `pismall` cover both
directions; the second one is caught by the `Y` row, since a binary `sigma` of
Hamming weight two passes the binary row unharmed.

The soundness error of one pass of the AEx proof is not negligible -- the
challenge lives in `GR(q,2)`, so a pass is worth about `3 tau / p_min^2`, around
`2^-66` at `tau = 1024` -- so a proof is `AEX_REPS` independent passes and the
verifier requires every one of them, which is how the test of `pismall.cpp` runs
it too.

### 6.2 Why it is not enough on its own: the sets are per CRT component

**The proof is coefficient-wise but not exact, because `q` is composite.** What
it checks for the binary set is the polynomial identity `c (c - 1) = 0` at every
coefficient position. Over a field that has two roots. Over
`Z_q = Z_{p_1} x Z_{p_2}` it has four: `0`, `1`, and the two CRT idempotents.
Ternary gives 9 roots instead of 3, and `{-1, 1}` gives 4 instead of 2. The test

```
KNOWN GAP: the coefficient sets are per CRT component
```

in `pismall` exhibits a witness that is `+1` modulo `p_1` and `-1` modulo `p_2`
in every coefficient — an element of full size over `Z_q` — and the proof
accepts it as ternary.

For the shuffle the consequence is exact: what `pismall_mono_prove()`
establishes is that `sigma_i` is a monomial **in each CRT component**, which is
one component short of `sigma_i in D`. The prover of the test
`shuffle proof rejects CRT-mixed sigma` is precisely of that shape, and this
sub-proof accepts it. What rejects it is the norm bound of 6.3.

**No purely algebraic identity can do better.** The solution set of any system
of polynomial equations over `Z_q` is the product of the per-component solution
sets, while `D = {x^i}` is the diagonal of such a product and not a product
itself. So membership in `D` cannot be established by polynomial identities over
a composite modulus, whatever the identities are. It needs a prime modulus, or
information that is not algebraic — a bound on the size of the coefficients.

**This observation is not specific to the monomial instance.** It is the
exactness claim of `Pi_SMALL` itself: for the commitment randomness the proof
establishes "ternary in each CRT component", membership in a set of 9 values of
which 6 are full-size over `Z_q`, and not "ternary". Anything in this repository
that reads `Pi_SMALL` as an exact norm statement inherits that.

### 6.3 The norm bound, which closes it

`pibnd_short_prove()` bounds the openings of the same `P_i`. `Pi_BND` of
`src/pibnd.cpp`, the amortized approximate norm proof already in this
repository, is instantiated on the commitment equation itself,

```
  row 0    P_i.c1 = r_0 + sum_j A1[0][j] r_{j+HEIGHT}
  row 1    P_i.c2 = sum_j A2[0][j] r_j + sigma_i
```

`R = HEIGHT + 1` rows and `V = WIDTH + 1` components, amortized over exactly the
`MSGS` commitments and needing no padding, since nothing here is interpolated.
The row carrying `Y = w sigma_i` is left out: once `sigma_i` is binary over the
integers, `Y` is determined over the integers too and needs no bound of its own.

**Why the two sub-proofs together are exact.** The CRT idempotents `e_1` and
`e_2` are non-zero multiples of `p_2` and of `p_1`, so their centred
representatives are at least `min(p_1, p_2)`, about `2^39`; at the primes of
this RNS basis they are `+/- 67146933941338983279272`, about `2^75.8`. The bound
the verifier enforces on each masked opening is `sigma_ANEx * sqrt(2N)`, about
`2^23` at `MSGS = 2` and `2^27` at `MSGS = 1000`; extraction loosens it by a
small constant and no more. A coefficient of `sigma_i` is therefore in
`{0, 1, e_1, e_2}` by the membership proof and below `2^28` by the norm proof,
hence in `{0, 1}` as an integer. The `Y` row then reads `Y_0 = S`, the Hamming
weight, an integer in `[0, N]` that is `+/-1` in each CRT component, so `S = 1`
and `sigma_i = x^a`, an element of `D`. The margin is eleven bits in the worst
case a composite `q` of this size allows and forty-seven at these primes, so the
looseness of an approximate norm proof is irrelevant here.

The test `shuffle proof rejects CRT-mixed sigma` is the check: the prover this
branch used to accept is now rejected, and rejected by the norm bound, since the
membership proof on its own still accepts it.

Two implementation notes, both visible in `src/pibnd.cpp`:

* A prover whose witness is not short cannot pass rejection sampling.
  `pibnd_prover()` gives up after `PIBND_TRIES` attempts and emits the masked
  opening it has, which the verifier rejects on the norm test, rather than
  looping forever. An honest prover passes both checks with probability about
  `1/3` per attempt, so giving up is a `3^-64` event.
* The last witness row is sampled with `sigma-hat_ANEx`, which needs the
  quad-precision sampler only when it runs past `2^64`, as it does when that row
  is the mix-net's decryption noise. Here the row is a committed monomial and
  `sigma-hat` is a few thousand, so the double sampler covers it. Choosing the
  sampler by magnitude rather than by row index makes `Pi_BND` about ten times
  faster, the mix-net's own instance included, since its test witness is ternary
  as well.

### 6.4 What is still not checked

**The two sub-proofs are read as statements about one opening.** `Pi_SMALL`
extracts an exact opening of `P_i`. `Pi_BND`, like every Fiat-Shamir Sigma
protocol of this shape, extracts a relaxed one: a short `s'` with `A s' = t c`
for `c` a difference of challenges. The argument in 6.3 treats the `sigma_i` of
the two as the same ring element. Identifying them is the usual appeal to the
binding of the commitment scheme, except that the usual appeal wants the exact
opening to be short, which is the thing being proven. This is the step of this
branch that has not been worked out, and it is why this document still opens by
saying what it is.

Two alternatives to the pair of sub-proofs, both larger, and neither needed if
the step above goes through:

1. **Move `D` to the small scalars**, `g(i) = i`, the choice of Costa, Martinez
   and Morillo, legal here because a non-zero scalar smaller than `p_1` is
   coprime to `q` and hence a unit. Membership then means "is a small element of
   degree 0". The degree-0 half is exact even over composite `q`, since `c = 0`
   has one root and not four, but the smallness half needs the same norm bound
   and so the same argument.
2. **Delegate the sub-proof** to a general-purpose lattice proof system, which
   is what Protocol 1 of ePrint 2025/658 does, at the cost of a large new
   dependency. Such a system proves `is_bin` over the integers, norm included,
   in one proof and with one extraction.

## 7. Soundness error of the product argument

Worth stating plainly, because it is a property of the parameters rather than
of this branch, and the fix does not change it. Lemma 2 of ePrint 2025/658
(Schwartz-Zippel over a ring) needs a challenge set whose pairwise differences
are not zero divisors. The challenges here are uniform elements of `R_q`, which
in a ring this split is best analysed slot by slot: if the product identity
fails in some slot, the check passes only if the challenge hits a root of a
degree-`MSGS` polynomial in that slot, with probability at most
`MSGS / p_min`, about `2^-29` at `MSGS = 1000`. That is the soundness error of
the product argument, and it is far short of the 128 bits the parameters are
otherwise chosen for.

The same observation is made, and dealt with, elsewhere in this repository:
`pismall` draws its challenges from the quadratic Galois extension `GR(q,2)`
precisely so that a single challenge is worth `deg / p_min^2` rather than
`deg / p_min`. The remedies for the shuffle are the same — repeat the argument
with independent challenges, or draw them from an extension.

This term, and not the membership sub-proofs, is what bounds the whole protocol.
At `MSGS = 1000` the sub-proofs of section 6 contribute about `2^-133` for
`Pi_SMALL` — `2^-66` per pass from the `GR(q,2)` challenge, squared by the two
repetitions, with the column-opening test at `2^-82` or better on 325 of 16384
columns at relative distance 0.48 — and `Pi_BND` runs at its own `NTI = 130`.
All of that sits a hundred bits behind the `2^-29` above. Reading the fix of
section 6 as raising the soundness of the shuffle would therefore be a mistake:
it closes a hole that no number of bits would have closed, and leaves the
quantitative bound exactly where it was.

## 8. Summary

| | before | on this branch |
| --- | --- | --- |
| product identity | `prod a_i = prod b_i` | Lemma 5, `D` the monomials |
| CRT-mixed messages | accepted | rejected |
| membership `sigma_i in D` | not proven at all | `Pi_SMALL` and `Pi_BND`, see 6 |
| `sigma_i` outside `D`, one component | accepted | rejected |
| CRT-mixed `sigma_i` | accepted | rejected, by the norm bound |
| coefficient sets of `Pi_SMALL` | per CRT component | per CRT component, see 6.2 |
| the two sub-proofs as one opening | n/a | **not worked out, see 6.4** |
| verifier equality | one slot in 8192 | all slots |
| soundness error of the product argument | `~2^-29` | `~2^-29`, unchanged |
| mask on the published `s_i` | ternary | uniform, see Section 5 |
