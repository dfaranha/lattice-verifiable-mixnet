# Soundness of the proof of shuffle on this branch

## Status of this document

This is a **draft argument, not a reviewed result.** It records what the
`fix-pkc` branch changes in `src/shuffle.cpp`, why those changes are believed
to be necessary and sufficient against the published attack, and — just as
importantly — **what this branch still does not prove.** Section 6 is the part
to read before trusting anything here: the fix is incomplete by construction,
and the test suite asserts the remaining hole rather than hiding it.

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

## 6. What is **not** established

**Lemma 5 requires `sigma_i in D`, and this branch does not prove it.**

Protocol 1 of ePrint 2025/658 discharges that requirement with a sub-proof of
`is_bin(sigma_i)` delegated to a general-purpose proof system. The `fix-pkc`
branch of the CT-RSA 2021 code discharges it with a norm check on a masked
opening of `sigma_i`, which works there because `k = 2`. Neither is available
here, and nothing has replaced them. A prover who applies to the committed
`sigma_i` the same CRT mixing it applies to the messages balances `(**)` in
every slot again and is accepted. The test

```
KNOWN GAP: CRT-mixed sigma is accepted, D is not proven
```

asserts exactly that, so that adding a membership sub-proof turns the test red
and forces it to be rewritten as the rejection it should be.

What this branch does buy: the attack of Section 4.1 of the paper, the one
mounted against the CT-RSA 2021 implementation, mixes the *messages* and leaves
the index encodings alone. That attack is now rejected, and rejected by the
intended check — instrumenting `shuffle_chal_hash` to force `tau = 0`, which
collapses `(**)` back to Neff's product, makes it pass again.

Three ways to close the gap, none of them small:

1. **An exact coefficient-level proof that `sigma_i` is a monomial**, that is,
   binary coefficients summing to one. `pismall` already proves, exactly and
   amortized over `TAU` relations, that committed witnesses are ternary; what
   is missing is a coefficient-level linear constraint, which its AEx encoding
   could express in principle. This is the most promising route because the
   machinery is already in the repository.
2. **Move `D` to the small scalars**, `g(i) = i`, which is the choice of Costa,
   Martínez and Morillo and is legal here because a non-zero scalar smaller
   than `p_1` is coprime to `q` and hence a unit. Membership then means "is a
   small element of degree 0", which a masked opening *can* establish if the
   challenge of that sub-proof is itself a scalar, since the response is then a
   scalar too. The catch is that responses grow linearly in the magnitude of
   the challenge while the binding of the commitment leaves only a small factor
   of slack, so the challenge has to be small and the sub-proof repeated, with
   the repetitions amortized over all `MSGS` commitments. This needs a proper
   parameter derivation before anyone builds it.
3. **Delegate the sub-proof** to a general-purpose lattice proof system, which
   is what Protocol 1 does, at the cost of a large new dependency.

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

## 8. Summary

| | before | on this branch |
| --- | --- | --- |
| product identity | `prod a_i = prod b_i` | Lemma 5, `D` the monomials |
| CRT-mixed messages | accepted | rejected |
| CRT-mixed `sigma_i` | n/a | **accepted, see Section 6** |
| verifier equality | one slot in 8192 | all slots |
| soundness error of the product argument | `~2^-29` | `~2^-29`, unchanged |
| mask on the published `s_i` | ternary | uniform, see Section 5 |
