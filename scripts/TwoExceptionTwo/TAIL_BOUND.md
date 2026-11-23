# Tail bound statement (Rankin part of a `deficient` leaf)

This is the single statement that every `deficient` leaf of the certificate (`cert.jsonl.xz`,
format in `FORMAT.md`) instantiates. Its Lean counterpart is `rankin_tail_general` with
`prod_fv_le_of_rankin_tail_general` in `OddPerfect/RankinTailGeneral.lean` and
`prod_fv_le_of_rankin_tail_general_pade` in `OddPerfect/RankinTailPade.lean` (with the hypotheses
on the rows stated through their prime factors), used through `defSound` of
`OddPerfect/TwoExcEngineTail.lean`; the text below is the specification the search follows. All hypotheses are rational or integral; no real root
appears. The hits and the bounded slots (a, b, c, d) are outside the statement (section 3).

## 1. Statement

**Data.**

* Integers x ≥ 2, k ≥ 3, u ≥ 0 and MHIT ≥ 1.
* A finite list K of integers g ≥ 2.
* A finite set P of integers p ≥ x with |P| ≤ u.

Primality is not needed for K or P, and neither is disjointness of K and P.

Put L = x² + x + 1 and M = max(L, MHIT).

**Witnesses** (rationals):

* (H1) for each g ∈ K, α_g with 0 < α_g < 1 and α_g^k · g ≥ 1;
* (H2) α_x with 0 < α_x < 1 and α_x^k · x ≥ 1;
* (H3) m_L ≥ 0 with m_L^{2k} · L^{k−2} ≥ 1;
* (H4) m_M ≥ 0 with m_M^{2k} · M^{k−2} ≥ 1.

Define

    G = ∏_{g ∈ K} 1/(1 − α_g),
    R = m_L · G · ((1 − α_x)^{−u} − 1) + m_M · G,
    S = ((x + 1)/x)² · R.

* (H5) S < 1 (old form) or S < 3 (Padé form).

**Rows.** Let T be a finite set of integers t ≥ x, and write n_t = t² + t + 1.

* (H6) Each t ∈ T satisfies (A) or (B).
  * (A) n_t = ∏_{g∈K} g^{e_g} · ∏_{p∈P} p^{f_p} with natural exponents and some f_p > 0.
  * (B) n_t = ∏_{g∈K} g^{e_g} with natural exponents, and n_t ≥ MHIT.

**Conclusion.**

    ∏_{t ∈ T} n_t / t² ≤ 1/(1 − S)                  (old form, S < 1),
    ∏_{t ∈ T} n_t / t² ≤ (S² + 4S + 6)/(6 − 2S)     (Padé form, S < 3).

## 2. Proof sketch (natural powers only)

1. **The rows are distinct.** t ↦ n_t is injective on t ≥ 0. Choose one representation (e, f)
   for each t. Then t ↦ (e, f) is injective, because the vector determines n_t.
2. **Each row is small.** Put y_t = (t+1)/t². Then y_t = ((t+1)/t)²/(t+1) ≤ ((x+1)/x)²/(t+1).
3. **Bound for class (A).** Let W = ∏ α_g^{e_g} · α_x^{Σ f_p}.
   * By (H1) and (H2), p ≥ x and α_x^k p ≥ 1, so W^k · n_t ≥ 1.
   * Since t ≥ x, n_t ≥ L. So by (H3), m_L^{2k} ≥ L^{−(k−2)} ≥ n_t^{−(k−2)}.
   * Therefore (m_L W)^{2k} ≥ n_t^{−(k−2)} · n_t^{−2} = n_t^{−k} > (t+1)^{−2k}, because
     (t+1)² > n_t.
   * Hence 1/(t+1) < m_L · W, by monotonicity of the 2k-th power on nonnegatives.
4. **Bound for class (B).** This is the same argument with α_x unused, n_t ≥ M (since
   n_t ≥ L and n_t ≥ MHIT) and (H4). It gives 1/(t+1) < m_M · ∏ α_g^{e_g}.
5. **Summing.** By injectivity, Σ_{(A)} W ≤ Σ_{e} ∏ α_g^{e_g} · Σ_{f ≠ 0} α_x^{Σ f}.
   This equals G · ((1 − α_x)^{−|P|} − 1) ≤ G · ((1 − α_x)^{−u} − 1). Similarly
   Σ_{(B)} ∏ α_g^{e_g} ≤ G. These are geometric series, since all α < 1. So Σ_{t∈T} y_t ≤ S.
6. **Conclusion.** n_t/t² = 1 + y_t, and ∏ (1 + y) ≤ ∏ 1/(1 − y) ≤ 1/(1 − Σ y) for y ≥ 0 with
   Σ y < 1. For the Padé form, `prod_one_add_le_pade21` (`OddPerfect/ProductBound.lean`) gives
   ∏ (1 + y) ≤ (s² + 4s + 6)/(6 − 2s) for y ≥ 0 and Σ y ≤ s < 3, by induction on T.

## 3. How a deficient leaf instantiates it

**Instantiation.** At the leaf's state with its x, take:

* K = the non-exact free primes ≡ 1 (mod 3) (field `K`);
* P = the undecided free primes (q if undecided, and the missing exceptions), with
  u = a + b (field `u`);
* MHIT = the header value 10^30;
* k, α_g, α_x, m_L, m_M from `rankin`.

**The set T.** T is the set of undecided square primes t ≡ 2 (mod 3), t ≥ x, dividing N, whose
row is of type (e) (all prime factors in K ∪ P; `FORMAT.md` rule 6), and that are
not hits.

**(H6) holds.** A row of type (e) either has some factor from P, which is (A), or is in ⟨K⟩.

* If it is in ⟨K⟩ with n_t ≥ MHIT, it is (B).
* If it is in ⟨K⟩ with n_t < MHIT, then n_t is a generated value. Its candidate t is an odd
  prime ≡ 2 (mod 3), at least x and unlisted, so t is a hit and not in T.

**The leaf inequality.** The leaf combines the statement with factors outside it:

    σ(N)/N < H · (x/(x−1))^{a+b} · ((x²+x+1)/x²)^{c+d} · ∏_{hits} n/t² · ∏_{t∈T} n_t/t²
           ≤ U = H · (x/(x−1))^{a+b} · ((x²+x+1)/x²)^{c+d} · ∏_{hits} n/t² · V < 2,

with V = 1/(1 − S) (old path, S < 1) or, when that U is not below 2,
V = (S² + 4S + 6)/(6 − 2S) (Padé path, S < 3).

The factors outside the statement are:

* H = hi: the listed components;
* (x/(x−1))^{a+b}: types (a) and (b);
* ((x²+x+1)/x²)^{c+d}: types (c) and (d);
* ∏_{hits} n/t²: the hits.

The bound contradicts σ(N)/N = 2.

## 4. Check against the certificate

The Python mirror of the Lean checker in `engine.py` checks, for each of the 707 `deficient`
leaves, (H1) to (H5) with the stored rationals, recomputes G, R and S from them, and checks that
U < 2 for the product of section 3, as the Lean checker does; `check.py` recomputes the
witnesses itself from the definitions of `FORMAT.md` rule 6 and checks U < 2 by one of the two
paths. Both accept all 707 leaves, each by the old path. (H6) is not checked by a script; it follows from the argument in section
3 and from the enumeration of the hits.

* Every leaf is in mode `theta`. extra_ab = extra_cd = 0, M = max(L, 10^30) and k ≥ 3.
* No leaf has K empty and u = 0; that degenerate case, with T empty and S = 0, would not
  be an instance, but it does not occur.

The shapes (|K|, u, k), with leaf counts:

| (|K|, u, k) | leaves |
|---|---|
| (3, 0, 24) | 471 |
| (2, 0, 24) | 84 |
| (2, 1, 3) | 76 |
| (1, 1, 4) | 33 |
| (2, 1, 4) | 24 |
| (1, 1, 5) | 6 |
| (1, 0, 24) | 4 |
| (1, 1, 3) | 4 |
| (1, 1, 6) | 2 |
| (1, 2, 3) | 2 |
| (1, 2, 4) | 1 |

In total |K| ≤ 3 and u ≤ 2. 559 leaves have u = 0, where the first term of R is 0 and only m_M
matters.

The undecided generators form one fixed set P of at most u integers ≥ x, shared by all rows; a
row cannot use its own further primes. This holds in the search, because P is the set of
undecided free primes of N.
