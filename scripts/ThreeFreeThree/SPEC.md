# Three exceptional primes: certificate specification

This document specifies the certificate `cert3_final.json` (published here compressed as
`cert3_final.json.xz`; the SHA-256 of the uncompressed file is in `cert3_final.sha256`) and the
argument that turns it into a proof. The certificate was produced by `cert3f.py` with exact
rational arithmetic and is accepted by `check3.py` and `verify3.py`, both written from this
document. The argument is formalized in the Lean library as
`OddPerfect.three_dvd_of_three_mod_exceptions` (`OddPerfect/ThreeFreeThree.lean`), with the
exact square case `OddPerfect.three_dvd_of_three_exceptions` as a corollary; there the
certificate is checked again by the kernel; this document and the scripts are not trusted.

The certificate was generated for the exact square hypothesis (stored `floor` and `bound`,
threshold `1999/1000`). The weaker hypothesis `3 ∣ e + 1` is handled by the **corrected
bound** of Section 4, computed from the same certificate; no tree or weight changed.

Reader assumed: someone who knows `OddPerfect/ThreeFreeTwo.lean`.

## 1. Statement

**Target.** Let `N` be an odd perfect number, `q` a prime with `N.factorization q` odd, and
`r₁, r₂, r₃` natural numbers such that every `p ∈ N.primeFactors` with `p ∉ {q, r₁, r₂, r₃}`
has `3 ∣ N.factorization p + 1` (for example `N.factorization p = 2`). Then `3 ∣ N`.

## 2. Reduction to the core case

Assume `3 ∤ N`. The hypothesis only gets weaker when the set of labels grows. `N` has at
least four prime factors (`four_le_card_primeFactors`), so the labels `rᵢ` that are prime
factors of `N` other than `q` (at most three) are contained in a set of exactly three distinct
prime factors of `N` other than `q`; these replace `r₁, r₂, r₃`. So we are in the **core
context**:

* `N` is an odd perfect number with `3 ∤ N`;
* `q` is prime with odd exponent;
* `r₁, r₂, r₃` are distinct prime factors of `N`, all different from `q`;
* every other prime factor (an **ordinary** prime; their set is `S`) has an exponent `e` with
  `3 ∣ e + 1`.

The hypothesis is symmetric in `r₁, r₂, r₃`, so they may be relabeled (Section 5.1).

## 3. Arithmetic facts used

The ThreeFreeTwo names are given for comparison; the four slot versions are in
`ThreeFreeThreeCore.lean`.

* **F1.** `q ≡ 1 (mod 12)`, hence `q ≥ 13` (`Ctx.q_mod`). It uses only Euler's theorem and
  `3 ∤ N`.
* **F2.** Every prime factor of `N` is at least 5 (`Ctx.five_le`).
* **F3.** For `s ∈ S` with exponent `e`: `s` is prime, `s ≥ 5`, and `1 + s + s² = σ(s²)`
  divides `σ(s^e)` (since `3 ∣ e + 1`), which divides `2N`; being odd, `1 + s + s² ∣ N`. If
  `s ≡ 1 (mod 3)` then `3 ∣ 1 + s + s² ∣ N`, which is excluded; so `s ≡ 2 (mod 3)`
  (`cyc_dvd_of_mod`, `Ctx4.ord_facts`).
* **F4.** For `s ∈ S`, every prime `d ∣ 1 + s + s²` divides `N`, is not 3, and so has
  `d ≡ 1 (mod 3)` (`OPNThreeFree.target_mod_three`); by F3 it is not ordinary, so it lies in
  `{q, r₁, r₂, r₃}` (`Ctx4.tgt`).
* **F5.** `1 + s + s² = q^a r₁^b r₂^c r₃^d`. Write `vec(s) = (a, b, c, d)`; it is not all even
  (`Ctx.shape`, `ne_sq`).
* **F6.** `vec` is injective on `S` (`Ctx.vec_inj`).
* **F7.** If the value of a slot is `≡ 2 (mod 3)`, that coordinate of `vec(s)` is 0
  (`Ctx.vec_zero`).
* **F8.** `2 = A(q^e) · ∏ᵢ A(rᵢ^{eᵢ}) · ∏_{s∈S} A(s^{e_s})`, where `A` is abundancy.
* **F9.** For a prime `p` and `2 ≤ m ≤ p`: `A(p^e) < p/(p − 1) ≤ m/(m − 1)`
  (`abundancy_prime_pow_lt`, `rho_le`).
* **F10.** For `s ≥ 2`, `s/(s − 1) = fv(s) · s³/(s³ − 1)` with `fv(s) = (s² + s + 1)/s²`. For a
  finite set `T` of integers `s ≥ 300`, `∏_{s∈T} s³/(s³ − 1) ≤ 178802/178801`: write
  `s³/(s³ − 1) = 1 + x_s` with `x_s = 1/(s³ − 1)`; then `∏ (1 + x_s) ≤ 1/(1 − Σ x_s)`, and
  `x_s ≤ (1/(s − 1)² − 1/s²)/2` (equivalent to `3s³ − 2s² − 2s + 1 ≥ 0`), so the sum
  telescopes to at most `1/(2 · 299²) = 1/178802` (`prod_rv_le`, `tailF 300`).

## 4. Definitions used by a leaf

Constants:

* cap `= 300`;
* box size `M = 5`;
* `k = (301/300)²`;
* threshold `= 1999/1000`;
* class order `5, 7, 13, 19, 31, 37, 43, n2, big`.

**Slots.** There are four slots in the order `q, r1, r2, r3`. Each slot has:

* a **kind**: `q`, `fix`, `n2` or `big`;
* a **class name** `cls`: `q` for the `q` slot, otherwise the slot's class.

The **class residue test** is:

* kind `q`: `x % 12 = 1`;
* kind `n2`: `x % 3 = 2`;
* kind `big`: `x % 3 = 1`.

A slot is either **pinned** to a natural number `p`, or **free** with a lower bound `lb` and a
finite **excluded** set. Fixed classes are always pinned: `5, 7, 13, 19, 31, 37, 43`.

**Root of a class triple** `(c₁, c₂, c₃)`:

* `q` is free with `lb = 13` and nothing excluded;
* each `rᵢ` with `cᵢ = n2` is free with `lb = 11`;
* each `rᵢ` with `cᵢ = big` is free with `lb = 61`;
* each `rᵢ` with a fixed class is pinned to that number.

**Least values** `m₁ … m₄` are computed in slot order. Let `prev` be the least value of the
most recent earlier slot with the same `cls` (if there is one).

* Pinned slot: `m = p`. If `prev` exists and `p ≤ prev`, the leaf is vacuous; none occur.
* Free slot: `m` is the least integer `x ≥ max(lb, prev + 1)` that passes the class residue
  test, is not excluded, and differs from every pinned value of the leaf. No primality test
  is applied.

*Validity.* The actual value of each slot is `≥ m`. Induct along the slots: the actual value
is a prime `≥ lb`, larger than the actual value of the previous slot of its class (which is
`≥ prev`), passes the residue test (F1 for `q`; the definition of `n2` and `big`), is not
excluded, and is distinct from the other primes.

**Acceptance.** A slot accepts a prime `f` when:

* the slot is pinned to `p` and `f = p`; or
* the slot is free, `f` passes the residue test, `f ≥ m`, `f` is not excluded, and `f` is not
  a pinned value of the leaf.

By the validity above, if `f` is the actual value of a slot, that slot accepts `f`.

**The table.** For every prime `s ≡ 2 (mod 3)` with `5 ≤ s < 300` (32 primes), the file gives
the factorization of `1 + s + s²` (this is `Ctx.table`).

**Small set `C`.** `s ∈ C` if and only if:

* `s` is a table prime;
* `s` is not a pinned value; and
* every prime factor of `1 + s + s²` is accepted by at least one slot.

Each factor is tested on its own, with no injectivity. By F4 every ordinary `s < 300` is in `C`.

**Targets and weights.** Slot `i` is a **target** if its kind is `q` or `big`, or if it is
pinned with `mᵢ ≡ 1 (mod 3)`. Non-targets get weight `wᵢ = 0`, and their exponent is 0 by F7.
Kind `n2` and the pinned 5 are non-targets.

A target gets a rational `wᵢ` with `0 < wᵢ < 1` and `wᵢ² · mᵢ ≥ 1`; the certificate also
satisfies denominator `≤ 1000`. Since the actual value is `≥ mᵢ`, `wᵢ² · (value) ≥ 1`. Write
`w(v) = ∏ wᵢ^{vᵢ}`, with the convention `0⁰ = 1`: a non-target coordinate with `vᵢ = 0`
contributes the factor 1.

**Box.** The box is the set of `v ∈ ℕ⁴` with `vᵢ ∈ [0, 5)` for targets and `vᵢ = 0` for
non-targets, excluding vectors with all coordinates even. Enumeration order is lexicographic
in `(v_q, v_r1, v_r2, v_r3)` with the last coordinate fastest (Python `itertools.product`).

**Exact part.** A target coordinate is **exact** if its slot is pinned. A box vector is in the
exact part if `vᵢ = 0` for every non-exact target coordinate. For such `v`, put
`n(v) = ∏_{i exact} pᵢ^{vᵢ}`.

**Witnesses.** Each exact-part vector carries exactly one witness, listed in enumeration
order:

* `hit` with `s`: `4n(v) − 3 = (2s + 1)²` and `s ≥ 300`;
* `small` with `s`: `4n(v) − 3 = (2s + 1)²` and `s < 300`;
* `nonsquare` with `r`: `r² < 4n(v) − 3 < (r + 1)²`.

**The quantities.**

* `E = Σ_{hits} (s + 1)/s²`.
* `R = Σ_{box vectors not in the exact part} min(1/300, w(v))`.
* `Tl = (Σᵢ wᵢ⁵) / ∏ᵢ (1 − wᵢ)`, where non-targets contribute `0⁵ = 0` and a factor `1`.
* `X = E + k · (R + Tl)`, which must be `< 1`.
* `floor = ∏ᵢ mᵢ/(mᵢ − 1) · ∏_{s∈C} fv(s)`, over all four slots.
* `bound = floor / (1 − X)`, which must be `≤ 1999/1000` (the exact square case).
* **Corrected bound** (not stored): `cbound = ∏ᵢ mᵢ/(mᵢ − 1) · ∏_{s∈C} s/(s − 1) ·
  (178802/178801) / (1 − X)`, which must be `< 2`. The Lean checker tests the same rational
  value against 2 (`≤ 2`, cross multiplied in natural numbers, `finalOK`). On the published
  certificate every leaf passes; the largest corrected bound is about 1.996532 at leaf 388.

## 5. Why a leaf is contradictory

Consider any `N` in the core context whose `(q, r₁, r₂, r₃)` meets the leaf's constraints.

1. **Exceptional factors.** By F9 with the least values, `A(q^e) · ∏ A(rᵢ^{eᵢ}) < ∏ mᵢ/(mᵢ − 1)`.
   For every ordinary `s`, `A(s^{e_s}) < s/(s − 1)`.
2. **Small ordinary primes.** Each `s ∈ S` with `s < 300` is in `C`, and `s/(s − 1) ≥ 1`
   (`one_le_rv`), so `∏_{s∈S, s<300} s/(s − 1) ≤ ∏_C s/(s − 1)`.
3. **Large ordinary primes** (`s ≥ 300`): by F10, `∏ s/(s − 1) ≤ (178802/178801) · ∏ fv(s)`.
   For the product of `fv(s)`, put `x_s = fv(s) − 1 ≥ 0` and `v = vec(s)`.
   * *Weight inequality.* `w(v)² (1 + s + s²) = ∏ (wᵢ² · valueᵢ)^{vᵢ} ≥ 1`, using F7 for
     non-targets (their coordinate is 0, and `0⁰ = 1`). Since `1 + s + s² < (s + 1)²`, this
     gives `w(v)(s + 1) ≥ 1` (`Ctx.weight` with free weights).
   * *Cap.* `x_s ≤ k/(s + 1) ≤ k · min(1/300, w(v))` (`fv_sub_le`).
   * *Exact part (Lemma X).* If `v` is in the exact part, then `1 + s + s² = n(v)` (F5; the
     non-exact coordinates of `v` are 0), so `4n(v) − 3 = (2s + 1)²`. A `nonsquare` witness
     contradicts this. A `small` witness gives `s < 300`, which also contradicts. So the
     witness is a `hit` with the same `s`, and `x_s = (s + 1)/s²`.
   * *Summation.* By F6 distinct `s` give distinct `v`. The vectors `vec(s)` that occur have
     coordinate 0 at every non-target (F7) and are not all even (F5), so each one that is not
     in the box has a coordinate `≥ 5`. Then
     `Σ x_s ≤ E + k · (R + Σ' w(v)) ≤ E + k · (R + Tl) = X`, where `Σ'` ranges over the
     vectors `vec(s)` that occur and are not in the box, each counted once. The exact part
     contributes at most `E` (each hit is used at most once), and the other box vectors at
     most `k · R`, since every term of `R` is nonnegative. Finally `Σ' w(v) ≤ Tl` is `tail3`
     in four coordinates: `Σ'` is at most the sum of `w(v)` over all `v ∈ ℕ⁴` with zero
     non-target coordinates and some coordinate `≥ 5`, which is bounded by geometric series
     (`cube_sum`, `geom_le`).
   * *Product bound.* `∏(1 + x_s) ≤ 1/(1 − Σ x_s) ≤ 1/(1 − X)` (`prod_one_add_le`; side
     condition `X < 1`).
4. By F8, `2 < cbound ≤ 2`. Contradiction. (In the exact square case F8 holds with `fv(s)`
   in place of `A(s^{e_s})` and `2 < bound ≤ 1999/1000` directly; that is how the certificate
   was produced.)

A leaf has up to 544 box vectors, and `n(v)` has up to 43 digits. The witnesses reduce
Lemma X to integer comparisons; in Lean the square test is recomputed by an integer square
root instead of being read from the certificate.

## 5.1 Coverage

**Classes.** Each `rᵢ` is in exactly one class: `5, 7, 13, 19, 31, 37, 43`, `n2` (prime
`≡ 2 (mod 3)`, `≥ 11`) or `big` (prime `≡ 1 (mod 3)`, `≥ 61`) (F2, `Ctx.cls`).

Relabel the `rᵢ` so that their classes are nondecreasing in class order, and so that within
one class the values strictly increase. Since `q ≥ 13`, `q ≡ 1 (mod 12)` and `q` is a different
prime, it is covered by its root constraints.

The class sequences are the 102 multisets of size 3 over the 9 classes in which each fixed
class appears at most once, listed in `combinations_with_replacement` order.

**Splits.** A split node names one free slot `i` of kind `q` or `big` and a nonempty list of
distinct integers `p₁, …, p_k`. The children, in order, are:

* for each `j`: slot `i` pinned to `pⱼ`. Every **later** free slot with the same `cls` gets
  `lb := max(lb, pⱼ + 1)`, which is valid by the increasing order inside a class. Earlier
  slots are unchanged.
* **generic:** slot `i` keeps its constraints and adds `p₁, …, p_k` to its excluded set.

This is exhaustive with no conditions: the value of slot `i` is one of the `pⱼ` or is not.

The generator chooses `pⱼ` as either:

* every accepted prime factor of some `1 + s + s²` with `s ∈ C` (`rule: relevant`); or
* the single current least value (`rule: peel`).

The rule is informational only. Peeled values can be composite (25 and 49 occur for `q`);
those leaves are impossible but are still checked numerically, which is sound.

**Node ids.** Ids are a preorder numbering from 1, across the triples in listed order, with
children visited in listed order (the generic child last).

## 6. File format (`cert3_final.json`)

All fractions are `[numerator, denominator]` pairs with a positive denominator.

Top level:

| field | meaning |
|---|---|
| `format` | `"cert3_final v1"` |
| `rules` | the generator switches (informational) |
| `cap`, `box`, `k`, `threshold`, `weight_denominator_max` | `300`, `5`, `[90601, 90000]`, `[1999, 1000]`, `1000` |
| `classes` | the 9 class names in class order |
| `table` | map from `s` (string) to `[[p, e], …]` with `∏ p^e = s² + s + 1`; every `p` prime |
| `leaf_count`, `split_count` | 1223, 78 |
| `worst_bound`, `worst_leaf` | the largest leaf bound and its node id |
| `pilot_leaves` | four leaf ids of interest (informational): the first leaf with no pinned target (205), the first with `E > 0` (15), the leaf of the worst bound (388), and the first using an upper bound (none) |
| `triples` | 102 records `{triple, root, tree}` |

`root` lists the four root slots in the leaf slot format, without `least`.

A tree node is either `{id, split: {slot, pins, rule}, children}` or `{id, leaf}`.

A leaf holds:

* `id`, and `status` (`closed`);
* `slots`: four records `{name, kind, cls, pinned}` or
  `{name, kind, cls, lb, ub: null, excluded, least}`;
* `C`: records `{s, n, factorization, assignment}`, where `assignment` maps each factor (as a
  string) to the list of slot names that accept it;
* `target` (4 booleans), `weights` (4 fractions), `exact_coords` (4 booleans);
* `witnesses`: `{v, kind, s}` or `{v, kind: "nonsquare", r}`, in enumeration order;
* `floor`, `E`, `R`, `Tl`, `X`, `bound` (fractions).

A verifier must check the following; `verify3.py` performs every check of this list.

* Header: `format` is `"cert3_final v1"`; `cap`, `box`, `k` (exactly `[90601, 90000]`),
  `threshold`, `weight_denominator_max` and `classes` have the values above.
* Table: the keys are exactly the 32 primes, and each entry equals the factorization of
  `s² + s + 1` recomputed by trial division.
* Triples: there are 102 records, each with exactly the keys `triple`, `root`, `tree`; the
  triples are the 102 multisets in the listed order, and each `root` equals the root of its
  triple.
* Tree: node ids are the preorder numbering; a leaf node has exactly the keys `id`, `leaf`
  and a split node exactly `id`, `split`, `children`; a split has exactly the keys `slot`,
  `pins`, `rule`, names a slot that is free and of kind `q` or `big`, has a nonempty list of
  distinct integer pins, and has exactly one child per pin plus the generic child. Every
  node's constraints are rebuilt from the root and the splits.
* Leaf slots: the leaf `id` equals the node id and `status` is `closed`; there are four
  slots; a pinned slot record equals the rebuilt one; a free slot record has exactly the keys
  above, the rebuilt `name`, `kind`, `cls` and `lb`, `ub` null, an `excluded` list of
  distinct integers equal as a set to the rebuilt one, and `least` equal to the recomputed
  least value.
* `C`: the records have exactly the keys above and distinct `s`; the set of `s` equals the
  recomputed `C`; `n = 1 + s + s²`; `factorization` equals the table entry; `assignment` has
  one key per prime factor, and each list has no repetition and equals as a set the slots
  that accept that factor.
* `target` and `exact_coords` equal the recomputed lists.
* Weights: four fractions; each target weight satisfies `0 < w < 1`, `w² · m ≥ 1` and
  denominator `≤ 1000`; each non-target weight is 0.
* Witnesses: one per exact-part vector, in enumeration order, with the vector `v` of that
  position and no extra witness; a `hit` or `small` witness has exactly the keys `v`, `kind`,
  `s` and a `nonsquare` witness exactly `v`, `kind`, `r`; the conditions of Section 4 hold.
* Quantities: the stored `E`, `R`, `Tl`, `X`, `floor` and `bound` equal the recomputed values;
  `X < 1` and `bound ≤ threshold`; the corrected bound is `< 2`.
* Totals: `leaf_count`, `split_count`, `worst_bound` and `worst_leaf` equal the recomputed
  values.

`rules` and `pilot_leaves` are not checked. `verify3.py` counts vacuous leaves instead of
rejecting them (none occur). `check3.py` performs the mathematical checks of this list (least
values, `C` as a set, targets, `exact_coords`, weights, witnesses, `E`, `R`, `Tl`, `X`,
`floor`, `bound`, the corrected bound, the node constraints, the table and the triples); it does not check the
format string, the `classes` field, the key sets, the `root` records, the `cls` fields, the `n`, `factorization` and `assignment` fields of `C`,
`weight_denominator_max`, `split_count` or `worst_leaf`, it only checks `threshold < 2`, and it
checks the table by primality of each factor and the product instead of recomputing the
factorization. On the published file both accept 1223 closed leaves, 0 vacuous, 194 with
`E > 0`, a worst bound of 1.994970 at leaf 388, and a worst corrected bound of 1.996532 at
leaf 388.

## 7. Lean side

* `OddPerfect/ThreeFreeThreeCore.lean`: the four slot core context `Ctx4`, the reduction to it
  (`ctx4_of_not_three_dvd`), the facts of Section 3 in four slot form, the tail bounds (`tail4`,
  `prod_rv_le`) and the closing inequality `Ctx4.close`.
* `OddPerfect/ThreeFreeThreeChecker.lean`: the Boolean checker `leafOK` of one leaf and
  `treeOK` of a binary split tree, their soundness (`treeOK_sound`), the relabeling into
  sorted class triples (`Ctx4.cover`) and `three_dvd_of_three_exceptions_of_check`. The final
  test `finalOK` checks the corrected bound. A split with pins `p₁, …, p_k` of the
  certificate becomes `k` nested binary splits, each pinning one value and excluding it in the
  other child. `leafOK` recomputes the least values, `C`, the box sums and the square tests
  from the constraints and the weights alone; witnesses and stored quantities are not read.
* `OddPerfect/ThreeFreeThreeData01.lean` to `ThreeFreeThreeData11.lean`: the subtrees of the
  102 trees, each checked by `decide +kernel` on groups of five leaves.
* `OddPerfect/ThreeFreeThree.lean`: the 102 trees, `allOK_trees` and the theorems
  `three_dvd_of_three_mod_exceptions`, `three_dvd_of_three_exceptions` and
  `four_le_card_mod_exceptions`.

The data modules and the final module are written by `gen_lean.py`, whose mode `mirror`
recomputes every leaf with a Python copy of `leafOK` (with the corrected final test) and
compares it with the certificate.

## Appendix: mechanisms dropped from the final certificate

Each is valid but unused.

* Upper bounds on earlier slots of a class: never used (0 leaves).
* Injective assignment in `C`.
* Primality and `s mod 3` tests in Lemma X.
* Primality in least values.
* The exact parity tail `∏ 1/(1 − w) − ∏ 1/(1 − w²)`.
* The residue filters modulo 5, 7, 11, 13.

The first four are the switches `noub`, `noinj`, `noprimex` and `noprimem` of `cert3f.py`:
leaving one out of `RULES` turns the mechanism back on. The last two are not implemented in
`cert3f.py`.
