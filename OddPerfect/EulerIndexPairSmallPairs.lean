import OddPerfect.EulerIndexPairEmitters
import OddPerfect.OmegaSevenFinal
import OddPerfect.Network
import OddPerfect.Valuation
import OddPerfect.Cyclotomic
import OddPerfect.PureRows
import OddPerfect.SquareRow
import OddPerfect.NagellPrime

/-!
# Two prime Euler index: the pairs `(13, 3)` and `(31, 5)`

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors.
`eulerIndex_pair_emitter_small` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`,
`σ(u ^ f) = t ^ j` (`e = v_t(N)`, `f = v_u(N)`, `j` odd) and leaves the cases
`(t, u) = (13, 3)`, `(t, u) = (31, 5)`, `t = 43` with `f = 6`, and `t ≥ 53`.

* `sigma_prime_pow_eq_pow_mul_pow_mod_four`: for an odd prime `p`, even `g`, `t ≡ 3`,
  `u ≡ 1 (mod 4)` and odd `x`, `σ(p ^ g) = t ^ x u ^ y` forces `p ≡ 1` and `g ≡ 2 (mod 4)`.
* `eulerIndex_pair_emitter_ge`: both small pairs are impossible. For both pairs
  `f + 1` is prime and `t ≡ 1 (mod 2 (f + 1))`, which gives `f ≤ 2`, except `f = 4` for
  `(31, 5)`, where `σ(5 ^ 4) = 31 ^ j` is excluded modulo 4 (`geom_sum_eq_pow_mod_four`); so
  `f ≤ 3`. Step 1 is a short consequence of the landed `sigma_prime_pow_even_mod_four`.
  Every prime `p` of `N` outside `{q, t, u}` (an outsider, exponent `g`) has
  `σ(p ^ g) = t ^ x u ^ y`; such a row is
  never a pure power of `t`, so `u ∣ σ(p ^ g)`. A pure row `σ(p ^ g) = t ^ x` has `g + 1`
  prime and `g + 1 ∣ t - 1` (the order of `p` modulo `t` is `1` only when `g + 1 = t`, and then
  lifting the exponent gives `σ(p ^ g) = t`, too small); for `t = 13` this leaves `g = 2` and
  Nagell's lemma gives `p ^ 2 + p + 1 = 13`, `p = 3 = u`; for `t = 31` it leaves `g = 2`
  (`p = 5 = u` in the same way) and `g = 4` (odd `x` against the residue modulo 4, even `x`
  against `isSquare_sigma_prime_pow_iff`). There are at least four outsiders
  (`seven_le_card_primeFactors`), and the weights they send to `u` add up to at most
  `v_u(N) = f ≤ 3` (`sigmaWeight_sum_eq`).

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). The case is not excluded: `t = 43` with `f = 6` and every `t ≥ 53` remain. Their
novelty has not been verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairSmallPairs

/-- `t ^ x % 4 = 3` for `t % 4 = 3` and odd `x`. -/
private lemma espp_pow_mod_four {t x : ℕ} (ht : t % 4 = 3) (hx : Odd x) : t ^ x % 4 = 3 := by
  obtain ⟨k, rfl⟩ := hx
  rw [Nat.pow_mod, ht]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

end EulerIndexPairSmallPairs

open EulerIndexPairSmallPairs

/-- **Odd prime rows supported on a prime `≡ 3` and a prime `≡ 1 (mod 4)`.** Let `p` be an odd
prime, `g` even, `t ≡ 3 (mod 4)`, `u ≡ 1 (mod 4)` and `x` odd. If `σ(p ^ g) = t ^ x u ^ y`,
then `p ≡ 1 (mod 4)` and `g ≡ 2 (mod 4)`: the right side is `3 (mod 4)`, while
`σ(p ^ g) ≡ 1` for `p ≡ 3` and `σ(p ^ g) ≡ g + 1` for `p ≡ 1 (mod 4)`. -/
theorem sigma_prime_pow_eq_pow_mul_pow_mod_four {p g t u x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hg : Even g) (ht : t % 4 = 3) (hu : u % 4 = 1) (hx : Odd x)
    (h : σ 1 (p ^ g) = t ^ x * u ^ y) : p % 4 = 1 ∧ g % 4 = 2 := by
  have h1 : t ^ x % 4 = 3 := espp_pow_mod_four ht hx
  have h2 : u ^ y % 4 = 1 := by rw [Nat.pow_mod, hu, one_pow]; norm_num
  have h3 : (t ^ x * u ^ y) % 4 = 3 := by rw [Nat.mul_mod, h1, h2]
  rw [← h, sigma_one_apply_prime_pow hp] at h3
  have hpo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · rw [geom_sum_mod_four_of_one h4] at h3
    exact ⟨h4, by omega⟩
  · rw [geom_sum_mod_four_of_three h4 hg.add_one] at h3
    omega

namespace EulerIndexPairSmallPairs

/-- `σ(p ^ g) ≥ p ^ g + 1` for `g ≠ 0`. -/
private lemma espp_sigma_ge {p g : ℕ} (hp : p.Prime) (hg0 : g ≠ 0) :
    p ^ g + 1 ≤ σ 1 (p ^ g) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have h1 : p ^ 0 ≤ ∑ i ∈ Finset.range g, p ^ i :=
    Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.pos_of_ne_zero hg0))
  rw [pow_zero] at h1
  omega

/-- A prime `t ∣ σ(p ^ g)` with `g + 1` prime: either `g + 1 = t` and `p ≡ 1 (mod t)`, or
`g + 1 ∣ t - 1`. -/
private lemma espp_order {p g t : ℕ} (hp : p.Prime) (ht : t.Prime) (hpt : p ≠ t)
    (hl : (g + 1).Prime) (hd : t ∣ σ 1 (p ^ g)) :
    (g + 1 = t ∧ t ∣ p - 1) ∨ g + 1 ∣ t - 1 := by
  rw [dvd_sigma_prime_pow_iff hp ht hpt] at hd
  have := Fact.mk ht
  split_ifs at hd with h1
  · left
    refine ⟨((Nat.prime_dvd_prime_iff_eq ht hl).mp hd).symm, ?_⟩
    have hc : (p : ZMod t) = 1 := orderOf_eq_one_iff.mp h1
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hp.one_le, hc, Nat.cast_one, sub_self]
  · right
    have he : orderOf (p : ZMod t) = g + 1 := (hl.eq_one_or_self_of_dvd _ hd).resolve_left h1
    rw [← he]
    apply ZMod.orderOf_dvd_card_sub_one
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdv
    exact hpt ((Nat.prime_dvd_prime_iff_eq ht hp).mp hdv).symm

/-- A pure row `σ(p ^ g) = t ^ x` (odd primes `p ≠ t`, `g` even and nonzero): `g + 1` is
prime, `g + 1 ∣ t - 1`, and for `g = 2` the row is `t` itself. -/
private lemma espp_pure_row {p g t x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : Even g)
    (hg0 : g ≠ 0) (ht : t.Prime) (ht2 : t ≠ 2) (hpt : p ≠ t) (h : σ 1 (p ^ g) = t ^ x) :
    (g + 1).Prime ∧ g + 1 ∣ t - 1 ∧ (g = 2 → phi3 p = t) := by
  have hl := prime_succ_of_sigma_prime_pow_eq_prime_pow hp hp2 hg hg0 ht h
  have hge := espp_sigma_ge hp hg0
  have hgp : g < p ^ g := Nat.lt_pow_self hp.one_lt
  have hx : x ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    omega
  have htd : t ∣ σ 1 (p ^ g) := by rw [h]; exact dvd_pow_self t hx
  have := Fact.mk ht
  rcases espp_order hp ht hpt hl htd with ⟨hlt, htp⟩ | hd
  · exfalso
    have hv := padicValNat_sigma_prime_pow_of_dvd_pred (a := g) hp ht ht2 htp
    rw [h, padicValNat.prime_pow, hlt, padicValNat_self] at hv
    have h' : σ 1 (p ^ g) = g + 1 := by rw [h, hv, pow_one, hlt]
    rw [h'] at hge
    generalize p ^ g = P at hge hgp
    omega
  · refine ⟨hl, hd, fun hg2 => ?_⟩
    subst hg2
    have hphi : phi3 p = t ^ x := by
      rw [← h, sigma_one_apply_prime_pow hp, phi3]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
      ring
    rw [hphi, phi3_eq_prime_pow_exponent ht hp (Nat.one_le_iff_ne_zero.mpr hx) hphi, pow_one]

/-- An outsider row for `(t, u) = (13, 3)` is divisible by `3`. -/
private lemma espp_row13 {p g x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : Even g)
    (hg0 : g ≠ 0) (hp3 : p ≠ 3) (hp13 : p ≠ 13) (h : σ 1 (p ^ g) = 13 ^ x * 3 ^ y) :
    3 ∣ σ 1 (p ^ g) := by
  by_contra hnd
  have hy : y = 0 := by
    by_contra hy
    exact hnd (by rw [h]; exact dvd_mul_of_dvd_right (dvd_pow_self 3 hy) _)
  rw [hy, pow_zero, mul_one] at h
  obtain ⟨hl, hdvd, h2⟩ := espp_pure_row hp hp2 hg hg0 (by norm_num) (by norm_num) hp13 h
  have hg2 : g = 2 := by
    have : g ≤ 11 := by have := Nat.le_of_dvd (by norm_num) hdvd; omega
    rw [Nat.even_iff] at hg
    interval_cases g <;> omega
  have hphi := h2 hg2
  unfold phi3 at hphi
  have hp4 : p ≤ 3 := by nlinarith
  interval_cases p <;> omega

/-- An outsider row for `(t, u) = (31, 5)` is divisible by `5`. -/
private lemma espp_row31 {p g x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : Even g)
    (hg0 : g ≠ 0) (hp5 : p ≠ 5) (hp31 : p ≠ 31) (h : σ 1 (p ^ g) = 31 ^ x * 5 ^ y) :
    5 ∣ σ 1 (p ^ g) := by
  by_contra hnd
  have hy : y = 0 := by
    by_contra hy
    exact hnd (by rw [h]; exact dvd_mul_of_dvd_right (dvd_pow_self 5 hy) _)
  rw [hy, pow_zero, mul_one] at h
  obtain ⟨hl, hdvd, h2⟩ := espp_pure_row hp hp2 hg hg0 (by norm_num) (by norm_num) hp31 h
  have hg24 : g = 2 ∨ g = 4 := by
    have : g ≤ 29 := by have := Nat.le_of_dvd (by norm_num) hdvd; omega
    rw [Nat.even_iff] at hg
    interval_cases g <;> first | omega | norm_num at hdvd hl
  rcases hg24 with hg2 | hg4
  · have hphi := h2 hg2
    unfold phi3 at hphi
    have hp6 : p ≤ 5 := by nlinarith
    interval_cases p <;> omega
  · subst hg4
    rcases Nat.even_or_odd x with ⟨k, hk⟩ | hxo
    · have hsq : IsSquare (σ 1 (p ^ 4)) := ⟨31 ^ k, by rw [h, hk, pow_add]⟩
      obtain ⟨rfl, -⟩ := (isSquare_sigma_prime_pow_iff hp hp2 ⟨2, rfl⟩ (by norm_num)).mp hsq
      have h121 : σ 1 (3 ^ 4) = 121 := by
        rw [sigma_one_apply_prime_pow Nat.prime_three]
        norm_num [Finset.sum_range_succ]
      rw [h121] at h
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · norm_num at h
      · have h31 : 31 ∣ 121 := by rw [h]; exact dvd_pow_self 31 hx.ne'
        norm_num at h31
    · have h' : σ 1 (p ^ 4) = 31 ^ x * 5 ^ 0 := by rw [h, pow_zero, mul_one]
      have := (sigma_prime_pow_eq_pow_mul_pow_mod_four hp hp2 ⟨2, rfl⟩ (by norm_num)
        (by norm_num) hxo h').2
      norm_num at this

/-- Facts for a prime of the Euler index. -/
private lemma espp_index_prime {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p ∈ (eulerIndex q 1 m).primeFactors) :
    p.Prime ∧ p ∣ m ∧ p ≠ 2 := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpm : p ∣ m := hpp.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hp).trans (eulerIndex_dvd_sq h hq hN1 hqm))
  refine ⟨hpp, hpm, ?_⟩
  rintro rfl
  exact h.not_two_dvd (hN ▸ dvd_mul_of_dvd_right (dvd_pow hpm two_ne_zero) q)

/-- Facts for an outsider, a prime of `N` outside `{q, r, s}`. -/
private lemma espp_outsider {N q m r s t u p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p.Prime ∧ p ≠ 2 ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u ∧
      Even (N.factorization p) ∧ N.factorization p ≠ 0 := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨hpN, hpq, hpt, hpu⟩ := hp
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have hpd := Nat.dvd_of_mem_primeFactors hpN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  refine ⟨hpN, hpp, ?_, hpq, hpt, hpu, ?_, (hpp.factorization_pos_of_dvd h.ne_zero hpd).ne'⟩
  · rintro rfl
    exact h.not_two_dvd hpd
  · rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
      Nat.factorization_pow]
    exact ⟨m.factorization p, by simp [two_mul]⟩

/-- The labeling is unique: a labeling `(t', u')` of the same pair with
`σ(u' ^ v_u'(N)) = t' ^ j` agrees with `(t, u)`, where `σ(t ^ v_t(N)) = q u ^ v`. Otherwise
`q ∣ u ^ j`, so `q = u ∣ m`. -/
private lemma espp_label {N q m t u t' u' v j : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hu : u.Prime) (hum : u ∣ m) (htu : ({t, u} : Finset ℕ) = {t', u'}) (hne' : t' ≠ u')
    (hA : σ 1 (t ^ N.factorization t) = q * u ^ v)
    (hB : σ 1 (u' ^ N.factorization u') = t' ^ j) : t' = t ∧ u' = u := by
  have ht' : t' ∈ ({t, u} : Finset ℕ) := by rw [htu]; simp
  have hu' : u' ∈ ({t, u} : Finset ℕ) := by rw [htu]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht' hu'
  rcases ht' with rfl | rfl
  · rcases hu' with rfl | rfl
    · exact absurd rfl hne'
    · exact ⟨rfl, rfl⟩
  · exfalso
    rcases hu' with rfl | rfl
    · rw [hA] at hB
      have hqd := hq.dvd_of_dvd_pow (Dvd.intro _ hB)
      have hqu := (Nat.prime_dvd_prime_iff_eq hq hu).mp hqd
      exact hqm (by rw [hqu]; exact hum)
    · exact hne' rfl

end EulerIndexPairSmallPairs

variable {N q m r s : ℕ}

/-- **Two prime index, the small pairs are impossible.** Let `N = q m ^ 2` be an odd perfect
number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_emitter_small` (with `σ(t ^ v_t(N)) = q u ^ v` and
`σ(u ^ v_u(N)) = t ^ j`, `j` odd), either `t = 43` and `v_u(N) = 6`, or `t ≥ 53`: the pairs
`(13, 3)` and `(31, 5)` do not occur. For them `v_u(N) ≤ 3`, while each of the at least four
primes of `N` outside `{q, r, s}` sends weight at least 1 to `u`. This is a restricted result
(special exponent 1, index supported on exactly two primes); it does not exclude this case:
`t = 43` with `v_u(N) = 6` and every `t ≥ 53` remain. Its novelty has not been verified. -/
theorem eulerIndex_pair_emitter_ge (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (N.factorization u + 1).Prime ∧ t % (2 * (N.factorization u + 1)) = 1 ∧
      ((t = 43 ∧ N.factorization u = 6) ∨ 53 ≤ t) := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hjo, hB⟩, h3, hf1, hmod, hsmall⟩ :=
    eulerIndex_pair_emitter_small h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hjo, hB⟩, h3, hf1, hmod, ?_⟩
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  obtain ⟨hu, hum, hu2⟩ := espp_index_prime h hq hN hqm huJ
  obtain ⟨t1, u1, htu1, hne1, -, ⟨j1, -, -, hB1⟩, -, -, -, -, -, -, -, hrest⟩ :=
    eulerIndex_pair_pure_exponent_odd h hq hN hqm hr hs hrs hJ
  obtain ⟨ht1, hu1⟩ := espp_label hq hqm hu hum (htu.trans htu1.symm) hne1 hA hB1
  rw [ht1, hu1] at hrest
  set O := N.primeFactors \ {q, r, s} with hOdef
  -- the weights sent to `u` by the outsiders add up to at most `v_u(N)`
  have hcnt : ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization u ≤
      N.factorization u := by
    have hle := Finset.sum_le_sum_of_subset (f := fun p => sigmaWeight N p u)
      (Finset.sdiff_subset : O ⊆ N.primeFactors)
    rw [sigmaWeight_sum_eq h.perfect hu hu2] at hle
    exact hle
  -- at least four outsiders
  have hcard : 4 ≤ O.card := by
    have h7 := seven_le_card_primeFactors h
    have h3' : ({q, r, s} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    have := Finset.le_card_sdiff ({q, r, s} : Finset ℕ) N.primeFactors
    rw [← hOdef] at this
    omega
  have key : (∀ p ∈ O, u ∣ σ 1 (p ^ N.factorization p)) → N.factorization u ≤ 3 →
      False := by
    intro hdv hf
    have h1 : ∀ p ∈ O, 1 ≤ (σ 1 (p ^ N.factorization p)).factorization u := fun p hp =>
      hu.factorization_pos_of_dvd (sigma_pos 1 _ (pow_ne_zero _
        (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).ne_zero)).ne' (hdv p hp)
    have := Finset.card_nsmul_le_sum O _ 1 h1
    rw [smul_eq_mul, mul_one] at this
    omega
  rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h' | h'
  · exfalso
    refine key (fun p hp => ?_) ?_
    · obtain ⟨hpN, hpp, hp2, hpq, hpt, hpu, hg, hg0⟩ := espp_outsider h hq hN hqm htu hp
      obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hrest p hpN hpq hpt hpu
      exact espp_row13 hpp hp2 hg hg0 hpu hpt hxy
    · generalize N.factorization 3 = f at hf1 hmod ⊢
      by_contra hc
      have hf5 : f ≤ 5 := by
        by_contra h6
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      interval_cases f <;> (revert hmod hf1; norm_num)
  · exfalso
    refine key (fun p hp => ?_) ?_
    · obtain ⟨hpN, hpp, hp2, hpq, hpt, hpu, hg, hg0⟩ := espp_outsider h hq hN hqm htu hp
      obtain ⟨⟨x, y, hxy⟩, -, -⟩ := hrest p hpN hpq hpt hpu
      exact espp_row31 hpp hp2 hg hg0 hpu hpt hxy
    · generalize N.factorization 5 = f at hf1 hmod hB ⊢
      by_contra hc
      have hf14 : f ≤ 14 := by
        by_contra h6
        rw [Nat.mod_eq_of_lt (by omega)] at hmod
        omega
      interval_cases f <;> (revert hmod hf1; norm_num)
      rw [sigma_one_apply_prime_pow (by norm_num)] at hB
      exact absurd (geom_sum_eq_pow_mod_four ⟨2, rfl⟩ ⟨2, rfl⟩ (by norm_num) hjo hB).2
        (by norm_num)
  · exact Or.inl h'
  · exact Or.inr h'

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_eq_pow_mul_pow_mod_four
#print axioms OddPerfect.eulerIndex_pair_emitter_ge
