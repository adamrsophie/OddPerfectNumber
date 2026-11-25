import Mathlib
import OddPerfect.SignedRepunitJacobi

/-!
# Primes of odd valuation in half a divisor sum: every negative level has a witness

Let `q` be a prime with `q ≡ 1 (mod 4)`, let `L` be odd and put `H(L) = σ(q ^ (2 L - 1)) / 2`.
Write `Ω(L)` for the number of prime factors of `L` counted with multiplicity and
`C(L) = ∑ p ∈ L.primeFactors with ¬ p ∣ q - 1, L.factorization p`. Under the two hypotheses of
`OddPerfect.cardFactors_le_card_odd_valuation_half_sigma`, taken as explicit arguments,

* `hpos`: `Σ_{i < n} (q ^ h) ^ i` is never a square for odd `h` and odd `n ≥ 3`;
* `hneg`: `(q ^ h) ^ n + 1 ≠ (q ^ h + 1) y ^ 2` for `h ≠ 0`, `q ^ h ≡ 1 (mod 4)`, odd `n ≥ 3`,

this module proves that at least `Ω(L) + C(L)` primes have odd valuation in `H(L)`, and at
least `Ω(L) + 1` when `L ≥ 3`. Neither hypothesis is proved here. This is arithmetic only; no
odd perfect number appears.

Method. Strong induction on `L` as in `OddPerfect.OddValuationCountFree`: `L = p L'` with `p`
the least prime factor, `X = q ^ L'`, `H(L) = H(L') B₊ B₋`, `B₊ = Σ_{i < p} X ^ i` and
`B₋ = (X ^ p + 1) / (X + 1)`. The change is at the negative factor: write `B₋ = d₁ ^ 2 d₂` with
`d₂` squarefree. Then `d₂ ≠ 1` by `hneg` and `d₂ ≠ p` by
`OddPerfect.alternating_sum_ne_prime_mul_sq` (here `X ≡ 1 (mod 4)`), so some prime `r ≠ p`
has odd valuation in `B₋`. Then `-X` has order `p` modulo `r`, so `p < r`, `r ∤ X ^ 2 - 1` and
`r ∤ B₊`. Hence every level contributes a negative witness, with no condition `p ∤ q + 1`; earlier
witnesses survive as before, since they exceed `p` and divide `X ^ 2 - 1`.
The positive factor contributes a witness when `p ∤ q - 1`, as before. For the extra one at
`L ≥ 3`: `H(L) = R_L ((q ^ L + 1) / 2)` with `R_L = Σ_{i < L} q ^ i` odd and not a square by
`hpos`, and a prime of odd valuation in `R_L` divides `q ^ L - 1`, hence not `q ^ L + 1`,
which every negative witness divides.

Controls: for `q = 5` and `L = 3`, `H = 3 ^ 2 * 7 * 31` has two primes of odd valuation and the
bound `Ω(3) + 1 = 2` is sharp. A positive level can lack a witness when `p ∣ q - 1`:
`Σ_{i < 3} 313 ^ i = 3 * 181 ^ 2`.

Published context: Y. Hirakawa (arXiv 2309.17084, Theorem 1.1, page checked) proves that two
primes have odd valuation in the Euler index for a special exponent above one. No published
source was checked for the count in this module; its novelty is not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Half the divisor sum `σ(q ^ (2 L - 1)) / 2`. -/
private def ovcsH (q L : ℕ) : ℕ := σ 1 (q ^ (2 * L - 1)) / 2

/-- The count `∑ p ∈ L.primeFactors with ¬ p ∣ q - 1, L.factorization p`. -/
private def ovcsC (q L : ℕ) : ℕ :=
  ∑ p ∈ L.primeFactors.filter (fun p => ¬ p ∣ q - 1), L.factorization p

/-! ## Helpers -/

/-- A nonzero number that is not a square has a prime factor of odd valuation. -/
private lemma ovcs_exists_odd_val {B : ℕ} (hB : B ≠ 0) (hns : ∀ y : ℕ, B ≠ y ^ 2) :
    ∃ t, t.Prime ∧ t ∣ B ∧ Odd (padicValNat t B) := by
  obtain ⟨d₂, d₁, hd, hsf⟩ := Nat.sq_mul_squarefree B
  have hd₁ : d₁ ≠ 0 := by rintro rfl; apply hB; rw [← hd]; simp
  have hd₂ : d₂ ≠ 1 := by rintro rfl; exact hns d₁ (by rw [← hd, mul_one])
  have hd₂0 : d₂ ≠ 0 := hsf.ne_zero
  have ht : d₂.minFac.Prime := Nat.minFac_prime hd₂
  have htd : d₂.minFac ∣ d₂ := Nat.minFac_dvd d₂
  refine ⟨d₂.minFac, ht, ?_, ?_⟩
  · rw [← hd]; exact dvd_mul_of_dvd_right htd _
  · rw [← Nat.factorization_def B ht, ← hd, Nat.factorization_mul (pow_ne_zero 2 hd₁) hd₂0,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hsf ht htd]
    exact ⟨_, rfl⟩

/-- A nonzero number that is neither a square nor `p` times a square, `p` prime, has a prime
factor `r ≠ p` of odd valuation. -/
private lemma ovcs_exists_odd_val_ne {B p : ℕ} (hp : p.Prime) (hB : B ≠ 0)
    (hns : ∀ y : ℕ, B ≠ y ^ 2) (hpm : ∀ y : ℕ, B ≠ p * y ^ 2) :
    ∃ t, t.Prime ∧ t ≠ p ∧ t ∣ B ∧ Odd (padicValNat t B) := by
  obtain ⟨d₂, d₁, hd, hsf⟩ := Nat.sq_mul_squarefree B
  have hd₁ : d₁ ≠ 0 := by rintro rfl; apply hB; rw [← hd]; simp
  have hd₂ : d₂ ≠ 1 := by rintro rfl; exact hns d₁ (by rw [← hd, mul_one])
  have hd₂p : d₂ ≠ p := by rintro rfl; exact hpm d₁ (by rw [← hd, mul_comm])
  have hd₂0 : d₂ ≠ 0 := hsf.ne_zero
  obtain ⟨t, ht, htd, htp⟩ : ∃ t, t.Prime ∧ t ∣ d₂ ∧ t ≠ p := by
    by_cases hpd : p ∣ d₂
    · obtain ⟨e, he⟩ := hpd
      have he1 : e ≠ 1 := by rintro rfl; exact hd₂p (by rw [he, mul_one])
      refine ⟨e.minFac, Nat.minFac_prime he1, (Nat.minFac_dvd e).trans ⟨p, by rw [he]; ring⟩,
        fun hep => ?_⟩
      have hpe : p ∣ e := hep ▸ Nat.minFac_dvd e
      have hu := hsf p (by rw [he]; exact Nat.mul_dvd_mul_left p hpe)
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
    · have hm := Nat.minFac_dvd d₂
      exact ⟨d₂.minFac, Nat.minFac_prime hd₂, hm, fun h => hpd (h ▸ hm)⟩
  refine ⟨t, ht, htp, ?_, ?_⟩
  · rw [← hd]; exact dvd_mul_of_dvd_right htd _
  · rw [← Nat.factorization_def B ht, ← hd, Nat.factorization_mul (pow_ne_zero 2 hd₁) hd₂0,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hsf ht htd]
    exact ⟨_, rfl⟩

/-- The geometric sum identity in `ℕ`. -/
private lemma ovcs_geom_nat (u n : ℕ) (hu : 1 ≤ u) :
    (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = u ^ n - 1 := by
  have h1 : 1 ≤ u ^ n := Nat.one_le_pow _ _ hu
  zify [hu, h1]
  exact geom_sum_mul (u : ℤ) n

/-- The alternating sum: `B (u + 1) = u ^ p + 1` with `p` odd gives `B = Σ_{i < p} (-u) ^ i`. -/
private lemma ovcs_neg_sum {B u p : ℕ} (hp : Odd p) (hmul : B * (u + 1) = u ^ p + 1) :
    (B : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
  have hg := geom_sum_mul (-(u : ℤ)) p
  rw [Odd.neg_pow hp] at hg
  have hne : (u : ℤ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  have h : (B : ℤ) * ((u : ℤ) + 1) = (u : ℤ) ^ p + 1 := by exact_mod_cast hmul
  rw [h]
  linear_combination hg

/-- In a field, if `x ≠ 1` and `x ^ n = x` then `Σ_{i < n} x ^ i = 1`. -/
private lemma ovcs_geom_eq_one {F : Type*} [Field F] {x : F} {n : ℕ} (hx : x ≠ 1)
    (hn : x ^ n = x) : ∑ i ∈ Finset.range n, x ^ i = 1 := by
  have h := geom_sum_mul x n
  rw [hn] at h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hx) (h.trans (one_mul _).symm)

/-- Both factors are nonzero. -/
private lemma ovcs_factors_ne_zero {X p : ℕ} (hp : Odd p) :
    ∑ i ∈ Finset.range p, X ^ i ≠ 0 ∧ (X ^ p + 1) / (X + 1) ≠ 0 := by
  constructor
  · have h1 : X ^ 0 ≤ ∑ i ∈ Finset.range p, X ^ i :=
      Finset.single_le_sum (f := fun i => X ^ i) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hp.pos)
    rw [pow_zero] at h1
    omega
  · have hdvd : X + 1 ∣ X ^ p + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow X 1 hp
    intro h0
    have h1 := Nat.div_mul_cancel hdvd
    rw [h0, zero_mul] at h1
    omega

/-- Valuation of a product of three nonzero factors. -/
private lemma ovcs_val3 {r a b c : ℕ} (hr : r.Prime) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    padicValNat r (a * b * c) = padicValNat r a + padicValNat r b + padicValNat r c := by
  have := Fact.mk hr
  rw [padicValNat.mul (mul_ne_zero ha hb) hc, padicValNat.mul ha hb]

/-- `2 ≠ 0` modulo a prime above an odd prime. -/
private lemma ovcs_two_ne_zero {r p : ℕ} (hp : p.Prime) (hpr : p < r) :
    (2 : ZMod r) ≠ 0 := by
  intro h
  have h2 : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd two_pos h2
  have := hp.two_le
  omega

/-! ## Order and availability -/

/-- If `Σ_{i < p} z ^ i = 0` modulo a prime `r ≠ p` with `p` an odd prime, then `z ^ p = 1`,
`z ^ 2 ≠ 1` and `p < r`. -/
private lemma ovcs_core {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r ≠ p)
    (z : ZMod r) (hS : ∑ i ∈ Finset.range p, z ^ i = 0) :
    z ^ p = 1 ∧ z ^ 2 ≠ 1 ∧ p < r := by
  have := Fact.mk hr
  have := Fact.mk hp
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1] at hS
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hS
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp ((ZMod.natCast_eq_zero_iff p r).mp hS))
  have hzp : z ^ p = 1 := by
    have hg := geom_sum_mul z p
    rw [hS, zero_mul] at hg
    exact sub_eq_zero.mp hg.symm
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hzp
    exact zero_ne_one hzp
  refine ⟨hzp, fun h2 => ?_, ?_⟩
  · have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hd
    have := Nat.le_of_dvd two_pos hd
    have := hp.two_le
    exact hp2 (by omega)
  · have hd := ZMod.orderOf_dvd_card_sub_one hz0
    rw [hord] at hd
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hd
    omega

/-- If every prime factor of `L ≠ 0` is at least `p` and `y ^ L = 1` modulo `p`, then `y = 1`. -/
private lemma ovcs_eq_one_of_pow {p L : ℕ} (hp : p.Prime) (hL0 : L ≠ 0)
    (hmin : ∀ t, t.Prime → t ∣ L → p ≤ t) (y : ZMod p) (hy : y ^ L = 1) : y = 1 := by
  have := Fact.mk hp
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0] at hy
    exact zero_ne_one hy
  have h2 : y ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy0
  have hcop : Nat.Coprime L (p - 1) := Nat.coprime_of_dvd fun k hk hkL hkp => by
    have h1 := hmin k hk hkL
    have h4 := hp.two_le
    have h3 := Nat.le_of_dvd (by omega) hkp
    omega
  have h := (pow_gcd_eq_one (a := y) (m := L) (n := p - 1)).mpr ⟨hy, h2⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

/-- The positive factor is available when `p ∤ q - 1`. -/
private lemma ovcs_avail_plus {q p L : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hL0 : L ≠ 0)
    (hmin : ∀ t, t.Prime → t ∣ L → p ≤ t) (hpq : ¬ p ∣ q - 1) :
    ((q ^ L : ℕ) : ZMod p) ≠ 1 := by
  have := Fact.mk hp
  intro h
  push_cast at h
  have h1 := ovcs_eq_one_of_pow hp hL0 hmin _ h
  apply hpq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1, Nat.cast_one, sub_self]

/-! ## Witnesses -/

/-- A witness in the positive factor `Σ_{i < p} X ^ i`. -/
private lemma ovcs_plus_witness {X p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : 1 ≤ X)
    (hav : (X : ZMod p) ≠ 1) (hns : ∀ y : ℕ, ∑ i ∈ Finset.range p, X ^ i ≠ y ^ 2) :
    ∃ r, r.Prime ∧ p < r ∧ r ∣ ∑ i ∈ Finset.range p, X ^ i ∧
      Odd (padicValNat r (∑ i ∈ Finset.range p, X ^ i)) ∧ ¬ r ∣ (X - 1) * (X + 1) ∧
      ¬ r ∣ (X ^ p + 1) / (X + 1) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hB0 := (ovcs_factors_ne_zero (X := X) hpo).1
  have hpB : ¬ p ∣ ∑ i ∈ Finset.range p, X ^ i := by
    have := Fact.mk hp
    intro hdvd
    have h0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    have hS := ovcs_geom_eq_one hav (ZMod.pow_card (X : ZMod p))
    push_cast at h0
    rw [hS] at h0
    exact one_ne_zero h0
  obtain ⟨r, hr, hrB, hodd⟩ := ovcs_exists_odd_val hB0 hns
  have hrp : r ≠ p := by rintro rfl; exact hpB hrB
  have := Fact.mk hr
  have hS : ∑ i ∈ Finset.range p, (X : ZMod r) ^ i = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrB
    push_cast at h0
    exact h0
  obtain ⟨hzp, hz2, hpr⟩ := ovcs_core hr hp hp2 hrp _ hS
  have hr2 := ovcs_two_ne_zero hp hpr
  refine ⟨r, hr, hpr, hrB, hodd, fun hd => hz2 ?_, fun hd => ?_⟩
  · have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    push_cast [Nat.cast_sub hX] at h0
    linear_combination h0
  · have hdvd : X + 1 ∣ X ^ p + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow X 1 hpo
    have hmul : (X ^ p + 1) / (X + 1) * (X + 1) = X ^ p + 1 := Nat.div_mul_cancel hdvd
    generalize (X ^ p + 1) / (X + 1) = C at hmul hd
    have hc := congrArg (Nat.cast : ℕ → ZMod r) hmul
    push_cast at hc
    have h0 : (C : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    apply hr2
    linear_combination ((X : ZMod r) + 1) * h0 - hc - hzp

/-- A witness in the negative factor `(X ^ p + 1) / (X + 1)`, for `X ≡ 1 (mod 4)`: no
availability condition is needed. -/
private lemma ovcs_minus_witness {X p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : 1 ≤ X)
    (hX4 : X % 4 = 1) (hns : ∀ y : ℕ, (X ^ p + 1) / (X + 1) ≠ y ^ 2) :
    ∃ r, r.Prime ∧ p < r ∧ r ∣ (X ^ p + 1) / (X + 1) ∧
      Odd (padicValNat r ((X ^ p + 1) / (X + 1))) ∧ ¬ r ∣ (X - 1) * (X + 1) ∧
      ¬ r ∣ ∑ i ∈ Finset.range p, X ^ i := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hB0 := (ovcs_factors_ne_zero (X := X) hpo).2
  have hdvd : X + 1 ∣ X ^ p + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow X 1 hpo
  have hmul : (X ^ p + 1) / (X + 1) * (X + 1) = X ^ p + 1 := Nat.div_mul_cancel hdvd
  generalize (X ^ p + 1) / (X + 1) = B at hmul hns hB0 ⊢
  have hZ := ovcs_neg_sum hpo hmul
  have hpm : ∀ y : ℕ, B ≠ p * y ^ 2 := by
    intro y hy
    apply alternating_sum_ne_prime_mul_sq (y := y) hX4 hp hp2
    rw [← hmul, hy, mul_comm]
  obtain ⟨r, hr, hrp, hrB, hodd⟩ := ovcs_exists_odd_val_ne hp hB0 hns hpm
  have := Fact.mk hr
  have hS : ∑ i ∈ Finset.range p, (-(X : ZMod r)) ^ i = 0 := by
    have h0 : (B : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff B r).mpr hrB
    have hc := congrArg (fun z : ℤ => (z : ZMod r)) hZ
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc
    rw [← hc]
    exact h0
  obtain ⟨hzp, hz2, hpr⟩ := ovcs_core hr hp hp2 hrp _ hS
  have hr2 := ovcs_two_ne_zero hp hpr
  rw [Odd.neg_pow hpo] at hzp
  refine ⟨r, hr, hpr, hrB, hodd, fun hd => hz2 ?_, fun hd => ?_⟩
  · have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    push_cast [Nat.cast_sub hX] at h0
    linear_combination h0
  · have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
    push_cast at h0
    have hg := geom_sum_mul (X : ZMod r) p
    apply hr2
    linear_combination -(((X : ZMod r) - 1) * h0) + hg - hzp

/-- An earlier witness `r > p` with `r ∣ X ^ 2 - 1` divides neither new factor. -/
private lemma ovcs_survive {X p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hpr : p < r) (hX : 1 ≤ X) (hrX : r ∣ (X - 1) * (X + 1)) :
    ¬ r ∣ ∑ i ∈ Finset.range p, X ^ i ∧ ¬ r ∣ (X ^ p + 1) / (X + 1) := by
  have := Fact.mk hr
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hdvd : X + 1 ∣ X ^ p + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow X 1 hpo
  have hmul : (X ^ p + 1) / (X + 1) * (X + 1) = X ^ p + 1 := Nat.div_mul_cancel hdvd
  generalize (X ^ p + 1) / (X + 1) = C at hmul ⊢
  have hc := congrArg (Nat.cast : ℕ → ZMod r) hmul
  push_cast at hc
  have hg := geom_sum_mul (X : ZMod r) p
  have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrX
  push_cast [Nat.cast_sub hX] at h0
  have hr2 := ovcs_two_ne_zero hp hpr
  have hpr0 : (p : ZMod r) ≠ 0 := by
    intro h
    have := Nat.le_of_dvd hp.pos ((ZMod.natCast_eq_zero_iff p r).mp h)
    omega
  rcases mul_eq_zero.mp h0 with h1 | h1
  · have hy : (X : ZMod r) = 1 := sub_eq_zero.mp h1
    constructor
    · intro hd
      have h0' := (ZMod.natCast_eq_zero_iff _ r).mpr hd
      push_cast at h0'
      rw [hy] at h0'
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h0'
      exact hpr0 h0'
    · intro hd
      have h0' : (C : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
      rw [h0', hy, one_pow, zero_mul] at hc
      apply hr2
      linear_combination -hc
  · have hy : (X : ZMod r) = -1 := eq_neg_of_add_eq_zero_left h1
    constructor
    · intro hd
      have h0' := (ZMod.natCast_eq_zero_iff _ r).mpr hd
      push_cast at h0'
      rw [h0', hy, Odd.neg_one_pow hpo] at hg
      apply hr2
      linear_combination hg
    · intro hd
      have h0' : (C : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hd
      have hZ := ovcs_neg_sum hpo hmul
      have hc' := congrArg (fun z : ℤ => (z : ZMod r)) hZ
      simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc'
      rw [hy, neg_neg] at hc'
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc'
      rw [h0'] at hc'
      exact hpr0 hc'.symm

/-! ## The product decomposition -/

/-- `(q - 1) (2 H(L)) = (q ^ L - 1) (q ^ L + 1)`. -/
private lemma ovcs_sigma_two_mul {q L : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) :
    (q - 1) * (2 * ovcsH q L) = (q ^ L - 1) * (q ^ L + 1) := by
  unfold ovcsH
  rw [sigma_one_apply_prime_pow hq, show 2 * L - 1 + 1 = 2 * L by omega]
  have h2 : 2 ∣ ∑ i ∈ Finset.range (2 * L), q ^ i := by
    rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
    have : ∀ i ∈ Finset.range (2 * L), q ^ i % 2 = 1 := fun i _ => by
      simp [Nat.pow_mod, Nat.odd_iff.mp hqo]
    rw [Finset.sum_congr rfl this]
    simp
  rw [Nat.mul_div_cancel' h2, mul_comm, ovcs_geom_nat q _ hq.one_le]
  have hA : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  rw [two_mul, pow_add]
  generalize q ^ L = A at hA ⊢
  have hAA : 1 ≤ A * A := by nlinarith
  zify [hA, hAA]
  ring

/-- `H(p L) = H(L) B₊ B₋` with `X = q ^ L`, `B₊ = Σ_{i < p} X ^ i`, `B₋ = (X ^ p + 1) / (X + 1)`. -/
private lemma ovcs_H_mul {q L p : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) (hp : Odd p) :
    ovcsH q (p * L) = ovcsH q L * (∑ i ∈ Finset.range p, (q ^ L) ^ i) *
      (((q ^ L) ^ p + 1) / (q ^ L + 1)) := by
  have hp1 : 1 ≤ p := hp.pos
  have e1 := ovcs_sigma_two_mul hq hqo (L := p * L) (by have := Nat.mul_pos hp1 hL; omega)
  have e2 := ovcs_sigma_two_mul hq hqo hL
  rw [pow_mul'] at e1
  have hX : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  have hdvd : q ^ L + 1 ∣ (q ^ L) ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (q ^ L) 1 hp
  have hmul := Nat.div_mul_cancel hdvd
  have hg := ovcs_geom_nat (q ^ L) p hX
  generalize ((q ^ L) ^ p + 1) / (q ^ L + 1) = C at hmul ⊢
  generalize ∑ i ∈ Finset.range p, (q ^ L) ^ i = B at hg ⊢
  generalize ovcsH q (p * L) = A at e1 ⊢
  generalize ovcsH q L = A' at e2 ⊢
  generalize q ^ L = X at hX hmul hg e1 e2
  have hXp : 1 ≤ X ^ p := Nat.one_le_pow _ _ (by omega)
  have hq1 : 1 ≤ q := hq.one_le
  have hq2 : 0 < (q - 1) * 2 := by have := hq.two_le; omega
  apply Nat.eq_of_mul_eq_mul_left hq2
  zify [hX, hXp, hq1] at e1 e2 hg hmul ⊢
  linear_combination e1 - (B : ℤ) * (C : ℤ) * e2 - (C : ℤ) * ((X : ℤ) + 1) * hg -
    ((X : ℤ) ^ p - 1) * hmul

/-! ## Counting -/

private lemma ovcsC_eq (q L : ℕ) :
    ovcsC q L = L.factorization.sum (fun t e => if ¬ t ∣ q - 1 then e else 0) := by
  unfold ovcsC
  rw [Finset.sum_filter, Finsupp.sum, Nat.support_factorization]

private lemma ovcsC_mul {q p L : ℕ} (hp : p.Prime) (hL : L ≠ 0) :
    ovcsC q (p * L) = (if ¬ p ∣ q - 1 then 1 else 0) + ovcsC q L := by
  rw [ovcsC_eq, ovcsC_eq, Nat.factorization_mul hp.ne_zero hL, Finsupp.sum_add_index',
    hp.factorization, Finsupp.sum_single_index]
  all_goals
    intros
    try dsimp only
    split_ifs <;> simp


/-- The induction: a set `W` of primes of odd valuation in `H(L)`, each above every prime that is
at most all prime factors of `L`, with at least `Ω(L) + C(L)` elements, and a subset `Wm` of at
least `Ω(L)` elements, all dividing `q ^ L + 1`. -/
private lemma ovcs_main {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) (L : ℕ) (hL : Odd L) :
    ∃ W Wm : Finset ℕ, cardFactors L + ovcsC q L ≤ W.card ∧ cardFactors L ≤ Wm.card ∧
      Wm ⊆ W ∧ (∀ r ∈ Wm, r ∣ q ^ L + 1) ∧
      ∀ r ∈ W, r.Prime ∧ Odd (padicValNat r (ovcsH q L)) ∧
        ∀ s, s.Prime → (∀ t, t.Prime → t ∣ L → s ≤ t) → s < r := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  by_cases hL1 : L = 1
  · subst hL1
    refine ⟨∅, ∅, ?_, by simp, subset_refl _, fun r hr => absurd hr (Finset.notMem_empty r),
      fun r hr => absurd hr (Finset.notMem_empty r)⟩
    simp [ovcsC]
  obtain ⟨p, hp, hpL, hpmin⟩ : ∃ p, p.Prime ∧ p ∣ L ∧ ∀ t, t.Prime → t ∣ L → p ≤ t :=
    ⟨L.minFac, Nat.minFac_prime hL1, Nat.minFac_dvd L,
      fun t ht htL => Nat.minFac_le_of_dvd ht.two_le htL⟩
  obtain ⟨L', rfl⟩ := hpL
  have hpo : Odd p := (Nat.odd_mul.mp hL).1
  have hL'o : Odd L' := (Nat.odd_mul.mp hL).2
  have hp2 : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hpo) even_two
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hL'1 : 1 ≤ L' := hL'o.pos
  have hL'0 : L' ≠ 0 := by omega
  have hlt : L' < p * L' := by have := hp.two_le; nlinarith
  obtain ⟨W, Wm, hWcard, hWmcard, hsub, hWmdvd, hW⟩ := ih L' hlt hL'o
  have hmin' : ∀ t, t.Prime → t ∣ L' → p ≤ t := fun t ht htL =>
    hpmin t ht (Dvd.dvd.mul_left htL p)
  have hX : 1 ≤ q ^ L' := Nat.one_le_pow _ _ hq.pos
  have hHm := ovcs_H_mul hq hqo hL'1 hpo
  have e2 := ovcs_sigma_two_mul hq hqo hL'1
  have hH0 : ovcsH q L' ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at e2
    have hX2 : 1 < q ^ L' := Nat.one_lt_pow hL'0 hq.one_lt
    have : 0 < (q ^ L' - 1) * (q ^ L' + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hHdvd : ovcsH q L' ∣ (q ^ L' - 1) * (q ^ L' + 1) :=
    ⟨(q - 1) * 2, by rw [← e2]; ring⟩
  have hB := ovcs_factors_ne_zero (X := q ^ L') hpo
  have hdvd : q ^ L' + 1 ∣ (q ^ L') ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (q ^ L') 1 hpo
  -- earlier witnesses survive
  have hold : ∀ r ∈ W, r.Prime ∧ Odd (padicValNat r (ovcsH q (p * L'))) ∧
      ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r := by
    intro r hr
    obtain ⟨hrp, hodd, hinv⟩ := hW r hr
    have hpr : p < r := hinv p hp hmin'
    have hrH : r ∣ ovcsH q L' := by
      have := Fact.mk hrp
      exact dvd_of_one_le_padicValNat hodd.pos
    obtain ⟨h1, h2⟩ := ovcs_survive hp hp2 hrp hpr hX (hrH.trans hHdvd)
    refine ⟨hrp, ?_, fun s hs hst => hinv s hs fun t ht htL =>
      hst t ht (Dvd.dvd.mul_left htL p)⟩
    rw [hHm, ovcs_val3 hrp hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd h1,
      padicValNat.eq_zero_of_not_dvd h2]
    simpa using hodd
  have hnotW : ∀ r, ¬ r ∣ ovcsH q L' → r ∉ W := by
    intro r hrH hrW
    obtain ⟨hrp, hodd', -⟩ := hW r hrW
    have := Fact.mk hrp
    exact hrH (dvd_of_one_le_padicValNat hodd'.pos)
  have hinvnew : ∀ r, p < r → ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r :=
    fun r hpr s _ hst => lt_of_le_of_lt (hst p hp (dvd_mul_right p L')) hpr
  -- a new witness in the positive factor
  have hnewp : ¬ p ∣ q - 1 → ∃ r, r ∉ W ∧ r.Prime ∧
      Odd (padicValNat r (ovcsH q (p * L'))) ∧
      (∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r) ∧
      ¬ r ∣ ((q ^ L') ^ p + 1) / (q ^ L' + 1) := by
    intro hpq
    obtain ⟨r, hr, hpr, -, hodd, hrX, hrC⟩ := ovcs_plus_witness hp hp2 hX
      (ovcs_avail_plus hp hq.one_le hL'0 hmin' hpq) (fun y => hpos L' p y hL'o hpo hp3)
    have hrH : ¬ r ∣ ovcsH q L' := fun h => hrX (h.trans hHdvd)
    refine ⟨r, hnotW r hrH, hr, ?_, hinvnew r hpr, hrC⟩
    rw [hHm, ovcs_val3 hr hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd hrH,
      padicValNat.eq_zero_of_not_dvd hrC]
    simpa using hodd
  -- a new witness in the negative factor, always
  have hnewm : ∃ r, r ∉ W ∧ r.Prime ∧
      Odd (padicValNat r (ovcsH q (p * L'))) ∧
      (∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r) ∧
      r ∣ ((q ^ L') ^ p + 1) / (q ^ L' + 1) := by
    have hu4 : q ^ L' % 4 = 1 := by simp [Nat.pow_mod, hq4]
    have hns : ∀ y : ℕ, ((q ^ L') ^ p + 1) / (q ^ L' + 1) ≠ y ^ 2 := by
      intro y hy
      apply hneg L' p y hL'0 hu4 hpo hp3
      rw [← Nat.div_mul_cancel hdvd, hy, mul_comm]
    obtain ⟨r, hr, hpr, hrC, hodd, hrX, hrB⟩ := ovcs_minus_witness hp hp2 hX hu4 hns
    have hrH : ¬ r ∣ ovcsH q L' := fun h => hrX (h.trans hHdvd)
    refine ⟨r, hnotW r hrH, hr, ?_, hinvnew r hpr, hrC⟩
    rw [hHm, ovcs_val3 hr hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd hrH,
      padicValNat.eq_zero_of_not_dvd hrB]
    simpa using hodd
  -- the count
  have hcard : cardFactors (p * L') = cardFactors L' + 1 := by
    rw [cardFactors_mul hp.ne_zero hL'0, cardFactors_apply_prime hp]
    ring
  have hfree := ovcsC_mul (q := q) hp hL'0
  have hXp : q ^ (p * L') + 1 = (q ^ L') ^ p + 1 := by rw [pow_mul']
  have hBdvd : ((q ^ L') ^ p + 1) / (q ^ L' + 1) ∣ q ^ (p * L') + 1 := by
    rw [hXp]; exact Nat.div_dvd_of_dvd hdvd
  have hXdvd : q ^ L' + 1 ∣ q ^ (p * L') + 1 := by rw [hXp]; exact hdvd
  obtain ⟨rm, hrmW, hrm, hoddm, hinvm, hrmC⟩ := hnewm
  have hrmWm : rm ∉ Wm := fun h => hrmW (hsub h)
  have hWm' : ∀ r ∈ insert rm Wm, r ∣ q ^ (p * L') + 1 := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hrmC.trans hBdvd
    · exact (hWmdvd r hr).trans hXdvd
  have hins : ∀ x ∈ insert rm W, x.Prime ∧ Odd (padicValNat x (ovcsH q (p * L'))) ∧
      ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hrm, hoddm, hinvm⟩
    · exact hold x hx
  have hWmc : cardFactors (p * L') ≤ (insert rm Wm).card := by
    rw [Finset.card_insert_of_notMem hrmWm]
    omega
  by_cases h1 : p ∣ q - 1
  · have hc : (if ¬ p ∣ q - 1 then 1 else 0) = 0 := if_neg (not_not.mpr h1)
    refine ⟨insert rm W, insert rm Wm, ?_, hWmc, Finset.insert_subset_insert _ hsub, hWm',
      hins⟩
    rw [Finset.card_insert_of_notMem hrmW]
    omega
  · have hc : (if ¬ p ∣ q - 1 then 1 else 0) = 1 := if_pos h1
    obtain ⟨rp, hrpW, hrp, hoddp, hinvp, hrpC⟩ := hnewp h1
    have hne : rp ∉ insert rm W := by
      rw [Finset.mem_insert]
      rintro (h | h)
      · exact hrpC (by rw [h]; exact hrmC)
      · exact hrpW h
    refine ⟨insert rp (insert rm W), insert rm Wm, ?_, hWmc,
      (Finset.insert_subset_insert _ hsub).trans (Finset.subset_insert _ _), hWm', ?_⟩
    · rw [Finset.card_insert_of_notMem hne, Finset.card_insert_of_notMem hrmW]
      omega
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hrp, hoddp, hinvp⟩
      · exact hins x hx

/-- A set of primes of odd valuation in `H(L)` is at most the number of such primes. -/
private lemma ovcs_card_le {q L : ℕ} {W : Finset ℕ}
    (hW : ∀ r ∈ W, r.Prime ∧ Odd (padicValNat r (ovcsH q L))) :
    W.card ≤ ((σ 1 (q ^ (2 * L - 1)) / 2).primeFactors.filter
        fun t => Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization t)).card := by
  refine Finset.card_le_card fun r hr => ?_
  obtain ⟨hr, hodd⟩ := hW r hr
  unfold ovcsH at hodd
  have hodd' : Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization r) := by
    rw [Nat.factorization_def _ hr]
    exact hodd
  refine Finset.mem_filter.mpr ⟨?_, hodd'⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro h0
  rw [h0] at hodd'
  exact Nat.not_odd_zero hodd'

/-- Let `q` be a prime with `q ≡ 1 (mod 4)` and `L` odd. Under the two hypotheses `hpos` and
`hneg` (taken as explicit arguments, not proved here), at least `Ω(L) + C(L)` primes have odd
valuation in `σ(q ^ (2 L - 1)) / 2`, where `Ω(L)` counts the prime factors of `L` with
multiplicity and `C(L)` counts, with multiplicity, those that do not divide `q - 1`.
Arithmetic only. Published context: Y. Hirakawa (arXiv 2309.17084, Theorem 1.1) proves two odd
valuations in the Euler index for a special exponent above one; the novelty of this count is
not verified. -/
theorem cardFactors_add_signed_le_card_odd_valuation_half_sigma {q L : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 1) (hL : Odd L)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors L +
        ∑ p ∈ L.primeFactors.filter (fun p => ¬ p ∣ q - 1), L.factorization p ≤
      ((σ 1 (q ^ (2 * L - 1)) / 2).primeFactors.filter
        fun t => Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization t)).card := by
  obtain ⟨W, -, hcard, -, -, -, hW⟩ := ovcs_main hq hq4 hpos hneg L hL
  unfold ovcsC at hcard
  exact hcard.trans (ovcs_card_le fun r hr => ⟨(hW r hr).1, (hW r hr).2.1⟩)

/-- Let `q` be a prime with `q ≡ 1 (mod 4)` and `L ≥ 3` odd. Under the two hypotheses `hpos` and
`hneg` (taken as explicit arguments, not proved here), at least `Ω(L) + 1` primes have odd
valuation in `σ(q ^ (2 L - 1)) / 2`, where `Ω(L)` counts the prime factors of `L` with
multiplicity. The bound is sharp for `q = 5`, `L = 3`. Arithmetic only. Published context:
Y. Hirakawa (arXiv 2309.17084, Theorem 1.1) proves two odd valuations in the Euler index for a
special exponent above one; the novelty of this count is not verified. -/
theorem cardFactors_add_one_le_card_odd_valuation_half_sigma {q L : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 1) (hL : Odd L) (hL3 : 3 ≤ L)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors L + 1 ≤
      ((σ 1 (q ^ (2 * L - 1)) / 2).primeFactors.filter
        fun t => Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization t)).card := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨W, Wm, -, hWm, hsub, hWmdvd, hW⟩ := ovcs_main hq hq4 hpos hneg L hL
  have hRns : ∀ y : ℕ, ∑ i ∈ Finset.range L, q ^ i ≠ y ^ 2 := fun y => by
    simpa using hpos 1 L y odd_one hL hL3
  have hRodd : (∑ i ∈ Finset.range L, q ^ i) % 2 = 1 := by
    rw [Finset.sum_nat_mod]
    have : ∀ i ∈ Finset.range L, q ^ i % 2 = 1 := fun i _ => by
      simp [Nat.pow_mod, Nat.odd_iff.mp hqo]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    exact Nat.odd_iff.mp hL
  have hgeom := ovcs_geom_nat q L hq.one_le
  generalize ∑ i ∈ Finset.range L, q ^ i = R at hRns hRodd hgeom
  have hR0 : R ≠ 0 := by omega
  obtain ⟨r, hr, hrR, hodd⟩ := ovcs_exists_odd_val hR0 hRns
  have hA : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  have hqL2 : q ^ L % 2 = 1 := by simp [Nat.pow_mod, Nat.odd_iff.mp hqo]
  obtain ⟨Y, hY⟩ : 2 ∣ q ^ L + 1 := by omega
  have hHY : ovcsH q L = R * Y := by
    have e := ovcs_sigma_two_mul hq hqo (by omega : 1 ≤ L)
    rw [← hgeom, hY] at e
    have hq1 : 0 < (q - 1) * 2 := by have := hq.two_le; omega
    apply Nat.eq_of_mul_eq_mul_left hq1
    calc (q - 1) * 2 * ovcsH q L = (q - 1) * (2 * ovcsH q L) := by ring
      _ = R * (q - 1) * (2 * Y) := e
      _ = (q - 1) * 2 * (R * Y) := by ring
  have hrq : ¬ r ∣ q ^ L + 1 := by
    intro hd
    have h1 : r ∣ q ^ L - 1 := hrR.trans ⟨q - 1, hgeom.symm⟩
    have h3 : r ∣ (q ^ L + 1) - (q ^ L - 1) := Nat.dvd_sub hd h1
    rw [show q ^ L + 1 - (q ^ L - 1) = 2 by omega] at h3
    have h2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3
    rw [h2] at hrR
    omega
  have hrY : ¬ r ∣ Y := fun h => hrq (hY ▸ Dvd.dvd.mul_left h 2)
  have hY0 : Y ≠ 0 := by omega
  have hoddH : Odd (padicValNat r (ovcsH q L)) := by
    have := Fact.mk hr
    rw [hHY, padicValNat.mul hR0 hY0, padicValNat.eq_zero_of_not_dvd hrY, add_zero]
    exact hodd
  have hrWm : r ∉ Wm := fun h => hrq (hWmdvd r h)
  refine le_trans ?_ (ovcs_card_le (W := insert r Wm) ?_)
  · rw [Finset.card_insert_of_notMem hrWm]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hr, hoddH⟩
    · exact ⟨(hW x (hsub hx)).1, (hW x (hsub hx)).2.1⟩

end OddPerfect

#print axioms OddPerfect.cardFactors_add_signed_le_card_odd_valuation_half_sigma
#print axioms OddPerfect.cardFactors_add_one_le_card_odd_valuation_half_sigma
