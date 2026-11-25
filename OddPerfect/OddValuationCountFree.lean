import Mathlib

/-!
# More primes of odd valuation in half a divisor sum of a prime power

Let `q` be a prime with `q ≡ 1 (mod 4)`, let `L` be odd and put `H(L) = σ(q ^ (2 L - 1)) / 2`.
Write `Ω(L)` for the number of prime factors of `L` counted with multiplicity and
`Ω_free(L) = ∑ p ∈ L.primeFactors with ¬ p ∣ q ^ 2 - 1, L.factorization p`. This module proves
that at least `Ω(L) + Ω_free(L)` primes have odd valuation in `H(L)`, under the two hypotheses
of `OddPerfect.cardFactors_le_card_odd_valuation_half_sigma`, taken as explicit arguments:

* `hpos`: `Σ_{i < n} (q ^ h) ^ i` is never a square for odd `h` and odd `n ≥ 3`;
* `hneg`: `(q ^ h) ^ n + 1 ≠ (q ^ h + 1) y ^ 2` for `h ≠ 0`, `q ^ h ≡ 1 (mod 4)`, odd `n ≥ 3`.

Neither hypothesis is proved here.

Method. Strong induction on `L`, removing the least prime factor `p` of `L` last: `L = p L'`
where every prime factor of `L'` is at least `p`. With `X = q ^ L'` we have
`H(L) = H(L') B₊ B₋`, `B₊ = Σ_{i < p} X ^ i` and `B₋ = (X ^ p + 1) / (X + 1)`.

* Availability: `gcd(L', p - 1) = 1`, so `p ∣ B₊` forces `p ∣ q - 1` and `p ∣ B₋` forces
  `p ∣ q + 1`. At least one sign is available, both when `p ∤ q ^ 2 - 1`.
* A prime `r` of odd valuation in an available `B₊` (resp. `B₋`) has `X` (resp. `-X`) of order
  `p` modulo `r`, so `p < r`, `r ∤ X ^ 2 - 1` (hence `r ∤ H(L')`) and `r` does not divide the
  other factor. So `v_r(H(L)) = v_r(B₊)` (resp. `v_r(B₋)`) is odd.
* An earlier witness `r` divides `X ^ 2 - 1` and exceeds `p`, so `B₊` and `B₋` are `1` or `p`
  modulo `r` and keep `v_r(H)` unchanged. Taking the least prime last means no witness is lost.

The landed count orders the levels differently and can lose a witness: for `q = 37` and
`L = 21` it gives `Ω(L) = 2`, while here `Ω_free(21) = 1` (`37 ^ 2 - 1 = 2 ^ 3 3 ^ 2 19`) and the
bound is `3`.

Published context: Y. Hirakawa (2024) proves that two primes have odd valuation in the Euler
index for a special exponent above one. The novelty of the count in this module is not
verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Half the divisor sum `σ(q ^ (2 L - 1)) / 2`. -/
private def ovcfH (q L : ℕ) : ℕ := σ 1 (q ^ (2 * L - 1)) / 2

/-- The free count `∑ p ∈ L.primeFactors with ¬ p ∣ q ^ 2 - 1, L.factorization p`. -/
private def ovcfFree (q L : ℕ) : ℕ :=
  ∑ p ∈ L.primeFactors.filter (fun p => ¬ p ∣ q ^ 2 - 1), L.factorization p

/-! ## Helpers -/

/-- A nonzero number that is not a square has a prime factor of odd valuation. -/
private lemma ovcf_exists_odd_val {B : ℕ} (hB : B ≠ 0) (hns : ∀ y : ℕ, B ≠ y ^ 2) :
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

/-- The geometric sum identity in `ℕ`. -/
private lemma ovcf_geom_nat (u n : ℕ) (hu : 1 ≤ u) :
    (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = u ^ n - 1 := by
  have h1 : 1 ≤ u ^ n := Nat.one_le_pow _ _ hu
  zify [hu, h1]
  exact geom_sum_mul (u : ℤ) n

/-- The alternating sum: `B (u + 1) = u ^ p + 1` with `p` odd gives `B = Σ_{i < p} (-u) ^ i`. -/
private lemma ovcf_neg_sum {B u p : ℕ} (hp : Odd p) (hmul : B * (u + 1) = u ^ p + 1) :
    (B : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
  have hg := geom_sum_mul (-(u : ℤ)) p
  rw [Odd.neg_pow hp] at hg
  have hne : (u : ℤ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  have h : (B : ℤ) * ((u : ℤ) + 1) = (u : ℤ) ^ p + 1 := by exact_mod_cast hmul
  rw [h]
  linear_combination hg

/-- In a field, if `x ≠ 1` and `x ^ n = x` then `Σ_{i < n} x ^ i = 1`. -/
private lemma ovcf_geom_eq_one {F : Type*} [Field F] {x : F} {n : ℕ} (hx : x ≠ 1)
    (hn : x ^ n = x) : ∑ i ∈ Finset.range n, x ^ i = 1 := by
  have h := geom_sum_mul x n
  rw [hn] at h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hx) (h.trans (one_mul _).symm)

/-- Both factors are nonzero. -/
private lemma ovcf_factors_ne_zero {X p : ℕ} (hp : Odd p) :
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
private lemma ovcf_val3 {r a b c : ℕ} (hr : r.Prime) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    padicValNat r (a * b * c) = padicValNat r a + padicValNat r b + padicValNat r c := by
  have := Fact.mk hr
  rw [padicValNat.mul (mul_ne_zero ha hb) hc, padicValNat.mul ha hb]

/-- `2 ≠ 0` modulo a prime above an odd prime. -/
private lemma ovcf_two_ne_zero {r p : ℕ} (hp : p.Prime) (hpr : p < r) :
    (2 : ZMod r) ≠ 0 := by
  intro h
  have h2 : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by exact_mod_cast h)
  have := Nat.le_of_dvd two_pos h2
  have := hp.two_le
  omega

/-! ## Order and availability -/

/-- If `Σ_{i < p} z ^ i = 0` modulo a prime `r ≠ p` with `p` an odd prime, then `z ^ p = 1`,
`z ^ 2 ≠ 1` and `p < r`. -/
private lemma ovcf_core {r p : ℕ} (hr : r.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r ≠ p)
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
private lemma ovcf_eq_one_of_pow {p L : ℕ} (hp : p.Prime) (hL0 : L ≠ 0)
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
private lemma ovcf_avail_plus {q p L : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hL0 : L ≠ 0)
    (hmin : ∀ t, t.Prime → t ∣ L → p ≤ t) (hpq : ¬ p ∣ q - 1) :
    ((q ^ L : ℕ) : ZMod p) ≠ 1 := by
  have := Fact.mk hp
  intro h
  push_cast at h
  have h1 := ovcf_eq_one_of_pow hp hL0 hmin _ h
  apply hpq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1, Nat.cast_one, sub_self]

/-- The negative factor is available when `p ∤ q + 1`. -/
private lemma ovcf_avail_minus {q p L : ℕ} (hp : p.Prime) (hL : Odd L)
    (hmin : ∀ t, t.Prime → t ∣ L → p ≤ t) (hpq : ¬ p ∣ q + 1) :
    -((q ^ L : ℕ) : ZMod p) ≠ 1 := by
  have := Fact.mk hp
  intro h
  push_cast at h
  rw [← Odd.neg_pow hL] at h
  have h1 := ovcf_eq_one_of_pow hp hL.pos.ne' hmin _ h
  apply hpq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  linear_combination -h1

/-! ## Witnesses -/

/-- A witness in the positive factor `Σ_{i < p} X ^ i`. -/
private lemma ovcf_plus_witness {X p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : 1 ≤ X)
    (hav : (X : ZMod p) ≠ 1) (hns : ∀ y : ℕ, ∑ i ∈ Finset.range p, X ^ i ≠ y ^ 2) :
    ∃ r, r.Prime ∧ p < r ∧ r ∣ ∑ i ∈ Finset.range p, X ^ i ∧
      Odd (padicValNat r (∑ i ∈ Finset.range p, X ^ i)) ∧ ¬ r ∣ (X - 1) * (X + 1) ∧
      ¬ r ∣ (X ^ p + 1) / (X + 1) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hB0 := (ovcf_factors_ne_zero (X := X) hpo).1
  have hpB : ¬ p ∣ ∑ i ∈ Finset.range p, X ^ i := by
    have := Fact.mk hp
    intro hdvd
    have h0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    have hS := ovcf_geom_eq_one hav (ZMod.pow_card (X : ZMod p))
    push_cast at h0
    rw [hS] at h0
    exact one_ne_zero h0
  obtain ⟨r, hr, hrB, hodd⟩ := ovcf_exists_odd_val hB0 hns
  have hrp : r ≠ p := by rintro rfl; exact hpB hrB
  have := Fact.mk hr
  have hS : ∑ i ∈ Finset.range p, (X : ZMod r) ^ i = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrB
    push_cast at h0
    exact h0
  obtain ⟨hzp, hz2, hpr⟩ := ovcf_core hr hp hp2 hrp _ hS
  have hr2 := ovcf_two_ne_zero hp hpr
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

/-- A witness in the negative factor `(X ^ p + 1) / (X + 1)`. -/
private lemma ovcf_minus_witness {X p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : 1 ≤ X)
    (hav : -(X : ZMod p) ≠ 1) (hns : ∀ y : ℕ, (X ^ p + 1) / (X + 1) ≠ y ^ 2) :
    ∃ r, r.Prime ∧ p < r ∧ r ∣ (X ^ p + 1) / (X + 1) ∧
      Odd (padicValNat r ((X ^ p + 1) / (X + 1))) ∧ ¬ r ∣ (X - 1) * (X + 1) ∧
      ¬ r ∣ ∑ i ∈ Finset.range p, X ^ i := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hB0 := (ovcf_factors_ne_zero (X := X) hpo).2
  have hdvd : X + 1 ∣ X ^ p + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow X 1 hpo
  have hmul : (X ^ p + 1) / (X + 1) * (X + 1) = X ^ p + 1 := Nat.div_mul_cancel hdvd
  generalize (X ^ p + 1) / (X + 1) = B at hmul hns hB0 ⊢
  have hZ := ovcf_neg_sum hpo hmul
  have hpB : ¬ p ∣ B := by
    have := Fact.mk hp
    intro hd
    have h0 : (B : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff B p).mpr hd
    have hS := ovcf_geom_eq_one hav (ZMod.pow_card (-(X : ZMod p)))
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hZ
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc
    rw [hc, hS] at h0
    exact one_ne_zero h0
  obtain ⟨r, hr, hrB, hodd⟩ := ovcf_exists_odd_val hB0 hns
  have hrp : r ≠ p := by rintro rfl; exact hpB hrB
  have := Fact.mk hr
  have hS : ∑ i ∈ Finset.range p, (-(X : ZMod r)) ^ i = 0 := by
    have h0 : (B : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff B r).mpr hrB
    have hc := congrArg (fun z : ℤ => (z : ZMod r)) hZ
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc
    rw [← hc]
    exact h0
  obtain ⟨hzp, hz2, hpr⟩ := ovcf_core hr hp hp2 hrp _ hS
  have hr2 := ovcf_two_ne_zero hp hpr
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
private lemma ovcf_survive {X p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
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
  have hr2 := ovcf_two_ne_zero hp hpr
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
      have hZ := ovcf_neg_sum hpo hmul
      have hc' := congrArg (fun z : ℤ => (z : ZMod r)) hZ
      simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at hc'
      rw [hy, neg_neg] at hc'
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc'
      rw [h0'] at hc'
      exact hpr0 hc'.symm

/-! ## The product decomposition -/

/-- `(q - 1) (2 H(L)) = (q ^ L - 1) (q ^ L + 1)`. -/
private lemma ovcf_sigma_two_mul {q L : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) :
    (q - 1) * (2 * ovcfH q L) = (q ^ L - 1) * (q ^ L + 1) := by
  unfold ovcfH
  rw [sigma_one_apply_prime_pow hq, show 2 * L - 1 + 1 = 2 * L by omega]
  have h2 : 2 ∣ ∑ i ∈ Finset.range (2 * L), q ^ i := by
    rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
    have : ∀ i ∈ Finset.range (2 * L), q ^ i % 2 = 1 := fun i _ => by
      simp [Nat.pow_mod, Nat.odd_iff.mp hqo]
    rw [Finset.sum_congr rfl this]
    simp
  rw [Nat.mul_div_cancel' h2, mul_comm, ovcf_geom_nat q _ hq.one_le]
  have hA : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  rw [two_mul, pow_add]
  generalize q ^ L = A at hA ⊢
  have hAA : 1 ≤ A * A := by nlinarith
  zify [hA, hAA]
  ring

/-- `H(p L) = H(L) B₊ B₋` with `X = q ^ L`, `B₊ = Σ_{i < p} X ^ i`, `B₋ = (X ^ p + 1) / (X + 1)`. -/
private lemma ovcf_H_mul {q L p : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) (hp : Odd p) :
    ovcfH q (p * L) = ovcfH q L * (∑ i ∈ Finset.range p, (q ^ L) ^ i) *
      (((q ^ L) ^ p + 1) / (q ^ L + 1)) := by
  have hp1 : 1 ≤ p := hp.pos
  have e1 := ovcf_sigma_two_mul hq hqo (L := p * L) (by have := Nat.mul_pos hp1 hL; omega)
  have e2 := ovcf_sigma_two_mul hq hqo hL
  rw [pow_mul'] at e1
  have hX : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  have hdvd : q ^ L + 1 ∣ (q ^ L) ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (q ^ L) 1 hp
  have hmul := Nat.div_mul_cancel hdvd
  have hg := ovcf_geom_nat (q ^ L) p hX
  generalize ((q ^ L) ^ p + 1) / (q ^ L + 1) = C at hmul ⊢
  generalize ∑ i ∈ Finset.range p, (q ^ L) ^ i = B at hg ⊢
  generalize ovcfH q (p * L) = A at e1 ⊢
  generalize ovcfH q L = A' at e2 ⊢
  generalize q ^ L = X at hX hmul hg e1 e2
  have hXp : 1 ≤ X ^ p := Nat.one_le_pow _ _ (by omega)
  have hq1 : 1 ≤ q := hq.one_le
  have hq2 : 0 < (q - 1) * 2 := by have := hq.two_le; omega
  apply Nat.eq_of_mul_eq_mul_left hq2
  zify [hX, hXp, hq1] at e1 e2 hg hmul ⊢
  linear_combination e1 - (B : ℤ) * (C : ℤ) * e2 - (C : ℤ) * ((X : ℤ) + 1) * hg -
    ((X : ℤ) ^ p - 1) * hmul

/-! ## Counting -/

private lemma ovcfFree_eq (q L : ℕ) :
    ovcfFree q L = L.factorization.sum (fun t e => if ¬ t ∣ q ^ 2 - 1 then e else 0) := by
  unfold ovcfFree
  rw [Finset.sum_filter, Finsupp.sum, Nat.support_factorization]

private lemma ovcfFree_mul {q p L : ℕ} (hp : p.Prime) (hL : L ≠ 0) :
    ovcfFree q (p * L) = (if ¬ p ∣ q ^ 2 - 1 then 1 else 0) + ovcfFree q L := by
  rw [ovcfFree_eq, ovcfFree_eq, Nat.factorization_mul hp.ne_zero hL, Finsupp.sum_add_index',
    hp.factorization, Finsupp.sum_single_index]
  all_goals
    intros
    try dsimp only
    split_ifs <;> simp

/-- The induction: a set of primes of odd valuation in `H(L)`, each above every prime that is at
most all prime factors of `L`, with at least `Ω(L) + Ω_free(L)` elements. -/
private lemma ovcf_main {q : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) (L : ℕ) (hL : Odd L) :
    ∃ W : Finset ℕ, cardFactors L + ovcfFree q L ≤ W.card ∧
      ∀ r ∈ W, r.Prime ∧ Odd (padicValNat r (ovcfH q L)) ∧
        ∀ s, s.Prime → (∀ t, t.Prime → t ∣ L → s ≤ t) → s < r := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  by_cases hL1 : L = 1
  · subst hL1
    refine ⟨∅, ?_, fun r hr => absurd hr (Finset.notMem_empty r)⟩
    simp [ovcfFree]
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
  obtain ⟨W, hWcard, hW⟩ := ih L' hlt hL'o
  have hmin' : ∀ t, t.Prime → t ∣ L' → p ≤ t := fun t ht htL =>
    hpmin t ht (Dvd.dvd.mul_left htL p)
  have hX : 1 ≤ q ^ L' := Nat.one_le_pow _ _ hq.pos
  have hX2 : 1 < q ^ L' := Nat.one_lt_pow hL'0 hq.one_lt
  have hHm := ovcf_H_mul hq hqo hL'1 hpo
  have e2 := ovcf_sigma_two_mul hq hqo hL'1
  have hH0 : ovcfH q L' ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at e2
    have : 0 < (q ^ L' - 1) * (q ^ L' + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hHdvd : ovcfH q L' ∣ (q ^ L' - 1) * (q ^ L' + 1) :=
    ⟨(q - 1) * 2, by rw [← e2]; ring⟩
  have hB := ovcf_factors_ne_zero (X := q ^ L') hpo
  -- earlier witnesses survive
  have hold : ∀ r ∈ W, r.Prime ∧ Odd (padicValNat r (ovcfH q (p * L'))) ∧
      ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r := by
    intro r hr
    obtain ⟨hrp, hodd, hinv⟩ := hW r hr
    have hpr : p < r := hinv p hp hmin'
    have hrH : r ∣ ovcfH q L' := by
      have := Fact.mk hrp
      exact dvd_of_one_le_padicValNat hodd.pos
    obtain ⟨h1, h2⟩ := ovcf_survive hp hp2 hrp hpr hX (hrH.trans hHdvd)
    refine ⟨hrp, ?_, fun s hs hst => hinv s hs fun t ht htL =>
      hst t ht (Dvd.dvd.mul_left htL p)⟩
    rw [hHm, ovcf_val3 hrp hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd h1,
      padicValNat.eq_zero_of_not_dvd h2]
    simpa using hodd
  have hnotW : ∀ r, ¬ r ∣ ovcfH q L' → r ∉ W := by
    intro r hrH hrW
    obtain ⟨hrp, hodd', -⟩ := hW r hrW
    have := Fact.mk hrp
    exact hrH (dvd_of_one_le_padicValNat hodd'.pos)
  have hinvnew : ∀ r, p < r → ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r :=
    fun r hpr s _ hst => lt_of_le_of_lt (hst p hp (dvd_mul_right p L')) hpr
  -- a new witness in the positive factor
  have hnewp : ¬ p ∣ q - 1 → ∃ r, r ∉ W ∧ r.Prime ∧
      Odd (padicValNat r (ovcfH q (p * L'))) ∧
      (∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r) ∧
      ¬ r ∣ ((q ^ L') ^ p + 1) / (q ^ L' + 1) := by
    intro hpq
    obtain ⟨r, hr, hpr, -, hodd, hrX, hrC⟩ := ovcf_plus_witness hp hp2 hX
      (ovcf_avail_plus hp hq.one_le hL'0 hmin' hpq) (fun y => hpos L' p y hL'o hpo hp3)
    have hrH : ¬ r ∣ ovcfH q L' := fun h => hrX (h.trans hHdvd)
    refine ⟨r, hnotW r hrH, hr, ?_, hinvnew r hpr, hrC⟩
    rw [hHm, ovcf_val3 hr hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd hrH,
      padicValNat.eq_zero_of_not_dvd hrC]
    simpa using hodd
  -- a new witness in the negative factor
  have hnewm : ¬ p ∣ q + 1 → ∃ r, r ∉ W ∧ r.Prime ∧
      Odd (padicValNat r (ovcfH q (p * L'))) ∧
      (∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r) ∧
      r ∣ ((q ^ L') ^ p + 1) / (q ^ L' + 1) := by
    intro hpq
    have hu4 : q ^ L' % 4 = 1 := by simp [Nat.pow_mod, hq4]
    have hdvd : q ^ L' + 1 ∣ (q ^ L') ^ p + 1 := by
      simpa using Odd.nat_add_dvd_pow_add_pow (q ^ L') 1 hpo
    have hns : ∀ y : ℕ, ((q ^ L') ^ p + 1) / (q ^ L' + 1) ≠ y ^ 2 := by
      intro y hy
      apply hneg L' p y hL'0 hu4 hpo hp3
      rw [← Nat.div_mul_cancel hdvd, hy, mul_comm]
    obtain ⟨r, hr, hpr, hrC, hodd, hrX, hrB⟩ := ovcf_minus_witness hp hp2 hX
      (ovcf_avail_minus hp hL'o hmin' hpq) hns
    have hrH : ¬ r ∣ ovcfH q L' := fun h => hrX (h.trans hHdvd)
    refine ⟨r, hnotW r hrH, hr, ?_, hinvnew r hpr, hrC⟩
    rw [hHm, ovcf_val3 hr hH0 hB.1 hB.2, padicValNat.eq_zero_of_not_dvd hrH,
      padicValNat.eq_zero_of_not_dvd hrB]
    simpa using hodd
  -- the count
  have hcard : cardFactors (p * L') = cardFactors L' + 1 := by
    rw [cardFactors_mul hp.ne_zero hL'0, cardFactors_apply_prime hp]
    ring
  have hfree := ovcfFree_mul (q := q) hp hL'0
  have hq2 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 := hq.one_le
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq.pos
    zify [h1, h2]
    ring
  have hboth : ¬ (p ∣ q - 1 ∧ p ∣ q + 1) := by
    rintro ⟨h1, h2⟩
    have h3 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h2 h1
    rw [show (q + 1) - (q - 1) = 2 by have := hq.two_le; omega] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hins : ∀ r, r.Prime → Odd (padicValNat r (ovcfH q (p * L'))) →
      (∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < r) →
      ∀ x ∈ insert r W, x.Prime ∧ Odd (padicValNat x (ovcfH q (p * L'))) ∧
        ∀ s, s.Prime → (∀ t, t.Prime → t ∣ p * L' → s ≤ t) → s < x := by
    intro r hr hodd hinv x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hr, hodd, hinv⟩
    · exact hold x hx
  by_cases h1 : p ∣ q - 1
  · have h2 : ¬ p ∣ q + 1 := fun h2 => hboth ⟨h1, h2⟩
    have hc : (if ¬ p ∣ q ^ 2 - 1 then 1 else 0) = 0 :=
      if_neg (not_not.mpr (by rw [hq2]; exact Dvd.dvd.mul_right h1 _))
    obtain ⟨r, hrW, hr, hodd, hinv, -⟩ := hnewm h2
    refine ⟨insert r W, ?_, hins r hr hodd hinv⟩
    rw [Finset.card_insert_of_notMem hrW]
    omega
  · by_cases h2 : p ∣ q + 1
    · have hc : (if ¬ p ∣ q ^ 2 - 1 then 1 else 0) = 0 :=
        if_neg (not_not.mpr (by rw [hq2]; exact Dvd.dvd.mul_left h2 _))
      obtain ⟨r, hrW, hr, hodd, hinv, -⟩ := hnewp h1
      refine ⟨insert r W, ?_, hins r hr hodd hinv⟩
      rw [Finset.card_insert_of_notMem hrW]
      omega
    · have hc : (if ¬ p ∣ q ^ 2 - 1 then 1 else 0) = 1 := by
        refine if_pos fun h => ?_
        rw [hq2] at h
        rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · exact h1 h
        · exact h2 h
      obtain ⟨rp, hrpW, hrp, hoddp, hinvp, hrpC⟩ := hnewp h1
      obtain ⟨rm, hrmW, hrm, hoddm, hinvm, hrmC⟩ := hnewm h2
      have hne : rp ∉ insert rm W := by
        rw [Finset.mem_insert]
        rintro (h | h)
        · exact hrpC (by rw [h]; exact hrmC)
        · exact hrpW h
      refine ⟨insert rp (insert rm W), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hne, Finset.card_insert_of_notMem hrmW]
        omega
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨hrp, hoddp, hinvp⟩
        · exact hins rm hrm hoddm hinvm x hx

/-- Let `q` be a prime with `q ≡ 1 (mod 4)` and `L` odd. Under the two hypotheses `hpos` and
`hneg` (taken as explicit arguments, not proved here), at least `Ω(L) + Ω_free(L)` primes have
odd valuation in `σ(q ^ (2 L - 1)) / 2`, where `Ω(L)` counts the prime factors of `L` with
multiplicity and `Ω_free(L)` counts, with multiplicity, those that do not divide `q ^ 2 - 1`.
This strengthens `OddPerfect.cardFactors_le_card_odd_valuation_half_sigma`. Published context:
Y. Hirakawa (2024) proves two odd valuations in the Euler index for a special exponent above
one; the novelty of this count is not verified. -/
theorem cardFactors_add_free_le_card_odd_valuation_half_sigma {q L : ℕ} (hq : q.Prime)
    (hq4 : q % 4 = 1) (hL : Odd L)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors L +
        ∑ p ∈ L.primeFactors.filter (fun p => ¬ p ∣ q ^ 2 - 1), L.factorization p ≤
      ((σ 1 (q ^ (2 * L - 1)) / 2).primeFactors.filter
        fun t => Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization t)).card := by
  obtain ⟨W, hcard, hW⟩ := ovcf_main hq hq4 hpos hneg L hL
  unfold ovcfFree at hcard
  refine hcard.trans (Finset.card_le_card fun r hr => ?_)
  obtain ⟨hr, hodd, -⟩ := hW r hr
  unfold ovcfH at hodd
  have hodd' : Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization r) := by
    rw [Nat.factorization_def _ hr]
    exact hodd
  refine Finset.mem_filter.mpr ⟨?_, hodd'⟩
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  intro h0
  rw [h0] at hodd'
  exact Nat.not_odd_zero hodd'

end OddPerfect

#print axioms OddPerfect.cardFactors_add_free_le_card_odd_valuation_half_sigma
