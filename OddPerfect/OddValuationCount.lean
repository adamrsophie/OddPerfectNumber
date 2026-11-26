import Mathlib

/-!
# Primes of odd valuation in half a divisor sum of a prime power

Let `q` be a prime with `q ≡ 1 (mod 4)`, let `L` be odd and put
`H = σ(q ^ (2 L - 1)) / 2 = R S` with `R = (q ^ L - 1) / (q - 1)` and `S = (q ^ L + 1) / 2`.
This module proves that at least `Ω(L)` primes (prime factors of `L` counted with multiplicity)
have odd valuation in `H`, under two hypotheses that are taken as explicit arguments:

* `hpos`: `Σ_{i < n} (q ^ h) ^ i` is never a square for odd `h` and odd `n ≥ 3`;
* `hneg`: `(q ^ h) ^ n + 1 ≠ (q ^ h + 1) y ^ 2` for `h ≠ 0`, `q ^ h ≡ 1 (mod 4)`, odd `n ≥ 3`.

Neither hypothesis is proved here.

Method. For a prime `p` with `p ^ d ∥ L`, a level `1 ≤ j ≤ d` and `u = q ^ (p ^ (j - 1))`, put
`B₊ = (u ^ p - 1) / (u - 1)` and `B₋ = (u ^ p + 1) / (u + 1)`. If `p ∤ q - 1` then `p ∤ B₊`, and
if `p ∤ q + 1` then `p ∤ B₋`; at least one of the two holds since `p` is odd. A prime `t` of odd
valuation in an available `B₊` (resp. `B₋`) has `q` (resp. `-q`) of order `p ^ j` modulo `t`,
and by lifting the exponent `v_t(H) = v_t(B) + v_t(L)`. So witnesses taken at different
(sign, prime, level) are different primes, and a witness loses its odd valuation in `H` only
if `t ∣ L` with `t ∤ q ^ 2 - 1`, that is `t` lies in the set `G` of such primes of `L`. Every
level has an available sign and every prime of `G` has both signs at every level, so there
are at least `Ω(L) + |G|` witnesses and at most `|G|` of them are lost.

A witness can really be lost: for `q = 37` and `L = 21` the prime `7` has
`v_7(37 ^ 2 + 37 + 1) = 1` but `v_7(R) = 2`.

Published context: Y. Hirakawa (2024) proves that two primes have odd valuation in the Euler
index for a special exponent above one. The novelty of the count in this module is not
verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Helpers -/

/-- A nonzero number that is not a square has a prime factor of odd valuation. -/
private lemma ovc_exists_odd_val {B : ℕ} (hB : B ≠ 0) (hns : ∀ y : ℕ, B ≠ y ^ 2) :
    ∃ t, t.Prime ∧ t ∣ B ∧ Odd (padicValNat t B) := by
  obtain ⟨d₂, d₁, hd, hsf⟩ := Nat.sq_mul_squarefree B
  have hd₁ : d₁ ≠ 0 := by rintro rfl; apply hB; rw [← hd]; simp
  have hd₂ : d₂ ≠ 1 := by rintro rfl; exact hns d₁ (by rw [← hd, mul_one])
  have hd₂0 : d₂ ≠ 0 := hsf.ne_zero
  have ht : d₂.minFac.Prime := Nat.minFac_prime hd₂
  have htd : d₂.minFac ∣ d₂ := Nat.minFac_dvd d₂
  refine ⟨d₂.minFac, ht, ?_, ?_⟩
  · rw [← hd]; exact dvd_mul_of_dvd_right htd _
  · rw [Nat.padicValNat_def, ← Nat.factorization_def B ht, ← hd,
      Nat.factorization_mul (pow_ne_zero 2 hd₁) hd₂0,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hsf ht htd]
    exact ⟨_, rfl⟩

/-- The geometric sum identity in `ℕ`. -/
private lemma ovc_geom_nat (u n : ℕ) (hu : 1 ≤ u) :
    (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = u ^ n - 1 := by
  have h1 : 1 ≤ u ^ n := Nat.one_le_pow _ _ hu
  zify [hu, h1]
  exact geom_sum_mul (u : ℤ) n

/-- The alternating sum: `B (u + 1) = u ^ p + 1` with `p` odd gives `B = Σ_{i < p} (-u) ^ i`. -/
private lemma ovc_neg_sum {B u p : ℕ} (hp : Odd p) (hmul : B * (u + 1) = u ^ p + 1) :
    (B : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
  have hg := geom_sum_mul (-(u : ℤ)) p
  rw [Odd.neg_pow hp] at hg
  have hne : (u : ℤ) + 1 ≠ 0 := by positivity
  apply mul_right_cancel₀ hne
  have h : (B : ℤ) * ((u : ℤ) + 1) = (u : ℤ) ^ p + 1 := by exact_mod_cast hmul
  rw [h]
  linear_combination hg

/-- In a field, if `x ≠ 1` and `x ^ n = x` then `Σ_{i < n} x ^ i = 1`. -/
private lemma ovc_geom_eq_one {F : Type*} [Field F] {x : F} {n : ℕ} (hx : x ≠ 1)
    (hn : x ^ n = x) : ∑ i ∈ Finset.range n, x ^ i = 1 := by
  have h := geom_sum_mul x n
  rw [hn] at h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hx) (h.trans (one_mul _).symm)

/-- If `Σ_{i < p} (y ^ (p ^ k)) ^ i = 0` modulo a prime `t ≠ p`, then `y ^ (p ^ k) ≠ 1` and `y`
has order `p ^ (k + 1)`. -/
private lemma ovc_order {t p k : ℕ} (ht : t.Prime) (hp : p.Prime) (htp : t ≠ p) (y : ZMod t)
    (hS : ∑ i ∈ Finset.range p, (y ^ p ^ k) ^ i = 0) :
    y ^ p ^ k ≠ 1 ∧ orderOf y = p ^ (k + 1) := by
  have := Fact.mk ht
  have := Fact.mk hp
  have hx1 : y ^ p ^ k ≠ 1 := by
    intro h1
    rw [h1] at hS
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hS
    exact htp ((Nat.prime_dvd_prime_iff_eq ht hp).mp ((ZMod.natCast_eq_zero_iff p t).mp hS))
  have hxp : (y ^ p ^ k) ^ p = 1 := by
    have hg := geom_sum_mul (y ^ p ^ k) p
    rw [hS, zero_mul] at hg
    exact sub_eq_zero.mp hg.symm
  refine ⟨hx1, orderOf_eq_prime_pow hx1 ?_⟩
  rw [pow_succ, pow_mul]
  exact hxp

/-- If `y = ± q` modulo an odd prime `t` has odd order `d ≠ 1`, then `t ∤ q - 1` and
`t ∤ q + 1`. -/
private lemma ovc_not_dvd_sub_add {t q d : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hq : 1 ≤ q)
    (hd : Odd d) (hd1 : d ≠ 1) (y : ZMod t) (hy : y = q ∨ y = -q) (hord : orderOf y = d) :
    ¬ t ∣ q - 1 ∧ ¬ t ∣ q + 1 := by
  have := Fact.mk ht
  have : Fact (2 < t) := ⟨by have := ht.two_le; omega⟩
  have key : ∀ z : ZMod t, (z = 1 ∨ z = -1) → orderOf z ≠ d := by
    rintro z (rfl | rfl) h
    · rw [orderOf_one] at h
      exact hd1 h.symm
    · have h1 := pow_orderOf_eq_one (-1 : ZMod t)
      rw [h, Odd.neg_one_pow hd] at h1
      exact ZMod.neg_one_ne_one h1
  constructor
  · intro hdvd
    have hq1 : (q : ZMod t) = 1 := by
      have h0 := (ZMod.natCast_eq_zero_iff (q - 1) t).mpr hdvd
      rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h0
      exact h0
    apply key y _ hord
    rcases hy with rfl | rfl
    · left; exact hq1
    · right; rw [hq1]
  · intro hdvd
    have hq1 : (q : ZMod t) = -1 := by
      have h0 := (ZMod.natCast_eq_zero_iff (q + 1) t).mpr hdvd
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    apply key y _ hord
    rcases hy with rfl | rfl
    · right; exact hq1
    · left; rw [hq1, neg_neg]

/-- Modulo an odd prime, `q` and `-q` cannot both have odd order. -/
private lemma ovc_order_disjoint {t d e q : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hd : Odd d)
    (he : Odd e) (h1 : orderOf (q : ZMod t) = d) (h2 : orderOf (-(q : ZMod t)) = e) : False := by
  have := Fact.mk ht
  have : Fact (2 < t) := ⟨by have := ht.two_le; omega⟩
  have a := pow_orderOf_eq_one (q : ZMod t)
  rw [h1] at a
  have b := pow_orderOf_eq_one (-(q : ZMod t))
  rw [h2] at b
  have c : (-(q : ZMod t)) ^ (d * e) = 1 := by rw [mul_comm, pow_mul, b, one_pow]
  rw [Odd.neg_pow (hd.mul he), pow_mul, a, one_pow] at c
  exact ZMod.neg_one_ne_one c

/-! ## One level -/

/-- A positive witness at the level `p ^ (k + 1)`: if `p ∤ q - 1`, a prime `t ≠ 2, p` with `q` of
order `p ^ (k + 1)` modulo `t` and `v_t(q ^ (p ^ (k + 1)) - 1)` odd. -/
private lemma ovc_plus_witness {q p : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hp : p.Prime)
    (hp2 : p ≠ 2) (k : ℕ) (hpq : ¬ p ∣ q - 1)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2) :
    ∃ t, t.Prime ∧ t ≠ 2 ∧ t ≠ p ∧ orderOf (q : ZMod t) = p ^ (k + 1) ∧
      t ∣ q ^ p ^ (k + 1) - 1 ∧ Odd (padicValNat t (q ^ p ^ (k + 1) - 1)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hu1 : 1 < q ^ p ^ k := Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hq.one_lt
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ i ∈ Finset.range p, (q ^ p ^ k) ^ i := ⟨_, rfl⟩
  have hBu : B * (q ^ p ^ k - 1) = q ^ p ^ (k + 1) - 1 := by
    rw [hB, ovc_geom_nat _ _ hu1.le, ← pow_mul, ← pow_succ]
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hBu
    have : 1 < q ^ p ^ (k + 1) := Nat.one_lt_pow (pow_ne_zero _ hp.ne_zero) hq.one_lt
    omega
  have hpB : ¬ p ∣ B := by
    have := Fact.mk hp
    intro hdvd
    have h0 : (B : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff B p).mpr hdvd
    have hq1 : (q : ZMod p) ≠ 1 := by
      intro h1
      apply hpq
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq.one_le, h1, Nat.cast_one, sub_self]
    have hS := ovc_geom_eq_one hq1 (ZMod.pow_card (q : ZMod p))
    rw [hB] at h0
    push_cast at h0
    simp only [ZMod.pow_card_pow] at h0
    rw [hS] at h0
    exact one_ne_zero h0
  have hns : ∀ y : ℕ, B ≠ y ^ 2 := by
    intro y
    rw [hB]
    exact hpos _ _ y hpo.pow hpo hp3
  obtain ⟨t, ht, htB, hodd⟩ := ovc_exists_odd_val hB0 hns
  have htp : t ≠ p := by rintro rfl; exact hpB htB
  have := Fact.mk ht
  have hS : ∑ i ∈ Finset.range p, ((q : ZMod t) ^ p ^ k) ^ i = 0 := by
    have h0 : (B : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff B t).mpr htB
    rw [hB] at h0
    push_cast at h0
    exact h0
  obtain ⟨hx1, hord⟩ := ovc_order ht hp htp (q : ZMod t) hS
  have ht2 : t ≠ 2 := by
    rintro rfl
    apply hx1
    rw [(ZMod.natCast_eq_one_iff_odd).mpr hqo, one_pow]
  have htu : ¬ t ∣ q ^ p ^ k - 1 := by
    intro hdvd
    apply hx1
    have h0 := (ZMod.natCast_eq_zero_iff _ t).mpr hdvd
    rw [Nat.cast_sub hu1.le, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
    exact h0
  refine ⟨t, ht, ht2, htp, hord, ?_, ?_⟩
  · rw [← hBu]; exact dvd_mul_of_dvd_left htB _
  · rw [← hBu, Nat.padicValNat_def, Nat.multiplicity_mul hB0 (by omega),
      multiplicity_eq_zero_of_not_dvd htu, add_zero, ← Nat.padicValNat_def]
    exact hodd

/-- A negative witness at the level `p ^ (k + 1)`: if `p ∤ q + 1`, a prime `t ≠ 2, p` with `-q`
of order `p ^ (k + 1)` modulo `t` and `v_t(q ^ (p ^ (k + 1)) + 1)` odd. -/
private lemma ovc_minus_witness {q p : ℕ} (hq4 : q % 4 = 1) (hp : p.Prime)
    (hp2 : p ≠ 2) (k : ℕ) (hpq : ¬ p ∣ q + 1)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ∃ t, t.Prime ∧ t ≠ 2 ∧ t ≠ p ∧ orderOf (-(q : ZMod t)) = p ^ (k + 1) ∧
      t ∣ q ^ p ^ (k + 1) + 1 ∧ Odd (padicValNat t (q ^ p ^ (k + 1) + 1)) := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hpko : Odd (p ^ k) := hpo.pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hu4 : q ^ p ^ k % 4 = 1 := by simp [Nat.pow_mod, hq4]
  have hdvd : q ^ p ^ k + 1 ∣ (q ^ p ^ k) ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (q ^ p ^ k) 1 hpo
  obtain ⟨B, hB⟩ : ∃ B, B = ((q ^ p ^ k) ^ p + 1) / (q ^ p ^ k + 1) := ⟨_, rfl⟩
  have hmul : B * (q ^ p ^ k + 1) = (q ^ p ^ k) ^ p + 1 := by
    rw [hB]; exact Nat.div_mul_cancel hdvd
  have hBu : B * (q ^ p ^ k + 1) = q ^ p ^ (k + 1) + 1 := by
    rw [hmul, ← pow_mul, ← pow_succ]
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hBu
    omega
  have hZ := ovc_neg_sum hpo hmul
  have hpB : ¬ p ∣ B := by
    have := Fact.mk hp
    intro hdvd
    have h0 : (B : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff B p).mpr hdvd
    have hq1 : -(q : ZMod p) ≠ 1 := by
      intro h1
      apply hpq
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      linear_combination -h1
    have hS := ovc_geom_eq_one hq1 (ZMod.pow_card (-(q : ZMod p)))
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hZ
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg, Nat.cast_pow,
      ZMod.pow_card_pow] at hc
    rw [hc, hS] at h0
    exact one_ne_zero h0
  have hns : ∀ y : ℕ, B ≠ y ^ 2 := by
    intro y hy
    apply hneg _ _ y (pow_ne_zero _ hp.ne_zero) hu4 hpo hp3
    rw [← hmul, hy, mul_comm]
  obtain ⟨t, ht, htB, hodd⟩ := ovc_exists_odd_val hB0 hns
  have htp : t ≠ p := by rintro rfl; exact hpB htB
  have := Fact.mk ht
  have hS : ∑ i ∈ Finset.range p, ((-(q : ZMod t)) ^ p ^ k) ^ i = 0 := by
    have h0 : (B : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff B t).mpr htB
    have hc := congrArg (fun z : ℤ => (z : ZMod t)) hZ
    simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg, Nat.cast_pow] at hc
    rw [Odd.neg_pow hpko, ← hc]
    exact h0
  obtain ⟨hx1, hord⟩ := ovc_order ht hp htp (-(q : ZMod t)) hS
  have ht2 : t ≠ 2 := by
    rintro rfl
    apply hx1
    rw [(ZMod.natCast_eq_one_iff_odd).mpr hqo, ZMod.neg_eq_self_mod_two, one_pow]
  have htu : ¬ t ∣ q ^ p ^ k + 1 := by
    intro hdvd
    apply hx1
    have h0 := (ZMod.natCast_eq_zero_iff _ t).mpr hdvd
    push_cast at h0
    rw [Odd.neg_pow hpko]
    linear_combination -h0
  refine ⟨t, ht, ht2, htp, hord, ?_, ?_⟩
  · rw [← hBu]; exact dvd_mul_of_dvd_left htB _
  · rw [← hBu, Nat.padicValNat_def, Nat.multiplicity_mul hB0 (by omega),
      multiplicity_eq_zero_of_not_dvd htu, add_zero, ← Nat.padicValNat_def]
    exact hodd

/-! ## Valuations in `H` -/

/-- `(q - 1) (2 H) = (q ^ L - 1) (q ^ L + 1)` for `H = σ(q ^ (2 L - 1)) / 2`. -/
private lemma ovc_sigma_two_mul {q L : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) :
    (q - 1) * (2 * (σ 1 (q ^ (2 * L - 1)) / 2)) = (q ^ L - 1) * (q ^ L + 1) := by
  rw [sigma_one_apply_prime_pow hq, show 2 * L - 1 + 1 = 2 * L by omega]
  have h2 : 2 ∣ ∑ i ∈ Finset.range (2 * L), q ^ i := by
    rw [Nat.dvd_iff_mod_eq_zero, Finset.sum_nat_mod]
    have : ∀ i ∈ Finset.range (2 * L), q ^ i % 2 = 1 := fun i _ => by
      simp [Nat.pow_mod, Nat.odd_iff.mp hqo]
    rw [Finset.sum_congr rfl this]
    simp
  rw [Nat.mul_div_cancel' h2, mul_comm, ovc_geom_nat q _ hq.one_le]
  have hA : 1 ≤ q ^ L := Nat.one_le_pow _ _ hq.pos
  rw [two_mul, pow_add]
  generalize q ^ L = A at hA ⊢
  have hAA : 1 ≤ A * A := by nlinarith
  zify [hA, hAA]
  ring

/-- For an odd prime `t ∤ q - 1`, `v_t(H) = v_t(q ^ L - 1) + v_t(q ^ L + 1)`. -/
private lemma ovc_val_H {q L t : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : 1 ≤ L) (ht : t.Prime)
    (ht2 : t ≠ 2) (htq : ¬ t ∣ q - 1) :
    padicValNat t (σ 1 (q ^ (2 * L - 1)) / 2) =
      padicValNat t (q ^ L - 1) + padicValNat t (q ^ L + 1) := by
  have := Fact.mk ht
  have e := ovc_sigma_two_mul hq hqo hL
  have hA : 1 < q ^ L := Nat.one_lt_pow (by omega) hq.one_lt
  have hne1 : q ^ L - 1 ≠ 0 := by omega
  have hne2 : q ^ L + 1 ≠ 0 := by omega
  have hq1 : q - 1 ≠ 0 := by have := hq.two_le; omega
  have hprod : (q - 1) * (2 * (σ 1 (q ^ (2 * L - 1)) / 2)) ≠ 0 := by
    rw [e]; exact mul_ne_zero hne1 hne2
  have hH : σ 1 (q ^ (2 * L - 1)) / 2 ≠ 0 := fun h0 => hprod (by rw [h0]; simp)
  have ht2' : ¬ t ∣ 2 := fun h => ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h)
  have h := congrArg (padicValNat t) e
  simp only [Nat.padicValNat_def] at h ⊢
  rw [Nat.multiplicity_mul hq1 (mul_ne_zero two_ne_zero hH), Nat.multiplicity_mul two_ne_zero hH,
    Nat.multiplicity_mul hne1 hne2, multiplicity_eq_zero_of_not_dvd htq,
    multiplicity_eq_zero_of_not_dvd ht2'] at h
  omega

/-- Valuation of a positive witness in `H`. -/
private lemma ovc_val_H_plus {q L t d : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : Odd L)
    (ht : t.Prime) (ht2 : t ≠ 2) (htq : ¬ t ∣ q - 1) (hdL : d ∣ L) (htd : ¬ t ∣ d)
    (hdt : t ∣ q ^ d - 1) :
    padicValNat t (σ 1 (q ^ (2 * L - 1)) / 2) = padicValNat t (q ^ d - 1) + padicValNat t L := by
  have := Fact.mk ht
  have hL1 : 1 ≤ L := hL.pos
  rw [ovc_val_H hq hqo hL1 ht ht2 htq]
  obtain ⟨m, hm⟩ := hdL
  have hd0 : d ≠ 0 := by rintro rfl; omega
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hqd : 1 < q ^ d := Nat.one_lt_pow hd0 hq.one_lt
  have hLeq : q ^ L = (q ^ d) ^ m := by rw [hm, pow_mul]
  have htL : t ∣ q ^ L - 1 := by
    rw [hLeq]; exact hdt.trans (by simpa using Nat.sub_dvd_pow_sub_pow (q ^ d) 1 m)
  have htL' : ¬ t ∣ q ^ L + 1 := by
    intro h
    have h2 : t ∣ (q ^ L + 1) - (q ^ L - 1) := Nat.dvd_sub h htL
    rw [show (q ^ L + 1) - (q ^ L - 1) = 2 by have := Nat.one_le_pow L q hq.pos; omega] at h2
    exact ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h2)
  have htqd : ¬ t ∣ q ^ d := by
    intro h
    have h1 : t ∣ q ^ d - (q ^ d - 1) := Nat.dvd_sub h hdt
    rw [show q ^ d - (q ^ d - 1) = 1 by omega] at h1
    exact ht.one_lt.ne' (Nat.dvd_one.mp h1)
  have hlte := padicValNat.pow_sub_pow (p := t) (ht.odd_of_ne_two ht2) (x := q ^ d) (y := 1)
    hqd hdt htqd hm0
  rw [one_pow] at hlte
  simp only [Nat.padicValNat_def]
  rw [multiplicity_eq_zero_of_not_dvd htL', add_zero, hLeq, hlte, hm, Nat.multiplicity_mul hd0 hm0,
    multiplicity_eq_zero_of_not_dvd htd, zero_add]

/-- Valuation of a negative witness in `H`. -/
private lemma ovc_val_H_minus {q L t d : ℕ} (hq : q.Prime) (hqo : Odd q) (hL : Odd L)
    (ht : t.Prime) (ht2 : t ≠ 2) (htq : ¬ t ∣ q - 1) (hdL : d ∣ L) (htd : ¬ t ∣ d)
    (hdt : t ∣ q ^ d + 1) :
    padicValNat t (σ 1 (q ^ (2 * L - 1)) / 2) = padicValNat t (q ^ d + 1) + padicValNat t L := by
  have := Fact.mk ht
  have hL1 : 1 ≤ L := hL.pos
  rw [ovc_val_H hq hqo hL1 ht ht2 htq]
  obtain ⟨m, hm⟩ := hdL
  have hd0 : d ≠ 0 := by rintro rfl; omega
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hmo : Odd m := by rw [hm] at hL; exact (Nat.odd_mul.mp hL).2
  have hLeq : q ^ L = (q ^ d) ^ m := by rw [hm, pow_mul]
  have htL : t ∣ q ^ L + 1 := by
    rw [hLeq]; exact hdt.trans (by simpa using Odd.nat_add_dvd_pow_add_pow (q ^ d) 1 hmo)
  have htL' : ¬ t ∣ q ^ L - 1 := by
    intro h
    have h2 : t ∣ (q ^ L + 1) - (q ^ L - 1) := Nat.dvd_sub htL h
    rw [show (q ^ L + 1) - (q ^ L - 1) = 2 by have := Nat.one_le_pow L q hq.pos; omega] at h2
    exact ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h2)
  have htqd : ¬ t ∣ q ^ d := by
    intro h
    have h1 : t ∣ (q ^ d + 1) - q ^ d := Nat.dvd_sub hdt h
    rw [show q ^ d + 1 - q ^ d = 1 by omega] at h1
    exact ht.one_lt.ne' (Nat.dvd_one.mp h1)
  have hlte := padicValNat.pow_add_pow (p := t) (ht.odd_of_ne_two ht2) (x := q ^ d) (y := 1)
    hdt htqd hmo
  rw [one_pow] at hlte
  simp only [Nat.padicValNat_def]
  rw [multiplicity_eq_zero_of_not_dvd htL', zero_add, hLeq, hlte, hm, Nat.multiplicity_mul hd0 hm0,
    multiplicity_eq_zero_of_not_dvd htd, zero_add]

/-! ## The count -/

/-- Let `q` be a prime with `q ≡ 1 (mod 4)` and `L` odd. Under the two hypotheses `hpos` and
`hneg` (taken as explicit arguments, not proved here), at least `Ω(L)` primes (prime factors of
`L` counted with multiplicity) have odd valuation in `σ(q ^ (2 L - 1)) / 2`. Published context:
Y. Hirakawa (2024) proves two odd valuations in the Euler index for a special exponent above
one; the novelty of this count is not verified. -/
theorem cardFactors_le_card_odd_valuation_half_sigma {q L : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hL : Odd L)
    (hpos : ∀ h n y : ℕ, Odd h → Odd n → 3 ≤ n → ∑ i ∈ Finset.range n, (q ^ h) ^ i ≠ y ^ 2)
    (hneg : ∀ h n y : ℕ, h ≠ 0 → q ^ h % 4 = 1 → Odd n → 3 ≤ n →
      (q ^ h) ^ n + 1 ≠ (q ^ h + 1) * y ^ 2) :
    ArithmeticFunction.cardFactors L ≤
      ((σ 1 (q ^ (2 * L - 1)) / 2).primeFactors.filter
        fun t => Odd ((σ 1 (q ^ (2 * L - 1)) / 2).factorization t)).card := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hL0 : L ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hL
  have hval_plus := fun {t d : ℕ} => @ovc_val_H_plus q L t d hq hqo hL
  have hval_minus := fun {t d : ℕ} => @ovc_val_H_minus q L t d hq hqo hL
  generalize σ 1 (q ^ (2 * L - 1)) / 2 = H at hval_plus hval_minus ⊢
  -- the index set of levels: pairs `⟨p, k⟩` with `p ^ (k + 1) ∣ L`
  set s : Finset ((_ : ℕ) × ℕ) := L.primeFactors.sigma fun p => Finset.range (L.factorization p)
    with hs
  have hcard_s : s.card = cardFactors L := by
    rw [hs, Finset.card_sigma, cardFactors_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization]
    simp only [Finset.card_range]
  have hmem : ∀ x ∈ s, x.1.Prime ∧ x.1 ≠ 2 ∧ x.1 ^ (x.2 + 1) ∣ L := by
    intro x hx
    rw [hs, Finset.mem_sigma, Finset.mem_range] at hx
    have hp := Nat.prime_of_mem_primeFactors hx.1
    refine ⟨hp, ?_, (hp.pow_dvd_iff_le_factorization hL0).mpr (by omega)⟩
    rintro h2
    have h2L := Nat.dvd_of_mem_primeFactors hx.1
    rw [h2] at h2L
    have := Nat.odd_iff.mp hL
    omega
  set Pp := s.filter fun x => ¬ x.1 ∣ q - 1 with hPp
  set Pm := s.filter fun x => ¬ x.1 ∣ q + 1 with hPm
  set G := L.primeFactors.filter fun p => ¬ p ∣ q - 1 ∧ ¬ p ∣ q + 1 with hG
  set O := H.primeFactors.filter fun t => Odd (H.factorization t) with hO
  -- every level has an available sign
  have hcov : s.card ≤ (Pp ∪ Pm).card := by
    refine Finset.card_le_card fun x hx => ?_
    obtain ⟨hp, hp2, -⟩ := hmem x hx
    by_cases h1 : x.1 ∣ q - 1
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, fun h2 => hp2 ?_⟩)
      have h3 : x.1 ∣ (q + 1) - (q - 1) := Nat.dvd_sub h2 h1
      rw [show (q + 1) - (q - 1) = 2 by have := hq.two_le; omega] at h3
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h1⟩)
  -- every prime of `G` has both signs at its first level
  have hGle : G.card ≤ (Pp ∩ Pm).card := by
    refine Finset.card_le_card_of_injOn (fun p => (⟨p, 0⟩ : (_ : ℕ) × ℕ)) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, hG, Finset.mem_filter] at hp
      have hpos' : 0 < L.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp
        (by rw [Nat.support_factorization]; exact hp.1))
      have hx : (⟨p, 0⟩ : (_ : ℕ) × ℕ) ∈ s := by
        rw [hs, Finset.mem_sigma, Finset.mem_range]
        exact ⟨hp.1, hpos'⟩
      rw [Finset.mem_coe, Finset.mem_inter]
      exact ⟨Finset.mem_filter.mpr ⟨hx, hp.2.1⟩, Finset.mem_filter.mpr ⟨hx, hp.2.2⟩⟩
    · intro a _ b _ hab
      exact congrArg Sigma.fst hab
  -- witnesses
  have hwp : ∀ x : (_ : ℕ) × ℕ, ∃ t : ℕ, x ∈ Pp → (t.Prime ∧ t ≠ 2 ∧ t ≠ x.1 ∧
      orderOf (q : ZMod t) = x.1 ^ (x.2 + 1) ∧ t ∣ q ^ x.1 ^ (x.2 + 1) - 1 ∧
      Odd (padicValNat t (q ^ x.1 ^ (x.2 + 1) - 1))) := by
    intro x
    by_cases hx : x ∈ Pp
    · obtain ⟨hxs, hxq⟩ := Finset.mem_filter.mp hx
      obtain ⟨hp, hp2, -⟩ := hmem x hxs
      obtain ⟨t, ht⟩ := ovc_plus_witness hq hq4 hp hp2 x.2 hxq hpos
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hx⟩
  have hwm : ∀ x : (_ : ℕ) × ℕ, ∃ t : ℕ, x ∈ Pm → (t.Prime ∧ t ≠ 2 ∧ t ≠ x.1 ∧
      orderOf (-(q : ZMod t)) = x.1 ^ (x.2 + 1) ∧ t ∣ q ^ x.1 ^ (x.2 + 1) + 1 ∧
      Odd (padicValNat t (q ^ x.1 ^ (x.2 + 1) + 1))) := by
    intro x
    by_cases hx : x ∈ Pm
    · obtain ⟨hxs, hxq⟩ := Finset.mem_filter.mp hx
      obtain ⟨hp, hp2, -⟩ := hmem x hxs
      obtain ⟨t, ht⟩ := ovc_minus_witness hq4 hp hp2 x.2 hxq hneg
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using hwp
  choose g hg using hwm
  -- a witness has odd valuation in `H` or lies in `G`
  have hland : ∀ t : ℕ, t.Prime → ¬ t ∣ q - 1 → ¬ t ∣ q + 1 → ∀ a : ℕ, Odd a →
      padicValNat t H = a + padicValNat t L → t ∈ O ∪ G := by
    intro t ht h1 h2 a ha hv
    by_cases hodd : Odd (padicValNat t H)
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨?_, ?_⟩)
      · rw [← Nat.support_factorization, Finsupp.mem_support_iff, Nat.factorization_def H ht,
        ← Nat.padicValNat_def]
        intro h0
        rw [h0] at hodd
        exact Nat.not_odd_zero hodd
      · rw [Nat.factorization_def H ht, ← Nat.padicValNat_def]
        exact hodd
    · have hb : Odd (padicValNat t L) := by
        rcases Nat.even_or_odd (padicValNat t L) with he | ho
        · rw [hv] at hodd
          exact absurd (ha.add_even he) hodd
        · exact ho
      have := Fact.mk ht
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, h1, h2⟩)
      exact Nat.mem_primeFactors.mpr ⟨ht,
        dvd_of_one_le_multiplicity (by rw [← Nat.padicValNat_def]; exact hb.pos), hL0⟩
  have hinj := Finset.card_le_card_of_injOn (s := Pp.disjSum Pm) (t := O ∪ G) (Sum.elim f g)
    ?maps ?inj
  · rw [Finset.card_disjSum] at hinj
    have hui := Finset.card_union_add_card_inter Pp Pm
    have hOG := Finset.card_union_le O G
    omega
  case maps =>
    intro a ha
    rw [Finset.mem_coe] at ha ⊢
    rcases a with x | x
    · rw [Finset.inl_mem_disjSum] at ha
      obtain ⟨ht, ht2, htp, hord, hdt, hodd⟩ := hf x ha
      obtain ⟨hp, hp2, hdL⟩ := hmem x (Finset.mem_filter.mp ha).1
      have hd1 : x.1 ^ (x.2 + 1) ≠ 1 :=
        (Nat.one_lt_pow (Nat.succ_ne_zero _) hp.one_lt).ne'
      obtain ⟨h1, h2⟩ := ovc_not_dvd_sub_add ht ht2 hq.one_le
        (hp.odd_of_ne_two hp2).pow hd1 _ (Or.inl rfl) hord
      have htd : ¬ f x ∣ x.1 ^ (x.2 + 1) := fun h =>
        htp ((Nat.prime_dvd_prime_iff_eq ht hp).mp (ht.dvd_of_dvd_pow h))
      exact hland _ ht h1 h2 _ hodd (hval_plus ht ht2 h1 hdL htd hdt)
    · rw [Finset.inr_mem_disjSum] at ha
      obtain ⟨ht, ht2, htp, hord, hdt, hodd⟩ := hg x ha
      obtain ⟨hp, hp2, hdL⟩ := hmem x (Finset.mem_filter.mp ha).1
      have hd1 : x.1 ^ (x.2 + 1) ≠ 1 :=
        (Nat.one_lt_pow (Nat.succ_ne_zero _) hp.one_lt).ne'
      obtain ⟨h1, h2⟩ := ovc_not_dvd_sub_add ht ht2 hq.one_le
        (hp.odd_of_ne_two hp2).pow hd1 _ (Or.inr rfl) hord
      have htd : ¬ g x ∣ x.1 ^ (x.2 + 1) := fun h =>
        htp ((Nat.prime_dvd_prime_iff_eq ht hp).mp (ht.dvd_of_dvd_pow h))
      exact hland _ ht h1 h2 _ hodd (hval_minus ht ht2 h1 hdL htd hdt)
  case inj =>
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    rcases a with ⟨p, k⟩ | ⟨p, k⟩ <;> rcases b with ⟨p', k'⟩ | ⟨p', k'⟩
    · rw [Finset.inl_mem_disjSum] at ha hb
      simp only [Sum.elim_inl] at hab
      have h1 := (hf _ ha).2.2.2.1
      have h2 := (hf _ hb).2.2.2.1
      rw [hab] at h1
      have hp := (hmem _ (Finset.mem_filter.mp ha).1).1
      have hp' := (hmem _ (Finset.mem_filter.mp hb).1).1
      obtain ⟨e1, e2⟩ := Nat.Prime.pow_inj hp hp' (h1.symm.trans h2)
      dsimp only at e1 e2
      subst e1 e2
      rfl
    · rw [Finset.inl_mem_disjSum] at ha
      rw [Finset.inr_mem_disjSum] at hb
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
      have h1 := (hf _ ha).2.2.2.1
      obtain ⟨ht, ht2, -, h2, -⟩ := hg _ hb
      rw [hab] at h1
      have hp := (hmem _ (Finset.mem_filter.mp ha).1)
      have hp' := (hmem _ (Finset.mem_filter.mp hb).1)
      exact (ovc_order_disjoint ht ht2 (hp.1.odd_of_ne_two hp.2.1).pow
        (hp'.1.odd_of_ne_two hp'.2.1).pow h1 h2).elim
    · rw [Finset.inr_mem_disjSum] at ha
      rw [Finset.inl_mem_disjSum] at hb
      simp only [Sum.elim_inl, Sum.elim_inr] at hab
      have h1 := (hg _ ha).2.2.2.1
      obtain ⟨ht, ht2, -, h2, -⟩ := hf _ hb
      rw [hab] at h1
      have hp := (hmem _ (Finset.mem_filter.mp ha).1)
      have hp' := (hmem _ (Finset.mem_filter.mp hb).1)
      exact (ovc_order_disjoint ht ht2 (hp'.1.odd_of_ne_two hp'.2.1).pow
        (hp.1.odd_of_ne_two hp.2.1).pow h2 h1).elim
    · rw [Finset.inr_mem_disjSum] at ha hb
      simp only [Sum.elim_inr] at hab
      have h1 := (hg _ ha).2.2.2.1
      have h2 := (hg _ hb).2.2.2.1
      rw [hab] at h1
      have hp := (hmem _ (Finset.mem_filter.mp ha).1).1
      have hp' := (hmem _ (Finset.mem_filter.mp hb).1).1
      obtain ⟨e1, e2⟩ := Nat.Prime.pow_inj hp hp' (h1.symm.trans h2)
      dsimp only at e1 e2
      subst e1 e2
      rfl

end OddPerfect

#print axioms OddPerfect.cardFactors_le_card_odd_valuation_half_sigma
