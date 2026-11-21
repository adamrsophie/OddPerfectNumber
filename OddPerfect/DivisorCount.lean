import OddPerfect.ExponentCap
import OddPerfect.ThreeFreeCert
import OddPerfect.RadicalBound

/-!
# Divisor counts, three free seeds without the three free hypothesis, radical defect

* `card_divisors_succ_factorization_le`: for every prime factor `p` of an odd perfect number,
  `τ(e_p + 1) ≤ ω(N)` (Nielsen, Lemma 2.1), including the special prime.
* `three_not_dvd_of_eleven`: if `5 ∣ N` and `v_11(N) ≡ 2 (mod 3)` then `3 ∤ N`; this removes
  the hypothesis `¬ 3 ∣ N` from the seed exclusions for 41 and 53.
* Radical defect: with `R = ∏ p`, `F = ∏ (p - 1)`, `Δ = R - 2 F` and `X` the least
  `p ^ (e_p + 1)`, a perfect number satisfies `R ≤ Δ X` and `Δ X ≤ ω(N) R`, and
  `R ∏ (p ^ (e_p + 1) - 1) = 2 F ∏ p ^ (e_p + 1)`.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

variable {N : ℕ}

/-! ## Divisor count for every prime factor -/

/-- Nielsen's Lemma 2.1: for every prime factor `p` of an odd perfect number, the number of
divisors of `e_p + 1` is at most `ω(N)`. For the special prime, the divisors `d ≥ 3` of `e + 1`
get primitive witnesses of order `d`, the divisor `2` gets an odd prime `r ∣ (p + 1)/2` (in which
`p` has order dividing two), and the divisor `1` is matched with `p` itself. -/
theorem card_divisors_succ_factorization_le (h : OddPerfect N) {p : ℕ}
    (hp : p ∈ N.primeFactors) :
    (N.factorization p + 1).divisors.card ≤ N.primeFactors.card := by
  rcases Nat.even_or_odd (N.factorization p) with hev | hodd
  · exact card_divisors_le_of_even h hp hev
  have hpp := Nat.prime_of_mem_primeFactors hp
  have h4 := (special_mod_four h hpp hodd).1
  have hp2 := hpp.two_le
  set r := ((p + 1) / 2).minFac with hrdef
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrdvd : r ∣ (p + 1) / 2 := Nat.minFac_dvd _
  have hr2 : r ≠ 2 := by
    intro h2
    rw [h2] at hrdvd
    omega
  have hrp1 : r ∣ p + 1 := hrdvd.trans (Nat.div_dvd_of_dvd (by omega : 2 ∣ p + 1))
  obtain ⟨hrN, hrp⟩ := prime_dvd_of_dvd_succ_special h hpp hodd hr hr2 hrp1
  have hrmem : r ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrN, h.ne_zero⟩
  have hord : orderOf (p : ZMod r) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    have h0 : ((p + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrp1
    push_cast at h0
    rw [eq_neg_of_add_eq_zero_left h0]
    norm_num
  set S := (N.factorization p + 1).divisors
  have hbig : (S.filter (3 ≤ ·)).card ≤ ((N.primeFactors.erase p).erase r).card := by
    calc _ ≤ (((N.primeFactors.erase p).erase r).image fun q => orderOf (p : ZMod q)).card := by
          apply Finset.card_le_card
          intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          obtain ⟨q, hq, ho, -⟩ := exists_primeFactor_modEq_one h hp hd.2 hd.1.1
          refine Finset.mem_image.mpr ⟨q, Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hq⟩⟩, ho⟩
          · rintro rfl
            have := Nat.le_of_dvd two_pos (ho ▸ hord)
            omega
          · rintro rfl
            have : Fact q.Prime := ⟨hpp⟩
            rw [ZMod.natCast_self, orderOf_zero] at ho
            omega
      _ ≤ _ := Finset.card_image_le
  have hsmall : (S.filter fun d => ¬ 3 ≤ d).card ≤ 2 := by
    calc _ ≤ ({1, 2} : Finset ℕ).card := Finset.card_le_card (by
          intro d hd
          rw [Finset.mem_filter, Nat.mem_divisors] at hd
          have : d ≠ 0 := by
            rintro rfl
            rw [zero_dvd_iff] at hd
            omega
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega)
      _ = 2 := rfl
  have h2 := Finset.card_filter_add_card_filter_not (s := S) (3 ≤ ·)
  have hc1 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hrp, hrmem⟩)
  have hc2 := Finset.card_erase_of_mem hp
  have hpos := Finset.card_pos.mpr ⟨r, Finset.mem_erase.mpr ⟨hrp, hrmem⟩⟩
  omega

/-! ## Three freeness from 5 and 11 -/

/-- If `5 ∣ N` and `v_11(N) ≡ 2 (mod 3)` for an odd perfect number `N`, then `3 ∤ N`:
`7 ∣ σ(11^2) ∣ σ(11^e)` gives `7 ∣ N`, and `105 ∤ N`. -/
theorem three_not_dvd_of_eleven (h : OddPerfect N) (h5 : 5 ∣ N)
    (h11 : N.factorization 11 % 3 = 2) : ¬ 3 ∣ N := by
  intro h3
  have h7s : 7 ∣ σ 1 (11 ^ 2) := by
    rw [sigma_one_apply_prime_pow (by norm_num)]
    decide
  have h7 : 7 ∣ N := OPNStarter.force_prime h.perfect (by norm_num) rfl (by norm_num) (by norm_num)
    (h7s.trans (OPNExample.sigma_prime_pow_dvd (by norm_num)
      (Nat.dvd_of_mod_eq_zero (by omega))))
  exact not_105_dvd h (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 15 7)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5) h7)

private lemma five_dvd (h : OddPerfect N) (h5 : N.factorization 5 = 2) : 5 ∣ N :=
  (Nat.prime_five.dvd_iff_one_le_factorization h.ne_zero).mpr (by omega)

/-- No odd perfect number has exponent exactly 2 at each of 5, 11, 41, 29. -/
theorem exclude_exact_squares_5_11_41_29 (h : OddPerfect N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h41 : N.factorization 41 = 2) (h29 : N.factorization 29 = 2) : False :=
  Cert.exclude_three_free_5_11_41_29 h (three_not_dvd_of_eleven h (five_dvd h h5) (by omega))
    h5 h11 h41 h29

/-- No odd perfect number has exponent exactly 2 at each of 5, 11, 53, 29. -/
theorem exclude_exact_squares_5_11_53_29 (h : OddPerfect N)
    (h5 : N.factorization 5 = 2) (h11 : N.factorization 11 = 2)
    (h53 : N.factorization 53 = 2) (h29 : N.factorization 29 = 2) : False :=
  Cert.exclude_three_free_5_11_53_29 h (three_not_dvd_of_eleven h (five_dvd h h5) (by omega))
    h5 h11 h53 h29

/-! ## Radical defect -/

private lemma one_lt_of_perfect (hN : N.Perfect) : 1 < N := by
  rcases Nat.lt_or_ge 1 N with h | h
  · exact h
  · obtain rfl : N = 1 := by have := hN.2; omega
    simp [Nat.Perfect] at hN

/-- For a perfect `N`: `R * ∏ (1 - 1/p^(e_p+1)) = 2 F` with `R = ∏ p`, `F = ∏ (p - 1)`. -/
theorem prod_mul_prod_one_sub_eq (hN : N.Perfect) :
    ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) *
        ∏ p ∈ N.primeFactors, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) =
      2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) := by
  have h := two_eq_prod_mul_prod hN
  rw [prod_div_sub_one_eq_div] at h
  have hF : (0 : ℚ) < ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  rw [h]
  field_simp

/-- Division free form of `∏ (1 - 1/p^(e_p+1)) = 2 F/R` for a perfect `N`:
`R * ∏ (p^(e_p+1) - 1) = 2 F * ∏ p^(e_p+1)`. -/
theorem prod_mul_prod_pow_sub_one_eq (hN : N.Perfect) :
    (∏ p ∈ N.primeFactors, p) * ∏ p ∈ N.primeFactors, (p ^ (N.factorization p + 1) - 1) =
      2 * (∏ p ∈ N.primeFactors, (p - 1)) * ∏ p ∈ N.primeFactors, p ^ (N.factorization p + 1) := by
  have h := prod_mul_prod_one_sub_eq hN
  have hq : ∀ p ∈ N.primeFactors, (((p ^ (N.factorization p + 1) - 1 : ℕ)) : ℚ) =
      (p : ℚ) ^ (N.factorization p + 1) * (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) := by
    intro p hp
    have hpos : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have h1 : 1 ≤ p ^ (N.factorization p + 1) := Nat.one_le_pow _ _ hpos
    have h0 : (p : ℚ) ^ (N.factorization p + 1) ≠ 0 := by positivity
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, mul_one_sub, mul_inv_cancel₀ h0]
  apply Nat.cast_injective (R := ℚ)
  push_cast [Finset.prod_congr rfl hq]
  rw [Finset.prod_mul_distrib]
  rw [Nat.cast_prod, Nat.cast_prod] at h
  linear_combination (∏ p ∈ N.primeFactors, (p : ℚ) ^ (N.factorization p + 1)) * h

/-- Radical defect, lower form: for a perfect `N`, with `X` the least `p^(e_p+1)` over the
prime factors, `R ≤ (R - 2 F) * X`. -/
theorem prod_le_sub_mul_inf (hN : N.Perfect) (hne : N.primeFactors.Nonempty) :
    ∏ p ∈ N.primeFactors, p ≤
      (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) *
        N.primeFactors.inf' hne (fun p => p ^ (N.factorization p + 1)) := by
  obtain ⟨q, hq, hX⟩ := Finset.exists_mem_eq_inf' hne (fun p => p ^ (N.factorization p + 1))
  rw [hX, mul_comm]
  exact prod_le_pow_succ_mul hN hq

/-- Radical defect, upper form: for a perfect `N`, with `X` the least `p^(e_p+1)` over the
prime factors, `(R - 2 F) * X ≤ ω(N) * R`. -/
theorem sub_mul_inf_le_card_mul (hN : N.Perfect) (hne : N.primeFactors.Nonempty) :
    (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) *
        N.primeFactors.inf' hne (fun p => p ^ (N.factorization p + 1)) ≤
      N.primeFactors.card * ∏ p ∈ N.primeFactors, p := by
  set R := ∏ p ∈ N.primeFactors, p
  set F := ∏ p ∈ N.primeFactors, (p - 1)
  set X := N.primeFactors.inf' hne (fun p => p ^ (N.factorization p + 1))
  set x : ℕ → ℚ := fun p => ((p : ℚ) ^ (N.factorization p + 1))⁻¹
  have hlt := two_mul_prod_sub_one_lt_prod hN
  have hX0 : 0 < X := by
    rw [Finset.lt_inf'_iff]
    intro p hp
    exact pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have hXq : (0 : ℚ) < X := by exact_mod_cast hX0
  have hR : (0 : ℚ) < R := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hbd : ∀ p ∈ N.primeFactors, 0 ≤ x p ∧ x p ≤ 1 := fun p hp => by
    have : (1 : ℚ) ≤ (p : ℚ) ^ (N.factorization p + 1) :=
      one_le_pow₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
    exact ⟨by positivity, inv_le_one_of_one_le₀ this⟩
  have hW := one_sub_sum_le_prod_one_sub N.primeFactors x (fun p hp => (hbd p hp).1)
    (fun p hp => (hbd p hp).2)
  have hid := prod_mul_prod_one_sub_eq hN
  have hsum : ∑ p ∈ N.primeFactors, x p ≤ N.primeFactors.card * (X : ℚ)⁻¹ := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    have hle : X ≤ p ^ (N.factorization p + 1) := Finset.inf'_le _ hp
    have : (X : ℚ) ≤ (p : ℚ) ^ (N.factorization p + 1) := by exact_mod_cast hle
    exact inv_anti₀ hXq this
  -- `R - 2 F ≤ R * ∑ x ≤ R ω / X`
  have h1 : (R : ℚ) - 2 * F ≤ R * (N.primeFactors.card * (X : ℚ)⁻¹) := by
    nlinarith
  have h2 : ((R : ℚ) - 2 * F) * X ≤ N.primeFactors.card * R := by
    have := mul_le_mul_of_nonneg_right h1 hXq.le
    rwa [mul_assoc, mul_assoc, inv_mul_cancel₀ hXq.ne', mul_one, mul_comm (R : ℚ)] at this
  have hcast : ((R - 2 * F : ℕ) : ℚ) = R - 2 * F := by
    rw [Nat.cast_sub hlt.le, Nat.cast_mul, Nat.cast_two]
  rw [← hcast] at h2
  exact_mod_cast h2

end OddPerfect

#print axioms OddPerfect.card_divisors_succ_factorization_le
#print axioms OddPerfect.three_not_dvd_of_eleven
#print axioms OddPerfect.exclude_exact_squares_5_11_41_29
#print axioms OddPerfect.exclude_exact_squares_5_11_53_29
#print axioms OddPerfect.prod_mul_prod_one_sub_eq
#print axioms OddPerfect.prod_mul_prod_pow_sub_one_eq
#print axioms OddPerfect.prod_le_sub_mul_inf
#print axioms OddPerfect.sub_mul_inf_le_card_mul
