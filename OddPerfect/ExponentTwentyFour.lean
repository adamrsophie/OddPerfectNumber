import OddPerfect.KanoldFive

/-!
# Ordinary exponents all equal to `24`

Let `N` be an odd perfect number with special prime `q`. This file shows that the ordinary
exponents cannot all equal `24`. This is a known result from the literature on odd perfect
numbers with equal ordinary exponents; the proof here follows the standard pattern.

* If `5` is ordinary, then `v_5(N) = 24`, and each ordinary prime `p ≡ 1 (mod 5)` supplies
  `v_5(25) = 2` to `v_5(N)`. The primes `11, 71, 101, 251, 401, 9384251` divide `σ(5 ^ 24)`, and
  `3221`, `211, 2221`, `6586781`, `181, 191`, `1361, 292661` divide `Φ_5(p)` for the sources
  `p = 11, 71, 251, 9384251, 211`, all `≡ 3 (mod 4)` and hence ordinary. These fourteen primes
  are `≡ 1 (mod 5)`, so at least thirteen are ordinary and supply `26 > 24`.
* If `5` is special, then `13 ≤ v_5(N)`, `3 ∣ 5 + 1` divides `N`, `11 ∣ σ(3 ^ 24)` divides `N`,
  and `3 ^ 4 · 5 ^ 5 · 11 ^ 2` is a divisor of abundancy `57722 / 28125 > 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ExpTwentyFour

/-- `σ(p ^ 4)` for a prime `p`. -/
private theorem sigma_four {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 4) = 1 + p + p ^ 2 + p ^ 3 + p ^ 4 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]

private theorem p3 : Nat.Prime 3 := by norm_num
private theorem p5 : Nat.Prime 5 := by norm_num
private theorem p11 : Nat.Prime 11 := by norm_num
private theorem p71 : Nat.Prime 71 := by norm_num
private theorem p101 : Nat.Prime 101 := by norm_num
private theorem p181 : Nat.Prime 181 := by norm_num
private theorem p191 : Nat.Prime 191 := by norm_num
private theorem p211 : Nat.Prime 211 := by norm_num
private theorem p251 : Nat.Prime 251 := by norm_num
private theorem p401 : Nat.Prime 401 := by norm_num
private theorem p1361 : Nat.Prime 1361 := by norm_num
private theorem p2221 : Nat.Prime 2221 := by norm_num
private theorem p3221 : Nat.Prime 3221 := by norm_num
private theorem p292661 : Nat.Prime 292661 := by norm_num
private theorem p6586781 : Nat.Prime 6586781 := by norm_num
private theorem p9384251 : Nat.Prime 9384251 := by norm_num

/-- `σ(5 ^ 24) = (5 ^ 25 - 1) / 4`. -/
private theorem sigma_five_24 : σ 1 (5 ^ 24) = 74505805969238281 := by
  rw [sigma_one_apply_prime_pow p5]
  norm_num [Finset.sum_range_succ]

/-- `σ(3 ^ 24) = (3 ^ 25 - 1) / 2`. -/
private theorem sigma_three_24 : σ 1 (3 ^ 24) = 423644304721 := by
  rw [sigma_one_apply_prime_pow p3]
  norm_num [Finset.sum_range_succ]

private theorem d11_3221 : 3221 ∣ 1 + 11 + 11 ^ 2 + 11 ^ 3 + 11 ^ 4 := by norm_num
private theorem d71_211 : 211 ∣ 1 + 71 + 71 ^ 2 + 71 ^ 3 + 71 ^ 4 := by norm_num
private theorem d71_2221 : 2221 ∣ 1 + 71 + 71 ^ 2 + 71 ^ 3 + 71 ^ 4 := by norm_num
private theorem d251 : 6586781 ∣ 1 + 251 + 251 ^ 2 + 251 ^ 3 + 251 ^ 4 := by norm_num
private theorem d9384251_181 :
    181 ∣ 1 + 9384251 + 9384251 ^ 2 + 9384251 ^ 3 + 9384251 ^ 4 := by norm_num
private theorem d9384251_191 :
    191 ∣ 1 + 9384251 + 9384251 ^ 2 + 9384251 ^ 3 + 9384251 ^ 4 := by norm_num
private theorem d211_1361 : 1361 ∣ 1 + 211 + 211 ^ 2 + 211 ^ 3 + 211 ^ 4 := by norm_num
private theorem d211_292661 : 292661 ∣ 1 + 211 + 211 ^ 2 + 211 ^ 3 + 211 ^ 4 := by norm_num

/-- The abundancy of `3 ^ 4 · 5 ^ 5 · 11 ^ 2` exceeds `2`. -/
private theorem two_lt_abundancy : 2 < abundancy (3 ^ 4 * 5 ^ 5 * 11 ^ 2) := by
  rw [abundancy_mul_of_coprime (by norm_num), abundancy_mul_of_coprime (by norm_num),
    abundancy_prime_pow p3, abundancy_prime_pow p5, abundancy_prime_pow p11]
  norm_num [Finset.sum_range_succ]

end ExpTwentyFour

open ExpTwentyFour in
/-- The ordinary exponents of an odd perfect number cannot all equal `24`. Let `N` be an odd
perfect number with special prime `q`. If `v_p(N) = 24` for every prime factor `p ≠ q`, then
`False`. -/
theorem not_all_exponents_eq_twenty_four {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 24) : False := by
  have hq4 := (mod_four_special h hq hodd).1
  have hmem : ∀ {p : ℕ}, p.Prime → p ∣ N → p ∈ N.primeFactors := fun hp hpN =>
    Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have hne : ∀ {p : ℕ}, p % 4 = 3 → p ≠ q := fun h3 hpq => by subst hpq; omega
  have h25 : ∀ p ∈ N.primeFactors, p ≠ q → 5 ^ 2 ∣ N.factorization p + 1 := by
    intro p hp hpq
    rw [hexp p hp hpq]
    norm_num
  by_cases h5q : (5 : ℕ) = q
  · -- `5` is the special prime
    subst h5q
    have h13 := thirteen_le_factorization_five_of_special h hodd h25
    obtain ⟨h3N, h35⟩ := prime_dvd_of_dvd_succ_special h p5 hodd p3 (by norm_num)
      (by norm_num : 3 ∣ 5 + 1)
    have e3 := hexp 3 (hmem p3 h3N) h35
    have h11N : 11 ∣ N := OPNStarter.force_prime h.perfect p3 e3 p11 (by norm_num)
      (sigma_three_24 ▸ (by norm_num))
    have e11 := hexp 11 (hmem p11 h11N) (by norm_num)
    have d3 : 3 ^ 4 ∣ N := (p3.pow_dvd_iff_le_factorization h.ne_zero).mpr (by rw [e3]; norm_num)
    have d5 : 5 ^ 5 ∣ N := (p5.pow_dvd_iff_le_factorization h.ne_zero).mpr (le_trans (by norm_num) h13)
    have d11 : 11 ^ 2 ∣ N := (p11.pow_dvd_iff_le_factorization h.ne_zero).mpr (by rw [e11]; norm_num)
    have hd : 3 ^ 4 * 5 ^ 5 * 11 ^ 2 ∣ N :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 d5) d11
    exact not_perfect_of_dvd_of_two_lt_abundancy hd two_lt_abundancy h.perfect
  -- `5` is ordinary
  have h5N : 5 ∣ N := dvd_of_dvd_succ h hq hodd p5 (by norm_num) fun p hp hpq =>
    (dvd_pow_self 5 two_ne_zero).trans (h25 p hp hpq)
  have e5 := hexp 5 (hmem p5 h5N) h5q
  have force : ∀ {p r : ℕ}, p.Prime → p ∣ N → p ≠ q → r.Prime → r ≠ 2 →
      r ∣ 1 + p + p ^ 2 + p ^ 3 + p ^ 4 → r ∣ N := by
    intro p r hp hpN hpq hr hr2 hd
    refine OPNStarter.force_prime h.perfect hp rfl hr hr2 ((sigma_four hp ▸ hd).trans ?_)
    exact OPNExample.sigma_prime_pow_dvd hp (by rw [hexp p (hmem hp hpN) hpq]; norm_num)
  have fσ : ∀ {r : ℕ}, r.Prime → r ∣ 74505805969238281 → r ∣ N := fun hr hd =>
    OPNStarter.force_prime h.perfect p5 e5 hr (by rintro rfl; norm_num at hd)
      (sigma_five_24 ▸ hd)
  have h11 : 11 ∣ N := fσ p11 (by norm_num)
  have h71 : 71 ∣ N := fσ p71 (by norm_num)
  have h101 : 101 ∣ N := fσ p101 (by norm_num)
  have h251 : 251 ∣ N := fσ p251 (by norm_num)
  have h401 : 401 ∣ N := fσ p401 (by norm_num)
  have h9384251 : 9384251 ∣ N := fσ p9384251 (by norm_num)
  have h3221 : 3221 ∣ N := force p11 h11 (hne (by norm_num)) p3221 (by norm_num) d11_3221
  have h211 : 211 ∣ N := force p71 h71 (hne (by norm_num)) p211 (by norm_num) d71_211
  have h2221 : 2221 ∣ N := force p71 h71 (hne (by norm_num)) p2221 (by norm_num) d71_2221
  have h6586781 : 6586781 ∣ N := force p251 h251 (hne (by norm_num)) p6586781 (by norm_num) d251
  have h181 : 181 ∣ N := force p9384251 h9384251 (hne (by norm_num)) p181 (by norm_num) d9384251_181
  have h191 : 191 ∣ N := force p9384251 h9384251 (hne (by norm_num)) p191 (by norm_num) d9384251_191
  have h1361 : 1361 ∣ N := force p211 h211 (hne (by norm_num)) p1361 (by norm_num) d211_1361
  have h292661 : 292661 ∣ N := force p211 h211 (hne (by norm_num)) p292661 (by norm_num) d211_292661
  set U : Finset ℕ := {11, 71, 101, 251, 401, 9384251, 3221, 211, 2221, 6586781, 181, 191,
    1361, 292661} with hU
  set T := U.erase q with hT
  have hTsub : T ⊆ N.primeFactors.filter (fun p => p % 5 = 1) := by
    intro p hp
    have hpU := Finset.mem_of_mem_erase hp
    simp only [hU, Finset.mem_insert, Finset.mem_singleton] at hpU
    rcases hpU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hmem p11 h11, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p71 h71, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p101 h101, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p251 h251, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p401 h401, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p9384251 h9384251, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p3221 h3221, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p211 h211, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p2221 h2221, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p6586781 h6586781, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p181 h181, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p191 h191, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p1361 h1361, by norm_num⟩
    · exact Finset.mem_filter.mpr ⟨hmem p292661 h292661, by norm_num⟩
  clear force fσ h11 h71 h101 h251 h401 h9384251 h3221 h211 h2221 h6586781 h181 h191 h1361
    h292661
  have hTcard : 13 ≤ T.card := by
    have := Finset.pred_card_le_card_erase (s := U) (a := q)
    have hc : U.card = 14 := by rw [hU]; decide
    rw [← hT, hc] at this
    exact this
  have hlo : ∀ p ∈ T, 2 ≤ padicValNat 5 (N.factorization p + 1) := by
    intro p hp
    have : Fact (Nat.Prime 5) := ⟨p5⟩
    rw [Nat.padicValNat_def]
    exact (padicValNat_dvd_iff_le (by omega)).mp
      (h25 p (Finset.mem_filter.mp (hTsub hp)).1 (Finset.ne_of_mem_erase hp))
  have hsum := Finset.card_nsmul_le_sum T _ 2 hlo
  have hsub := Finset.sum_le_sum_of_subset (f := fun p => padicValNat 5 (N.factorization p + 1))
    hTsub
  have hled := sum_padicValNat_succ_le h.perfect (l := 5) p5 (by norm_num)
  rw [smul_eq_mul] at hsum
  omega

end OddPerfect

#print axioms OddPerfect.not_all_exponents_eq_twenty_four
