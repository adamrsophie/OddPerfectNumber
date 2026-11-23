import OddPerfect.SmallestPrime

/-!
# A cubic bound for the least prime factor

We bound a product over integers coprime to six and use it to show that
the least prime factor of an odd perfect number satisfies `7 p₁ < 3 ω + 21`.
-/

namespace OddPerfect

/-- An integer is coprime to six exactly when neither two nor three divides it. -/
private theorem six_coprime_iff_not_dvd {x : ℕ} :
    Nat.Coprime 6 x ↔ ¬ 2 ∣ x ∧ ¬ 3 ∣ x := by
  rw [show (6 : ℕ) = 2 * 3 by decide, Nat.coprime_mul_iff_left,
    Nat.prime_two.coprime_iff_not_dvd, Nat.prime_three.coprime_iff_not_dvd]

/-- A set of integers coprime to six in `[m, M]` has size at most `(M - m + 4) / 3`
if `M` is not a multiple of three. -/
private theorem card_coprime_six_interval (S : Finset ℕ) {m M : ℕ}
    (hmM : m ≤ M) (hM : ¬ 3 ∣ M) (hS : ∀ x ∈ S, m ≤ x ∧ x ≤ M ∧ Nat.Coprime 6 x) :
    3 * S.card + m ≤ M + 4 := by
  have hcard : S.card ≤ (Finset.range (M / 3 + 1 - m / 3)).card := by
    apply Finset.card_le_card_of_injOn (fun x => x / 3 - m / 3)
    · intro x hx
      obtain ⟨hxlo, hxhi, _⟩ := hS x (Finset.mem_coe.mp hx)
      change x / 3 - m / 3 ∈ Finset.range (M / 3 + 1 - m / 3)
      apply Finset.mem_range.mpr
      omega
    · intro x hx y hy hxy
      obtain ⟨hxlo, _, hx6⟩ := hS x (Finset.mem_coe.mp hx)
      obtain ⟨hylo, _, hy6⟩ := hS y (Finset.mem_coe.mp hy)
      obtain ⟨hx2, hx3⟩ := six_coprime_iff_not_dvd.mp hx6
      obtain ⟨hy2, hy3⟩ := six_coprime_iff_not_dvd.mp hy6
      rw [Nat.dvd_iff_mod_eq_zero] at hx2 hx3 hy2 hy3
      change x / 3 - m / 3 = y / 3 - m / 3 at hxy
      have hdiv : x / 3 = y / 3 := by omega
      have hxrem : x % 3 = 1 ∨ x % 3 = 2 := by omega
      have hyrem : y % 3 = 1 ∨ y % 3 = 2 := by omega
      rcases hxrem with hxrem | hxrem <;> rcases hyrem with hyrem | hyrem <;> omega
  rw [Finset.card_range] at hcard
  rw [Nat.dvd_iff_mod_eq_zero] at hM
  omega

/-- For `x ≥ u ≥ 3`, the cube of `x / (x - 1)` is below `(u + 1) / (u - 2)`. -/
private theorem cube_ratio_lt {u x : ℚ} (hu : 3 ≤ u) (hux : u ≤ x) :
    (x / (x - 1)) ^ 3 < (u + 1) / (u - 2) := by
  have hu1 : 0 < u - 1 := by linarith
  have hu2 : 0 < u - 2 := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hratio : x / (x - 1) ≤ u / (u - 1) := by
    rw [div_le_div_iff₀ hx1 hu1]
    nlinarith only [hux]
  calc
    (x / (x - 1)) ^ 3 ≤ (u / (u - 1)) ^ 3 :=
      pow_le_pow_left₀ (div_nonneg hx0 hx1.le) hratio 3
    _ < (u + 1) / (u - 2) := by
      rw [div_pow, div_lt_div_iff₀ (pow_pos hu1 3) hu2]
      nlinarith only [hu]

/-- For a finite set of integers coprime to six and at least `m ≥ 5`, the product
of the cubed ratios `x / (x - 1)` is at most `(m + 3 |S| - 3) / (m - 3)`. -/
private theorem cube_prod_div_sub_one_le (S : Finset ℕ) {m : ℕ} (hm : 5 ≤ m)
    (hS : ∀ x ∈ S, m ≤ x ∧ Nat.Coprime 6 x) :
    ∏ x ∈ S, ((x : ℚ) / (x - 1)) ^ 3 ≤ ((m : ℚ) + 3 * S.card - 3) / (m - 3) := by
  have hm' : (5 : ℚ) ≤ m := by exact_mod_cast hm
  induction S using Finset.induction_on_max with
  | empty =>
    have hden : (m : ℚ) - 3 ≠ 0 := by linarith
    simp [hden]
  | insert a S ha ih =>
    have haS : a ∉ S := fun h => lt_irrefl a (ha a h)
    obtain ⟨hma, hac⟩ := hS a (Finset.mem_insert_self a S)
    have hcount := card_coprime_six_interval (insert a S) hma
      (six_coprime_iff_not_dvd.mp hac).2 (fun x hx => by
        obtain ⟨hlo, hc⟩ := hS x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨hlo, le_rfl, hc⟩
        · exact ⟨hlo, (ha x hx).le, hc⟩)
    rw [Finset.card_insert_of_notMem haS] at hcount
    have huNat : m + 3 * S.card ≤ a + 1 := by omega
    have huRat : (m : ℚ) + 3 * (S.card : ℚ) ≤ (a : ℚ) + 1 := by exact_mod_cast huNat
    have hcard : (0 : ℚ) ≤ S.card := by positivity
    let b : ℚ := (m : ℚ) + 3 * S.card - 3
    have hb : 0 < b := by dsimp [b]; linarith
    have hcube := cube_ratio_lt (u := b + 2) (x := (a : ℚ))
      (by dsimp [b]; linarith) (by dsimp [b]; linarith)
    rw [show b + 2 + 1 = b + 3 by ring, show b + 2 - 2 = b by ring] at hcube
    have hrest : (∏ x ∈ S, ((x : ℚ) / (x - 1)) ^ 3) ≤ b / (m - 3) :=
      ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hden : (0 : ℚ) < (m : ℚ) - 3 := by linarith
    have ha' : (m : ℚ) ≤ a := by exact_mod_cast hma
    have hrat : (0 : ℚ) ≤ (a : ℚ) / (a - 1) := div_nonneg (by linarith) (by linarith)
    rw [Finset.prod_insert haS, Finset.card_insert_of_notMem haS, Nat.cast_add, Nat.cast_one]
    calc
      ((a : ℚ) / (a - 1)) ^ 3 * (∏ x ∈ S, ((x : ℚ) / (x - 1)) ^ 3)
          ≤ ((a : ℚ) / (a - 1)) ^ 3 * (b / (m - 3)) :=
            mul_le_mul_of_nonneg_left hrest (pow_nonneg hrat 3)
      _ ≤ (b + 3) / b * (b / (m - 3)) :=
        mul_le_mul_of_nonneg_right hcube.le (div_nonneg hb.le hden.le)
      _ = (b + 3) / (m - 3) := div_mul_div_cancel₀ hb.ne'
      _ = _ := by
        congr 1
        dsimp [b]
        ring

/-- The least prime factor `p₁` of an odd perfect number with `ω` distinct prime factors
satisfies `7 p₁ < 3 ω + 21`. -/
theorem seven_mul_minFac_lt {N : ℕ} (h : OddPerfect N) :
    7 * N.minFac < 3 * N.primeFactors.card + 21 := by
  have hm := three_le_minFac h
  by_cases h3 : N.minFac = 3
  · have hk := three_le_card_primeFactors h
    omega
  have hN : N ≠ 1 := by
    intro h1
    rw [h1, Nat.minFac_one] at hm
    omega
  have h4 : N.minFac ≠ 4 := by
    intro he
    have hp := Nat.minFac_prime hN
    rw [he] at hp
    norm_num at hp
  have h5 : 5 ≤ N.minFac := by omega
  have hbound := cube_prod_div_sub_one_le N.primeFactors h5 (fun p hp => by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hle := Nat.minFac_le_of_dvd hprime.two_le (Nat.dvd_of_mem_primeFactors hp)
    refine ⟨hle, six_coprime_iff_not_dvd.mpr ⟨?_, ?_⟩⟩
    · intro hd
      exact Nat.not_prime_of_dvd_of_lt hd (by omega) (by omega) hprime
    · intro hd
      exact Nat.not_prime_of_dvd_of_lt hd (by omega) (by omega) hprime)
  rw [Finset.prod_pow] at hbound
  have hprod := two_lt_prod_primeFactors h
  have hcubed : (8 : ℚ) < (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) ^ 3 := by
    calc
      (8 : ℚ) = 2 ^ 3 := by norm_num
      _ < _ := pow_lt_pow_left₀ (n := 3) hprod (by norm_num) (by decide)
  have hm' : (5 : ℚ) ≤ N.minFac := by exact_mod_cast h5
  have hlinear := (lt_div_iff₀ (by linarith : (0 : ℚ) < (N.minFac : ℚ) - 3)).mp
    (hcubed.trans_le hbound)
  have hrat : 7 * (N.minFac : ℚ) < 3 * (N.primeFactors.card : ℚ) + 21 := by linarith
  exact_mod_cast hrat

end OddPerfect

#print axioms OddPerfect.seven_mul_minFac_lt
