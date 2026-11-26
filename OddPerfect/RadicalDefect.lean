import OddPerfect.RadicalBound

/-!
# A uniform bound on the radical defect

For an odd perfect number `N` write `R = ∏_{p ∣ N} p`, `F = ∏_{p ∣ N} (p - 1)`,
`y_p = p^(e_p + 1)` and `δ = 1 - 2F/R`, the radical defect. From
`∏ (1 - 1/y_p) = 2F/R` and the Weierstrass inequality, `δ ≤ ∑ 1/y_p`.

Uniform tail: for odd `B`, if every `y_p ≥ B³` then `δ < (3B + 2)/(4B³)`, a bound that does not
depend on the number of prime factors. At `B = 5` this gives a trichotomy for every odd perfect
number: `3² ∥ N`, or `5 ∥ N`, or `500 (R - 2F) < 17 R`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Local helpers -/

private theorem rd_odd {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : Odd p :=
  (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two fun h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)

private theorem rd_one_le {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    1 ≤ N.factorization p :=
  ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization h.ne_zero).mp
    (Nat.dvd_of_mem_primeFactors hp)

/-- Exponent dichotomy: each exponent of an odd perfect number is even and at least two, or the
prime and the exponent are both `≡ 1 (mod 4)` (the special prime). -/
theorem exponent_even_or_special {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) :
    (Even (N.factorization p) ∧ 2 ≤ N.factorization p) ∨
      (p % 4 = 1 ∧ N.factorization p % 4 = 1) := by
  have h1 := rd_one_le h hp
  rcases Nat.even_or_odd (N.factorization p) with he | ho
  · left
    obtain ⟨j, hj⟩ := he
    exact ⟨⟨j, hj⟩, by omega⟩
  · right
    exact special_mod_four h (Nat.prime_of_mem_primeFactors hp) ho

/-! ## The tail sum over odd numbers -/

private theorem inv_cube_le_tele {m : ℚ} (hm : 1 ≤ m) :
    ((m + 2) ^ 3)⁻¹ ≤ 1 / (4 * m ^ 2) - 1 / (4 * (m + 2) ^ 2) := by
  have h0 : 0 < m := by linarith
  have e : 1 / (4 * m ^ 2) - 1 / (4 * (m + 2) ^ 2) = (m + 1) / (m ^ 2 * (m + 2) ^ 2) := by
    field_simp
    ring
  rw [e, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg m, mul_pos h0 h0]

/-- Telescoping tail: if every element of `T` has the form `B + 2 + 2k` with `B ≥ 1`, then
`∑_{n ∈ T} 1/n³ < 1/(4B²)`. -/
theorem sum_inv_cube_lt {B : ℕ} (hB : 1 ≤ B) (T : Finset ℕ)
    (hT : ∀ n ∈ T, ∃ k, n = B + 2 + 2 * k) :
    ∑ n ∈ T, (((n : ℚ)) ^ 3)⁻¹ < 1 / (4 * (B : ℚ) ^ 2) := by
  set K := T.sup id + 1
  set ψ : ℕ → ℕ := fun k => B + 2 + 2 * k
  set g : ℕ → ℚ := fun k => 1 / (4 * ((B : ℚ) + 2 * k) ^ 2)
  have hsub : T ⊆ (Finset.range K).image ψ := by
    intro n hn
    obtain ⟨k, rfl⟩ := hT n hn
    have : B + 2 + 2 * k ≤ T.sup id := Finset.le_sup (f := id) hn
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  have hinj : Set.InjOn ψ (Finset.range K : Set ℕ) := fun a _ b _ hab => by
    simp only [ψ] at hab; omega
  have hB' : (1 : ℚ) ≤ B := by exact_mod_cast hB
  calc ∑ n ∈ T, ((n : ℚ) ^ 3)⁻¹
      ≤ ∑ n ∈ (Finset.range K).image ψ, ((n : ℚ) ^ 3)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ k ∈ Finset.range K, (((ψ k : ℕ) : ℚ) ^ 3)⁻¹ := Finset.sum_image hinj
    _ ≤ ∑ k ∈ Finset.range K, (g k - g (k + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        have hm : (1 : ℚ) ≤ B + 2 * k := by have : (0 : ℚ) ≤ k := k.cast_nonneg; linarith
        have := inv_cube_le_tele hm
        calc (((ψ k : ℕ) : ℚ) ^ 3)⁻¹ = (((B : ℚ) + 2 * k + 2) ^ 3)⁻¹ := by
              simp only [ψ]; push_cast; ring
          _ ≤ _ := this
          _ = g k - g (k + 1) := by simp only [g]; push_cast; ring
    _ = g 0 - g K := Finset.sum_range_sub' g K
    _ < g 0 := by
        have : 0 < g K := by simp only [g]; positivity
        linarith
    _ = 1 / (4 * (B : ℚ) ^ 2) := by simp [g]

/-! ## The defect is at most the sum of reciprocals -/

/-- For a perfect `N`, `1 - 2F/R ≤ ∑_{p ∣ N} 1/p^(e_p+1)`. -/
theorem one_sub_two_mul_div_le_sum {N : ℕ} (hN : N.Perfect) :
    1 - 2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) ≤
      ∑ p ∈ N.primeFactors, ((p : ℚ) ^ (N.factorization p + 1))⁻¹ := by
  have hφ : (0 : ℚ) < ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
  have hR : (0 : ℚ) < ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hP : ∏ p ∈ N.primeFactors, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) =
      2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) := by
    have h := two_eq_prod_mul_prod hN
    rw [prod_div_sub_one_eq_div] at h
    rw [eq_div_iff hR.ne', h]
    field_simp
  have hW := one_sub_sum_le_prod_one_sub N.primeFactors
    (fun p => ((p : ℚ) ^ (N.factorization p + 1))⁻¹)
    (fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)
    (fun p hp => inv_le_one_of_one_le₀
      (one_le_pow₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))
  rw [hP] at hW
  linarith

/-! ## The uniform tail lemma -/

/-- Rational form of the uniform tail lemma: if `B` is odd and every component of the odd perfect
number `N` satisfies `p^(e_p+1) ≥ B³`, then `1 - 2F/R < (3B + 2)/(4B³)`. -/
theorem one_sub_two_mul_div_lt {N B : ℕ} (h : OddPerfect N) (hB : Odd B)
    (hy : ∀ p ∈ N.primeFactors, B ^ 3 ≤ p ^ (N.factorization p + 1)) :
    1 - 2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) <
      (3 * B + 2) / (4 * (B : ℚ) ^ 3) := by
  classical
  obtain ⟨q, -, -, -, -, hev⟩ := exists_special_prime h
  set S := N.primeFactors
  set x : ℕ → ℚ := fun p => ((p : ℚ) ^ (N.factorization p + 1))⁻¹
  obtain ⟨b, rfl⟩ := hB
  set c : ℚ := 1 / ((2 * b + 1 : ℕ) : ℚ) ^ 3
  have hx : ∀ p ∈ S, x p ≤ c := by
    intro p hp
    have hc : (((2 * b + 1 : ℕ) : ℚ)) ^ 3 ≤ (p : ℚ) ^ (N.factorization p + 1) := by
      exact_mod_cast hy p hp
    simp only [x, c, one_div]
    exact inv_anti₀ (by positivity) hc
  set S1 := S.filter (· ≤ 2 * b + 1)
  set S2 := S.filter (fun p => ¬ p ≤ 2 * b + 1)
  set S3 := S2.filter (· = q)
  set S4 := S2.filter (fun p => ¬ p = q)
  have hsplit : ∑ p ∈ S, x p = ∑ p ∈ S1, x p + (∑ p ∈ S3, x p + ∑ p ∈ S4, x p) := by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.sum_filter_add_sum_filter_not]
  have hc1 : S1.card ≤ b := by
    have := Finset.card_le_card_of_injOn (fun p => p / 2) (t := Finset.Icc 1 b)
      (fun p hp => by
        have hp' : p ∈ S ∧ p ≤ 2 * b + 1 := Finset.mem_filter.mp (show p ∈ S1 from hp)
        have := (Nat.prime_of_mem_primeFactors hp'.1).two_le
        obtain ⟨j, hj⟩ := rd_odd h hp'.1
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨(by omega : 1 ≤ p / 2), (by omega : p / 2 ≤ b)⟩))
      (fun p hp p' hp' e => by
        have a : p ∈ S ∧ p ≤ 2 * b + 1 := Finset.mem_filter.mp (show p ∈ S1 from hp)
        have a' : p' ∈ S ∧ p' ≤ 2 * b + 1 := Finset.mem_filter.mp (show p' ∈ S1 from hp')
        obtain ⟨j, hj⟩ := rd_odd h a.1
        obtain ⟨j', hj'⟩ := rd_odd h a'.1
        have e' : p / 2 = p' / 2 := e
        omega)
    simpa using this
  have hc3 : S3.card ≤ 1 := Finset.card_le_one.mpr fun a ha a' ha' => by
    simp only [S3, Finset.mem_filter] at ha ha'
    rw [ha.2, ha'.2]
  have h1 : ∑ p ∈ S1, x p ≤ S1.card • c :=
    Finset.sum_le_card_nsmul _ _ _ fun p hp => hx p (Finset.mem_of_mem_filter p hp)
  have h3 : ∑ p ∈ S3, x p ≤ S3.card • c :=
    Finset.sum_le_card_nsmul _ _ _ fun p hp =>
      hx p (Finset.mem_of_mem_filter p (Finset.mem_of_mem_filter p hp))
  have h4 : ∑ p ∈ S4, x p < 1 / (4 * ((2 * b + 1 : ℕ) : ℚ) ^ 2) := by
    calc ∑ p ∈ S4, x p ≤ ∑ p ∈ S4, ((p : ℚ) ^ 3)⁻¹ := by
          apply Finset.sum_le_sum
          intro p hp
          simp only [S4, S2, Finset.mem_filter] at hp
          have hpp := Nat.prime_of_mem_primeFactors hp.1.1
          obtain ⟨j, hj⟩ := hev p hpp hp.2
          have := rd_one_le h hp.1.1
          have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hpp.one_le
          simp only [x]
          exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hp1 (by omega))
      _ < _ := sum_inv_cube_lt (by omega) S4 fun n hn => by
          simp only [S4, S2, Finset.mem_filter] at hn
          obtain ⟨j, hj⟩ := rd_odd h hn.1.1
          exact ⟨(n - (2 * b + 1) - 2) / 2, by omega⟩
  have hδ := one_sub_two_mul_div_le_sum h.perfect
  have hc1' : (S1.card : ℚ) ≤ b := by exact_mod_cast hc1
  have hc3' : (S3.card : ℚ) ≤ 1 := by exact_mod_cast hc3
  have hc0 : 0 ≤ c := by positivity
  rw [nsmul_eq_mul] at h1 h3
  have hsum : ∑ p ∈ S, x p < b * c + c + 1 / (4 * ((2 * b + 1 : ℕ) : ℚ) ^ 2) := by
    rw [hsplit]
    nlinarith
  have harith : (b : ℚ) * c + c + 1 / (4 * ((2 * b + 1 : ℕ) : ℚ) ^ 2) =
      (3 * ((2 * b + 1 : ℕ) : ℚ) + 2) / (4 * ((2 * b + 1 : ℕ) : ℚ) ^ 3) := by
    simp only [c]
    push_cast
    field_simp
    ring
  simp only [x] at hsum
  linarith

/-- Uniform tail lemma: if `B` is odd and every prime factor `p` of the odd perfect number `N`
has `p^(e_p+1) ≥ B³`, then `δ < (3B + 2)/(4B³)`, in integers
`4 B³ (R - 2F) < (3B + 2) R` with `R = ∏ p` and `F = ∏ (p - 1)` over the prime factors.
The bound does not depend on the number of prime factors. -/
theorem four_mul_cube_mul_sub_lt {N B : ℕ} (h : OddPerfect N) (hB : Odd B)
    (hy : ∀ p ∈ N.primeFactors, B ^ 3 ≤ p ^ (N.factorization p + 1)) :
    4 * B ^ 3 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
      (3 * B + 2) * ∏ p ∈ N.primeFactors, p := by
  have key := one_sub_two_mul_div_lt h hB hy
  set R := ∏ p ∈ N.primeFactors, p
  set F := ∏ p ∈ N.primeFactors, (p - 1)
  have hlt := two_mul_prod_sub_one_lt_prod h.perfect
  have hR : (0 : ℚ) < R := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hB0 : (0 : ℚ) < (B : ℚ) := by
    obtain ⟨b, rfl⟩ := hB; positivity
  have hcast : ((R - 2 * F : ℕ) : ℚ) = R - 2 * F := by
    rw [Nat.cast_sub hlt.le, Nat.cast_mul, Nat.cast_two]
  have h2 : 4 * (B : ℚ) ^ 3 * (R - 2 * F) < (3 * B + 2) * R := by
    have e1 : (R : ℚ) - 2 * F = (1 - 2 * (F : ℚ) / R) * R := by field_simp
    rw [e1]
    have h3 := mul_lt_mul_of_pos_right key hR
    have h4 : (0 : ℚ) < 4 * (B : ℚ) ^ 3 := by positivity
    calc 4 * (B : ℚ) ^ 3 * ((1 - 2 * (F : ℚ) / R) * R)
        < 4 * (B : ℚ) ^ 3 * ((3 * B + 2) / (4 * (B : ℚ) ^ 3) * R) := mul_lt_mul_of_pos_left h3 h4
      _ = (3 * B + 2) * R := by field_simp
  rw [← hcast] at h2
  exact_mod_cast h2

/-! ## The certificate rule -/

private theorem ratio_eq (T : Finset ℕ) (hT : ∀ p ∈ T, 1 ≤ p) :
    ((∏ p ∈ T, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ T, p : ℕ) : ℚ) = ∏ p ∈ T, ((p : ℚ) - 1) / p := by
  rw [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_prod]
  congr 1
  exact Finset.prod_congr rfl fun p hp => by rw [Nat.cast_sub (hT p hp), Nat.cast_one]

/-- Certificate rule: let `B` be odd and `T` a set of prime factors of the odd perfect number `N`
with `4 B³ δ_T ≥ 3B + 2`, where `δ_T = 1 - 2 ∏_{p ∈ T} (p - 1)/p`, written without subtraction.
Then some prime factor `p` of `N` (possibly outside `T`) has `p^(e_p+1) < B³`. -/
theorem exists_pow_succ_lt_of_certificate {N B : ℕ} (h : OddPerfect N) (hB : Odd B)
    {T : Finset ℕ} (hT : T ⊆ N.primeFactors)
    (hcert : (3 * B + 2) * ∏ p ∈ T, p + 8 * B ^ 3 * ∏ p ∈ T, (p - 1) ≤ 4 * B ^ 3 * ∏ p ∈ T, p) :
    ∃ p ∈ N.primeFactors, p ^ (N.factorization p + 1) < B ^ 3 := by
  classical
  by_contra hcon
  push Not at hcon
  have key := one_sub_two_mul_div_lt h hB hcon
  have hpos : ∀ p ∈ N.primeFactors, 1 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).one_le
  have hposT : ∀ p ∈ T, 1 ≤ p := fun p hp => hpos p (hT hp)
  rw [mul_div_assoc, ratio_eq _ hpos] at key
  set f : ℕ → ℚ := fun p => ((p : ℚ) - 1) / p
  have hf0 : ∀ p ∈ N.primeFactors, 0 ≤ f p := fun p hp => by
    have : (1 : ℚ) ≤ p := by exact_mod_cast hpos p hp
    exact div_nonneg (by linarith) (by linarith)
  have hf1 : ∀ p ∈ N.primeFactors, f p ≤ 1 := fun p hp => by
    have : (1 : ℚ) ≤ p := by exact_mod_cast hpos p hp
    rw [div_le_one (by linarith)]; linarith
  have hmono : ∏ p ∈ N.primeFactors, f p ≤ ∏ p ∈ T, f p := by
    rw [← Finset.prod_sdiff hT]
    apply mul_le_of_le_one_left (Finset.prod_nonneg fun p hp => hf0 p (hT hp))
    exact Finset.prod_le_one₀ (fun p hp => hf0 p (Finset.mem_sdiff.mp hp).1)
      fun p hp => hf1 p (Finset.mem_sdiff.mp hp).1
  have hRT : (0 : ℚ) < ((∏ p ∈ T, p : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hT hp)).pos
  have hc : (3 * (B : ℚ) + 2) * ((∏ p ∈ T, p : ℕ) : ℚ) +
      8 * (B : ℚ) ^ 3 * ((∏ p ∈ T, (p - 1) : ℕ) : ℚ) ≤ 4 * (B : ℚ) ^ 3 * ((∏ p ∈ T, p : ℕ) : ℚ) := by
    exact_mod_cast hcert
  have hB0 : (0 : ℚ) < (B : ℚ) := by obtain ⟨b, rfl⟩ := hB; positivity
  have hTr : (3 * B + 2 : ℚ) / (4 * (B : ℚ) ^ 3) ≤ 1 - 2 * ∏ p ∈ T, f p := by
    rw [← ratio_eq _ hposT, div_le_iff₀ (by positivity)]
    have e : (1 - 2 * (((∏ p ∈ T, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ T, p : ℕ) : ℚ))) *
        (4 * (B : ℚ) ^ 3) = (4 * (B : ℚ) ^ 3 * ((∏ p ∈ T, p : ℕ) : ℚ) -
          8 * (B : ℚ) ^ 3 * ((∏ p ∈ T, (p - 1) : ℕ) : ℚ)) / ((∏ p ∈ T, p : ℕ) : ℚ) := by
      field_simp
      ring
    rw [e, le_div_iff₀ hRT]
    linarith
  linarith

/-! ## Small components -/

/-- The admissible components below `11³`: if a prime factor `p` of an odd perfect number has
`p^(e_p+1) < 1331`, then `(p, e_p)` is one of `(3, 2), (3, 4), (5, 1), (5, 2), (7, 2), (13, 1),
(17, 1), (29, 1)`. -/
theorem small_component_cases {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors)
    (hlt : p ^ (N.factorization p + 1) < 1331) :
    (p = 3 ∧ N.factorization p = 2) ∨ (p = 3 ∧ N.factorization p = 4) ∨
      (p = 5 ∧ N.factorization p = 1) ∨ (p = 5 ∧ N.factorization p = 2) ∨
      (p = 7 ∧ N.factorization p = 2) ∨ (p = 13 ∧ N.factorization p = 1) ∨
      (p = 17 ∧ N.factorization p = 1) ∨ (p = 29 ∧ N.factorization p = 1) := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 := hpp.two_le
  obtain ⟨j, hj⟩ := rd_odd h hp
  have hd := exponent_even_or_special h hp
  generalize N.factorization p = e at hd hlt ⊢
  have hp3 : 3 ≤ p := by omega
  have h3e : 3 ^ (e + 1) ≤ p ^ (e + 1) := Nat.pow_le_pow_left hp3 _
  have he6 : e + 1 < 7 := by
    by_contra hc
    have : 3 ^ 7 ≤ 3 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h37 : (3 : ℕ) ^ 7 = 2187 := by norm_num
    omega
  rcases hd with ⟨⟨i, hi⟩, he2⟩ | ⟨hp4, he4⟩
  · -- even exponent `e ≥ 2`: `p³ < 1331`, so `p ≤ 7`
    have hc : p ^ 3 ≤ p ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp7 : p < 11 := by
      by_contra hc'
      have : 11 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) _
      have h113 : (11 : ℕ) ^ 3 = 1331 := by norm_num
      omega
    have h24 : e = 2 ∨ e = 4 := by omega
    interval_cases p <;> first
      | omega
      | (norm_num at hpp; done)
      | (rcases h24 with h' | h' <;> subst h' <;> omega)
  · -- the special prime: `e ≡ 1 (mod 4)` and `e + 1 < 7` force `e = 1`
    have e1 : e = 1 := by
      by_contra hne
      have h5 : e = 5 := by omega
      subst h5
      have hl : p ^ 6 < 1331 := hlt
      have : 5 ^ 6 ≤ p ^ 6 := Nat.pow_le_pow_left (by omega) _
      have h56 : (5 : ℕ) ^ 6 = 15625 := by norm_num
      omega
    subst e1
    norm_num at hlt
    have hp36 : p < 37 := by
      by_contra hc'
      have : 37 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) _
      have h372 : (37 : ℕ) ^ 2 = 1369 := by norm_num
      omega
    interval_cases p <;> first | omega | norm_num at hpp

/-! ## Trichotomies -/

/-- Trichotomy at `B = 5`: every odd perfect number `N` has `3² ∥ N`, or `5 ∥ N`, or
`500 (R - 2F) < 17 R` (equivalently `R/F < 1000/483`), with `R = ∏ p` and `F = ∏ (p - 1)` over
the prime factors. -/
theorem radical_trichotomy_five {N : ℕ} (h : OddPerfect N) :
    N.factorization 3 = 2 ∨ N.factorization 5 = 1 ∨
      500 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
        17 * ∏ p ∈ N.primeFactors, p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h3, h5, hR⟩ := hcon
  have hy : ∀ p ∈ N.primeFactors, 5 ^ 3 ≤ p ^ (N.factorization p + 1) := by
    intro p hp
    by_contra hlt
    push Not at hlt
    rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
      ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
      first | omega | (rw [e] at hlt; norm_num at hlt)
  have key := four_mul_cube_mul_sub_lt h (by decide) hy
  norm_num at key
  omega

/-- Trichotomy at `B = 7`: every odd perfect number `N` has `e_3 ∈ {2, 4}`, or `e_5 ∈ {1, 2}`, or
`e_13 = 1`, or `e_17 = 1`, or `1372 (R - 2F) < 23 R`. -/
theorem radical_trichotomy_seven {N : ℕ} (h : OddPerfect N) :
    N.factorization 3 = 2 ∨ N.factorization 3 = 4 ∨ N.factorization 5 = 1 ∨
      N.factorization 5 = 2 ∨ N.factorization 13 = 1 ∨ N.factorization 17 = 1 ∨
      1372 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
        23 * ∏ p ∈ N.primeFactors, p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a1, a2, a3, a4, a5, a6, hR⟩ := hcon
  have hy : ∀ p ∈ N.primeFactors, 7 ^ 3 ≤ p ^ (N.factorization p + 1) := by
    intro p hp
    by_contra hlt
    push Not at hlt
    rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
      ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
      first | omega | (rw [e] at hlt; norm_num at hlt)
  have key := four_mul_cube_mul_sub_lt h (by decide) hy
  norm_num at key
  omega

/-- Trichotomy at `B = 9`: every odd perfect number `N` has `e_3 ∈ {2, 4}`, or `e_5 ∈ {1, 2}`, or
`e_7 = 2`, or `e_13 = 1`, or `e_17 = 1`, or `2916 (R - 2F) < 29 R`. -/
theorem radical_trichotomy_nine {N : ℕ} (h : OddPerfect N) :
    N.factorization 3 = 2 ∨ N.factorization 3 = 4 ∨ N.factorization 5 = 1 ∨
      N.factorization 5 = 2 ∨ N.factorization 7 = 2 ∨ N.factorization 13 = 1 ∨
      N.factorization 17 = 1 ∨
      2916 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
        29 * ∏ p ∈ N.primeFactors, p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, hR⟩ := hcon
  have hy : ∀ p ∈ N.primeFactors, 9 ^ 3 ≤ p ^ (N.factorization p + 1) := by
    intro p hp
    by_contra hlt
    push Not at hlt
    rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
      ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
      first | omega | (rw [e] at hlt; norm_num at hlt)
  have key := four_mul_cube_mul_sub_lt h (by decide) hy
  norm_num at key
  omega

/-- Trichotomy at `B = 11`: every odd perfect number `N` has `e_3 ∈ {2, 4}`, or `e_5 ∈ {1, 2}`, or
`e_7 = 2`, or `e_13 = 1`, or `e_17 = 1`, or `e_29 = 1`, or `5324 (R - 2F) < 35 R`. -/
theorem radical_trichotomy_eleven {N : ℕ} (h : OddPerfect N) :
    N.factorization 3 = 2 ∨ N.factorization 3 = 4 ∨ N.factorization 5 = 1 ∨
      N.factorization 5 = 2 ∨ N.factorization 7 = 2 ∨ N.factorization 13 = 1 ∨
      N.factorization 17 = 1 ∨ N.factorization 29 = 1 ∨
      5324 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
        35 * ∏ p ∈ N.primeFactors, p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, hR⟩ := hcon
  have hy : ∀ p ∈ N.primeFactors, 11 ^ 3 ≤ p ^ (N.factorization p + 1) := by
    intro p hp
    by_contra hlt
    push Not at hlt
    rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
      ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ <;>
      omega
  have key := four_mul_cube_mul_sub_lt h (by decide) hy
  norm_num at key
  omega

/-! ## Consequences -/

private theorem three_dvd_of_five_special {N : ℕ} (h : OddPerfect N) (e : N.factorization 5 = 1) :
    3 ∣ N :=
  (prime_dvd_of_dvd_succ_special h (by norm_num : Nat.Prime 5) (by rw [e]; exact odd_one)
    Nat.prime_three (by norm_num) (by norm_num)).1

/-- If `3 ∤ N` for an odd perfect number `N`, the third branch of the trichotomy holds:
`500 (R - 2F) < 17 R`, that is `R/F < 1000/483`. -/
theorem radical_bound_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    500 * (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) <
      17 * ∏ p ∈ N.primeFactors, p := by
  rcases radical_trichotomy_five h with e | e | hR
  · exact absurd (Nat.dvd_of_factorization_pos (by omega)) h3
  · exact absurd (three_dvd_of_five_special h e) h3
  · exact hR

private theorem rd_mem {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N) :
    p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩

/-- Certificate instance `T = {3, 7, 11, 13}`, `B = 5` (`δ_T = 41/1001 > 17/500`): an odd perfect
number divisible by `3, 7, 11, 13` has `3² ∥ N`. (The branch `5 ∥ N` is excluded since
`105 ∤ N`.) -/
theorem factorization_three_eq_two_of_three_seven_eleven_thirteen {N : ℕ} (h : OddPerfect N)
    (h3 : 3 ∣ N) (h7 : 7 ∣ N) (h11 : 11 ∣ N) (h13 : 13 ∣ N) : N.factorization 3 = 2 := by
  obtain ⟨p, hp, hlt⟩ := exists_pow_succ_lt_of_certificate (B := 5) (T := {3, 7, 11, 13}) h
    (by decide)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact rd_mem h (by norm_num) h3
      · exact rd_mem h (by norm_num) h7
      · exact rd_mem h (by norm_num) h11
      · exact rd_mem h (by norm_num) h13)
    (by decide)
  rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
    ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
  · exact e
  all_goals first
    | (rw [e] at hlt; norm_num at hlt; done)
    | exact absurd h7 (not_seven_dvd_of_three_five h h3 (Nat.dvd_of_mem_primeFactors hp))

/-- Certificate instance `T = {5, 7, 11, 13, 17, 19, 23, 29}`, `B = 5`: no odd perfect number is
divisible by all of `5, 7, 11, 13, 17, 19, 23, 29`. (The certificate gives `3² ∥ N` or `5 ∥ N`, so
`3 ∣ N`, contradicting `105 ∤ N`.) -/
theorem not_five_to_twentynine {N : ℕ} (h : OddPerfect N) :
    ¬ (5 ∣ N ∧ 7 ∣ N ∧ 11 ∣ N ∧ 13 ∣ N ∧ 17 ∣ N ∧ 19 ∣ N ∧ 23 ∣ N ∧ 29 ∣ N) := by
  rintro ⟨h5, h7, h11, h13, h17, h19, h23, h29⟩
  obtain ⟨p, hp, hlt⟩ := exists_pow_succ_lt_of_certificate (B := 5)
    (T := {5, 7, 11, 13, 17, 19, 23, 29}) h (by decide)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact rd_mem h (by norm_num) h5
      · exact rd_mem h (by norm_num) h7
      · exact rd_mem h (by norm_num) h11
      · exact rd_mem h (by norm_num) h13
      · exact rd_mem h (by norm_num) h17
      · exact rd_mem h (by norm_num) h19
      · exact rd_mem h (by norm_num) h23
      · exact rd_mem h (by norm_num) h29)
    (by norm_num [Finset.prod_insert, Finset.prod_singleton])
  have h3 : 3 ∣ N := by
    rcases small_component_cases h hp (hlt.trans_le (by norm_num)) with
      ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
    · exact Nat.dvd_of_mem_primeFactors hp
    · rw [e] at hlt; norm_num at hlt
    · exact three_dvd_of_five_special h e
    all_goals (rw [e] at hlt; norm_num at hlt)
  exact not_seven_dvd_of_three_five h h3 h5 h7

/-- The instance `T = {3, 5, 17, 19}` of the certificate rule is vacuous: no odd perfect number is
divisible by all of `3, 5, 17, 19`. Proof by abundancy: `3² ∥ N` forces `13 ∣ N` and
`3² · 5 · 13 · 17 · 19²` is abundant; otherwise `3⁴ ∣ N`, and `3⁴ · 5 · 17² · 19²` (when `5 ∥ N`)
or `3⁴ · 5² · 17 · 19²` (when `5² ∣ N`) is abundant. -/
theorem not_three_five_seventeen_nineteen {N : ℕ} (h : OddPerfect N) :
    ¬ (3 ∣ N ∧ 5 ∣ N ∧ 17 ∣ N ∧ 19 ∣ N) := by
  rintro ⟨h3, h5, h17, h19⟩
  have pd : ∀ {p a : ℕ}, p.Prime → a ≤ N.factorization p → p ^ a ∣ N := fun hp ha =>
    (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr ha
  have m3 := rd_mem h Nat.prime_three h3
  have m5 := rd_mem h (by norm_num) h5
  have m17 := rd_mem h (by norm_num) h17
  have m19 := rd_mem h (by norm_num) h19
  have e3 : Even (N.factorization 3) ∧ 2 ≤ N.factorization 3 :=
    (exponent_even_or_special h m3).resolve_right (by omega)
  have e19 : 2 ≤ N.factorization 19 :=
    ((exponent_even_or_special h m19).resolve_right (by omega)).2
  have e5 := rd_one_le h m5
  have e17 := rd_one_le h m17
  have p5 : Nat.Prime 5 := by norm_num
  have p13 : Nat.Prime 13 := by norm_num
  have p17 : Nat.Prime 17 := by norm_num
  have p19 : Nat.Prime 19 := by norm_num
  suffices hd : ∃ d, d ∣ N ∧ 2 < abundancy d by
    obtain ⟨d, hd, hab⟩ := hd
    exact not_perfect_of_dvd_of_two_lt_abundancy hd hab h.perfect
  by_cases h32 : N.factorization 3 = 2
  · have h13 : 13 ∣ N := OPNStarter.thirteen_dvd_of_three_sq h.perfect h32
    have e13 := rd_one_le h (rd_mem h p13 h13)
    refine ⟨3 ^ 2 * 5 * 13 * 17 * 19 ^ 2, ?_, ?_⟩
    · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ (pd p19 e19)
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h17
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h13
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (pd Nat.prime_three e3.2) h5
    · rw [abundancy_mul_of_coprime (a := 3 ^ 2 * 5 * 13 * 17) (b := 19 ^ 2) (by norm_num),
        abundancy_mul_of_coprime (a := 3 ^ 2 * 5 * 13) (b := 17) (by norm_num),
        abundancy_mul_of_coprime (a := 3 ^ 2 * 5) (b := 13) (by norm_num),
        abundancy_mul_of_coprime (a := 3 ^ 2) (b := 5) (by norm_num),
        ← pow_one 5, ← pow_one 13, ← pow_one 17,
        abundancy_prime_pow Nat.prime_three, abundancy_prime_pow p5, abundancy_prime_pow p13,
        abundancy_prime_pow p17, abundancy_prime_pow p19]
      norm_num [Finset.sum_range_succ]
  · have e34 : 4 ≤ N.factorization 3 := by obtain ⟨⟨i, hi⟩, _⟩ := e3; omega
    by_cases h51 : N.factorization 5 = 1
    · have e17' : 2 ≤ N.factorization 17 := by
        obtain ⟨j, hj⟩ := even_factorization_of_ne h p5 (by rw [h51]; exact odd_one) p17
          (by norm_num)
        omega
      refine ⟨3 ^ 4 * 5 * 17 ^ 2 * 19 ^ 2, ?_, ?_⟩
      · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ (pd p19 e19)
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ (pd p17 e17')
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (pd Nat.prime_three e34) h5
      · rw [abundancy_mul_of_coprime (a := 3 ^ 4 * 5 * 17 ^ 2) (b := 19 ^ 2) (by norm_num),
          abundancy_mul_of_coprime (a := 3 ^ 4 * 5) (b := 17 ^ 2) (by norm_num),
          abundancy_mul_of_coprime (a := 3 ^ 4) (b := 5) (by norm_num),
          ← pow_one 5, abundancy_prime_pow Nat.prime_three, abundancy_prime_pow p5,
          abundancy_prime_pow p17, abundancy_prime_pow p19]
        norm_num [Finset.sum_range_succ]
    · have e52 : 2 ≤ N.factorization 5 := by omega
      refine ⟨3 ^ 4 * 5 ^ 2 * 17 * 19 ^ 2, ?_, ?_⟩
      · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ (pd p19 e19)
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) ?_ h17
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (pd Nat.prime_three e34) (pd p5 e52)
      · rw [abundancy_mul_of_coprime (a := 3 ^ 4 * 5 ^ 2 * 17) (b := 19 ^ 2) (by norm_num),
          abundancy_mul_of_coprime (a := 3 ^ 4 * 5 ^ 2) (b := 17) (by norm_num),
          abundancy_mul_of_coprime (a := 3 ^ 4) (b := 5 ^ 2) (by norm_num),
          ← pow_one 17, abundancy_prime_pow Nat.prime_three, abundancy_prime_pow p5,
          abundancy_prime_pow p17, abundancy_prime_pow p19]
        norm_num [Finset.sum_range_succ]

/-! ## Control

The data `S = {3, 5, 17, 19} ∪ {10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091,
10093}` (the ten smallest primes above `10000`) with exponent `5` at `5`, `6` at `17` and `4`
elsewhere has components `y_3 = 3⁵ = 243 = min y`, `y_5 = 5⁶`, `y_17 = 17⁷`, `y_19 = 19⁵`, `y_p = p⁵`, all at
least `125`. Its defect `δ ≈ 0.04986` passes the older band `1 ≤ δ · min y ≤ |S| = 14`
(`δ · 243 ≈ 12.12`), but `δ > 17/500`, so the uniform tail lemma at `B = 5` rejects it. -/
example :
    let R : ℚ := 3 * 5 * 17 * 19 * 10007 * 10009 * 10037 * 10039 * 10061 * 10067 * 10069 *
      10079 * 10091 * 10093
    let F : ℚ := 2 * 4 * 16 * 18 * 10006 * 10008 * 10036 * 10038 * 10060 * 10066 * 10068 *
      10078 * 10090 * 10092
    let δ := 1 - 2 * F / R
    (17 : ℚ) / 500 < δ ∧ 1 ≤ δ * 243 ∧ δ * 243 ≤ 14 := by
  norm_num

end OddPerfect

#print axioms OddPerfect.exponent_even_or_special
#print axioms OddPerfect.sum_inv_cube_lt
#print axioms OddPerfect.one_sub_two_mul_div_le_sum
#print axioms OddPerfect.one_sub_two_mul_div_lt
#print axioms OddPerfect.four_mul_cube_mul_sub_lt
#print axioms OddPerfect.exists_pow_succ_lt_of_certificate
#print axioms OddPerfect.small_component_cases
#print axioms OddPerfect.radical_trichotomy_five
#print axioms OddPerfect.radical_trichotomy_seven
#print axioms OddPerfect.radical_trichotomy_nine
#print axioms OddPerfect.radical_trichotomy_eleven
#print axioms OddPerfect.radical_bound_of_not_three_dvd
#print axioms OddPerfect.factorization_three_eq_two_of_three_seven_eleven_thirteen
#print axioms OddPerfect.not_five_to_twentynine
#print axioms OddPerfect.not_three_five_seventeen_nineteen
