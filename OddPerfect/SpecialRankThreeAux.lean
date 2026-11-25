import OddPerfect.RankTwoPaletteAux

/-!
# Arithmetic lemmas for the special exponent with two primes above the special prime

Helper results for `OddPerfect.SpecialRankThree`. No novelty is claimed.

* `sub_two_mul_cyclotomic_eval_le`: for real `x > 2` and `n ≥ 1`,
  `(x - 2) Φ_n(x) ≤ (x - 1) x ^ φ(n)`. By Möbius inversion,
  `Φ_n(x) / x ^ φ(n) = ∏_{d ∣ n} (1 - x ^ (-d)) ^ μ(n / d)`; every factor is at most
  `(1 - x ^ (-d))⁻¹`, and `∏_{d ∣ n} (1 - x ^ (-d)) ≥ 1 - ∑_{d ≥ 1} x ^ (-d) = (x - 2) / (x - 1)`.
* `pow_dvd_cyclotomic_orderOf_of_not_dvd_succ`: the one cyclotomic factor lemma of
  `OddPerfect.RankTwoPaletteAux` with the hypothesis `a + 1 < P` replaced by `P ∤ a + 1`.
* `sub_two_mul_pow_le_of_pow_dvd_sigma`: hence `(q - 2) P ^ k ≤ (q - 1) q ^ φ(a + 1)`.
* `two_mul_totient_two_mul_le`: `2 φ(2 m) ≤ 2 m`.
* Size comparisons over the integers: `srt_case_one`, `srt_case_four`, `srt_sigma_lt_two_mul`,
  `srt_gap`.
-/

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma ArithmeticFunction.Moebius

namespace OddPerfect

/-! ## A sharp upper bound for cyclotomic values -/

private theorem srt_prod_one_sub_ge (s : Finset ℕ) {a : ℕ → ℝ} (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hs : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have ha0 := h0 j (Finset.mem_insert_self j s)
    have ha1 := h1 j (Finset.mem_insert_self j s)
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr ha1), mul_nonneg ha0 hs]

private theorem srt_sum_divisors_inv_pow_le {n : ℕ} {x : ℝ} (hx : 1 < x) :
    ∑ d ∈ n.divisors, (x⁻¹) ^ d ≤ (x - 1)⁻¹ := by
  have hy0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
  have hy1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hsub : insert 0 n.divisors ⊆ Finset.range (n + 1) := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · simp
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd))
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => pow_nonneg hy0.le i) (f := fun d => (x⁻¹) ^ d)
  rw [Finset.sum_insert (fun h0 => by simp at h0)] at h1
  have hg := geom_sum_mul (x⁻¹) (n + 1)
  have hpow : 0 ≤ (x⁻¹) ^ (n + 1) := pow_nonneg hy0.le _
  simp only [pow_zero] at h1
  set y := x⁻¹ with hy
  set S := ∑ i ∈ Finset.range (n + 1), y ^ i
  set T := ∑ d ∈ n.divisors, y ^ d
  have hS : S * (1 - y) ≤ 1 := by nlinarith
  have h2 : (1 + T) * (1 - y) ≤ S * (1 - y) := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : T * (1 - y) ≤ y := by nlinarith
  have hxy : x * y = 1 := mul_inv_cancel₀ (by positivity)
  have h4 : x * (T * (1 - y)) ≤ x * y := mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 : T * (x - 1) ≤ 1 := by
    have e : x * (T * (1 - y)) = T * (x - 1) := by linear_combination (-T) * hxy
    linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [inv_eq_one_div, le_div_iff₀ hx1]
  exact h5

/-- Sharp upper bound for cyclotomic values: for real `x > 2` and `n ≥ 1`,
`(x - 2) Φ_n(x) ≤ (x - 1) x ^ φ(n)`. -/
theorem sub_two_mul_cyclotomic_eval_le {n : ℕ} {x : ℝ} (hn : 0 < n) (hx : 2 < x) :
    (x - 2) * (cyclotomic n ℝ).eval x ≤ (x - 1) * x ^ n.totient := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  set f : ℕ → ℝ := fun i => (cyclotomic i ℝ).eval x / x ^ i.totient with hf
  set g : ℕ → ℝ := fun i => 1 - (x⁻¹) ^ i with hg
  have hgx : ∀ i, g i = (x ^ i - 1) / x ^ i := by
    intro i
    simp only [hg, inv_pow]
    field_simp
  have hg0 : ∀ i, 0 < i → 0 < g i := by
    intro i hi
    simp only [hg, sub_pos]
    exact pow_lt_one₀ (inv_pos.mpr hx0).le (inv_lt_one_of_one_lt₀ hx1) hi.ne'
  have hg1 : ∀ i, g i ≤ 1 := by
    intro i
    simp only [hg, sub_le_self_iff]
    exact pow_nonneg (inv_pos.mpr hx0).le i
  have hprod : ∀ m > 0, ∏ i ∈ m.divisors, f i = g m := by
    intro m hm
    rw [hgx, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Nat.sum_totient]
    congr 1
    have h := congrArg (eval x) (prod_cyclotomic_eq_X_pow_sub_one hm ℝ)
    rw [eval_prod] at h
    simpa using h
  have hm := (prod_eq_iff_prod_pow_moebius_eq_of_nonzero
    (fun i hi => div_ne_zero (cyclotomic_pos' i hx1).ne' (pow_pos hx0 _).ne')
    (fun i hi => (hg0 i hi).ne')).1 hprod n hn
  have hle : f n ≤ ∏ i ∈ n.divisorsAntidiagonal, (g i.2)⁻¹ := by
    show (cyclotomic n ℝ).eval x / x ^ n.totient ≤ _
    rw [← hm]
    refine Finset.prod_le_prod (fun i hi => (zpow_pos (hg0 _ ?_) _).le) (fun i hi => ?_)
    · exact Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hi)
    · have hpos := hg0 _ (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hi))
      have hmu : (-1 : ℤ) ≤ μ i.1 := (abs_le.mp abs_moebius_le_one).1
      have := zpow_le_zpow_right_of_le_one₀ hpos (hg1 _) hmu
      simpa using this
  rw [Finset.prod_inv_distrib,
    Nat.prod_divisorsAntidiagonal' (f := fun _ j => g j)] at hle
  have hlow : 1 - (x - 1)⁻¹ ≤ ∏ i ∈ n.divisors, g i := by
    have h1 := srt_prod_one_sub_ge n.divisors (a := fun d => (x⁻¹) ^ d)
      (fun i _ => pow_nonneg (inv_pos.mpr hx0).le i)
      (fun i _ => pow_le_one₀ (inv_pos.mpr hx0).le (inv_le_one_of_one_le₀ hx1.le))
    have h2 := srt_sum_divisors_inv_pow_le (n := n) hx1
    simp only [hg]
    linarith
  have hx2 : 0 < x - 2 := by linarith
  have hxm1 : 0 < x - 1 := by linarith
  have hc : 1 - (x - 1)⁻¹ = (x - 2) / (x - 1) := by field_simp; ring
  rw [hc] at hlow
  have hP0 : 0 < ∏ i ∈ n.divisors, g i := lt_of_lt_of_le (by positivity) hlow
  have hinv : (∏ i ∈ n.divisors, g i)⁻¹ ≤ (x - 1) / (x - 2) := by
    rw [← inv_div]
    exact inv_anti₀ (by positivity) hlow
  have hfx : f n ≤ (x - 1) / (x - 2) := hle.trans hinv
  simp only [hf] at hfx
  rw [div_le_div_iff₀ (pow_pos hx0 _) hx2] at hfx
  linarith

/-! ## One cyclotomic factor without a size condition on the exponent -/

/-- One cyclotomic factor. Let `q < P` be primes with `q + 1 < P` and `P ∤ a + 1`, and let
`P ^ k ∣ σ(q ^ a)` with `k ≥ 1`. Then `t = ord_P(q)` satisfies `3 ≤ t`, `t ∣ a + 1`, and
`P ^ k ∣ Φ_t(q)`. -/
theorem pow_dvd_cyclotomic_orderOf_of_not_dvd_succ {q P a k : ℕ} (hq : q.Prime)
    (hP : P.Prime) (hqP : q + 1 < P) (hPa : ¬ P ∣ a + 1) (hk : 1 ≤ k)
    (hd : P ^ k ∣ σ 1 (q ^ a)) :
    3 ≤ orderOf (q : ZMod P) ∧ orderOf (q : ZMod P) ∣ a + 1 ∧
      (P : ℤ) ^ k ∣ (cyclotomic (orderOf (q : ZMod P)) ℤ).eval (q : ℤ) := by
  have : Fact P.Prime := ⟨hP⟩
  have hz : (P : ℤ) ^ k ∣ (q : ℤ) ^ (a + 1) - 1 := by
    rw [← rankTwo_sigma_mul_sub_one hq]
    exact Dvd.dvd.mul_right (by exact_mod_cast hd) _
  have hz1 : (P : ℤ) ∣ (q : ℤ) ^ (a + 1) - 1 :=
    (dvd_pow_self (P : ℤ) (by omega)).trans hz
  have hpow : (q : ZMod P) ^ (a + 1) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ P).mpr hz1
    push_cast at this
    exact sub_eq_zero.mp this
  have htd : orderOf (q : ZMod P) ∣ a + 1 := orderOf_dvd_of_pow_eq_one hpow
  have hinj : ∀ m n : ℕ, m < P → n < P → (m : ZMod P) = n → m = n := by
    intro m n hm hn hmn
    rw [ZMod.natCast_eq_natCast_iff'] at hmn
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at hmn
  have hq2 := hq.two_le
  have ht3 : 3 ≤ orderOf (q : ZMod P) := by
    have ht0 : 0 < orderOf (q : ZMod P) := Nat.pos_of_dvd_of_pos htd (by omega)
    have h2 := pow_orderOf_eq_one (q : ZMod P)
    by_contra hlt
    have hcases : (q : ZMod P) = 1 ∨ (q : ZMod P) + 1 = 0 := by
      rcases (show orderOf (q : ZMod P) = 1 ∨ orderOf (q : ZMod P) = 2 by omega) with h1 | h1
      · rw [h1, pow_one] at h2
        exact Or.inl h2
      · rw [h1] at h2
        have : ((q : ZMod P) - 1) * ((q : ZMod P) + 1) = 0 := by
          linear_combination h2
        rcases mul_eq_zero.mp this with h | h
        · exact Or.inl (sub_eq_zero.mp h)
        · exact Or.inr h
    rcases hcases with h1 | h1
    · have := hinj q 1 (by omega) (by omega) (by simpa using h1)
      omega
    · have h1' : ((q + 1 : ℕ) : ZMod P) = 0 := by push_cast; exact h1
      rw [ZMod.natCast_eq_zero_iff] at h1'
      have := Nat.le_of_dvd (by omega) h1'
      omega
  refine ⟨ht3, htd, ?_⟩
  have hmem : orderOf (q : ZMod P) ∈ (a + 1).divisors := Nat.mem_divisors.mpr ⟨htd, by omega⟩
  have hprod : (q : ℤ) ^ (a + 1) - 1 = (cyclotomic (orderOf (q : ZMod P)) ℤ).eval (q : ℤ) *
      ∏ d ∈ (a + 1).divisors.erase (orderOf (q : ZMod P)), (cyclotomic d ℤ).eval (q : ℤ) := by
    have h := congrArg (eval (q : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (Nat.succ_pos a) ℤ)
    rw [eval_prod, ← Finset.mul_prod_erase _ (fun d => (cyclotomic d ℤ).eval (q : ℤ)) hmem] at h
    simpa using h.symm
  have hPz : Prime (P : ℤ) := Nat.prime_iff_prime_int.mp hP
  have hQ : ¬ (P : ℤ) ∣
      ∏ d ∈ (a + 1).divisors.erase (orderOf (q : ZMod P)), (cyclotomic d ℤ).eval (q : ℤ) := by
    rw [hPz.dvd_finsetProd_iff]
    rintro ⟨d, hd, hdu⟩
    obtain ⟨hdt, hdmem⟩ := Finset.mem_erase.mp hd
    have := (orderOf_eq_of_dvd_cyclotomic_eval hP hdu fun hh =>
      hPa (hh.trans (Nat.dvd_of_mem_divisors hdmem))).1
    exact hdt this.symm
  rw [hprod] at hz
  exact (((hPz.coprime_iff_not_dvd).mpr hQ).pow_left).dvd_of_dvd_mul_right hz

/-- Sharp size form of one cyclotomic factor. Let `q ≥ 3` and `P` be primes with `q + 1 < P`
and `P ∤ a + 1`, and let `P ^ k ∣ σ(q ^ a)` with `k ≥ 1`. Then
`(q - 2) P ^ k ≤ (q - 1) q ^ φ(a + 1)`. -/
theorem sub_two_mul_pow_le_of_pow_dvd_sigma {q P a k : ℕ} (hq : q.Prime) (hP : P.Prime)
    (hq3 : 3 ≤ q) (hqP : q + 1 < P) (hPa : ¬ P ∣ a + 1) (hk : 1 ≤ k)
    (hd : P ^ k ∣ σ 1 (q ^ a)) :
    (q - 2) * P ^ k ≤ (q - 1) * q ^ (a + 1).totient := by
  obtain ⟨ht3, htd, hdvd⟩ := pow_dvd_cyclotomic_orderOf_of_not_dvd_succ hq hP hqP hPa hk hd
  set t := orderOf (q : ZMod P)
  have hpos : 0 < (cyclotomic t ℤ).eval (q : ℤ) := cyclotomic_pos' t (by exact_mod_cast hq.one_lt)
  have h1 := Int.le_of_dvd hpos hdvd
  have hr := sub_two_mul_cyclotomic_eval_le (n := t) (x := (q : ℝ)) (by omega)
    (by exact_mod_cast (show 2 < q by omega))
  have e : (cyclotomic t ℝ).eval (q : ℝ) = (((cyclotomic t ℤ).eval (q : ℤ) : ℤ) : ℝ) := by
    have := cyclotomic.eval_apply (q : ℤ) t (Int.castRingHom ℝ)
    simpa using this
  rw [e] at hr
  have hz : ((q : ℤ) - 2) * (cyclotomic t ℤ).eval (q : ℤ) ≤
      ((q : ℤ) - 1) * (q : ℤ) ^ t.totient := by
    exact_mod_cast hr
  have h2 : (q : ℤ) ^ t.totient ≤ (q : ℤ) ^ (a + 1).totient :=
    pow_le_pow_right₀ (by exact_mod_cast hq.one_lt.le)
      (Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.succ_pos a)) (Nat.totient_dvd_of_dvd htd))
  have hq2 : (0 : ℤ) ≤ (q : ℤ) - 2 := by have : (3 : ℤ) ≤ q := by exact_mod_cast hq3
                                         linarith
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
  have h3 := mul_le_mul_of_nonneg_left h1 hq2
  have h4 := mul_le_mul_of_nonneg_left h2 hq1
  zify [show 2 ≤ q by omega, show 1 ≤ q by omega]
  linarith

/-- `2 φ(2 m) ≤ 2 m`. -/
theorem two_mul_totient_two_mul_le (m : ℕ) : 2 * (2 * m).totient ≤ 2 * m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with hm | hm
    · rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp
      · obtain ⟨k, rfl⟩ := hm
        have hk : k < k + k := by omega
        have := ih k hk
        rw [Nat.totient_two_mul_of_even ⟨k, rfl⟩, ← two_mul]
        omega
    · rw [Nat.totient_two_mul_of_odd hm]
      have := Nat.totient_le m
      omega

/-! ## Size comparisons -/

/-- Case of one cyclotomic factor carrying all of `R ^ e`: integers `Q ≥ 5`, `S`, `X`, `F` with
`Q ^ w ≤ S < 2 X`, `X ≤ F` and `(Q - 2) F ≤ (Q - 1) Q ^ m` satisfy `w ≤ m`. -/
theorem srt_case_one {Q S X F : ℤ} {w m : ℕ} (hQ : 5 ≤ Q) (hS : Q ^ w ≤ S) (hSX : S < 2 * X)
    (hXF : X ≤ F) (hF : (Q - 2) * F ≤ (Q - 1) * Q ^ m) : w ≤ m := by
  by_contra hwm
  push Not at hwm
  have hp : Q ^ (m + 1) ≤ Q ^ w := pow_le_pow_right₀ (by linarith) hwm
  have hZ : 0 < Q ^ m := by positivity
  have e : Q ^ (m + 1) = Q * Q ^ m := by ring
  rw [e] at hp
  have hQ2 : 0 ≤ Q - 2 := by linarith
  have h2 : (Q - 2) * (Q * Q ^ m) ≤ (Q - 2) * S := mul_le_mul_of_nonneg_left (hp.trans hS) hQ2
  have h3 : (Q - 2) * S ≤ (Q - 2) * (2 * X) := mul_le_mul_of_nonneg_left hSX.le hQ2
  have h4 : (Q - 2) * X ≤ (Q - 2) * F := mul_le_mul_of_nonneg_left hXF hQ2
  have h5 : (Q - 2) * (Q * Q ^ m) < 2 * ((Q - 2) * F) := by
    have : (Q - 2) * S < (Q - 2) * (2 * X) := mul_lt_mul_of_pos_left hSX (by linarith)
    linarith
  generalize Q ^ m = Z at hZ hF h5
  nlinarith [mul_nonneg (show 0 ≤ Q - 5 by linarith) hZ.le]

/-- Case of one cyclotomic factor carrying `R ^ 3` with `e = 4`: integers `Q ≥ 5`, `R ≥ 5`,
`S`, `F` with `S (R - 1) < R ^ 5`, `Q ^ w ≤ S`, `R ^ 3 ≤ F` and `(Q - 2) F ≤ (Q - 1) Q ^ m`
satisfy `3 w ≤ 4 m + 1`. -/
theorem srt_case_four {Q R S F : ℤ} {w m : ℕ} (hQ : 5 ≤ Q) (hR : 5 ≤ R)
    (hSR : S * (R - 1) < R ^ 5) (hS : Q ^ w ≤ S) (hRF : R ^ 3 ≤ F)
    (hF : (Q - 2) * F ≤ (Q - 1) * Q ^ m) : 3 * w ≤ 4 * m + 1 := by
  by_contra hwm
  push Not at hwm
  have hp : Q ^ (4 * m + 2) ≤ Q ^ (3 * w) := pow_le_pow_right₀ (by linarith) (by omega)
  have e1 : Q ^ (4 * m + 2) = Q ^ 2 * (Q ^ m) ^ 4 := by ring
  have e2 : Q ^ (3 * w) = (Q ^ w) ^ 3 := by ring
  rw [e1, e2] at hp
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  have hF0 : 0 < F := lt_of_lt_of_le (by positivity) hRF
  have hR1 : 0 < R - 1 := by linarith
  have hQ2 : 0 < Q - 2 := by linarith
  generalize Q ^ m = Z at hp hF
  have hZ : 0 < Z := by
    by_contra hz
    push Not at hz
    have : 0 < (Q - 2) * F := by positivity
    nlinarith
  have h1 : (Q ^ w) ^ 3 ≤ S ^ 3 := pow_le_pow_left₀ (by positivity) hS 3
  have h2 : (S * (R - 1)) ^ 3 < (R ^ 5) ^ 3 := pow_lt_pow_left₀ hSR (by positivity) (by norm_num)
  have h3 : (R ^ 3) ^ 4 ≤ F ^ 4 := pow_le_pow_left₀ (by positivity) hRF 4
  have h4 : ((Q - 2) * F) ^ 4 ≤ ((Q - 1) * Z) ^ 4 := pow_le_pow_left₀ (by positivity) hF 4
  have hc : (Q - 2) ^ 4 * (Q ^ 2 * Z ^ 4) * (R - 1) ^ 3 < R ^ 3 * ((Q - 1) ^ 4 * Z ^ 4) :=
    calc (Q - 2) ^ 4 * (Q ^ 2 * Z ^ 4) * (R - 1) ^ 3
        ≤ (Q - 2) ^ 4 * (Q ^ w) ^ 3 * (R - 1) ^ 3 := by
          have := mul_le_mul_of_nonneg_left hp (show 0 ≤ (Q - 2) ^ 4 by positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ (Q - 2) ^ 4 * S ^ 3 * (R - 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity))
            (by positivity)
      _ = (Q - 2) ^ 4 * (S * (R - 1)) ^ 3 := by ring
      _ < (Q - 2) ^ 4 * (R ^ 5) ^ 3 := mul_lt_mul_of_pos_left h2 (by positivity)
      _ = R ^ 3 * ((Q - 2) ^ 4 * (R ^ 3) ^ 4) := by ring
      _ ≤ R ^ 3 * ((Q - 2) ^ 4 * F ^ 4) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity))
            (by positivity)
      _ = R ^ 3 * ((Q - 2) * F) ^ 4 := by ring
      _ ≤ R ^ 3 * ((Q - 1) * Z) ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = R ^ 3 * ((Q - 1) ^ 4 * Z ^ 4) := by ring
  have h5a : R ^ 3 ≤ 2 * (R - 1) ^ 3 := by nlinarith [sq_nonneg (R - 1), sq_nonneg (R - 5)]
  have h5b : 2 * (Q - 1) ^ 4 ≤ (Q - 2) ^ 4 * Q ^ 2 := by
    obtain ⟨t, rfl⟩ : ∃ t, Q = t + 5 := ⟨Q - 5, by ring⟩
    have ht : 0 ≤ t := by linarith
    have e : (t + 5 - 2) ^ 4 * (t + 5) ^ 2 - 2 * (t + 5 - 1) ^ 4 = t ^ 6 + 22 * t ^ 5 +
        197 * t ^ 4 + 916 * t ^ 3 + 2319 * t ^ 2 + 2998 * t + 1513 := by ring
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6]
  have h6 : R ^ 3 * (Q - 1) ^ 4 ≤ (R - 1) ^ 3 * ((Q - 2) ^ 4 * Q ^ 2) := by
    have := mul_le_mul h5a h5b (by positivity) (by positivity)
    nlinarith [pow_pos hR1 3]
  have hZ4 : 0 < Z ^ 4 := by positivity
  have h7 := mul_le_mul_of_nonneg_right h6 hZ4.le
  nlinarith

/-- `σ(M) < 2 M` for `M = L ^ g R ^ e`, in integers: if `A (L - 1) = L X - 1`,
`B (R - 1) = R Y - 1`, `L ≥ 7`, `R ≥ 8`, `X, Y ≥ 1`, then `A B < 2 X Y`. -/
theorem srt_sigma_lt_two_mul {L R A B X Y : ℤ} (hL : 7 ≤ L) (hR : 8 ≤ R) (hX : 1 ≤ X)
    (hY : 1 ≤ Y) (hA : A * (L - 1) = L * X - 1) (hB : B * (R - 1) = R * Y - 1) :
    A * B < 2 * (X * Y) := by
  have hD1 : (A - X) * (L - 1) = X - 1 := by linear_combination hA
  have hD2 : (B - Y) * (R - 1) = Y - 1 := by linear_combination hB
  have h1 : 0 ≤ A - X := by nlinarith
  have h2 : 0 ≤ B - Y := by nlinarith
  have h3 : 6 * (A - X) < X := by nlinarith
  have h4 : 7 * (B - Y) < Y := by nlinarith
  generalize hDd : A - X = D at h1 h3 hD1
  generalize hEd : B - Y = E at h2 h4 hD2
  obtain rfl : A = X + D := by linarith
  obtain rfl : B = Y + E := by linarith
  nlinarith [mul_le_mul h3.le h4.le (by linarith) (by linarith), mul_nonneg h1 h2,
    mul_lt_mul_of_pos_right h3 (show 0 < Y by linarith),
    mul_lt_mul_of_pos_left h4 (show 0 < X by linarith)]

/-- The gap inequality for `M = L ^ g R ^ e`, in integers: if `A (L - 1) = L X - 1`,
`B (R - 1) = R Y - 1`, `1 < L ≤ R`, `X, Y ≥ 1`, `Q ≥ 0`, and `C X Y < Q (A B - X Y)`, then
`C (L - 1) < 3 Q`. -/
theorem srt_gap {L R A B X Y Q C : ℤ} (hL : 1 < L) (hLR : L ≤ R) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hQ : 0 ≤ Q) (hA : A * (L - 1) = L * X - 1) (hB : B * (R - 1) = R * Y - 1)
    (hgap : C * (X * Y) < Q * (A * B - X * Y)) : C * (L - 1) < 3 * Q := by
  have hD1 : (A - X) * (L - 1) = X - 1 := by linear_combination hA
  have hD2 : (B - Y) * (R - 1) = Y - 1 := by linear_combination hB
  have h1 : 0 ≤ A - X := by nlinarith
  have h2 : 0 ≤ B - Y := by nlinarith
  have hBY : B < 2 * Y := by nlinarith
  have hk : (A * B - X * Y) * (L - 1) < 3 * (X * Y) := by
    have e : (A * B - X * Y) * (L - 1) = (A - X) * (L - 1) * B + X * ((B - Y) * (L - 1)) := by
      ring
    have h5 : (B - Y) * (L - 1) ≤ (B - Y) * (R - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    have h6 : X * ((B - Y) * (L - 1)) ≤ X * (Y - 1) := by
      rw [← hD2]; exact mul_le_mul_of_nonneg_left h5 (by linarith)
    rw [e, hD1]
    nlinarith
  have hL1 : 0 < L - 1 := by linarith
  have hXY : 0 < X * Y := by positivity
  have h7 : C * (X * Y) * (L - 1) < Q * (A * B - X * Y) * (L - 1) :=
    mul_lt_mul_of_pos_right hgap hL1
  have h8 : Q * ((A * B - X * Y) * (L - 1)) ≤ Q * (3 * (X * Y)) :=
    mul_le_mul_of_nonneg_left hk.le hQ
  have h9 : C * (L - 1) * (X * Y) < 3 * Q * (X * Y) := by nlinarith
  exact lt_of_mul_lt_mul_right h9 hXY.le

end OddPerfect

#print axioms OddPerfect.sub_two_mul_cyclotomic_eval_le
#print axioms OddPerfect.pow_dvd_cyclotomic_orderOf_of_not_dvd_succ
#print axioms OddPerfect.sub_two_mul_pow_le_of_pow_dvd_sigma
#print axioms OddPerfect.two_mul_totient_two_mul_le
#print axioms OddPerfect.srt_case_one
#print axioms OddPerfect.srt_case_four
#print axioms OddPerfect.srt_sigma_lt_two_mul
#print axioms OddPerfect.srt_gap
