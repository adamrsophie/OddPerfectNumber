import OddPerfect.RestrainedEighteen
import OddPerfect.RestrainedTwentyWheel

/-!
# Restrained odd perfect numbers: wheel packing on a smaller residue set

Setting of `restrained_omega_ge_wheel` (`OddPerfect.RestrainedEighteen`): `N` is an odd perfect
number with special prime `q`, every prime factor other than `q` and `3` has exponent 2, and
`R`, the prime factors other than `3` and `q`, consists of `Good` primes at least
`B = 132257`. The counted certificate `certC_all` leaves at most `d = 9063` members of `R` up
to `X = 10 ^ 6`.

`RestrainedEighteen` places the members of `R` above `X` in the residue classes prime to
`30030`. Here the modulus is `W = 51870 = 2 · 3 · 5 · 7 · 13 · 19`. A member `t` of `R` is
`Good`: no odd number `w` with `2 ≤ w < B` and prime to 3 divides `t ^ 2 + t + 1`. As `7`,
`13` and `19` divide `W`, the residue of `t` modulo `W` lies in `J20`, the residues `a` prime
to `W` with `a ^ 2 + a + 1` prime to `7 · 13 · 19` (`mem_J20`); `J20` has `5120` members
(`card_J20`, one kernel computation). The special prime `q` keeps its own factor
`B/(B - 1)` as before. The counting step `card_gt_of_wheel_on` (wheel packing `wheel_pow_le_on` of
`OddPerfect.RestrainedTwentyWheel`) reduces to one comparison of integers of about 5.4 million
bits (`final_ineq20`), which gives `#R ≥ 1338850`, hence `ω(N) ≥ 1338852`
(`restrained_omega_ge_wheel_res`), `v_3(N) ≥ 669426` (`restrained_three_ge_wheel_res`) and
`Ω(N) ≥ 3347127` (`restrained_Omega_ge_wheel_res`).

This is a restricted family, and these are lower bounds only; the family is not excluded. The
published comparator, Ochem and Zelinsky (2026 preprint, arXiv 2607.19746), states
`v_3(N) ≥ 23000000000` for this family, obtained by a long computation; that bound is not proved
here. Novelty is not verified. The odd perfect number conjecture is open and nothing here
decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

namespace RestrainedTwenty

open RestrainedSeven RestrainedEight RestrainedElevenCheck RestrainedEleven RestrainedSixteen
open RestrainedEighteen

/-- **The counting step on a residue set.** Setting of `card_gt_of_wheel`, with a set `J` of
`φ > 0` residues modulo `W` that contains the residue of every `Good` prime above `X`. Then
`M + d < #R`. -/
theorem card_gt_of_wheel_on {N q X B c a b d M W φ D Ep Em : ℕ} (J : Finset ℕ)
    (h : OddPerfect N) (h3 : 3 ∣ N)
    (hqN : q ∈ N.primeFactors) (hq3 : q ≠ 3) (hBc : B = c + 1) (hc : 1 ≤ c) (hqB : B ≤ q)
    (hR : ∀ r ∈ (N.primeFactors.erase 3).erase q, Good r ∧ B ≤ r) (hW : 0 < W) (hWX : W ≤ X)
    (hJ : J.card = φ) (hφ0 : 0 < φ) (hJm : ∀ t, t.Prime → X < t → Good t → t % W ∈ J)
    (hD : D + W = 2 * X + 1) (hEp : Ep = 2 * X + 1 + d)
    (hEm : Em + d = 2 * X + 1) (hEm0 : 0 < Em) (hcert : CertC X B (X + 1) a b d) (ha : 0 < a)
    (hineq : (3 * B * b * Ep) ^ W * (φ * D + 2 * W * M) ^ φ ≤
      (4 * c * a * Em) ^ W * (φ * D) ^ φ) :
    M + d < ((N.primeFactors.erase 3).erase q).card := by
  classical
  subst hBc
  set R := (N.primeFactors.erase 3).erase q with hRdef
  obtain ⟨-, T, hT, hcov, hcard, hprod⟩ := hcert
  have hgt := prod_erase_three_gt h h3
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [← Finset.mul_prod_erase _ _ hqm] at hgt
  have hrp : ∀ r ∈ R, r.Prime := fun r hr =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hX1 : 1 ≤ X := by omega
  set y : ℚ := ((X + 1 : ℚ) / X) with hy
  have hX' : (0 : ℚ) < X := by exact_mod_cast hX1
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ hX']
    linarith
  have hy0 : 0 ≤ y := by linarith
  have hF0 : ∀ n, 0 ≤ fac X n := fac_nonneg X
  -- the component of `q`
  have hAq : abundancy (q ^ N.factorization q) ≤ ((c + 1 : ℕ) : ℚ) / c :=
    (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hqN) _).le.trans
      (div_pred_le hc hqB)
  -- the components of `R`
  have hP0 : 0 ≤ ∏ r ∈ R, abundancy (r ^ N.factorization r) :=
    Finset.prod_nonneg fun r hr => (abundancy_pos (pow_ne_zero _ (hrp r hr).ne_zero)).le
  have hP1 : ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ ∏ r ∈ R, y * fac X r := by
    refine Finset.prod_le_prod₀ (fun r hr => (abundancy_pos (pow_ne_zero _
      (hrp r hr).ne_zero)).le) fun r hr => ?_
    rw [hy, ← div_pred_eq hX1 (hrp r hr).two_le]
    exact (abundancy_prime_pow_lt (hrp r hr) _).le
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hP1
  -- the split at `X`
  set Rhi := R.filter (fun r => X + 1 ≤ r) with hRhi
  set Rlo := R.filter (fun r => ¬ X + 1 ≤ r) with hRlo
  have hlo_sub : Rlo ⊆ T := fun r hr => by
    obtain ⟨hrR, hrX⟩ := Finset.mem_filter.mp hr
    exact hcov r (hR r hrR).2 (by omega) (hrp r hrR) (hR r hrR).1
  have hlo_card : Rlo.card ≤ d := (Finset.card_le_card hlo_sub).trans hcard
  have hsplit : Rhi.card + Rlo.card = R.card := Finset.card_filter_add_card_filter_not _
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (s := Rhi) (n := R.card - d)
    (by omega)
  have hS : ∀ t ∈ S, X + 1 ≤ t ∧ t.Prime ∧ Good t := fun t ht => by
    obtain ⟨htR, htX⟩ := Finset.mem_filter.mp (hSsub ht)
    exact ⟨htX, hrp t htR, (hR t htR).1⟩
  have hfR : ∏ r ∈ R, fac X r = (∏ r ∈ Rhi, fac X r) * ∏ r ∈ Rlo, fac X r :=
    (Finset.prod_filter_mul_prod_filter_not R _ _).symm
  have hlo : ∏ r ∈ Rlo, fac X r ≤ ∏ n ∈ T, fac X n := by
    refine Finset.prod_le_prod_of_subset_of_one_le₀ hlo_sub (fun r _ => hF0 r) fun n hn _ => ?_
    have := hT n hn
    exact one_le_fac (by omega) (by omega)
  have hhi : ∏ r ∈ Rhi, fac X r ≤ ∏ r ∈ S, fac X r := by
    refine Finset.prod_le_prod_of_subset_of_le_one₀ hSsub (fun r _ => hF0 r) fun r hr _ => ?_
    exact fac_le_one hX1 (Finset.mem_filter.mp hr).2
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hTb : ∏ n ∈ T, fac X n ≤ (b : ℚ) / a := by
    rw [le_div_iff₀ ha', mul_comm]
    exact hprod
  -- the tail
  set P := ∏ t ∈ S, (t : ℚ) / (t - 1) with hP
  have hPeq : P = y ^ S.card * ∏ t ∈ S, fac X t := by
    rw [hP, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [hy, ← div_pred_eq hX1 (hS t ht).2.1.two_le]
  have hP0' : 0 ≤ P := by
    rw [hPeq]
    exact mul_nonneg (pow_nonneg hy0 _) (Finset.prod_nonneg fun t _ => hF0 t)
  have hJne : J.Nonempty := Finset.card_pos.mp (hJ ▸ hφ0)
  have hPW : P ^ W ≤ (1 + 2 * (W : ℚ) * S.card / (J.card * (2 * ((X + 1 : ℕ) : ℚ) - W - 1)))
      ^ J.card :=
    wheel_pow_le_on hW (by omega) J hJne S fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hS t ht
      exact ⟨h1, hJm t h2 (by omega) h3⟩
  -- assembling
  by_contra hK
  have hSM : S.card ≤ M := by omega
  have hyR : y ^ R.card ≤ y ^ d * y ^ S.card := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hy1 (by omega)
  have hmain : ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ y ^ d * ((b : ℚ) / a) * P := by
    have hT0 : 0 ≤ ∏ n ∈ T, fac X n := Finset.prod_nonneg fun n _ => hF0 n
    have hS0 : 0 ≤ ∏ r ∈ S, fac X r := Finset.prod_nonneg fun r _ => hF0 r
    have hlo0 : 0 ≤ ∏ r ∈ Rlo, fac X r := Finset.prod_nonneg fun r _ => hF0 r
    have hfac : ∏ r ∈ R, fac X r ≤ (∏ r ∈ S, fac X r) * ∏ n ∈ T, fac X n := by
      rw [hfR]
      exact mul_le_mul hhi hlo hlo0 hS0
    calc ∏ r ∈ R, abundancy (r ^ N.factorization r) ≤ y ^ R.card * ∏ r ∈ R, fac X r := hP1
      _ ≤ (y ^ d * y ^ S.card) * ((∏ r ∈ S, fac X r) * ((b : ℚ) / a)) :=
          mul_le_mul hyR (hfac.trans (mul_le_mul_of_nonneg_left hTb hS0))
            (Finset.prod_nonneg fun r _ => hF0 r) (by positivity)
      _ = y ^ d * ((b : ℚ) / a) * P := by rw [hPeq]; ring
  -- the power of `y`
  have hEm' : (Em : ℚ) + d = 2 * X + 1 := by exact_mod_cast hEm
  have hEm0' : (0 : ℚ) < Em := by exact_mod_cast hEm0
  have hEp' : (Ep : ℚ) = 2 * X + 1 + d := by exact_mod_cast hEp
  have hyd : y ^ d ≤ (Ep : ℚ) / Em := by
    have h1 := ratio_pow_le (x := (X : ℚ) + 1) (n := d) (by linarith) (by linarith)
    have e1 : ((X : ℚ) + 1) / ((X : ℚ) + 1 - 1) = y := by rw [hy]; ring_nf
    have e2 : (2 * ((X : ℚ) + 1) + d - 1) / (2 * ((X : ℚ) + 1) - d - 1) = (Ep : ℚ) / Em := by
      rw [hEp', show (Em : ℚ) = 2 * X + 1 - d by linarith]
      ring_nf
    rwa [e1, e2] at h1
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  have hb0 : (0 : ℚ) ≤ b := by positivity
  have hlt : (4 : ℚ) / 3 < ((c : ℚ) + 1) / c * ((Ep : ℚ) / Em * ((b : ℚ) / a)) * P := by
    refine lt_of_lt_of_le hgt ?_
    have hba : (0 : ℚ) ≤ (b : ℚ) / a := by positivity
    calc abundancy (q ^ N.factorization q) * ∏ r ∈ R, abundancy (r ^ N.factorization r)
        ≤ ((c + 1 : ℕ) : ℚ) / c * (y ^ d * ((b : ℚ) / a) * P) :=
          mul_le_mul hAq hmain hP0 (by positivity)
      _ ≤ ((c + 1 : ℕ) : ℚ) / c * ((Ep : ℚ) / Em * ((b : ℚ) / a) * P) := by
          gcongr
      _ = ((c : ℚ) + 1) / c * ((Ep : ℚ) / Em * ((b : ℚ) / a)) * P := by push_cast; ring
  -- one power `W`
  set U : ℚ := 4 * c * a * Em with hU
  set V : ℚ := 3 * ((c : ℚ) + 1) * b * Ep with hV
  have hU0 : 0 < U := by positivity
  have hUV : U < V * P := by
    have e : ((c : ℚ) + 1) / c * ((Ep : ℚ) / Em * ((b : ℚ) / a)) * P =
        (((c : ℚ) + 1) * Ep * b * P) / (c * Em * a) := by
      field_simp
    rw [e, lt_div_iff₀ (by positivity)] at hlt
    rw [hU, hV]
    linarith
  have hWne : W ≠ 0 := by omega
  have hUW : U ^ W < V ^ W * P ^ W := by
    rw [← mul_pow]
    exact pow_lt_pow_left₀ hUV hU0.le hWne
  -- the tail with `M`
  have hD' : (D : ℚ) + W = 2 * X + 1 := by exact_mod_cast hD
  have hD0 : (0 : ℚ) < D := by
    have : (W : ℚ) ≤ X := by exact_mod_cast hWX
    linarith
  set G : ℚ := (φ : ℚ) * D with hG
  set H : ℚ := (φ : ℚ) * D + 2 * W * M with hH
  have hG0 : 0 < G := by positivity
  have hPH : P ^ W ≤ (H / G) ^ φ := by
    refine hPW.trans ?_
    rw [hJ]
    have hSM' : (S.card : ℚ) ≤ M := by exact_mod_cast hSM
    have e : (2 * (((X + 1 : ℕ)) : ℚ) - W - 1) = D := by push_cast; linarith
    rw [e]
    have e2 : H / G = 1 + 2 * (W : ℚ) * M / (φ * D) := by
      rw [hH, hG]
      field_simp
    rw [e2]
    have h0 : (0 : ℚ) ≤ 2 * (W : ℚ) * S.card / (φ * D) := by positivity
    gcongr
  have hVW : 0 ≤ V ^ W := by positivity
  have hfin : U ^ W * G ^ φ < V ^ W * H ^ φ := by
    have h1 : U ^ W < V ^ W * (H / G) ^ φ :=
      hUW.trans_le (mul_le_mul_of_nonneg_left hPH hVW)
    rw [div_pow, mul_div_assoc', lt_div_iff₀ (by positivity)] at h1
    exact h1
  have hq : ((3 * (c + 1) * b * Ep) ^ W * (φ * D + 2 * W * M) ^ φ : ℕ) ≤
      (((4 * c * a * Em) ^ W * (φ * D) ^ φ : ℕ) : ℚ) := by
    exact_mod_cast hineq
  push_cast at hq
  rw [hU, hV, hG, hH] at hfin
  linarith

/-- The residues `a < 51870` prime to `51870` with `a ^ 2 + a + 1` divisible by none of `7`,
`13`, `19`. -/
def J20 : Finset ℕ := (Finset.range 51870).filter fun a => Nat.Coprime 51870 a ∧
  (a * a + a + 1) % 7 ≠ 0 ∧ (a * a + a + 1) % 13 ≠ 0 ∧ (a * a + a + 1) % 19 ≠ 0

/-- `J20` has `5120 = 1 · 2 · 4 · 4 · 10 · 16` members (one kernel computation). -/
theorem card_J20 : J20.card = 5120 := by decide +kernel

/-- For a `Good` number `t` and an odd divisor `p` of `51870` with `2 ≤ p < 132257` and `p`
prime to 3, `p` does not divide `a ^ 2 + a + 1` for the residue `a` of `t` modulo `51870`. -/
theorem res_mod_ne {t p : ℕ} (hG : Good t) (hp2 : 2 ≤ p) (hpB : p < 132257) (hpo : p % 2 = 1)
    (hp3 : p % 3 ≠ 0) (hpW : p ∣ 51870) :
    (t % 51870 * (t % 51870) + t % 51870 + 1) % p ≠ 0 := by
  have h1 : t % 51870 ≡ t [MOD p] := Nat.mod_mod_of_dvd t hpW
  have e : t % 51870 * (t % 51870) + t % 51870 + 1 ≡ t * t + t + 1 [MOD p] :=
    ((h1.mul h1).add h1).add_right 1
  intro h0
  unfold Nat.ModEq at e
  rw [e] at h0
  exact hG p hp2 hpB hpo hp3 (Nat.dvd_of_mod_eq_zero h0)

/-- **Membership.** The residue modulo `51870` of a `Good` prime `t > 51870` lies in `J20`. -/
theorem mem_J20 {t : ℕ} (ht : t.Prime) (hlt : 51870 < t) (hG : Good t) : t % 51870 ∈ J20 := by
  have hcop : Nat.Coprime 51870 t :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd ht).mpr fun hdvd => by
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega)
  have hcop' : Nat.Coprime 51870 (t % 51870) := by
    unfold Nat.Coprime at hcop ⊢
    rw [Nat.gcd_comm, ← Nat.gcd_rec]
    exact hcop
  simp only [J20, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.mod_lt _ (by norm_num), hcop',
    res_mod_ne hG (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    res_mod_ne hG (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    res_mod_ne hG (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- The one large comparison, on integers of about 5.4 million bits (`W = 51870`,
`#J20 = 5120`, `D = 1948131`, `M = 1329786`). -/
theorem final_ineq20 : (3 * 132257 * 18677387639328032348 * 2009064) ^ 51870 *
    (5120 * 1948131 + 2 * 51870 * 1329786) ^ 5120 ≤
    (4 * 132256 * 18446744073709551616 * 1990938) ^ 51870 * (5120 * 1948131) ^ 5120 := by
  decide +kernel

end RestrainedTwenty

open RestrainedSeven RestrainedEight RestrainedElevenCheck RestrainedEleven RestrainedSixteen
open RestrainedEighteen RestrainedTwenty

/-- **Restrained family: `ω(N) ≥ 1338852`.** With the hypotheses of `restrained_omega_ge_wheel`,
the counted sieve certificate and the packing of the prime factors above `10 ^ 6` in the
`5120` residue classes `J20` modulo `51870` force at least 1338850 prime factors other than 3
and `q`. A restricted family; a lower bound only; the family is not excluded. Conditional
family result checked by the kernel; novelty is not verified. -/
theorem restrained_omega_ge_wheel_res {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    1338852 ≤ ω N := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h3 := restrained_three_dvd h hq hodd hr hrq hsq
  have hq3 : q ≠ 3 := by have := F.mod12; omega
  have hqN : q ∈ N.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq, ?_, h.ne_zero⟩
    obtain ⟨k, hk⟩ := hodd
    exact Nat.dvd_of_factorization_pos (by omega)
  have hlt := card_gt_of_wheel_on (B := 132257) (c := 132256) (X := 1000000) (d := 9063)
    (M := 1329786) (W := 51870) (φ := 5120) (D := 1948131) (Ep := 2009064) (Em := 1990938)
    J20 h h3 hqN hq3 rfl (by norm_num) (restrained_le_of_ne_three h hq hodd hr hrq hsq hqN hq3)
    (fun t ht => by
      obtain ⟨htq, ht'⟩ := Finset.mem_erase.mp ht
      obtain ⟨ht3, htN⟩ := Finset.mem_erase.mp ht'
      exact ⟨good_of_mem h hq hodd hr hrq hsq htN htq ht3,
        restrained_le_of_ne_three h hq hodd hr hrq hsq htN ht3⟩)
    (by norm_num) (by norm_num) card_J20 (by norm_num)
    (fun t ht hX hG => mem_J20 ht (by omega) hG) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) certC_all (by norm_num) final_ineq20
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hqm : q ∈ N.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨hq3, hqN⟩
  rw [Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem h3m] at hlt
  rw [cardDistinctFactors_eq_card_primeFactors]
  omega

/-- **Restrained family: `v_3(N) ≥ 669426`.** From `ω(N) ≥ 1338852`, `ω(N) ≤ 2 v_3(N) + 3`
(`restrained_omega_le`) and the evenness of `v_3(N)` (`restrained_exception_eq_three`).
Ochem and Zelinsky (2026 preprint, arXiv 2607.19746) state `v_3(N) ≥ 23000000000` for this
family, obtained by a long computation; it is not proved here. A restricted family; a lower
bound only; the family is not excluded. Novelty is not verified. -/
theorem restrained_three_ge_wheel_res {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    669426 ≤ N.factorization 3 := by
  have h1 := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h2 := restrained_omega_le h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨k, hk⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  omega

/-- **Restrained family: `Ω(N) ≥ 3347127`.** From `ω(N) ≥ 1338852`, `v_3(N) ≥ 669426` and
`2 ω(N) + v_3(N) ≤ Ω(N) + 3`. A restricted family; a lower bound only; the family is not
excluded. Novelty is not verified. -/
theorem restrained_Omega_ge_wheel_res {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    3347127 ≤ Ω N := by
  have h1 := restrained_omega_ge_wheel_res h hq hodd hr hrq hsq
  have h2 := restrained_three_ge_wheel_res h hq hodd hr hrq hsq
  have h3 := two_mul_card_add_factorization_three_le h
  omega

end OddPerfect

#print axioms OddPerfect.RestrainedTwenty.card_gt_of_wheel_on
#print axioms OddPerfect.RestrainedTwenty.card_J20
#print axioms OddPerfect.RestrainedTwenty.res_mod_ne
#print axioms OddPerfect.RestrainedTwenty.mem_J20
#print axioms OddPerfect.RestrainedTwenty.final_ineq20
#print axioms OddPerfect.restrained_omega_ge_wheel_res
#print axioms OddPerfect.restrained_three_ge_wheel_res
#print axioms OddPerfect.restrained_Omega_ge_wheel_res
