import OddPerfect.LargePrimes
import OddPerfect.EulerPart
import OddPerfect.Cyclotomic
import OddPerfect.EulerIndexPrimePower

/-!
# The special prime against the square root part

For an odd perfect number in Euler's form `N = q ^ k * m ^ 2` (special prime `q`, `q ∤ m`),
Dris conjectured `q ^ k < m`; the weaker `q < m` is claimed by Brown (2016 preprint, arXiv
1602.01591). This module does not use that preprint. It proves `q < m` outside one exceptional
shape with `k = 1`, and it proves that in that shape `m < q` holds; so `q < m` for every odd
perfect number is equivalent to the impossibility of the shape, which is not decided here.
How the literature treats that shape was not checked.

Here:

* `special_lt_of_exponent_ne_one`: `q < m` whenever `k ≠ 1` (from the landed
  `exponent_eq_one_of_lt`).
* `special_lt_or_shape_of_exponent_one`: for `k = 1`, either `q < m`, or there is a prime
  `p ∣ m` with exponent `e` in `N` such that `σ(p ^ e) = q`, `2 m ^ 2 = p ^ e (q + 1)` and
  `σ((q + 1) / 2) = p ^ e`; that is, `N = q * p ^ e * ((q + 1) / 2)`.
* `lt_special_of_shape`: that exceptional shape forces `m < q`, so for `k = 1` the inequality
  `m < q` holds exactly in the exceptional shape (`lt_special_iff_shape`).
* `special_lt_or_index_prime_pow`: in the exceptional shape the Euler index `σ(m ^ 2) / q` is
  the full component `p ^ e`, and `e + 1` is prime; this is the prime power index case of
  `OddPerfect/EulerIndexPrimePower.lean`.

The argument (an extension of Acquaah and Konyagin's): let `p` be the prime with
`q ∣ σ(p ^ e)`, `σ(p ^ e) = q u`, `m ^ 2 = p ^ e M`, `x = gcd(q + 1, p ^ e)`. Then
`(q + 1) u σ(M) = 2 p ^ e M`, `σ(M) = (p ^ e / x) T`, and `p ^ (e + 1) = (p - 1) u q + 1`.
With `X = (p - 1) u`, the bound `X ^ 2 T ≥ 2 x p (p - 1)` gives `q ^ 2 < m ^ 2`. It holds
except for `x = u = T = 1` (the exceptional shape) and `p = 3, x = 9, u = 5, T = 1`, which is
impossible because `3 ^ (e + 1) = 10 q + 1` has no solution with `e` even. Whether the
exceptional shape can occur is not decided here.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(q ^ 1) = q + 1`. -/
private lemma sigma_prime_one' {q : ℕ} (hq : q.Prime) : σ 1 (q ^ 1) = q + 1 := by
  rw [sigma_one_apply_prime_pow hq]
  simp [Finset.sum_range_succ, add_comm]

private lemma nine_pow_mod_five (j : ℕ) : 9 ^ j % 5 = 1 ∨ 9 ^ j % 5 = 4 := by
  induction j with
  | zero => left; rfl
  | succ j ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- The final size step: `X ^ 2 T ≥ 2 x p (p - 1)` gives `q ^ 2 < x P' M'` (with `p = w + 3`
and `X = (w + 2) u`). -/
private lemma final_arith {w q u T x P' M' Q' : ℕ}
    (hpP : (w + 3) * (x * P') = (w + 2) * u * q + 1) (hrel : Q' * u * T = 2 * M')
    (hQ : q + 1 = x * Q') (hkey : 2 * x * (w + 3) * (w + 2) ≤ ((w + 2) * u) ^ 2 * T)
    (hu : 1 ≤ u) (hT : 1 ≤ T) : q ^ 2 < x * P' * M' := by
  set X := (w + 2) * u with hX
  have hX0 : 0 < X := Nat.mul_pos (by omega) hu
  have e : 2 * x * (w + 3) * (w + 2) * (x * P' * M') = (X * q + 1) * X * T * (q + 1) := by
    calc 2 * x * (w + 3) * (w + 2) * (x * P' * M')
        = (w + 2) * x * ((w + 3) * (x * P')) * (2 * M') := by ring
      _ = (w + 2) * x * (X * q + 1) * (Q' * u * T) := by rw [hpP, hrel]
      _ = (X * q + 1) * X * T * (x * Q') := by rw [hX]; ring
      _ = _ := by rw [← hQ]
  have e2 : (X * q + 1) * X * T * (q + 1) = X ^ 2 * T * q ^ 2 + X * T * (X * q + q + 1) := by
    ring
  have hlt : 2 * x * (w + 3) * (w + 2) * q ^ 2 < 2 * x * (w + 3) * (w + 2) * (x * P' * M') := by
    rw [e, e2]
    calc 2 * x * (w + 3) * (w + 2) * q ^ 2 ≤ X ^ 2 * T * q ^ 2 := Nat.mul_le_mul_right _ hkey
      _ < X ^ 2 * T * q ^ 2 + X * T * (X * q + q + 1) :=
          Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.mul_pos hX0 (by omega)) (by omega))
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- The case analysis behind the bound `X ^ 2 T ≥ 2 x p (p - 1)` (with `p = w + 3`). -/
private lemma case_bound {w u T x a : ℕ} (hu : Odd u) (hT : Odd T) (hxa : x = (w + 3) ^ a)
    (hu2 : 1 < x → 2 * (w + 3) ≤ u + 1) (hdx : x ∣ (w + 2) * u - 1)
    (hexc : w = 0 → u ≠ 5) :
    (x = 1 ∧ u = 1 ∧ T = 1) ∨ 2 * x * (w + 3) * (w + 2) ≤ ((w + 2) * u) ^ 2 * T := by
  obtain ⟨t, rfl⟩ := hT
  have hu1 : 1 ≤ u := by obtain ⟨v, rfl⟩ := hu; omega
  rcases a with _ | _ | a
  · -- `x = 1`
    simp only [pow_zero] at hxa
    subst hxa
    by_cases hc : u = 1 ∧ 2 * t + 1 = 1
    · left; exact ⟨rfl, hc⟩
    right
    have h3 : 3 ≤ u * u * (2 * t + 1) := by
      rcases Nat.lt_or_ge t 1 with ht | ht
      · have ht0 : t = 0 := by omega
        subst ht0
        have : u ≠ 1 := fun h1 => hc ⟨h1, rfl⟩
        have hu3 : 3 ≤ u := by obtain ⟨v, rfl⟩ := hu; omega
        nlinarith
      · nlinarith
    calc 2 * 1 * (w + 3) * (w + 2) ≤ (w + 2) * (w + 2) * 3 := by nlinarith
      _ ≤ (w + 2) * (w + 2) * (u * u * (2 * t + 1)) := Nat.mul_le_mul_left _ h3
      _ = ((w + 2) * u) ^ 2 * (2 * t + 1) := by ring
  · -- `x = p`
    simp only [zero_add, pow_one] at hxa
    subst hxa
    right
    have hu5 : 2 * w + 5 ≤ u := by have := hu2 (by omega); omega
    have hXb : (w + 2) * (2 * w + 5) ≤ (w + 2) * u := Nat.mul_le_mul_left _ hu5
    have hsq : ((w + 2) * (2 * w + 5)) ^ 2 ≤ ((w + 2) * u) ^ 2 := Nat.pow_le_pow_left hXb 2
    calc 2 * (w + 3) * (w + 3) * (w + 2) ≤ ((w + 2) * (2 * w + 5)) ^ 2 := by nlinarith
      _ ≤ ((w + 2) * u) ^ 2 := hsq
      _ ≤ ((w + 2) * u) ^ 2 * (2 * t + 1) := Nat.le_mul_of_pos_right _ (by omega)
  · -- `x = p ^ (a + 2)`
    right
    have hx2 : (w + 3) ^ 2 ≤ x := by
      rw [hxa]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h1x : 1 < x := lt_of_lt_of_le (Nat.one_lt_pow (by norm_num) (by omega)) hx2
    have hu5 : 2 * w + 5 ≤ u := by have := hu2 h1x; omega
    set X := (w + 2) * u with hX
    have hXb : (w + 2) * (2 * w + 5) ≤ X := Nat.mul_le_mul_left _ hu5
    obtain ⟨j, hj⟩ := hdx
    have hX10 : 10 ≤ X := by nlinarith
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hj; omega
      · exact h0
    have hXx : x + 1 ≤ X := by have := Nat.le_mul_of_pos_right x hj1; omega
    rcases Nat.lt_or_ge t 1 with ht | ht
    · have ht0 : t = 0 := by omega
      subst ht0
      simp only [mul_zero, zero_add, mul_one]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1' : j = 1 := by omega
        subst hj1'
        have hXe : X = x + 1 := by omega
        -- `p - 1` divides `x - 1` and `x + 1`, so `p = 3`.
        have hd1 : w + 2 ∣ x - 1 := by
          have := Nat.sub_dvd_pow_sub_pow (w + 3) 1 (a + 2)
          rw [one_pow, show w + 3 - 1 = w + 2 by omega, ← hxa] at this
          exact this
        have hd2 : w + 2 ∣ x + 1 := hXe ▸ (Dvd.intro u rfl)
        have hd : w + 2 ∣ 2 := by
          have := Nat.dvd_sub hd2 hd1
          rwa [show x + 1 - (x - 1) = 2 by omega] at this
        have hw : w = 0 := by have := Nat.le_of_dvd (by norm_num) hd; omega
        subst hw
        rcases a with _ | a
        · exfalso
          norm_num at hxa
          subst hxa
          exact hexc rfl (by omega)
        · have h27 : 27 ≤ x := by
            rw [hxa]
            calc 27 = (0 + 3) ^ 3 := by norm_num
              _ ≤ (0 + 3) ^ (a + 1 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [hXe]
          nlinarith
      · have h2x : 2 * x + 1 ≤ X := by have := Nat.mul_le_mul_left x hj2; omega
        have hpx : (w + 3) * (w + 2) ≤ X := by nlinarith
        calc 2 * x * (w + 3) * (w + 2) = (2 * x) * ((w + 3) * (w + 2)) := by ring
          _ ≤ X * X := Nat.mul_le_mul (by omega) hpx
          _ = X ^ 2 := by ring
    · have hT3 : 3 ≤ 2 * t + 1 := by omega
      have h23 : 2 * (w + 3) ≤ 3 * (2 * w + 5) := by omega
      calc 2 * x * (w + 3) * (w + 2) = (x * (w + 2)) * (2 * (w + 3)) := by ring
        _ ≤ (x * (w + 2)) * (3 * (2 * w + 5)) := Nat.mul_le_mul_left _ h23
        _ = 3 * (x * ((w + 2) * (2 * w + 5))) := by ring
        _ ≤ 3 * (X * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hXb)
        _ = X ^ 2 * 3 := by ring
        _ ≤ X ^ 2 * (2 * t + 1) := Nat.mul_le_mul_left _ hT3

/-- Exponent one: either `q < m`, or `N = q * p ^ e * ((q + 1) / 2)` for a prime `p ∣ m` with
exponent `e` in `N`, `σ(p ^ e) = q` and `σ((q + 1) / 2) = p ^ e`. This proves
`q < m` for `k = 1` apart from that one exceptional shape. -/
theorem special_lt_or_shape_of_exponent_one {N q m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ 1 * m ^ 2) (hqm : ¬ q ∣ m) :
    q < m ∨ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ 2 * m ^ 2 = p ^ N.factorization p * (q + 1) ∧
      σ 1 (p ^ N.factorization p) = q ∧ σ 1 ((q + 1) / 2) = p ^ N.factorization p := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hN0 := h.ne_zero
  have hq1 : q ^ 1 ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfq : N.factorization q = 1 := by
    rw [hN, Nat.factorization_mul hq1 hm2, Finsupp.add_apply, Nat.factorization_pow,
      Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply, hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hq4 := (special_mod_four h hq (by rw [hfq]; exact odd_one)).1
  have hq2 : q ≠ 2 := by omega
  have hqN : q ∣ N := hN ▸ (dvd_mul_of_dvd_left (dvd_pow_self q one_ne_zero) _)
  have hqmem : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, hN0⟩
  obtain ⟨p, hpq, hpmem, -, hqd⟩ := exists_sigmaEdge_into h.perfect hqmem hq2
  have hp := Nat.prime_of_mem_primeFactors hpmem
  have hpN := Nat.dvd_of_mem_primeFactors hpmem
  have hpq1 : ¬ p ∣ q ^ 1 := by
    rw [pow_one]; intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  have hpm2 : p ∣ m ^ 2 := by
    rw [hN] at hpN
    exact (Nat.Coprime.dvd_of_dvd_mul_left ((hp.coprime_iff_not_dvd).mpr hpq1) hpN)
  have hpm : p ∣ m := hp.dvd_of_dvd_pow hpm2
  have hfp : N.factorization p = (m ^ 2).factorization p := by
    rw [hN, Nat.factorization_mul hq1 hm2, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpq1, zero_add]
  have he2 : N.factorization p = 2 * m.factorization p := by
    rw [hfp, Nat.factorization_pow]; simp
  -- `p = w + 3`
  have hpo : Odd p := h.odd.of_dvd_nat hpN
  obtain ⟨w, rfl⟩ : ∃ w, p = w + 3 := by
    have := hp.two_le
    rcases hp.eq_two_or_odd' with h2 | _
    · subst h2; exact absurd hpo (by decide)
    · exact ⟨p - 3, by obtain ⟨k, hk⟩ := hpo; omega⟩
  -- The components `P = p ^ e` and `M'` of `m ^ 2`.
  obtain ⟨e, he⟩ : ∃ e, N.factorization (w + 3) = e := ⟨_, rfl⟩
  rw [he] at hqd he2 hfp
  obtain ⟨P, M', hP, hPM, hcop⟩ : ∃ P M' : ℕ, P = (w + 3) ^ e ∧ P * M' = m ^ 2 ∧
      Nat.Coprime P M' :=
    ⟨_, _, by rw [hfp], Nat.ordProj_mul_ordCompl_eq_self (m ^ 2) (w + 3),
      (Nat.coprime_ordCompl hp hm2).pow_left _⟩
  rw [← hP] at hqd
  have hP0 : 0 < P := by rw [hP]; positivity
  have hσm : σ 1 (m ^ 2) = σ 1 P * σ 1 M' := by
    rw [← hPM]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
  have hmain : (q + 1) * σ 1 (m ^ 2) = 2 * (q ^ 1 * m ^ 2) := by
    have hc : Nat.Coprime (q ^ 1) (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow 1 2
    rw [← sigma_prime_one' hq, ← isMultiplicative_sigma.map_mul_of_coprime hc, ← hN]
    exact h.sigma_eq
  obtain ⟨u, hu⟩ := hqd
  have hodd := odd_sigma_sq h hq hN hqm
  rw [hσm] at hodd
  have hσPodd := (Nat.odd_mul.mp hodd).1
  have hσModd := (Nat.odd_mul.mp hodd).2
  have huodd : Odd u := by rw [hu] at hσPodd; exact (Nat.odd_mul.mp hσPodd).2
  have hu1 : 1 ≤ u := by obtain ⟨v, rfl⟩ := huodd; omega
  -- `(q + 1) u σ(M') = 2 P M'`
  have hrel0 : (q + 1) * u * σ 1 M' = 2 * P * M' := by
    refine Nat.eq_of_mul_eq_mul_left hq.pos ?_
    calc q * ((q + 1) * u * σ 1 M') = (q + 1) * σ 1 (m ^ 2) := by rw [hσm, hu]; ring
      _ = 2 * (q ^ 1 * m ^ 2) := hmain
      _ = q * (2 * P * M') := by rw [← hPM]; ring
  -- `p * P = X q + 1` with `X = (p - 1) u`
  have hpP : (w + 3) * P = (w + 2) * u * q + 1 := by
    have := sigma_prime_pow_mul_pred hp e
    rw [← hP, hu, show w + 3 - 1 = w + 2 by omega, pow_succ, ← hP] at this
    have h1 : 1 ≤ P * (w + 3) := Nat.mul_pos hP0 (by omega)
    rw [mul_comm (w + 3) P, show (w + 2) * u * q = q * u * (w + 2) by ring]
    omega
  -- `x = gcd(q + 1, P)`
  set x := Nat.gcd (q + 1) P with hx
  have hx0 : 0 < x := Nat.gcd_pos_of_pos_left _ (by omega)
  set Q' := (q + 1) / x with hQ'
  set P' := P / x with hP'
  have hQ : q + 1 = x * Q' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hPx : P = x * P' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have hcopQP : Nat.Coprime Q' P' := Nat.coprime_div_gcd_div_gcd hx0
  have hcuP : Nat.Coprime u P := by
    have hc1 : Nat.Coprime u (w + 3) :=
      Nat.Coprime.coprime_dvd_left (Dvd.intro_left q hu.symm)
        (by rw [hP]; exact coprime_sigma_prime_pow hp e)
    rw [hP]; exact hc1.pow_right e
  have hcPu : Nat.Coprime P' u :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro_left x hPx.symm) hcuP.symm
  have hrel1 : Q' * u * σ 1 M' = 2 * P' * M' := by
    refine Nat.eq_of_mul_eq_mul_left hx0 ?_
    calc x * (Q' * u * σ 1 M') = (q + 1) * u * σ 1 M' := by rw [hQ]; ring
      _ = 2 * P * M' := hrel0
      _ = x * (2 * P' * M') := by rw [hPx]; ring
  have hP'd : P' ∣ σ 1 M' := by
    have h1 : P' ∣ Q' * (u * σ 1 M') := ⟨2 * M', by rw [← mul_assoc, hrel1]; ring⟩
    exact hcPu.dvd_of_dvd_mul_left (hcopQP.symm.dvd_of_dvd_mul_left h1)
  obtain ⟨T, hT⟩ := hP'd
  have hP'0 : 0 < P' := by
    rcases Nat.eq_zero_or_pos P' with h0 | h0
    · rw [hPx, h0] at hP0; simp at hP0
    · exact h0
  have hTodd : Odd T := by rw [hT] at hσModd; exact (Nat.odd_mul.mp hσModd).2
  have hrel : Q' * u * T = 2 * M' := by
    refine Nat.eq_of_mul_eq_mul_left hP'0 ?_
    calc P' * (Q' * u * T) = Q' * u * σ 1 M' := by rw [hT]; ring
      _ = 2 * P' * M' := hrel1
      _ = P' * (2 * M') := by ring
  -- Facts about `x`.
  have hxP : x ∣ (w + 3) ^ e := hP ▸ Nat.gcd_dvd_right (q + 1) P
  obtain ⟨a, -, hxa⟩ := (Nat.dvd_prime_pow hp).mp hxP
  have hdx : x ∣ (w + 2) * u - 1 := by
    have hX1 : 1 ≤ (w + 2) * u := Nat.mul_pos (by omega) hu1
    have heq : (w + 2) * u * (q + 1) = (w + 3) * P + ((w + 2) * u - 1) := by
      rw [mul_add, mul_one, hpP]
      generalize (w + 2) * u * q = Z
      omega
    have h1 : x ∣ (w + 3) * P + ((w + 2) * u - 1) :=
      heq ▸ Dvd.dvd.mul_left (Nat.gcd_dvd_left _ _) _
    exact (Nat.dvd_add_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _)).mp h1
  have hu2 : 1 < x → 2 * (w + 3) ≤ u + 1 := by
    intro hx1
    have hpx : w + 3 ∣ x := by
      rw [hxa]
      rcases a with _ | a
      · simp at hxa; omega
      · exact dvd_pow_self _ (Nat.succ_ne_zero a)
    obtain ⟨c, hc⟩ := hpx.trans (Nat.gcd_dvd_left (q + 1) P)
    have hX1 : 1 ≤ (w + 2) * u := Nat.mul_pos (by omega) hu1
    have heq : (w + 2) * u * ((w + 3) * c) + (u + 1) = (w + 3) * (P + u) := by
      rw [← hc, mul_add, mul_one, mul_add (w + 3), hpP]
      have : (w + 2) * u + u = (w + 3) * u := by ring
      generalize (w + 2) * u * q = Z at *
      omega
    have hd : w + 3 ∣ u + 1 := by
      have h1 : w + 3 ∣ (w + 2) * u * ((w + 3) * c) + (u + 1) := heq ▸ dvd_mul_right _ _
      exact (Nat.dvd_add_right (Dvd.dvd.mul_left (dvd_mul_right _ _) _)).mp h1
    have h2 : 2 ∣ u + 1 := by obtain ⟨v, rfl⟩ := huodd; exact ⟨v + 1, by ring⟩
    have hcop2 : Nat.Coprime 2 (w + 3) :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    exact Nat.le_of_dvd (by omega) (hcop2.mul_dvd_of_dvd_of_dvd h2 hd)
  have hexc : w = 0 → u ≠ 5 := by
    rintro rfl rfl
    obtain ⟨f, hf⟩ : ∃ f, e = 2 * f := ⟨_, he2⟩
    have hP9 : P = 9 ^ f := by rw [hP, hf, pow_mul]; norm_num
    rw [hP9] at hpP
    have hmod : (0 + 3) * 9 ^ f % 5 = ((0 + 2) * 5 * q + 1) % 5 := by rw [hpP]
    have h1 : ((0 + 2) * 5 * q + 1) % 5 = 1 := by omega
    rcases nine_pow_mod_five f with h9 | h9 <;> omega
  rcases case_bound huodd hTodd hxa hu2 hdx hexc with ⟨hx1, hu1', hT1⟩ | hkey
  · -- the exceptional shape
    right
    refine ⟨w + 3, hp, hpm, ?_⟩
    rw [he, ← hP]
    refine ⟨?_, ?_, ?_⟩
    · rw [hx1, one_mul] at hQ
      rw [hu1', hT1, mul_one, mul_one, ← hQ] at hrel
      rw [← hPM, hrel]; ring
    · rw [hu, hu1', mul_one]
    · rw [hx1, one_mul] at hQ hPx
      rw [hu1', hT1, mul_one, mul_one, ← hQ] at hrel
      rw [show (q + 1) / 2 = M' by omega, hT, hT1, mul_one, ← hPx]
  · left
    have hlt := final_arith (hPx ▸ hpP) hrel hQ hkey hu1 (by obtain ⟨v, rfl⟩ := hTodd; omega)
    rw [← hPx, hPM] at hlt
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlt

/-- The exceptional shape forces `m < q`: if `2 m ^ 2 = p ^ e (q + 1)` and `σ(p ^ e) = q`
for primes `p` and `q`, then `m < q`. -/
theorem lt_special_of_shape {q m p e : ℕ} (hq : q.Prime) (hp : p.Prime)
    (h2 : 2 * m ^ 2 = p ^ e * (q + 1)) (hσ : σ 1 (p ^ e) = q) : m < q := by
  have hpos : 0 < p ^ e := pow_pos hp.pos e
  have h1 := sigma_prime_pow_mul_pred hp e
  rw [hσ, pow_succ] at h1
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have hlt : p ^ e < q := by
    by_contra hc
    push Not at hc
    have h3 : q * (p - 1) ≤ p ^ e * (p - 1) := Nat.mul_le_mul_right _ hc
    have h4 : p ^ e * (p - 1) + p ^ e = p ^ e * p := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel hp.one_lt.le]
    have hP1 : p ^ e = 1 := by
      have : 1 ≤ p ^ e * p := Nat.mul_pos hpos hp.pos
      omega
    rw [hP1] at hc h1
    have hq1 : q * (p - 1) = p - 1 := by simpa using h1
    have : q = 1 := by
      have := Nat.eq_of_mul_eq_mul_right (show 0 < p - 1 by omega)
        (hq1.trans (one_mul (p - 1)).symm)
      exact this
    exact hq.one_lt.ne' this
  have h5 : 2 * m ^ 2 < 2 * q ^ 2 := by
    rw [h2]
    calc p ^ e * (q + 1) < q * (q + 1) := Nat.mul_lt_mul_of_pos_right hlt (by omega)
      _ ≤ 2 * q ^ 2 := by nlinarith [hq.one_lt]
  exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (by omega)

/-- For exponent one, `m < q` holds exactly in the exceptional shape. -/
theorem lt_special_iff_shape {N q m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ 1 * m ^ 2) (hqm : ¬ q ∣ m) :
    m < q ↔ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ 2 * m ^ 2 = p ^ N.factorization p * (q + 1) ∧
      σ 1 (p ^ N.factorization p) = q ∧ σ 1 ((q + 1) / 2) = p ^ N.factorization p := by
  constructor
  · intro hlt
    rcases special_lt_or_shape_of_exponent_one h hq hN hqm with h1 | h1
    · exact absurd (h1.trans hlt) (lt_irrefl q)
    · exact h1
  · rintro ⟨p, hp, -, h2, hσ, -⟩
    exact lt_special_of_shape hq hp h2 hσ

/-- If the special exponent is not one, then `q < m`. -/
theorem special_lt_of_exponent_ne_one {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1) : q < m := by
  rcases lt_trichotomy q m with hlt | heq | hgt
  · exact hlt
  · subst heq; exact absurd dvd_rfl hqm
  · exact absurd (exponent_eq_one_of_lt h hq hN hqm hgt) hk

/-- Every odd perfect number `N = q ^ k * m ^ 2` in Euler's form satisfies `q < m`, unless
`k = 1` and `N = q * p ^ e * ((q + 1) / 2)` for a prime `p ∣ m` with exponent `e` in `N`,
`σ(p ^ e) = q` and `σ((q + 1) / 2) = p ^ e`. -/
theorem special_lt_or_shape {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    q < m ∨ (k = 1 ∧ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ 2 * m ^ 2 = p ^ N.factorization p * (q + 1) ∧
      σ 1 (p ^ N.factorization p) = q ∧ σ 1 ((q + 1) / 2) = p ^ N.factorization p) := by
  by_cases hk : k = 1
  · subst hk
    rcases special_lt_or_shape_of_exponent_one h hq hN hqm with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, h1⟩
  · exact Or.inl (special_lt_of_exponent_ne_one h hq hN hqm hk)

/-- If no component divisor sum `σ(p ^ v_p(N))` of an odd perfect number equals the special
prime `q`, then `q < m`. The hypothesis `hne` is an unproved assumption: it is not known to
hold for every odd perfect number. -/
theorem special_lt_of_forall_sigma_ne {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m)
    (hne : ∀ p ∈ N.primeFactors, σ 1 (p ^ N.factorization p) ≠ q) : q < m := by
  rcases special_lt_or_shape h hq hN hqm with h1 | ⟨-, p, hp, hpm, -, hσ, -⟩
  · exact h1
  · refine absurd hσ (hne p (Nat.mem_primeFactors.mpr ⟨hp, ?_, h.ne_zero⟩))
    rw [hN]
    exact (hpm.trans (dvd_pow_self m two_ne_zero)).mul_left _

/-- `q < m`, unless `k = 1` and the Euler index `σ(m ^ 2) / q` equals the full component
`p ^ e` of a prime `p ∣ m` (with `e` the exponent of `p` in `N`), with `σ(p ^ e) = q` and
`e + 1` prime. -/
theorem special_lt_or_index_prime_pow {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    q < m ∨ (k = 1 ∧ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧
      eulerIndex q 1 m = p ^ N.factorization p ∧ σ 1 (p ^ N.factorization p) = q ∧
      (N.factorization p + 1).Prime) := by
  rcases special_lt_or_shape h hq hN hqm with h1 | ⟨rfl, p, hp, hpm, h2, hσ, -⟩
  · exact Or.inl h1
  · refine Or.inr ⟨rfl, p, hp, hpm, ?_, hσ, prime_succ_of_prime_sigma_prime_pow hp (hσ ▸ hq)⟩
    have hi := sigma_special_mul_eulerIndex h hq hN hqm
    rw [sigma_prime_one' hq, h2, mul_comm (p ^ _)] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega) hi

end OddPerfect

#print axioms OddPerfect.special_lt_or_shape_of_exponent_one
#print axioms OddPerfect.lt_special_of_shape
#print axioms OddPerfect.lt_special_iff_shape
#print axioms OddPerfect.special_lt_of_exponent_ne_one
#print axioms OddPerfect.special_lt_or_shape
#print axioms OddPerfect.special_lt_of_forall_sigma_ne
#print axioms OddPerfect.special_lt_or_index_prime_pow
