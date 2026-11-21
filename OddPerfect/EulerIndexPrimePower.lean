import OddPerfect.EulerPart
import OddPerfect.Cyclotomic

/-!
# Odd perfect numbers whose Euler index is a prime power

Let `N = q * m ^ 2` be an odd perfect number with special prime `q`, special exponent `1`,
and `q ∤ m`. Suppose the Euler index `σ(m ^ 2) / q` is a prime power `r ^ b` with `b > 0`.
Then `m ^ 2 = r ^ b * M ^ 2` with `r ∤ M`, `σ(r ^ b) = q`, `q + 1 = 2 M ^ 2`,
`σ(M ^ 2) = r ^ b`, `b = v_r(m ^ 2)` is even, and `b + 1` is prime.

This is known mathematics. For any prime power `q ^ α` exactly dividing `N`, F.-J. Chen and
Y.-G. Chen (On the index of an odd perfect number, Colloq. Math. 136 (2014), 41 to 49) prove
that the index `σ(N / q ^ α) / q ^ α` is not of the form `p ^ (2 u)` with `2 u + 1`
composite; earlier results on small indices are due to Dris and Luca and to Broughan,
Delbourgo and Zhou. The normal form here covers only the special prime with exponent `1`;
it is an elementary consequence of the identities `σ(m ^ 2) = q i` and
`(q + 1) i = 2 m ^ 2`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma sigma_succ_eq_one_add {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- `σ(p ^ a)` determines `a`. -/
private lemma sigma_prime_pow_inj {p a c : ℕ} (hp : p.Prime)
    (h : σ 1 (p ^ a) = σ 1 (p ^ c)) : a = c := by
  have ha := sigma_prime_pow_mul_pred hp a
  have hc := sigma_prime_pow_mul_pred hp c
  rw [h, hc] at ha
  have h1 := Nat.one_le_pow (a + 1) p hp.pos
  have h2 := Nat.one_le_pow (c + 1) p hp.pos
  have : p ^ (c + 1) = p ^ (a + 1) := by omega
  have := Nat.pow_right_injective hp.two_le this
  omega

/-- If `σ(p ^ b)` is prime then `b + 1` is prime. -/
theorem prime_succ_of_prime_sigma_prime_pow {p b : ℕ} (hp : p.Prime)
    (hσ : (σ 1 (p ^ b)).Prime) : (b + 1).Prime := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hσ
    exact Nat.not_prime_one hσ
  refine Nat.prime_def.mpr ⟨by omega, fun d hd => ?_⟩
  obtain ⟨c, hc⟩ := hd
  have hd0 : d ≠ 0 := by rintro rfl; omega
  obtain ⟨u, rfl⟩ : ∃ u, d = u + 1 := ⟨d - 1, by omega⟩
  -- `σ(p ^ u) ∣ σ(p ^ b)`
  have hdvd : σ 1 (p ^ u) ∣ σ 1 (p ^ b) := by
    have hpp : 0 < p - 1 := by have := hp.two_le; omega
    have hx : σ 1 (p ^ u) * (p - 1) ∣ σ 1 (p ^ b) * (p - 1) := by
      rw [sigma_prime_pow_mul_pred hp, sigma_prime_pow_mul_pred hp, hc, pow_mul]
      exact Nat.sub_one_dvd_pow_sub_one _ _
    exact Nat.dvd_of_mul_dvd_mul_right hpp hx
  rcases hσ.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · left
    have : σ 1 (p ^ u) = σ 1 (p ^ 0) := by simpa using h1
    have := sigma_prime_pow_inj hp this
    omega
  · right
    rw [sigma_prime_pow_inj hp h1]

variable {N q m r b : ℕ}

/-- Normal form when the special exponent is `1` and the Euler index `σ(m ^ 2) / q` is a
prime power `r ^ b` with `b > 0`. -/
theorem eulerIndex_prime_pow_normal_form (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hb : 0 < b)
    (hI : eulerIndex q 1 m = r ^ b) :
    ∃ M, m ^ 2 = r ^ b * M ^ 2 ∧ ¬ r ∣ M ∧ Odd M ∧ 1 < M ∧ ¬ q ∣ M ∧
      σ 1 (r ^ b) = q ∧ q + 1 = 2 * M ^ 2 ∧ σ 1 (M ^ 2) = r ^ b ∧
      b = (m ^ 2).factorization r ∧ Even b ∧ (b + 1).Prime := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hs := sigma_sq_eq_mul_eulerIndex h hq hN1 hqm
  have hi := sigma_special_mul_eulerIndex h hq hN1 hqm
  have hdv := eulerIndex_dvd_sq h hq hN1 hqm
  rw [hI] at hs hi hdv
  rw [pow_one] at hs
  rw [sigma_one_apply_prime_pow hq] at hi
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
    pow_one] at hi
  -- now `hi : (1 + q) * r ^ b = 2 * m ^ 2`
  have hm0 : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hmodd : Odd m := h.odd.of_dvd_nat (hN ▸ (dvd_pow_self m two_ne_zero).mul_left _)
  have hrm : r ∣ m := hr.dvd_of_dvd_pow ((dvd_pow_self r hb.ne').trans hdv)
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hrm)
  -- split `m = r ^ v * M`
  set v := m.factorization r with hv
  set M := ordCompl[r] m with hM
  have hmM : r ^ v * M = m := Nat.ordProj_mul_ordCompl_eq_self m r
  have hrM : ¬ r ∣ M := Nat.not_dvd_ordCompl hr hm0
  have hv0 : v ≠ 0 := by
    rw [hv]
    exact (Nat.Prime.factorization_pos_of_dvd hr hm0 hrm).ne'
  clear_value v M
  have hm2 : m ^ 2 = r ^ (2 * v) * M ^ 2 := by rw [← hmM]; ring
  have hcop : Nat.Coprime (r ^ (2 * v)) (M ^ 2) :=
    ((hr.coprime_iff_not_dvd.mpr hrM).pow _ _)
  have hsplit : σ 1 (m ^ 2) = σ 1 (r ^ (2 * v)) * σ 1 (M ^ 2) := by
    rw [hm2, isMultiplicative_sigma.map_mul_of_coprime hcop]
  -- `σ(r ^ (2 v)) = q`
  have hσe : σ 1 (r ^ (2 * v)) = q := by
    have hd : σ 1 (r ^ (2 * v)) ∣ q * r ^ b := hs ▸ hsplit ▸ dvd_mul_right _ _
    have hc : Nat.Coprime (σ 1 (r ^ (2 * v))) (r ^ b) :=
      (coprime_sigma_prime_pow hr (2 * v)).pow_right b
    rcases hq.eq_one_or_self_of_dvd _ (hc.dvd_of_dvd_mul_right hd) with h1 | h1
    · exfalso
      have : σ 1 (r ^ (2 * v)) = σ 1 (r ^ 0) := by simpa using h1
      have := sigma_prime_pow_inj hr this
      omega
    · exact h1
  have hσM : σ 1 (M ^ 2) = r ^ b := by
    rw [hsplit, hσe] at hs
    exact Nat.eq_of_mul_eq_mul_left hq.pos hs
  -- `q ≡ 1 (mod r)`, so `r ∤ q + 1`
  obtain ⟨w, hw⟩ : ∃ w, 2 * v = w + 1 := ⟨2 * v - 1, by omega⟩
  have hq1 : q = 1 + r * σ 1 (r ^ w) := by rw [← hσe, hw, sigma_succ_eq_one_add hr]
  have hrq : ¬ r ∣ 1 + q := by
    intro hd
    have h2 : r ∣ 2 := by
      have : 1 + q = 2 + r * σ 1 (r ^ w) := by omega
      rw [this] at hd
      exact (Nat.dvd_add_left (dvd_mul_right r _)).mp hd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact hr.one_lt.ne' h
    · exact hr2 h
  -- compare powers of `r` in `(1 + q) r ^ b = 2 r ^ (2 v) M ^ 2`
  rw [hm2] at hi
  have hrpos : 0 < r := hr.pos
  have hbe : b = 2 * v := by
    rcases lt_trichotomy b (2 * v) with hlt | heq | hgt
    · exfalso
      apply hrq
      obtain ⟨t, ht⟩ : ∃ t, 2 * v = b + (t + 1) := ⟨2 * v - b - 1, by omega⟩
      rw [ht, pow_add] at hi
      have : 1 + q = 2 * (r ^ (t + 1) * M ^ 2) := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hrpos b)
        rw [mul_comm, hi]; ring
      rw [this]
      exact ((dvd_pow_self r (Nat.succ_ne_zero t)).mul_right _).mul_left _
    · exact heq
    · exfalso
      obtain ⟨t, ht⟩ : ∃ t, b = 2 * v + (t + 1) := ⟨b - 2 * v - 1, by omega⟩
      rw [ht, pow_add] at hi
      have : (1 + q) * r ^ (t + 1) = 2 * M ^ 2 := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hrpos (2 * v))
        calc r ^ (2 * v) * ((1 + q) * r ^ (t + 1)) = (1 + q) * (r ^ (2 * v) * r ^ (t + 1)) := by
              ring
          _ = r ^ (2 * v) * (2 * M ^ 2) := by rw [hi]; ring
      have hd : r ∣ 2 * M ^ 2 :=
        this ▸ (dvd_pow_self r (Nat.succ_ne_zero t)).mul_left _
      rcases (Nat.Prime.dvd_mul hr).mp hd with h2 | h2
      · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact hr.one_lt.ne' h
        · exact hr2 h
      · exact hrM (hr.dvd_of_dvd_pow h2)
  subst hbe
  have hqM : q + 1 = 2 * M ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hrpos (2 * v))
    rw [add_comm, hi]; ring
  have hMm : M ∣ m := ⟨r ^ v, by rw [← hmM, mul_comm]⟩
  refine ⟨M, hm2, hrM, hmodd.of_dvd_nat hMm, ?_, fun hd => hqm (hd.trans hMm), hσe, hqM,
    hσM, ?_, even_two_mul v, prime_succ_of_prime_sigma_prime_pow hr (hσe ▸ hq)⟩
  · by_contra hle
    have : M ≤ 1 := by omega
    interval_cases M
    · simp at hmM; exact hm0 hmM.symm
    · have := hq.two_le; omega
  · have hM0 : M ≠ 0 := by rintro rfl; simp at hmM; exact hm0 hmM.symm
    rw [hm2, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) (pow_ne_zero _ hM0),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd hrM]
    simp

/-- Existence free part of the normal form: under the same hypotheses, `σ(r ^ b) = q`,
`q ≡ 1 (mod r)`, `b = v_r(m ^ 2)`, `b` is even, and `b + 1` is prime. -/
theorem eulerIndex_prime_pow_facts (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hb : 0 < b)
    (hI : eulerIndex q 1 m = r ^ b) :
    σ 1 (r ^ b) = q ∧ q % r = 1 ∧ b = (m ^ 2).factorization r ∧ Even b ∧ (b + 1).Prime := by
  obtain ⟨M, -, -, -, -, -, hσ, -, -, hfac, hev, hpr⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hr hb hI
  refine ⟨hσ, ?_, hfac, hev, hpr⟩
  obtain ⟨w, rfl⟩ : ∃ w, b = w + 1 := ⟨b - 1, by omega⟩
  rw [← hσ, sigma_succ_eq_one_add hr, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hr.one_lt

/-- Corollary: under the same hypotheses, `q ≡ 1 (mod r)` and `q = 2 M ^ 2 - 1` for some
`M > 1` with `m ^ 2 = r ^ b * M ^ 2`. -/
theorem eulerIndex_prime_pow_special_eq (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hb : 0 < b)
    (hI : eulerIndex q 1 m = r ^ b) :
    q % r = 1 ∧ ∃ M, 1 < M ∧ m ^ 2 = r ^ b * M ^ 2 ∧ q = 2 * M ^ 2 - 1 := by
  obtain ⟨M, hm2, -, -, hM1, -, -, hqM, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hr hb hI
  exact ⟨(eulerIndex_prime_pow_facts h hq hN hqm hr hb hI).2.1, M, hM1, hm2, by omega⟩

end OddPerfect

#print axioms OddPerfect.prime_succ_of_prime_sigma_prime_pow
#print axioms OddPerfect.eulerIndex_prime_pow_normal_form
#print axioms OddPerfect.eulerIndex_prime_pow_facts
#print axioms OddPerfect.eulerIndex_prime_pow_special_eq
