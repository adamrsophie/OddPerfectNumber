import OddPerfect.SpecialPrime
import OddPerfect.Abundancy

/-!
# A component bound for odd perfect numbers

An inequality for every odd perfect number `N`: no prime power component `p ^ e` of even
exponent can be large against the part `A` of `N` outside it and one further component
`q ^ a`. With `A = N / (q ^ a * p ^ e)`:

* `p ^ e < 3 * (p - 1) * A * σ(A)`,
* `p ^ e < 36 * A ^ 4`,
* `N < 2592 * A ^ 10`, and the last bound for any two distinct prime factors.

The proof writes `σ(p ^ e) * σ(A) = q ^ a * J`, shows `J ≤ A * σ(A)` by a divisibility and
parity argument, and compares two integer identities in `K = 2 * A * (p - 1) - p * σ(A)`.
The results do not bound `N` and do not decide existence.
No published source was checked; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Helpers -/

/-- The geometric identity `(p - 1) * σ(p ^ e) + 1 = p ^ (e + 1)`. -/
private lemma comp_pred_mul_sigma_add_one {p e : ℕ} (hp : p.Prime) :
    (p - 1) * σ 1 (p ^ e) + 1 = p ^ (e + 1) := by
  have h1 := hp.one_lt
  rw [sigma_one_apply_prime_pow hp, mul_comm]
  have := geom_sum_mul_add (p - 1) (e + 1)
  rwa [Nat.sub_add_cancel h1.le] at this

/-- `σ(p ^ e)` is odd for an odd prime `p` and an even exponent `e`. -/
private lemma comp_odd_sigma_prime_pow {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : Even e) :
    Odd (σ 1 (p ^ e)) := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rw [sigma_one_apply_prime_pow hp, Nat.odd_iff, Finset.sum_nat_mod]
  have : ∀ i ∈ Finset.range (e + 1), p ^ i % 2 = 1 := fun i _ => by
    rw [Nat.pow_mod, hpo, one_pow, Nat.one_mod]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  obtain ⟨j, rfl⟩ := he
  omega

/-- A proper divisor of an odd perfect number is deficient. -/
private lemma comp_sigma_lt_two_mul {N d : ℕ} (h : OddPerfect N) (hd : d ∣ N) (hne : d ≠ N) :
    σ 1 d < 2 * d := by
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd h.pos
  have h1 := abundancy_lt_of_dvd_of_ne h.ne_zero hd hne
  rw [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect, abundancy,
    div_lt_iff₀ (by exact_mod_cast hd0)] at h1
  exact_mod_cast h1

/-- The integer core of the argument. -/
private lemma comp_core_int {p q A S X R J T Q : ℤ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hA : 1 ≤ A)
    (hS : 1 ≤ S) (hX : 1 ≤ X) (hT : 1 ≤ T) (hJ : 1 ≤ J) (h1 : R * S = Q * J)
    (h2 : (Q + T) * J = 2 * A * X) (h3 : (p - 1) * R + 1 = p * X) (hQ : (q - 1) * T + 1 = Q)
    (hJle : J ≤ A * S) (hK : 2 * A * (p - 1) - p * S ≠ 0) :
    X < 3 * (p - 1) * A * S := by
  set K := 2 * A * (p - 1) - p * S with hKdef
  have E1 : (p - 1) * T * J = K * X + S := by
    rw [hKdef]
    linear_combination (p - 1) * h2 + (p - 1) * h1 - S * h3
  have E2 : (2 * A * (p - 1) - q * K) * X = q * S + (p - 1) * J := by
    linear_combination -(p - 1) * h2 + q * E1 - (p - 1) * J * hQ
  have hpos' : 0 < (p - 1) * T * J := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  rcases lt_trichotomy K 0 with hneg | hzero | hpos
  · have hK1 : K ≤ -1 := by linarith [Int.lt_iff_add_one_le.mp hneg]
    have hKX : K * X ≤ -1 * X := mul_le_mul_of_nonneg_right hK1 (by linarith)
    have hXS : X < S := by linarith
    have h3A : 1 ≤ 3 * (p - 1) * A := by nlinarith
    have : S ≤ 3 * (p - 1) * A * S := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 3 * (p - 1) * A - 1)
        (by linarith : (0 : ℤ) ≤ S)]
    linarith
  · exact absurd hzero hK
  · have hK1 : 1 ≤ K := by linarith [Int.lt_iff_add_one_le.mp hpos]
    set c := 2 * A * (p - 1) - q * K with hc
    have hrhs : 0 < q * S + (p - 1) * J :=
      add_pos (mul_pos (by linarith) (by linarith)) (mul_pos (by linarith) (by linarith))
    have hc1 : 1 ≤ c := by
      by_contra hlt
      have hc0 : c ≤ 0 := by linarith [Int.lt_iff_add_one_le.mp (not_le.mp hlt)]
      have : c * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 (by linarith)
      linarith
    have hqK : q ≤ q * K := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ q) (by linarith : (0 : ℤ) ≤ K - 1)]
    have hq' : q ≤ 2 * A * (p - 1) - 1 := by linarith
    have hqS : q * S ≤ (2 * A * (p - 1) - 1) * S := mul_le_mul_of_nonneg_right hq' (by linarith)
    have hXc : X ≤ c * X := by
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ c - 1) (by linarith : (0 : ℤ) ≤ X)]
    have hJ2 : (p - 1) * J ≤ (p - 1) * (A * S) := mul_le_mul_of_nonneg_left hJle (by linarith)
    have e1 : (2 * A * (p - 1) - 1) * S + (p - 1) * (A * S) = 3 * (p - 1) * A * S - S := by
      ring
    linarith

/-- The natural number form of the core. -/
private lemma comp_core_nat {p q A S X R J T Q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hA : 1 ≤ A)
    (hS : 1 ≤ S) (hX : 1 ≤ X) (hT : 1 ≤ T) (hJ : 1 ≤ J) (h1 : R * S = Q * J)
    (h2 : (Q + T) * J = 2 * A * X) (h3 : (p - 1) * R + 1 = p * X) (hQ : (q - 1) * T + 1 = Q)
    (hJle : J ≤ A * S) (hK : 2 * A * (p - 1) ≠ p * S) :
    X < 3 * (p - 1) * A * S := by
  have hp1 : 1 ≤ p := by omega
  have hq1 : 1 ≤ q := by omega
  zify [hp1, hq1] at *
  exact comp_core_int hp hq hA hS hX hT hJ h1 h2 h3 hQ hJle
    (by intro h; exact hK (by linarith))

/-- The component bound for abstract parts `q ^ a`, `p ^ e`, `A`. -/
private lemma comp_core {p q a e A : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (ha : 1 ≤ a) (he : Even e) (hpA : Nat.Coprime p A) (hA0 : 0 < A)
    (hsig : σ 1 (q ^ a) * (σ 1 (p ^ e) * σ 1 A) = 2 * (q ^ a * (p ^ e * A))) :
    p ^ e < 3 * (p - 1) * A * σ 1 A := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hcopQ : Nat.Coprime (q ^ (b + 1)) (σ 1 (q ^ (b + 1))) :=
    ((coprime_sigma_prime_pow hq (b + 1)).pow_right (b + 1)).symm
  have hQdvd : q ^ (b + 1) ∣ σ 1 (p ^ e) * σ 1 A := by
    refine hcopQ.dvd_of_dvd_mul_right ⟨2 * (p ^ e * A), ?_⟩
    calc σ 1 (p ^ e) * σ 1 A * σ 1 (q ^ (b + 1))
        = σ 1 (q ^ (b + 1)) * (σ 1 (p ^ e) * σ 1 A) := mul_comm _ _
      _ = 2 * (q ^ (b + 1) * (p ^ e * A)) := hsig
      _ = q ^ (b + 1) * (2 * (p ^ e * A)) := by ring
  obtain ⟨J, hJ⟩ := hQdvd
  have hS0 : 0 < σ 1 A := sigma_pos 1 A hA0.ne'
  have hR0 : 0 < σ 1 (p ^ e) := sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)
  have hQ0 : 0 < q ^ (b + 1) := pow_pos hq.pos _
  have hT0 : 0 < σ 1 (q ^ b) := sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)
  have hX0 : 0 < p ^ e := pow_pos hp.pos _
  have hJ0 : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h0 | h0
    · rw [h0, mul_zero] at hJ
      exact absurd hJ (Nat.mul_pos hR0 hS0).ne'
    · exact h0
  have hσQ : σ 1 (q ^ (b + 1)) = q ^ (b + 1) + σ 1 (q ^ b) := by
    rw [sigma_one_apply_prime_pow hq, sigma_one_apply_prime_pow hq,
      Finset.sum_range_succ _ (b + 1)]
    exact add_comm _ _
  have hQT : (q - 1) * σ 1 (q ^ b) + 1 = q ^ (b + 1) := comp_pred_mul_sigma_add_one hq
  have hR : (p - 1) * σ 1 (p ^ e) + 1 = p * p ^ e := by
    rw [comp_pred_mul_sigma_add_one hp, pow_succ, mul_comm]
  have h2 : (q ^ (b + 1) + σ 1 (q ^ b)) * J = 2 * A * p ^ e := by
    have : q ^ (b + 1) * ((q ^ (b + 1) + σ 1 (q ^ b)) * J) = q ^ (b + 1) * (2 * A * p ^ e) := by
      calc q ^ (b + 1) * ((q ^ (b + 1) + σ 1 (q ^ b)) * J)
          = σ 1 (q ^ (b + 1)) * (q ^ (b + 1) * J) := by rw [hσQ]; ring
        _ = σ 1 (q ^ (b + 1)) * (σ 1 (p ^ e) * σ 1 A) := by rw [hJ]
        _ = 2 * (q ^ (b + 1) * (p ^ e * A)) := hsig
        _ = q ^ (b + 1) * (2 * A * p ^ e) := by ring
    exact Nat.eq_of_mul_eq_mul_left hQ0 this
  -- `J` divides `2 * A * σ(A)`
  have hcopXR : Nat.Coprime (p ^ e) (σ 1 (p ^ e)) :=
    ((coprime_sigma_prime_pow hp e).pow_right e).symm
  have hJd : J ∣ 2 * A * σ 1 A := by
    have d1 : J ∣ 2 * A * σ 1 A * p ^ e := by
      have : J ∣ 2 * A * p ^ e := ⟨q ^ (b + 1) + σ 1 (q ^ b), by rw [← h2]; ring⟩
      exact this.trans ⟨σ 1 A, by ring⟩
    have d2 : J ∣ 2 * A * σ 1 A * σ 1 (p ^ e) := by
      have : J ∣ σ 1 (p ^ e) * σ 1 A := ⟨q ^ (b + 1), by rw [hJ]; ring⟩
      exact this.trans ⟨2 * A, by ring⟩
    have := Nat.dvd_gcd d1 d2
    rwa [Nat.gcd_mul_left, show Nat.gcd (p ^ e) (σ 1 (p ^ e)) = 1 from hcopXR, mul_one] at this
  -- `J ≠ 2 * A * σ(A)` by parity
  have hRodd : Odd (σ 1 (p ^ e)) := comp_odd_sigma_prime_pow hp hp2 he
  have hJne : J ≠ 2 * A * σ 1 A := by
    intro hJeq
    rw [hJeq] at hJ
    have hR2 : σ 1 (p ^ e) = 2 * (q ^ (b + 1) * A) := by
      apply Nat.eq_of_mul_eq_mul_right hS0
      rw [hJ]
      ring
    rw [hR2] at hRodd
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_two_mul _)
  have hJle : J ≤ A * σ 1 A := by
    obtain ⟨c, hc⟩ := hJd
    have hpos : 0 < 2 * A * σ 1 A := Nat.mul_pos (Nat.mul_pos two_pos hA0) hS0
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact absurd hc hpos.ne'
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hc
      exact hJne hc.symm
    have hc2 : 2 ≤ c := by omega
    have := Nat.mul_le_mul_left J hc2
    linarith
  -- `2 * A * (p - 1) ≠ p * σ(A)`
  have hKnat : 2 * A * (p - 1) ≠ p * σ 1 A := by
    intro hK
    have hdvd : p ∣ 2 * A * (p - 1) := ⟨σ 1 A, hK⟩
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h'' | h''
      · have := Nat.le_of_dvd two_pos h''
        omega
      · exact (hp.coprime_iff_not_dvd.mp hpA) h''
    · have := Nat.le_of_dvd (by omega) h'
      omega
  exact comp_core_nat hp3 hq3 hA0 hS0 hX0 hT0 hJ0 hJ h2 hR hQT hJle hKnat

/-- The decomposition `N = q ^ a * (p ^ e * A)` and the divisor sum equation. -/
private lemma comp_setup {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    ∃ A, N / (q ^ N.factorization q * p ^ N.factorization p) = A ∧
      N = q ^ N.factorization q * (p ^ N.factorization p * A) ∧ 0 < A ∧ Nat.Coprime p A ∧
      σ 1 (q ^ N.factorization q) * (σ 1 (p ^ N.factorization p) * σ 1 A) =
        2 * (q ^ N.factorization q * (p ^ N.factorization p * A)) ∧
      σ 1 (p ^ N.factorization p * A) = σ 1 (p ^ N.factorization p) * σ 1 A := by
  set N1 := ordCompl[q] N with hN1
  have hN1z : N1 ≠ 0 := (Nat.ordCompl_pos q h.ne_zero).ne'
  have hf : N1.factorization p = N.factorization p := by
    rw [hN1, Nat.factorization_ordCompl, Finsupp.erase_ne hpq]
  set A := ordCompl[p] N1 with hA
  have hA0 : 0 < A := Nat.ordCompl_pos p hN1z
  have hN1eq : p ^ N.factorization p * A = N1 := by
    rw [← hf]
    exact Nat.ordProj_mul_ordCompl_eq_self N1 p
  have hNeq : q ^ N.factorization q * N1 = N := Nat.ordProj_mul_ordCompl_eq_self N q
  have hcq : Nat.Coprime q N1 := Nat.coprime_ordCompl hq h.ne_zero
  have hcp : Nat.Coprime p A := Nat.coprime_ordCompl hp hN1z
  have hN : N = q ^ N.factorization q * (p ^ N.factorization p * A) := by rw [hN1eq, hNeq]
  have hsigXA : σ 1 (p ^ N.factorization p * A) = σ 1 (p ^ N.factorization p) * σ 1 A :=
    isMultiplicative_sigma.map_mul_of_coprime (hcp.pow_left _)
  have hcQ : Nat.Coprime (q ^ N.factorization q) (p ^ N.factorization p * A) := by
    rw [hN1eq]
    exact hcq.pow_left _
  have hsigN : σ 1 N = σ 1 (q ^ N.factorization q) * σ 1 (p ^ N.factorization p * A) := by
    have := (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcQ
    rw [← hN] at this
    exact this
  refine ⟨A, ?_, hN, hA0, hcp, ?_, hsigXA⟩
  · refine Nat.div_eq_of_eq_mul_left
      (Nat.mul_pos (pow_pos hq.pos _) (pow_pos hp.pos _)) ?_
    calc N = q ^ N.factorization q * (p ^ N.factorization p * A) := hN
      _ = A * (q ^ N.factorization q * p ^ N.factorization p) := by ring
  · rw [← hsigXA, ← hsigN, h.sigma_eq, ← hN]

/-! ## The component bounds -/

/-- For two distinct prime factors `p`, `q` of an odd perfect number `N`, `p` of even
exponent `e`, and `A` the part of `N` prime to `p * q`: `p ^ e < 3 * (p - 1) * A * σ A`.
This is an inequality for every odd perfect number: no prime power component can be large
against the part of `N` outside it and one further component. It does not bound `N` and
does not decide existence. No published source was checked; novelty not verified. -/
theorem component_lt_three_mul {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime) (hq : q.Prime)
    (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q) (he : Even (N.factorization p)) :
    p ^ N.factorization p <
      3 * (p - 1) * (N / (q ^ N.factorization q * p ^ N.factorization p)) *
        σ 1 (N / (q ^ N.factorization q * p ^ N.factorization p)) := by
  obtain ⟨A, hAdef, -, hA0, hcp, hsig, -⟩ := comp_setup h hp hq hpq
  rw [hAdef]
  have ha : 1 ≤ N.factorization q := (hq.dvd_iff_one_le_factorization h.ne_zero).mp hqN
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd hpN
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd hqN
  exact comp_core hp hq hp2 hq2 ha he hcp hA0 hsig

/-- With the notation of `component_lt_three_mul`: `p ^ e < 36 * A ^ 4`. An inequality for
every odd perfect number: no prime power component can be large against the part of `N`
outside it and one further component. It does not bound `N` and does not decide existence.
No published source was checked; novelty not verified. -/
theorem component_lt_thirty_six_mul_pow_four {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hq : q.Prime) (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q)
    (he : Even (N.factorization p)) :
    p ^ N.factorization p < 36 * (N / (q ^ N.factorization q * p ^ N.factorization p)) ^ 4 := by
  have h1 := component_lt_three_mul h hp hq hpN hqN hpq he
  obtain ⟨A, hAdef, hN, hA0, -, -, -⟩ := comp_setup h hp hq hpq
  rw [hAdef] at h1 ⊢
  have he1 : 1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  have ha1 : 1 ≤ N.factorization q := (hq.dvd_iff_one_le_factorization h.ne_zero).mp hqN
  have he2 : 2 ≤ N.factorization p := by
    obtain ⟨j, hj⟩ := he
    omega
  have hX2 : p ^ 2 ≤ p ^ N.factorization p := Nat.pow_le_pow_right hp.pos he2
  have hQ2 : 2 ≤ q ^ N.factorization q :=
    le_trans hq.two_le (Nat.le_self_pow (by omega) q)
  have hX1 : 1 ≤ p ^ N.factorization p := Nat.one_le_pow _ _ hp.pos
  have hAN : A ∣ N := (dvd_mul_of_dvd_right (dvd_mul_left A _) _).trans (dvd_of_eq hN.symm)
  have hAlt : A < N := by
    have h3 := Nat.mul_le_mul hQ2 (Nat.mul_le_mul hX1 (le_refl A))
    have : A < q ^ N.factorization q * (p ^ N.factorization p * A) := by linarith
    exact lt_of_lt_of_eq this hN.symm
  have hSA : σ 1 A < 2 * A := comp_sigma_lt_two_mul h hAN hAlt.ne
  have hS0 : 0 < σ 1 A := sigma_pos 1 A hA0.ne'
  obtain ⟨r, hr⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [show p - 1 = r by omega] at h1
  have e1 : 3 * r * A * σ 1 A = r * (3 * A * σ 1 A) := by ring
  have hpS : p < 3 * A * σ 1 A := by
    by_contra hc
    push Not at hc
    have k1 := Nat.mul_le_mul_left r hc
    have k2 : r * p < p * p := Nat.mul_lt_mul_of_pos_right (by omega) hp.pos
    have k3 : p * p ≤ p ^ N.factorization p := by rw [← sq]; exact hX2
    linarith
  have hr3 : r < 3 * A * σ 1 A := by linarith
  have hpos : 0 < 3 * A * σ 1 A := Nat.mul_pos (Nat.mul_pos (by norm_num) hA0) hS0
  have hlt : 3 * A * σ 1 A < 3 * A * (2 * A) :=
    Nat.mul_lt_mul_of_pos_left hSA (Nat.mul_pos (by norm_num) hA0)
  calc p ^ N.factorization p < 3 * r * A * σ 1 A := h1
    _ = r * (3 * A * σ 1 A) := e1
    _ < (3 * A * σ 1 A) * (3 * A * σ 1 A) := Nat.mul_lt_mul_of_pos_right hr3 hpos
    _ < (3 * A * (2 * A)) * (3 * A * (2 * A)) := Nat.mul_self_lt_mul_self hlt
    _ = 36 * A ^ 4 := by ring

/-- With the notation of `component_lt_three_mul`: `N < 2592 * A ^ 10`. An inequality for
every odd perfect number in terms of the part of `N` outside two components. It does not
bound `N` and does not decide existence. No published source was checked; novelty not
verified. -/
theorem lt_mul_complement_pow_ten {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hq : q.Prime) (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q)
    (he : Even (N.factorization p)) :
    N < 2592 * (N / (q ^ N.factorization q * p ^ N.factorization p)) ^ 10 := by
  have h2 := component_lt_thirty_six_mul_pow_four h hp hq hpN hqN hpq he
  obtain ⟨A, hAdef, hN, hA0, -, hsig, hsigXA⟩ := comp_setup h hp hq hpq
  rw [hAdef] at h2 ⊢
  have ha1 : 1 ≤ N.factorization q := (hq.dvd_iff_one_le_factorization h.ne_zero).mp hqN
  have hQ2 : 2 ≤ q ^ N.factorization q :=
    le_trans hq.two_le (Nat.le_self_pow (by omega) q)
  have hX1 : 1 ≤ p ^ N.factorization p := Nat.one_le_pow _ _ hp.pos
  have hcopQ : Nat.Coprime (q ^ N.factorization q) (σ 1 (q ^ N.factorization q)) :=
    ((coprime_sigma_prime_pow hq _).pow_right _).symm
  have hQd : q ^ N.factorization q ∣ σ 1 (p ^ N.factorization p) * σ 1 A := by
    refine hcopQ.dvd_of_dvd_mul_right ⟨2 * (p ^ N.factorization p * A), ?_⟩
    calc σ 1 (p ^ N.factorization p) * σ 1 A * σ 1 (q ^ N.factorization q)
        = σ 1 (q ^ N.factorization q) * (σ 1 (p ^ N.factorization p) * σ 1 A) := mul_comm _ _
      _ = 2 * (q ^ N.factorization q * (p ^ N.factorization p * A)) := hsig
      _ = q ^ N.factorization q * (2 * (p ^ N.factorization p * A)) := by ring
  have hXA0 : 0 < p ^ N.factorization p * A := Nat.mul_pos (pow_pos hp.pos _) hA0
  have hRS0 : 0 < σ 1 (p ^ N.factorization p) * σ 1 A :=
    Nat.mul_pos (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)) (sigma_pos 1 A hA0.ne')
  have hQle := Nat.le_of_dvd hRS0 hQd
  have hXAN : p ^ N.factorization p * A ∣ N :=
    (dvd_mul_left _ _).trans (dvd_of_eq hN.symm)
  have hXAlt : p ^ N.factorization p * A < N := by
    have h3 := Nat.mul_le_mul_right (p ^ N.factorization p * A) hQ2
    have : p ^ N.factorization p * A < q ^ N.factorization q * (p ^ N.factorization p * A) := by
      linarith
    exact lt_of_lt_of_eq this hN.symm
  have hXA := comp_sigma_lt_two_mul h hXAN hXAlt.ne
  rw [hsigXA] at hXA
  have hQlt : q ^ N.factorization q < 2 * (p ^ N.factorization p * A) := lt_of_le_of_lt hQle hXA
  calc N = q ^ N.factorization q * (p ^ N.factorization p * A) := hN
    _ < (2 * (p ^ N.factorization p * A)) * (p ^ N.factorization p * A) :=
        Nat.mul_lt_mul_of_pos_right hQlt hXA0
    _ = 2 * A ^ 2 * (p ^ N.factorization p * p ^ N.factorization p) := by ring
    _ < 2 * A ^ 2 * ((36 * A ^ 4) * (36 * A ^ 4)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_self_lt_mul_self h2)
          (Nat.mul_pos two_pos (pow_pos hA0 2))
    _ = 2592 * A ^ 10 := by ring

/-- `N < 2592 * A ^ 10` for any two distinct prime factors `p`, `q` of an odd perfect number
`N`, with `A = N / (q ^ a * p ^ e)`. At most one prime factor has an odd exponent, so one of
`p`, `q` has an even exponent, and the bound is symmetric in `p`, `q`. It does not bound `N`
and does not decide existence. No published source was checked; novelty not verified. -/
theorem lt_mul_complement_pow_ten_of_ne {N p q : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hq : q.Prime) (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q) :
    N < 2592 * (N / (q ^ N.factorization q * p ^ N.factorization p)) ^ 10 := by
  by_cases he : Even (N.factorization p)
  · exact lt_mul_complement_pow_ten h hp hq hpN hqN hpq he
  · have heq : Even (N.factorization q) := by
      by_contra hq'
      exact hpq ((existsUnique_odd_exponent h).unique ⟨hp, Nat.not_even_iff_odd.mp he⟩
        ⟨hq, Nat.not_even_iff_odd.mp hq'⟩)
    have := lt_mul_complement_pow_ten h hq hp hqN hpN (Ne.symm hpq) heq
    rwa [mul_comm (p ^ N.factorization p)] at this

end OddPerfect

#print axioms OddPerfect.component_lt_three_mul
#print axioms OddPerfect.component_lt_thirty_six_mul_pow_four
#print axioms OddPerfect.lt_mul_complement_pow_ten
#print axioms OddPerfect.lt_mul_complement_pow_ten_of_ne
