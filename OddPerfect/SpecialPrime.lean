import OddPerfect.Euler
import OddPerfect.Abundancy
import OddPerfect.Seed.Example

/-!
# The special prime of an odd perfect number

Classical consequences of Euler's form `N = q ^ k * m ^ 2`: congruences and divisibility
facts for the special prime `q`, the abundancy split between `q ^ k` and `m ^ 2`, the
refined Touchard congruence, and small abundant divisor obstructions such as `105 ∤ N`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q : ℕ}

/-! ## Part A: the special prime -/

/-- A prime with odd exponent in an odd perfect number is `≡ 1 (mod 4)`, and so is its
exponent. -/
theorem special_mod_four (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    q % 4 = 1 ∧ N.factorization q % 4 = 1 := by
  obtain ⟨q', -, -, h4, hk4, hev⟩ := exists_special_prime h
  obtain rfl : q = q' := by
    by_contra hne
    exact Nat.not_even_iff_odd.mpr hodd (hev q hq hne)
  exact ⟨h4, hk4⟩

/-- Every prime other than the special prime has an even exponent. -/
theorem even_factorization_of_ne (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) :
    Even (N.factorization p) := by
  by_contra hev
  exact hpq ((existsUnique_odd_exponent h).unique ⟨hp, Nat.not_even_iff_odd.mp hev⟩ ⟨hq, hodd⟩)

/-- A prime factor other than the special prime divides `N` at least to the second power. -/
theorem sq_dvd_of_ne_special (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) (hpN : p ∣ N) :
    p ^ 2 ∣ N := by
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hp hpq
  have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  rw [hp.pow_dvd_iff_le_factorization h.ne_zero]
  omega

/-- `q + 1` divides the divisor sum of the special component. -/
theorem succ_dvd_sigma_special (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : q + 1 ∣ σ 1 (q ^ N.factorization q) := by
  have h1 : σ 1 (q ^ 1) = q + 1 := by
    rw [sigma_one_apply_prime_pow hq]
    simp [Finset.sum_range_succ, add_comm]
  rw [← h1]
  obtain ⟨j, hj⟩ := hodd
  exact OPNExample.sigma_prime_pow_dvd hq ⟨j + 1, by omega⟩

/-- `(q + 1) / 2` divides `N`. -/
theorem half_succ_dvd (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    (q + 1) / 2 ∣ N := by
  have h4 := (special_mod_four h hq hodd).1
  have hd : q + 1 ∣ 2 * N := (succ_dvd_sigma_special hq hodd).trans
    (OPNStarter.component_sigma_dvd h.perfect hq rfl)
  rw [show q + 1 = 2 * ((q + 1) / 2) by omega] at hd
  exact Nat.dvd_of_mul_dvd_mul_left two_pos hd

/-- Every odd prime dividing `q + 1` divides `N` and differs from `q`. -/
theorem prime_dvd_of_dvd_succ_special (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ q + 1) :
    r ∣ N ∧ r ≠ q := by
  refine ⟨OPNStarter.force_prime h.perfect hq rfl hr hr2
    (hrq.trans (succ_dvd_sigma_special hq hodd)), ?_⟩
  rintro rfl
  exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_refl r)).mp hrq))

/-- The divisor sum of a prime power `q ^ k` is coprime to `q`. -/
theorem coprime_sigma_prime_pow (hq : q.Prime) (k : ℕ) : Nat.Coprime (σ 1 (q ^ k)) q := by
  rw [Nat.coprime_comm, hq.coprime_iff_not_dvd, sigma_one_apply_prime_pow hq,
    Finset.sum_range_succ', pow_zero]
  intro hd
  have : q ∣ ∑ i ∈ Finset.range k, q ^ (i + 1) :=
    Finset.dvd_sum fun i _ => dvd_pow_self q (Nat.succ_ne_zero i)
  exact hq.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right this).mp hd))

/-- Shared facts about an Euler decomposition `N = q ^ k * m ^ 2` with `q ∤ m`. -/
private lemma euler_setup (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    Nat.Coprime (q ^ k) (m ^ 2) ∧ N.factorization q = k ∧ Odd k ∧
      σ 1 (q ^ k) * σ 1 (m ^ 2) = 2 * N := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hcop : Nat.Coprime (q ^ k) (m ^ 2) := (hq.coprime_iff_not_dvd.mpr hqm).pow k 2
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  refine ⟨hcop, hfac, ?_, ?_⟩
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  · rw [← isMultiplicative_sigma.map_mul_of_coprime hcop, ← hN]
    exact h.sigma_eq

/-- In Euler's form, `σ(q ^ k)` divides `2 * m ^ 2`. -/
theorem sigma_special_dvd (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : σ 1 (q ^ k) ∣ 2 * m ^ 2 := by
  obtain ⟨-, -, -, hprod⟩ := euler_setup h hq hN hqm
  refine ((coprime_sigma_prime_pow hq k).pow_right k).dvd_of_dvd_mul_right
    ⟨σ 1 (m ^ 2), ?_⟩
  rw [hprod, hN]
  ring

/-- In Euler's form, `q ^ k` divides `σ(m ^ 2)`. -/
theorem pow_dvd_sigma_sq (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q ^ k ∣ σ 1 (m ^ 2) := by
  obtain ⟨-, -, -, hprod⟩ := euler_setup h hq hN hqm
  refine (((coprime_sigma_prime_pow hq k).pow_right k).symm).dvd_of_dvd_mul_right
    ⟨2 * m ^ 2, ?_⟩
  rw [mul_comm, hprod, hN]
  ring

/-- In Euler's form, `σ(m ^ 2)` is odd. -/
theorem odd_sigma_sq (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : Odd (σ 1 (m ^ 2)) := by
  obtain ⟨-, hfac, hk, hprod⟩ := euler_setup h hq hN hqm
  have h4 := (special_mod_four h hq (hfac ▸ hk)).1
  have h2q : 2 ∣ σ 1 (q ^ k) := by
    rw [← hfac]
    exact (show 2 ∣ q + 1 by omega).trans (succ_dvd_sigma_special hq (hfac ▸ hk))
  rcases Nat.even_or_odd (σ 1 (m ^ 2)) with he | ho
  · have h22 := mul_dvd_mul h2q he.two_dvd
    rw [hprod] at h22
    have := h.not_two_dvd
    omega
  · exact ho

/-- In Euler's form, `q ^ k < 2 * m ^ 2`. -/
theorem pow_lt_two_mul_sq (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q ^ k < 2 * m ^ 2 := by
  obtain ⟨-, -, hk, -⟩ := euler_setup h hq hN hqm
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hle := Nat.le_of_dvd (by positivity) (sigma_special_dvd h hq hN hqm)
  have hlt : q ^ k < σ 1 (q ^ k) := by
    rw [sigma_one_apply_prime_pow hq, Finset.sum_range_succ]
    have : 1 ≤ ∑ i ∈ Finset.range k, q ^ i := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by obtain ⟨i, hi⟩ := hk; omega⟩
      rw [Finset.sum_range_succ']
      simp
    omega
  omega

/-- The special component has abundancy below `5/4`. -/
theorem abundancy_special_lt (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) : abundancy (q ^ N.factorization q) < 5 / 4 := by
  have h4 := (special_mod_four h hq hodd).1
  have h5 : (5 : ℚ) ≤ q := by
    have := hq.two_le
    exact_mod_cast (show 5 ≤ q by omega)
  refine (abundancy_prime_pow_lt hq _).trans_le ?_
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- In Euler's form, `8/5 < abundancy (m ^ 2) < 2`. -/
theorem abundancy_sq_bounds (h : OddPerfect N) (hq : q.Prime) {k m : ℕ}
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    8 / 5 < abundancy (m ^ 2) ∧ abundancy (m ^ 2) < 2 := by
  obtain ⟨hcop, hfac, hk, -⟩ := euler_setup h hq hN hqm
  have hA : abundancy (q ^ k) * abundancy (m ^ 2) = 2 := by
    rw [← abundancy_mul_of_coprime hcop, ← hN]
    exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hlt : abundancy (q ^ k) < 5 / 4 := hfac ▸ abundancy_special_lt h hq (hfac ▸ hk)
  have hgt : 1 + (q : ℚ)⁻¹ ≤ abundancy (q ^ k) :=
    one_add_inv_le_abundancy_prime_pow hq hk.pos
  have hinv : (0 : ℚ) < (q : ℚ)⁻¹ := by
    have : (0 : ℚ) < q := by exact_mod_cast hq.pos
    positivity
  have hm0 : 0 ≤ abundancy (m ^ 2) := by unfold abundancy; positivity
  constructor <;> nlinarith

/-! ## Part B: refined congruences -/

/-- Refinement of Touchard's congruence. -/
theorem mod_refined (h : OddPerfect N) :
    N % 12 = 1 ∨ N % 468 = 117 ∨ N % 324 = 81 := by
  have h4 := mod_four h
  by_cases h3 : 3 ∣ N
  · obtain ⟨q, hq, -, hq4, -, hev⟩ := exists_special_prime h
    obtain ⟨j, hj⟩ := hev 3 Nat.prime_three (by rintro rfl; omega)
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization h.ne_zero).mp h3
    by_cases he : N.factorization 3 = 2
    · have h13 := OPNStarter.thirteen_dvd_of_three_sq h.perfect he
      have h9 : 3 ^ 2 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization h.ne_zero).mpr (by omega)
      right; left
      omega
    · have h81 : 3 ^ 4 ∣ N := (Nat.prime_three.pow_dvd_iff_le_factorization h.ne_zero).mpr (by omega)
      right; right
      omega
  · rcases touchard h with h12 | h36
    · exact Or.inl h12
    · exact absurd (by omega) h3

/-! ## Part C: abundant divisor obstructions -/

private lemma sigma_five : σ 1 5 = 6 := by
  rw [show (5 : ℕ) = 5 ^ 1 by norm_num, sigma_one_apply_prime_pow Nat.prime_five]
  decide

private lemma sigma_thirteen : σ 1 13 = 14 := by
  rw [show (13 : ℕ) = 13 ^ 1 by norm_num, sigma_one_apply_prime_pow (by decide)]
  decide

/-- An abundant divisor excludes perfection. -/
private lemma not_of_abundant_dvd {d : ℕ} (h : OddPerfect N) (hd : d ∣ N)
    (hσ : 2 * d < σ 1 d) : False := by
  rw [sigma_one_apply] at hσ
  have hab := (Nat.abundant_iff_sum_divisors.mpr hσ).of_dvd hd h.ne_zero
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient h.pos.ne).mp h.perfect).1 hab

/-- The classical obstruction: an odd perfect number is not divisible by `105`. -/
theorem not_105_dvd (h : OddPerfect N) : ¬ 105 ∣ N := by
  intro h105
  have h9 := sq_dvd_of_prime_dvd_of_mod_four_eq_three h Nat.prime_three (by omega) (by decide)
  have h49 := sq_dvd_of_prime_dvd_of_mod_four_eq_three h (by decide : Nat.Prime 7)
    (by omega) (by decide)
  have hd : 3 ^ 2 * 5 * 7 ^ 2 ∣ N :=
    (show Nat.Coprime (3 ^ 2 * 5) (7 ^ 2) by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime (3 ^ 2) 5 by decide).mul_dvd_of_dvd_of_dvd h9 (by omega)) h49
  apply not_of_abundant_dvd h hd
  repeat' rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
  rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_five,
    sigma_one_apply_prime_pow (by decide : Nat.Prime 7)]
  decide

/-- Restatement of `not_105_dvd`. -/
theorem not_seven_dvd_of_three_five (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N) :
    ¬ 7 ∣ N := fun h7 => not_105_dvd h (by omega)

/-- An odd perfect number is not divisible by all of `3`, `5`, `11`, and `13`. -/
theorem not_three_five_eleven_thirteen (h : OddPerfect N) :
    ¬ (3 ∣ N ∧ 5 ∣ N ∧ 11 ∣ N ∧ 13 ∣ N) := by
  rintro ⟨h3, h5, h11, h13⟩
  have p11 : Nat.Prime 11 := by decide
  have p13 : Nat.Prime 13 := by decide
  have h9 := sq_dvd_of_prime_dvd_of_mod_four_eq_three h Nat.prime_three h3 (by decide)
  have h121 := sq_dvd_of_prime_dvd_of_mod_four_eq_three h p11 h11 (by decide)
  have h1089 := (show Nat.Coprime (3 ^ 2) (11 ^ 2) by decide).mul_dvd_of_dvd_of_dvd h9 h121
  by_cases ho : Odd (N.factorization 5)
  · have h169 := sq_dvd_of_ne_special h Nat.prime_five ho p13 (by decide) h13
    have hd : 3 ^ 2 * 11 ^ 2 * 5 * 13 ^ 2 ∣ N :=
      (show Nat.Coprime (3 ^ 2 * 11 ^ 2 * 5) (13 ^ 2) by decide).mul_dvd_of_dvd_of_dvd
        ((show Nat.Coprime (3 ^ 2 * 11 ^ 2) 5 by decide).mul_dvd_of_dvd_of_dvd h1089 h5) h169
    apply not_of_abundant_dvd h hd
    repeat' rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow p11,
      sigma_five, sigma_one_apply_prime_pow p13]
    decide
  · obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.mp ho
    have h1 := (Nat.prime_five.dvd_iff_one_le_factorization h.ne_zero).mp h5
    have h25 : 5 ^ 2 ∣ N :=
      (Nat.prime_five.pow_dvd_iff_le_factorization h.ne_zero).mpr (by omega)
    have hd : 3 ^ 2 * 11 ^ 2 * 5 ^ 2 * 13 ∣ N :=
      (show Nat.Coprime (3 ^ 2 * 11 ^ 2 * 5 ^ 2) 13 by decide).mul_dvd_of_dvd_of_dvd
        ((show Nat.Coprime (3 ^ 2 * 11 ^ 2) (5 ^ 2) by decide).mul_dvd_of_dvd_of_dvd h1089 h25)
        h13
    apply not_of_abundant_dvd h hd
    repeat' rw [isMultiplicative_sigma.map_mul_of_coprime (by decide)]
    rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow p11,
      sigma_one_apply_prime_pow Nat.prime_five, sigma_thirteen]
    decide

end OddPerfect

#print axioms OddPerfect.special_mod_four
#print axioms OddPerfect.even_factorization_of_ne
#print axioms OddPerfect.sq_dvd_of_ne_special
#print axioms OddPerfect.succ_dvd_sigma_special
#print axioms OddPerfect.half_succ_dvd
#print axioms OddPerfect.prime_dvd_of_dvd_succ_special
#print axioms OddPerfect.coprime_sigma_prime_pow
#print axioms OddPerfect.sigma_special_dvd
#print axioms OddPerfect.pow_dvd_sigma_sq
#print axioms OddPerfect.odd_sigma_sq
#print axioms OddPerfect.pow_lt_two_mul_sq
#print axioms OddPerfect.abundancy_special_lt
#print axioms OddPerfect.abundancy_sq_bounds
#print axioms OddPerfect.mod_refined
#print axioms OddPerfect.not_105_dvd
#print axioms OddPerfect.not_seven_dvd_of_three_five
#print axioms OddPerfect.not_three_five_eleven_thirteen
