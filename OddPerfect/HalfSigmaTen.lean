import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr
import Mathlib.Data.Nat.ModEq

/-!
# Half of `σ(p ^ 10) + 1` is never a square

Restricted result; no published source was checked; novelty not verified.

For an odd prime `p` the number `σ(p ^ 10) + 1 = p ^ 10 + p ^ 9 + ... + p + 2` is never of the
form `2 z ^ 2`. The module `HalfSigmaSix` treats the exponent `6` by the same method. Pure
arithmetic: no perfect number appears, and nothing here bears on whether an odd perfect number
exists, which remains open.

* `sigma_prime_pow_ten_add_one_ne_two_mul_sq`: `σ 1 (p ^ 10) + 1 ≠ 2 * z ^ 2`.
* `prime_pow_ten_poly_ne_two_mul_sq`: the same statement written as a polynomial in `p`.

Controls. The hypothesis `p ≠ 2` is needed at exponent `6`: `2 ^ 6 + ... + 2 + 2 = 128 = 2 * 8 ^ 2`.
At the exponent `2` the odd prime `5` gives a solution: `5 ^ 2 + 5 + 2 = 32 = 2 * 4 ^ 2`.

Proof. Put `B = 2048 + 512 p + 448 p ^ 2 + 400 p ^ 3 + 363 p ^ 4`. Then
`(2048 z) ^ 2 - B ^ 2 = p ^ 5 Q(p)` with
`Q = 1367040 + 1611904 p + 1806752 p ^ 2 + 1965383 p ^ 3 + 2097152 p ^ 4 + 2097152 p ^ 5`.
As `p ∤ B`, the prime `p ^ 5` divides `2048 z - B` or `2048 z + B`: `2048 Z = B + c p ^ 5` with
`Z = ± z`. Size bounds (`|z| < p ^ 5`, `0 < B < 197 p ^ 5`) give `-2244 ≤ c ≤ 2047`.
Substituting and cancelling `p ^ 5` leaves `c ^ 2 p ^ 5 + 2 B c = Q`, so modulo `p` the prime
divides `1024 (4 c - 1335)`, hence `4 c - 1335`, an odd number of size at most `10311`; so
`p ≤ 10311`. For each odd `p` from `3` to `10311` one of ten moduli `m ≤ 59` shows that
`p ^ 10 + ... + p + 2` is not `2` times a square modulo `m`; the kernel checks the residue
tables and the cover.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace HalfSigmaTen

/-- The polynomial `p ^ 10 + p ^ 9 + ... + p + 2`. -/
private def H (p : ℕ) : ℕ :=
  p ^ 10 + p ^ 9 + p ^ 8 + p ^ 7 + p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2

/-- Reduction modulo `m`. -/
private lemma red (m : ℕ) {p z : ℕ} (h : H p = 2 * z ^ 2) :
    H (p % m) % m = 2 * (z % m) ^ 2 % m := by
  have hp := Nat.mod_modEq p m
  have hz := Nat.mod_modEq z m
  have h1 : H (p % m) ≡ H p [MOD m] := by unfold H; gcongr
  have h2 : 2 * (z % m) ^ 2 ≡ 2 * z ^ 2 [MOD m] := by gcongr
  rw [h] at h1
  exact h1.trans h2.symm

private lemma res_56 : ∀ r < 56, ∀ y < 56, 35742769366359930 / 2 ^ r % 2 = 1 →
    H r % 56 ≠ 2 * y ^ 2 % 56 := by
  decide +kernel

private lemma res_17 : ∀ r < 17, ∀ y < 17, 32754 / 2 ^ r % 2 = 1 →
    H r % 17 ≠ 2 * y ^ 2 % 17 := by
  decide +kernel

private lemma res_47 : ∀ r < 47, ∀ y < 47, 43428978630616 / 2 ^ r % 2 = 1 →
    H r % 47 ≠ 2 * y ^ 2 % 47 := by
  decide +kernel

private lemma res_37 : ∀ r < 37, ∀ y < 37, 17397116618 / 2 ^ r % 2 = 1 →
    H r % 37 ≠ 2 * y ^ 2 % 37 := by
  decide +kernel

private lemma res_53 : ∀ r < 53, ∀ y < 53, 25660661460248 / 2 ^ r % 2 = 1 →
    H r % 53 ≠ 2 * y ^ 2 % 53 := by
  decide +kernel

private lemma res_29 : ∀ r < 29, ∀ y < 29, 90798560 / 2 ^ r % 2 = 1 →
    H r % 29 ≠ 2 * y ^ 2 % 29 := by
  decide +kernel

private lemma res_59 : ∀ r < 59, ∀ y < 59, 159970082453730698 / 2 ^ r % 2 = 1 →
    H r % 59 ≠ 2 * y ^ 2 % 59 := by
  decide +kernel

private lemma res_19 : ∀ r < 19, ∀ y < 19, 8880 / 2 ^ r % 2 = 1 →
    H r % 19 ≠ 2 * y ^ 2 % 19 := by
  decide +kernel

private lemma res_32 : ∀ r < 32, ∀ y < 32, 1608416250 / 2 ^ r % 2 = 1 →
    H r % 32 ≠ 2 * y ^ 2 % 32 := by
  decide +kernel

private lemma res_9 : ∀ r < 9, ∀ y < 9, 18 / 2 ^ r % 2 = 1 →
    H r % 9 ≠ 2 * y ^ 2 % 9 := by
  decide +kernel

private lemma cover : ∀ a < 81, ∀ b < 128, 128 * a + b < 10312 →
    (128 * a + b) % 2 = 1 → 3 ≤ 128 * a + b →
      35742769366359930 / 2 ^ ((128 * a + b) % 56) % 2 = 1 ∨
      32754 / 2 ^ ((128 * a + b) % 17) % 2 = 1 ∨
      43428978630616 / 2 ^ ((128 * a + b) % 47) % 2 = 1 ∨
      17397116618 / 2 ^ ((128 * a + b) % 37) % 2 = 1 ∨
      25660661460248 / 2 ^ ((128 * a + b) % 53) % 2 = 1 ∨
      90798560 / 2 ^ ((128 * a + b) % 29) % 2 = 1 ∨
      159970082453730698 / 2 ^ ((128 * a + b) % 59) % 2 = 1 ∨
      8880 / 2 ^ ((128 * a + b) % 19) % 2 = 1 ∨
      1608416250 / 2 ^ ((128 * a + b) % 32) % 2 = 1 ∨
      18 / 2 ^ ((128 * a + b) % 9) % 2 = 1 := by
  refine @of_decide_eq_true _ (@Nat.decidableBallLT 81 _ fun _ _ =>
    @Nat.decidableBallLT 128 _ fun _ _ => inferInstance) ?_
  decide +kernel

/-- The core: for an odd prime `p` and an integer `z`, the equation
`p ^ 10 + ... + p + 2 = 2 z ^ 2` forces `p ≤ 10311`. -/
private lemma core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : ℤ}
    (h : (p : ℤ) ^ 10 + p ^ 9 + p ^ 8 + p ^ 7 + p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2 =
      2 * z ^ 2) : p ≤ 10311 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hP3 : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hP0 : (0 : ℤ) < p := by linarith
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn2 : ∀ k : ℕ, ¬ (p : ℤ) ∣ 2 ^ k := by
    intro k hk
    have hk' : p ∣ 2 ^ k := by exact_mod_cast hk
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hk'))
  set B : ℤ := 2048 + 512 * p + 448 * p ^ 2 + 400 * p ^ 3 + 363 * p ^ 4 with hBdef
  have hB : ¬ (p : ℤ) ∣ B := by
    intro hd
    have h11 : (p : ℤ) ∣ 2 ^ 11 := by
      have : (p : ℤ) ∣ B - p * (512 + 448 * p + 400 * p ^ 2 + 363 * p ^ 3) :=
        dvd_sub hd (dvd_mul_right _ _)
      have e : B - p * (512 + 448 * p + 400 * p ^ 2 + 363 * p ^ 3) = 2 ^ 11 := by
        rw [hBdef]; ring
      rwa [e] at this
    exact hn2 11 h11
  have hid : (2048 * z - B) * (2048 * z + B) = (p : ℤ) ^ 5 * (1367040 + 1611904 * p +
      1806752 * p ^ 2 + 1965383 * p ^ 3 + 2097152 * p ^ 4 + 2097152 * p ^ 5) := by
    rw [hBdef]; linear_combination (-2097152 : ℤ) * h
  have hboth : ¬ ((p : ℤ) ∣ 2048 * z - B ∧ (p : ℤ) ∣ 2048 * z + B) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 * B := by
      have := dvd_sub h2 h1
      have e : 2048 * z + B - (2048 * z - B) = 2 * B := by ring
      rwa [e] at this
    rcases hpi.dvd_or_dvd h3 with h4 | h4
    · exact hn2 1 (by simpa using h4)
    · exact hB h4
  have hdvd : (p : ℤ) ^ 5 ∣ (2048 * z - B) * (2048 * z + B) := by
    rw [hid]; exact dvd_mul_right _ _
  obtain ⟨Z, c, hZz, hZc⟩ : ∃ Z c : ℤ, Z ^ 2 = z ^ 2 ∧ 2048 * Z = B + c * (p : ℤ) ^ 5 := by
    by_cases hd : (p : ℤ) ∣ 2048 * z + B
    · have hn : ¬ (p : ℤ) ∣ 2048 * z - B := fun h1 => hboth ⟨h1, hd⟩
      have hc : IsCoprime ((p : ℤ) ^ 5) (2048 * z - B) :=
        ((_root_.Prime.coprime_iff_not_dvd hpi).mpr hn).pow_left
      obtain ⟨d, hd'⟩ := hc.dvd_of_dvd_mul_left hdvd
      exact ⟨-z, -d, by ring, by linear_combination (-1 : ℤ) * hd'⟩
    · have hc : IsCoprime ((p : ℤ) ^ 5) (2048 * z + B) :=
        ((_root_.Prime.coprime_iff_not_dvd hpi).mpr hd).pow_left
      rw [mul_comm] at hdvd
      obtain ⟨d, hd'⟩ := hc.dvd_of_dvd_mul_left hdvd
      exact ⟨z, d, rfl, by linear_combination hd'⟩
  -- size bounds
  have e1 : 3 * (p : ℤ) ≤ p ^ 2 := by nlinarith
  have e2 : 3 * (p : ℤ) ^ 2 ≤ p ^ 3 := by nlinarith [pow_pos hP0 2]
  have e3 : 3 * (p : ℤ) ^ 3 ≤ p ^ 4 := by nlinarith [pow_pos hP0 3]
  have e4 : 3 * (p : ℤ) ^ 4 ≤ p ^ 5 := by nlinarith [pow_pos hP0 4]
  have e5 : 3 * (p : ℤ) ^ 5 ≤ p ^ 6 := by nlinarith [pow_pos hP0 5]
  have e6 : 3 * (p : ℤ) ^ 6 ≤ p ^ 7 := by nlinarith [pow_pos hP0 6]
  have e7 : 3 * (p : ℤ) ^ 7 ≤ p ^ 8 := by nlinarith [pow_pos hP0 7]
  have e8 : 3 * (p : ℤ) ^ 8 ≤ p ^ 9 := by nlinarith [pow_pos hP0 8]
  have e9 : 3 * (p : ℤ) ^ 9 ≤ p ^ 10 := by nlinarith [pow_pos hP0 9]
  have hZ2 : Z ^ 2 < ((p : ℤ) ^ 5) ^ 2 := by
    have : ((p : ℤ) ^ 5) ^ 2 = p ^ 10 := by ring
    rw [this, hZz]; linarith
  have hZabs := abs_lt.mp (abs_lt_of_sq_lt_sq hZ2 (pow_pos hP0 5).le)
  have hBlt : B < 197 * p ^ 5 := by rw [hBdef]; linarith
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hc1 : c ≤ 2047 := by
    by_contra hc
    have := mul_nonneg (show (0 : ℤ) ≤ c - 2048 by linarith) (pow_pos hP0 5).le
    linarith
  have hc2 : -2244 ≤ c := by
    by_contra hc
    have := mul_nonneg (show (0 : ℤ) ≤ -2245 - c by linarith) (pow_pos hP0 5).le
    linarith
  -- substitution and cancellation of `p ^ 5`
  have hq : c ^ 2 * (p : ℤ) ^ 5 + 2 * B * c - (1367040 + 1611904 * p + 1806752 * p ^ 2 +
      1965383 * p ^ 3 + 2097152 * p ^ 4 + 2097152 * p ^ 5) = 0 := by
    have h0 : (p : ℤ) ^ 5 * (c ^ 2 * (p : ℤ) ^ 5 + 2 * B * c - (1367040 + 1611904 * p +
        1806752 * p ^ 2 + 1965383 * p ^ 3 + 2097152 * p ^ 4 + 2097152 * p ^ 5)) = 0 := by
      rw [hBdef] at hZc ⊢
      linear_combination (-(2048 * Z + (2048 + 512 * p + 448 * p ^ 2 + 400 * p ^ 3 +
        363 * p ^ 4) + c * p ^ 5)) * hZc + 4194304 * hZz - 2097152 * h
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 5 hP0.ne')
  -- modulo `p`: `p ∣ 4 c - 1335`, hence `p ≤ 10311`
  have h1024 : (p : ℤ) ∣ 2 ^ 10 * (4 * c - 1335) :=
    ⟨-(c ^ 2 * p ^ 4 + 2 * c * (512 + 448 * p + 400 * p ^ 2 + 363 * p ^ 3) -
      (1611904 + 1806752 * p + 1965383 * p ^ 2 + 2097152 * p ^ 3 + 2097152 * p ^ 4)), by
      rw [hBdef] at hq; linear_combination hq⟩
  have h4c : (p : ℤ) ∣ 4 * c - 1335 := by
    rcases hpi.dvd_or_dvd h1024 with h4 | h4
    · exact absurd h4 (hn2 10)
    · exact h4
  obtain ⟨m, hm⟩ := h4c
  have hple : (p : ℤ) ≤ 10311 := by
    rcases (show 1 ≤ m ∨ m ≤ -1 ∨ m = 0 by omega) with hm1 | hm1 | hm1
    · have := mul_nonneg hP0.le (show (0 : ℤ) ≤ m - 1 by linarith)
      nlinarith
    · have := mul_nonneg hP0.le (show (0 : ℤ) ≤ -1 - m by linarith)
      nlinarith
    · subst hm1; omega
  omega

/-- The natural number form, through the bound of `core` and the residue cover. -/
private lemma main {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : H p ≠ 2 * z ^ 2 := by
  intro hz
  have hz' := congrArg (fun n : ℕ => (n : ℤ)) hz
  simp only [H] at hz'
  push_cast at hz'
  have hle := core hp hp2 hz'
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hcov := cover (p / 128) (by omega) (p % 128) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at hcov
  have hb := hcov (by omega) hodd h3
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb
  · exact res_56 (p % 56) (Nat.mod_lt _ (by norm_num)) (z % 56) (Nat.mod_lt _ (by norm_num))
      hb (red 56 hz)
  · exact res_17 (p % 17) (Nat.mod_lt _ (by norm_num)) (z % 17) (Nat.mod_lt _ (by norm_num))
      hb (red 17 hz)
  · exact res_47 (p % 47) (Nat.mod_lt _ (by norm_num)) (z % 47) (Nat.mod_lt _ (by norm_num))
      hb (red 47 hz)
  · exact res_37 (p % 37) (Nat.mod_lt _ (by norm_num)) (z % 37) (Nat.mod_lt _ (by norm_num))
      hb (red 37 hz)
  · exact res_53 (p % 53) (Nat.mod_lt _ (by norm_num)) (z % 53) (Nat.mod_lt _ (by norm_num))
      hb (red 53 hz)
  · exact res_29 (p % 29) (Nat.mod_lt _ (by norm_num)) (z % 29) (Nat.mod_lt _ (by norm_num))
      hb (red 29 hz)
  · exact res_59 (p % 59) (Nat.mod_lt _ (by norm_num)) (z % 59) (Nat.mod_lt _ (by norm_num))
      hb (red 59 hz)
  · exact res_19 (p % 19) (Nat.mod_lt _ (by norm_num)) (z % 19) (Nat.mod_lt _ (by norm_num))
      hb (red 19 hz)
  · exact res_32 (p % 32) (Nat.mod_lt _ (by norm_num)) (z % 32) (Nat.mod_lt _ (by norm_num))
      hb (red 32 hz)
  · exact res_9 (p % 9) (Nat.mod_lt _ (by norm_num)) (z % 9) (Nat.mod_lt _ (by norm_num))
      hb (red 9 hz)

end HalfSigmaTen

open HalfSigmaTen

/-- **Polynomial form.** For an odd prime `p`, `p ^ 10 + p ^ 9 + ... + p + 2` is never of the
form `2 z ^ 2`. Restricted result; novelty not verified. -/
theorem prime_pow_ten_poly_ne_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ 10 + p ^ 9 + p ^ 8 + p ^ 7 + p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2 ≠
      2 * z ^ 2 :=
  main hp hp2

/-- **Half of `σ(p ^ 10) + 1` never a square.** For an odd prime `p`, `σ(p ^ 10) + 1` is never
of the form `2 z ^ 2`. Restricted result; novelty not verified. -/
theorem sigma_prime_pow_ten_add_one_ne_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (p ^ 10) + 1 ≠ 2 * z ^ 2 := by
  have hs : σ 1 (p ^ 10) =
      p ^ 10 + p ^ 9 + p ^ 8 + p ^ 7 + p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  rw [hs]
  exact prime_pow_ten_poly_ne_two_mul_sq hp hp2

end OddPerfect

#print axioms OddPerfect.prime_pow_ten_poly_ne_two_mul_sq
#print axioms OddPerfect.sigma_prime_pow_ten_add_one_ne_two_mul_sq
