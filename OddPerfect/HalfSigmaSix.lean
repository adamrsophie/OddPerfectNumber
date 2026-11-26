import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Half of `σ(p ^ 6) + 1` is never a square

Restricted result; no published source was checked; novelty not verified.

For an odd prime `p` the number `σ(p ^ 6) + 1 = p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2`
is never of the form `2 z ^ 2`. The module `HalfSigmaSquare` treats the exponents `2` and `4`.
Pure arithmetic: no perfect number appears, and nothing here bears on whether an odd perfect
number exists, which remains open.

* `sigma_prime_pow_six_add_one_ne_two_mul_sq`: `σ 1 (p ^ 6) + 1 ≠ 2 * z ^ 2`.
* `prime_pow_six_poly_ne_two_mul_sq`: the same statement written as a polynomial in `p`.

The hypothesis `p ≠ 2` is needed: `p = 2` gives `128 = 2 * 8 ^ 2`.

Proof. Put `B = 32 + 8 p + 7 p ^ 2`. Then
`(32 z) ^ 2 - B ^ 2 = p ^ 3 (512 p ^ 3 + 512 p ^ 2 + 463 p + 400)`. As `p ∤ B`, the prime `p`
cannot divide both `32 z - B` and `32 z + B`, so `p ^ 3` divides one of them:
`32 Z = B + c p ^ 3` with `Z = ± z`. Size bounds (`|z| < p ^ 3`, `0 < B < 5 p ^ 3`) give
`-36 ≤ c ≤ 31`. Substituting and cancelling `p ^ 3` leaves
`(c ^ 2 - 512) p ^ 3 + (14 c - 512) p ^ 2 + (16 c - 463) p + 64 c - 400 = 0`, so
`p ∣ 4 c - 25`, a nonzero number of size at most `169`; hence `p ≤ 169`. A kernel checked
finite search over `2 ≤ p ≤ 169` and the `68` values of `c` shows the cubic never vanishes.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace HalfSigmaSix

/-- The finite part: for `2 ≤ q < 170` and `c = k - 36` with `k < 68` the cubic is nonzero.
Checked by the kernel. -/
private lemma cubic_ne_zero_small : ∀ q : ℕ, q < 170 → ∀ k : ℕ, k < 68 → 2 ≤ q →
    ((((k : ℤ) - 36) ^ 2 - 512) * (q : ℤ) ^ 3 + (14 * ((k : ℤ) - 36) - 512) * (q : ℤ) ^ 2 +
      (16 * ((k : ℤ) - 36) - 463) * (q : ℤ) + 64 * ((k : ℤ) - 36) - 400) ≠ 0 := by
  decide +kernel

/-- The core: for an odd prime `p` and an integer `z`, the equation
`p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2 = 2 z ^ 2` is impossible. -/
private lemma core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : ℤ}
    (h : (p : ℤ) ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2 = 2 * z ^ 2) : False := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hP3 : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hP0 : (0 : ℤ) < p := by linarith
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- `p` divides no power of `2`
  have hn2 : ∀ k : ℕ, ¬ (p : ℤ) ∣ 2 ^ k := by
    intro k hk
    have hk' : p ∣ 2 ^ k := by exact_mod_cast hk
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hk'))
  -- `p ∤ B`
  have hB : ¬ (p : ℤ) ∣ 32 + 8 * p + 7 * p ^ 2 := by
    intro hd
    have h32 : (p : ℤ) ∣ 2 ^ 5 := by
      have : (p : ℤ) ∣ (32 + 8 * p + 7 * p ^ 2) - p * (8 + 7 * p) :=
        dvd_sub hd (dvd_mul_right _ _)
      have e : (32 + 8 * (p : ℤ) + 7 * p ^ 2) - p * (8 + 7 * p) = 2 ^ 5 := by ring
      rwa [e] at this
    exact hn2 5 h32
  -- the identity `(32 z - B) (32 z + B) = p ^ 3 Q`
  have hid : (32 * z - (32 + 8 * p + 7 * p ^ 2)) * (32 * z + (32 + 8 * p + 7 * p ^ 2)) =
      (p : ℤ) ^ 3 * (512 * p ^ 3 + 512 * p ^ 2 + 463 * p + 400) := by
    linear_combination (-512 : ℤ) * h
  -- `p` does not divide both factors
  have hboth : ¬ ((p : ℤ) ∣ 32 * z - (32 + 8 * p + 7 * p ^ 2) ∧
      (p : ℤ) ∣ 32 * z + (32 + 8 * p + 7 * p ^ 2)) := by
    rintro ⟨h1, h2⟩
    have h3 : (p : ℤ) ∣ 2 * (32 + 8 * p + 7 * p ^ 2) := by
      have := dvd_sub h2 h1
      have e : 32 * z + (32 + 8 * (p : ℤ) + 7 * p ^ 2) - (32 * z - (32 + 8 * p + 7 * p ^ 2)) =
          2 * (32 + 8 * p + 7 * p ^ 2) := by ring
      rwa [e] at this
    rcases hpi.dvd_or_dvd h3 with h4 | h4
    · exact hn2 1 (by simpa using h4)
    · exact hB h4
  have hdvd : (p : ℤ) ^ 3 ∣ (32 * z - (32 + 8 * p + 7 * p ^ 2)) *
      (32 * z + (32 + 8 * p + 7 * p ^ 2)) := by
    rw [hid]; exact dvd_mul_right _ _
  -- the splitting: `32 Z = B + c p ^ 3` with `Z ^ 2 = z ^ 2`
  obtain ⟨Z, c, hZz, hZc⟩ : ∃ Z c : ℤ, Z ^ 2 = z ^ 2 ∧
      32 * Z = (32 + 8 * p + 7 * p ^ 2) + c * (p : ℤ) ^ 3 := by
    by_cases hd : (p : ℤ) ∣ 32 * z + (32 + 8 * p + 7 * p ^ 2)
    · have hn : ¬ (p : ℤ) ∣ 32 * z - (32 + 8 * p + 7 * p ^ 2) := fun h1 => hboth ⟨h1, hd⟩
      have hc : IsCoprime ((p : ℤ) ^ 3) (32 * z - (32 + 8 * p + 7 * p ^ 2)) :=
        ((_root_.Prime.coprime_iff_not_dvd hpi).mpr hn).pow_left
      obtain ⟨d, hd'⟩ := hc.dvd_of_dvd_mul_left hdvd
      exact ⟨-z, -d, by ring, by linear_combination (-1 : ℤ) * hd'⟩
    · have hc : IsCoprime ((p : ℤ) ^ 3) (32 * z + (32 + 8 * p + 7 * p ^ 2)) :=
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
  have hZ2 : Z ^ 2 < ((p : ℤ) ^ 3) ^ 2 := by
    have : ((p : ℤ) ^ 3) ^ 2 = p ^ 6 := by ring
    rw [this, hZz]; linarith
  have hZabs := abs_lt.mp (abs_lt_of_sq_lt_sq hZ2 (pow_pos hP0 3).le)
  have hBlt : 32 + 8 * (p : ℤ) + 7 * p ^ 2 < 5 * p ^ 3 := by linarith
  have hBpos : 0 < 32 + 8 * (p : ℤ) + 7 * p ^ 2 := by positivity
  have hc1 : c ≤ 31 := by
    by_contra hc
    have := mul_nonneg (show (0 : ℤ) ≤ c - 32 by linarith) (pow_pos hP0 3).le
    linarith
  have hc2 : -36 ≤ c := by
    by_contra hc
    have := mul_nonneg (show (0 : ℤ) ≤ -37 - c by linarith) (pow_pos hP0 3).le
    linarith
  -- substitution and cancellation of `p ^ 3`
  have hcub : (c ^ 2 - 512) * (p : ℤ) ^ 3 + (14 * c - 512) * p ^ 2 + (16 * c - 463) * p +
      64 * c - 400 = 0 := by
    have h0 : (p : ℤ) ^ 3 * ((c ^ 2 - 512) * p ^ 3 + (14 * c - 512) * p ^ 2 +
        (16 * c - 463) * p + 64 * c - 400) = 0 := by
      linear_combination (-(32 * Z + (32 + 8 * p + 7 * p ^ 2) + c * p ^ 3)) * hZc +
        1024 * hZz - 512 * h
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 3 hP0.ne')
  -- modulo `p`: `p ∣ 4 c - 25`, hence `p ≤ 169`
  have h16 : (p : ℤ) ∣ 16 * (4 * c - 25) :=
    ⟨-((c ^ 2 - 512) * p ^ 2 + (14 * c - 512) * p + (16 * c - 463)), by
      linear_combination hcub⟩
  have h425 : (p : ℤ) ∣ 4 * c - 25 := by
    rcases hpi.dvd_or_dvd h16 with h4 | h4
    · exact absurd (by simpa using h4) (hn2 4)
    · exact h4
  obtain ⟨m, hm⟩ := h425
  have hple : (p : ℤ) ≤ 169 := by
    rcases (show 1 ≤ m ∨ m ≤ -1 ∨ m = 0 by omega) with hm1 | hm1 | hm1
    · have := mul_nonneg hP0.le (show (0 : ℤ) ≤ m - 1 by linarith)
      nlinarith
    · have := mul_nonneg hP0.le (show (0 : ℤ) ≤ -1 - m by linarith)
      nlinarith
    · subst hm1; omega
  have hple' : p < 170 := by omega
  -- the finite part
  have hk : (((c + 36).toNat : ℕ) : ℤ) - 36 = c := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have := cubic_ne_zero_small p hple' (c + 36).toNat (by omega) hp.two_le
  rw [hk] at this
  exact this hcub

end HalfSigmaSix

open HalfSigmaSix

/-- **Polynomial form.** For an odd prime `p`, `p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2`
is never of the form `2 z ^ 2`. Restricted result; novelty not verified. -/
theorem prime_pow_six_poly_ne_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 2 ≠ 2 * z ^ 2 := by
  intro hz
  have := congrArg (fun n : ℕ => (n : ℤ)) hz
  push_cast at this
  exact core hp hp2 this

/-- **Half of `σ(p ^ 6) + 1` never a square.** For an odd prime `p`, `σ(p ^ 6) + 1` is never
of the form `2 z ^ 2`. Restricted result; novelty not verified. -/
theorem sigma_prime_pow_six_add_one_ne_two_mul_sq {p z : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    σ 1 (p ^ 6) + 1 ≠ 2 * z ^ 2 := by
  have hs : σ 1 (p ^ 6) = p ^ 6 + p ^ 5 + p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
    rw [sigma_one_apply_prime_pow hp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
    ring
  rw [hs]
  exact prime_pow_six_poly_ne_two_mul_sq hp hp2

end OddPerfect

#print axioms OddPerfect.prime_pow_six_poly_ne_two_mul_sq
#print axioms OddPerfect.sigma_prime_pow_six_add_one_ne_two_mul_sq
