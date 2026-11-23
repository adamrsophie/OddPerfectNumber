import Mathlib

/-!
# The Eisenstein integers

We use mathlib's `QuadraticAlgebra ℤ (-1) (-1)`: elements `a + b ω` with `ω ^ 2 = -1 - ω`.
We give the norm `a ^ 2 - a b + b ^ 2` as an integer, its basic properties, the units, the
elements of norm three, division with remainder and the `EuclideanDomain` instance, and the
fact that an element of prime norm is prime.
-/

namespace OddPerfect

/-- The Eisenstein integers `ℤ[ω]`, `ω ^ 2 = -1 - ω`. -/
abbrev Eis := QuadraticAlgebra ℤ (-1) (-1)

namespace Eis

open QuadraticAlgebra

/-- The norm of `a + b ω`, namely `a ^ 2 - a b + b ^ 2`. -/
def nrm (z : Eis) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

/-- `nrm` agrees with mathlib's `QuadraticAlgebra.norm`. -/
theorem nrm_eq_norm (z : Eis) : nrm z = QuadraticAlgebra.norm z := by
  rw [nrm, QuadraticAlgebra.norm_def]; ring

/-- The norm is multiplicative. -/
theorem nrm_mul (z w : Eis) : nrm (z * w) = nrm z * nrm w := by
  simp only [nrm, re_mul, im_mul]; ring

/-- The norm is nonnegative. -/
theorem nrm_nonneg (z : Eis) : 0 ≤ nrm z := by
  unfold nrm; nlinarith [sq_nonneg (z.re - z.im), sq_nonneg z.re, sq_nonneg z.im]

/-- The norm vanishes only at zero. -/
theorem nrm_eq_zero (z : Eis) : nrm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    unfold nrm at hz
    have h1 : z.re ^ 2 = 0 := by
      nlinarith [sq_nonneg (z.re - z.im), sq_nonneg z.re, sq_nonneg z.im]
    have h2 : z.im ^ 2 = 0 := by
      nlinarith [sq_nonneg (z.re - z.im), sq_nonneg z.re, sq_nonneg z.im]
    have h1' : z.re = 0 := pow_eq_zero_iff two_ne_zero |>.1 h1
    have h2' : z.im = 0 := pow_eq_zero_iff two_ne_zero |>.1 h2
    ext
    · exact h1'
    · exact h2'
  · rintro rfl; simp [nrm]

/-- The norm of the conjugate. -/
theorem nrm_star (z : Eis) : nrm (star z) = nrm z := by
  simp only [nrm, re_star, im_star]; ring

/-- The norm of an integer. -/
theorem nrm_intCast (n : ℤ) : nrm (n : Eis) = n ^ 2 := by
  simp [nrm]

/-- `z * star z` is the norm. -/
theorem mul_star_eq (z : Eis) : z * star z = ((nrm z : ℤ) : Eis) := by
  ext <;> simp only [re_mul, im_mul, re_star, im_star, re_intCast, im_intCast, Int.cast_id, nrm] <;>
    ring

theorem nrm_one : nrm 1 = 1 := by simp [nrm]

theorem nrm_mk (a b : ℤ) : nrm ⟨a, b⟩ = a ^ 2 - a * b + b ^ 2 := rfl

/-- Divisibility by an integer, coordinatewise. -/
theorem intCast_dvd_iff (n : ℤ) (z : Eis) : (n : Eis) ∣ z ↔ n ∣ z.re ∧ n ∣ z.im := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.re, by simp⟩, ⟨c.im, by simp⟩⟩
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    exact ⟨⟨r, i⟩, by ext <;> simp [hr, hi]⟩

instance : NoZeroDivisors Eis where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} h := by
    have h' : nrm x * nrm y = 0 := by rw [← nrm_mul, h]; simp [nrm]
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact Or.inl ((nrm_eq_zero x).1 h1)
    · exact Or.inr ((nrm_eq_zero y).1 h1)

instance : IsDomain Eis := NoZeroDivisors.to_isDomain _

/-- Units are the elements of norm one. -/
theorem isUnit_iff_nrm_eq_one (z : Eis) : IsUnit z ↔ nrm z = 1 := by
  rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, ← nrm_eq_norm, Int.isUnit_iff]
  constructor
  · rintro (h | h)
    · exact h
    · have := nrm_nonneg z; omega
  · exact Or.inl

private theorem nrm_one_coords (a b : ℤ) (h : a ^ 2 - a * b + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) ∨
      (a = -1 ∧ b = -1) ∨ (a = 1 ∧ b = 1) := by
  have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (2 * a - b)]
  have hb2 : -1 ≤ b := by nlinarith [sq_nonneg (2 * a - b)]
  have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (2 * b - a)]
  have ha2 : -1 ≤ a := by nlinarith [sq_nonneg (2 * b - a)]
  interval_cases a <;> interval_cases b <;> omega

/-- The six units. -/
theorem eq_of_nrm_eq_one {z : Eis} (h : nrm z = 1) :
    z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩ ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨-1, -1⟩ ∨ z = ⟨1, 1⟩ := by
  obtain ⟨a, b⟩ := z
  rcases nrm_one_coords a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

private theorem nrm_three_coords (a b : ℤ) (h : a ^ 2 - a * b + b ^ 2 = 3) :
    (a = 1 ∧ b = 2) ∨ (a = -1 ∧ b = -2) ∨ (a = -2 ∧ b = -1) ∨ (a = 2 ∧ b = 1) ∨
      (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  have hb1 : b ≤ 2 := by nlinarith [sq_nonneg (2 * a - b)]
  have hb2 : -2 ≤ b := by nlinarith [sq_nonneg (2 * a - b)]
  have ha1 : a ≤ 2 := by nlinarith [sq_nonneg (2 * b - a)]
  have ha2 : -2 ≤ a := by nlinarith [sq_nonneg (2 * b - a)]
  interval_cases a <;> interval_cases b <;> omega

/-- The six elements of norm three. -/
theorem eq_of_nrm_eq_three {z : Eis} (h : nrm z = 3) :
    z = ⟨1, 2⟩ ∨ z = ⟨-1, -2⟩ ∨ z = ⟨-2, -1⟩ ∨ z = ⟨2, 1⟩ ∨ z = ⟨1, -1⟩ ∨ z = ⟨-1, 1⟩ := by
  obtain ⟨a, b⟩ := z
  rcases nrm_three_coords a b h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- An element of norm three is a unit times `λ = 1 + 2 ω`. -/
theorem exists_unit_of_nrm_eq_three {z : Eis} (h : nrm z = 3) :
    ∃ u : Eis, IsUnit u ∧ z = u * ⟨1, 2⟩ := by
  have hu : ∀ a b : ℤ, a ^ 2 - a * b + b ^ 2 = 1 → IsUnit (⟨a, b⟩ : Eis) :=
    fun a b hab => (isUnit_iff_nrm_eq_one _).2 hab
  rcases eq_of_nrm_eq_three h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨1, 0⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩
  · exact ⟨⟨-1, 0⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩
  · exact ⟨⟨0, 1⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩
  · exact ⟨⟨0, -1⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩
  · exact ⟨⟨-1, -1⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩
  · exact ⟨⟨1, 1⟩, hu _ _ (by norm_num), by ext <;> norm_num⟩

/-- Rounding of `c / n` to a nearest integer. -/
def rnd (c n : ℤ) : ℤ := (2 * c + n) / (2 * n)

theorem rnd_spec (c n : ℤ) (hn : 0 < n) :
    -n ≤ 2 * (c - rnd c n * n) ∧ 2 * (c - rnd c n * n) ≤ n := by
  have h1 := Int.mul_ediv_add_emod (2 * c + n) (2 * n)
  have h2 := Int.emod_nonneg (2 * c + n) (by omega : (2 * n) ≠ 0)
  have h3 := Int.emod_lt_of_pos (2 * c + n) (by omega : 0 < 2 * n)
  unfold rnd
  generalize (2 * c + n) / (2 * n) = Q at *
  generalize (2 * c + n) % (2 * n) = R at *
  constructor <;> nlinarith

/-- The Euclidean quotient. -/
def quo (x y : Eis) : Eis := ⟨rnd (x * star y).re (nrm y), rnd (x * star y).im (nrm y)⟩

/-- The Euclidean remainder. -/
def rem (x y : Eis) : Eis := x - y * quo x y

theorem nrm_rem_lt (x : Eis) {y : Eis} (hy : y ≠ 0) : nrm (rem x y) < nrm y := by
  have hn : 0 < nrm y :=
    lt_of_le_of_ne (nrm_nonneg y) (fun h => hy ((nrm_eq_zero y).1 h.symm))
  obtain ⟨hs1, hs2⟩ := rnd_spec (x * star y).re (nrm y) hn
  obtain ⟨ht1, ht2⟩ := rnd_spec (x * star y).im (nrm y) hn
  have e : rem x y * star y =
      ⟨(x * star y).re - rnd (x * star y).re (nrm y) * nrm y,
        (x * star y).im - rnd (x * star y).im (nrm y) * nrm y⟩ := by
    rw [rem, sub_mul, mul_comm y, mul_assoc, mul_star_eq]
    ext <;> simp [quo]
  have key : nrm (rem x y) * nrm y =
      nrm ⟨(x * star y).re - rnd (x * star y).re (nrm y) * nrm y,
        (x * star y).im - rnd (x * star y).im (nrm y) * nrm y⟩ := by
    rw [← e, nrm_mul, nrm_star]
  generalize (x * star y).re - rnd (x * star y).re (nrm y) * nrm y = s at *
  generalize (x * star y).im - rnd (x * star y).im (nrm y) * nrm y = t at *
  change _ = s ^ 2 - s * t + t ^ 2 at key
  generalize nrm y = n at *
  generalize nrm (rem x y) = m at *
  have h4 : 4 * (s ^ 2 - s * t + t ^ 2) ≤ 3 * n ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * s) (by linarith : (0:ℤ) ≤ n + 2 * s),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * t) (by linarith : (0:ℤ) ≤ n + 2 * t),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2 * s) (by linarith : (0:ℤ) ≤ n - 2 * t),
      mul_nonneg (by linarith : (0:ℤ) ≤ n + 2 * s) (by linarith : (0:ℤ) ≤ n + 2 * t)]
  nlinarith

/-- Division with remainder. -/
theorem exists_div_rem (x y : Eis) (hy : y ≠ 0) :
    ∃ k r : Eis, x = k * y + r ∧ nrm r < nrm y :=
  ⟨quo x y, rem x y, by rw [rem]; ring, nrm_rem_lt x hy⟩

private theorem natAbs_nrm (z : Eis) : ((nrm z).natAbs : ℤ) = nrm z :=
  Int.natAbs_of_nonneg (nrm_nonneg z)

instance instEuclidean : EuclideanDomain Eis :=
  { (inferInstance : CommRing Eis), (inferInstance : Nontrivial Eis) with
    quotient := quo
    remainder := rem
    quotient_zero := fun a => by
      ext <;> simp [quo, rnd, nrm]
    quotient_mul_add_remainder_eq := fun a b => by rw [rem]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ nrm)).wf
    remainder_lt := fun a b hb => by
      show (nrm (rem a b)).natAbs < (nrm b).natAbs
      have := nrm_rem_lt a hb
      have h1 := natAbs_nrm (rem a b)
      have h2 := natAbs_nrm b
      omega
    mul_left_not_lt := fun a b hb => by
      show ¬ (nrm (a * b)).natAbs < (nrm a).natAbs
      have hb1 : 1 ≤ nrm b :=
        lt_of_le_of_ne (nrm_nonneg b) (fun h => hb ((nrm_eq_zero b).1 h.symm))
      have h1 := natAbs_nrm (a * b)
      have h2 := natAbs_nrm a
      have h3 : nrm a ≤ nrm (a * b) := by
        rw [nrm_mul]; nlinarith [nrm_nonneg a]
      omega }

/-- An element whose norm is a prime number is prime. -/
theorem prime_of_nrm_prime {π : Eis} (h : (nrm π).natAbs.Prime) : Prime π := by
  have hirr : Irreducible π := by
    rw [irreducible_iff]
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · rw [isUnit_iff_nrm_eq_one] at hu
      rw [hu] at h
      exact Nat.not_prime_one h
    · have hm : (nrm a).natAbs * (nrm b).natAbs = (nrm π).natAbs := by
        rw [hab, nrm_mul, Int.natAbs_mul]
      rw [← hm, Nat.prime_mul_iff] at h
      rcases h with ⟨-, hb⟩ | ⟨-, ha⟩
      · right
        rw [isUnit_iff_nrm_eq_one]
        have := natAbs_nrm b
        omega
      · left
        rw [isUnit_iff_nrm_eq_one]
        have := natAbs_nrm a
        omega
  exact hirr.prime

end Eis

end OddPerfect

#print axioms OddPerfect.Eis.nrm_mul
#print axioms OddPerfect.Eis.nrm_nonneg
#print axioms OddPerfect.Eis.nrm_eq_zero
#print axioms OddPerfect.Eis.nrm_star
#print axioms OddPerfect.Eis.nrm_intCast
#print axioms OddPerfect.Eis.mul_star_eq
#print axioms OddPerfect.Eis.intCast_dvd_iff
#print axioms OddPerfect.Eis.isUnit_iff_nrm_eq_one
#print axioms OddPerfect.Eis.eq_of_nrm_eq_one
#print axioms OddPerfect.Eis.eq_of_nrm_eq_three
#print axioms OddPerfect.Eis.exists_unit_of_nrm_eq_three
#print axioms OddPerfect.Eis.exists_div_rem
#print axioms OddPerfect.Eis.prime_of_nrm_prime
#print axioms OddPerfect.Eis.instEuclidean
