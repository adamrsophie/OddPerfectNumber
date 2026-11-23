import Mathlib

/-!
# Rational upper bounds for a finite product `∏ (1 + x i)` with `∑ x i ≤ S`

The certificate checker bounds a tail product by `∏ (1 + x i) ≤ 1/(1 - S)` when
`∑ x i ≤ S < 1`. This module gives two sharper rational bounds, both Padé type upper bounds
for `exp S`:

* `prod_one_add_le_pade11`: `∏ (1 + x i) ≤ (2 + S)/(2 - S)` for `S < 2`;
* `prod_one_add_le_pade21`: `∏ (1 + x i) ≤ (S^2 + 4 S + 6)/(6 - 2 S)` for `S < 3`;

together with the comparisons `pade21_le_pade11` and `pade11_le_inv`, and natural number forms
of both bounds for `S = n/d` (`pade11_nat_eq`, `pade21_nat_eq`) that a Boolean checker can
test without truncated subtraction on `ℕ`.

The proof is an induction on the finite set through `prod_one_add_le_of_step`: a function `R`
with `1 ≤ R S` on `[0, D)` and `(1 + x) R y ≤ R (x + y)` bounds every such product. For the
two bounds the step reduces to the polynomial identities
`(2 + x + y)(2 - y) - (1 + x)(2 + y)(2 - x - y) = x (2 x + x y + y^2)` and
`((x + y)^2 + 4 (x + y) + 6)(6 - 2 y) - (1 + x)(y^2 + 4 y + 6)(6 - 2 x - 2 y)
  = 2 x (x y^2 + 3 x y + 9 x + y^3)`.

These are tool lemmas. They make no claim about odd perfect numbers by themselves.
-/

namespace OddPerfect

/-- A generic product bound: if `1 ≤ R S` for `0 ≤ S < D` and `(1 + x) R y ≤ R (x + y)`
for `0 ≤ x`, `0 ≤ y`, `x + y < D`, then `∏ (1 + x i) ≤ R S` whenever the `x i` are
nonnegative and `∑ x i ≤ S < D`. -/
theorem prod_one_add_le_of_step (R : ℚ → ℚ) {D : ℚ} (h1 : ∀ S, 0 ≤ S → S < D → 1 ≤ R S)
    (hstep : ∀ x y, 0 ≤ x → 0 ≤ y → x + y < D → (1 + x) * R y ≤ R (x + y))
    {ι : Type*} (s : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {S : ℚ} (hS : ∑ i ∈ s, x i ≤ S) (hSD : S < D) :
    ∏ i ∈ s, (1 + x i) ≤ R S := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty =>
    simp only [Finset.sum_empty] at hS
    simpa using h1 S hS hSD
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rw [Finset.sum_insert ha] at hS
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
    have hrec := ih hxs (S := S - x a) (by linarith) (by linarith)
    calc (1 + x a) * ∏ i ∈ s, (1 + x i) ≤ (1 + x a) * R (S - x a) :=
          mul_le_mul_of_nonneg_left hrec (by linarith)
      _ ≤ R (x a + (S - x a)) := hstep _ _ hxa (by linarith) (by linarith)
      _ = R S := by rw [add_sub_cancel]

/-- The `(1,1)` Padé bound: if `0 ≤ x i` and `∑ x i ≤ S < 2`, then
`∏ (1 + x i) ≤ (2 + S)/(2 - S)`. -/
theorem prod_one_add_le_pade11 {ι : Type*} (s : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {S : ℚ} (hS : ∑ i ∈ s, x i ≤ S) (hS2 : S < 2) :
    ∏ i ∈ s, (1 + x i) ≤ (2 + S) / (2 - S) := by
  refine prod_one_add_le_of_step (fun S => (2 + S) / (2 - S)) ?_ ?_ s x hx hS hS2
  · intro S h0 h2
    rw [le_div_iff₀ (by linarith)]
    linarith
  · intro a b ha hb hab
    have hb2 : 0 < 2 - b := by linarith
    have hab2 : 0 < 2 - (a + b) := by linarith
    rw [← mul_div_assoc, div_le_div_iff₀ hb2 hab2]
    have key : 0 ≤ a * (2 * a + a * b + b ^ 2) := by positivity
    nlinarith [key]

/-- The `(2,1)` Padé bound: if `0 ≤ x i` and `∑ x i ≤ S < 3`, then
`∏ (1 + x i) ≤ (S^2 + 4 S + 6)/(6 - 2 S)`. -/
theorem prod_one_add_le_pade21 {ι : Type*} (s : Finset ι) (x : ι → ℚ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {S : ℚ} (hS : ∑ i ∈ s, x i ≤ S) (hS3 : S < 3) :
    ∏ i ∈ s, (1 + x i) ≤ (S ^ 2 + 4 * S + 6) / (6 - 2 * S) := by
  refine prod_one_add_le_of_step (fun S => (S ^ 2 + 4 * S + 6) / (6 - 2 * S)) ?_ ?_
    s x hx hS hS3
  · intro S h0 h3
    rw [le_div_iff₀ (by linarith)]
    nlinarith [sq_nonneg S]
  · intro a b ha hb hab
    have hb3 : 0 < 6 - 2 * b := by linarith
    have hab3 : 0 < 6 - 2 * (a + b) := by linarith
    rw [← mul_div_assoc, div_le_div_iff₀ hb3 hab3]
    have key : 0 ≤ 2 * a * (a * b ^ 2 + 3 * a * b + 9 * a + b ^ 3) := by positivity
    nlinarith [key]

/-- On `0 ≤ S < 2` the `(2,1)` bound is at most the `(1,1)` bound; the cross difference
is `S^3`. -/
theorem pade21_le_pade11 {S : ℚ} (h0 : 0 ≤ S) (h2 : S < 2) :
    (S ^ 2 + 4 * S + 6) / (6 - 2 * S) ≤ (2 + S) / (2 - S) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have key : 0 ≤ S ^ 3 := by positivity
  nlinarith [key]

/-- On `0 ≤ S < 1` the `(1,1)` bound is at most `1/(1 - S)`; the cross difference is
`S^2`. The hypothesis `0 ≤ S` is not needed by the proof. -/
theorem pade11_le_inv {S : ℚ} (_h0 : 0 ≤ S) (h1 : S < 1) : (2 + S) / (2 - S) ≤ 1 / (1 - S) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [sq_nonneg S]

/-- Natural number form of the `(1,1)` bound at `S = n/d`: for `0 < d` and `n < 2 d`, the
quotient `(2 d + n)/(2 d - n)` of naturals (the subtraction does not truncate) equals
`(2 + S)/(2 - S)`. -/
theorem pade11_nat_eq {n d : ℕ} (hd : 0 < d) (hn : n < 2 * d) :
    ((2 * d + n : ℕ) : ℚ) / ((2 * d - n : ℕ) : ℚ) =
      (2 + (n : ℚ) / d) / (2 - (n : ℚ) / d) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hn' : (n : ℚ) < 2 * d := by exact_mod_cast hn
  rw [Nat.cast_sub hn.le]
  push_cast
  rw [div_eq_div_iff (by linarith) (by rw [sub_ne_zero]; intro h; field_simp at h; linarith)]
  field_simp

/-- Natural number form of the `(2,1)` bound at `S = n/d`: for `0 < d` and `n < 3 d`, the
quotient `(n^2 + 4 n d + 6 d^2)/(6 d^2 - 2 n d)` of naturals (the subtraction does not
truncate) equals `(S^2 + 4 S + 6)/(6 - 2 S)`. -/
theorem pade21_nat_eq {n d : ℕ} (hd : 0 < d) (hn : n < 3 * d) :
    ((n ^ 2 + 4 * n * d + 6 * d ^ 2 : ℕ) : ℚ) / ((6 * d ^ 2 - 2 * n * d : ℕ) : ℚ) =
      (((n : ℚ) / d) ^ 2 + 4 * ((n : ℚ) / d) + 6) / (6 - 2 * ((n : ℚ) / d)) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hn' : (n : ℚ) < 3 * d := by exact_mod_cast hn
  have hle : 2 * n * d ≤ 6 * d ^ 2 := by nlinarith
  rw [Nat.cast_sub hle]
  push_cast
  have hden : (6 : ℚ) - 2 * ((n : ℚ) / d) ≠ 0 := by
    have : (n : ℚ) / d < 3 := by rw [div_lt_iff₀ hd']; linarith
    linarith
  rw [div_eq_div_iff (by nlinarith) hden]
  field_simp

end OddPerfect

#print axioms OddPerfect.prod_one_add_le_of_step
#print axioms OddPerfect.prod_one_add_le_pade11
#print axioms OddPerfect.prod_one_add_le_pade21
#print axioms OddPerfect.pade21_le_pade11
#print axioms OddPerfect.pade11_le_inv
#print axioms OddPerfect.pade11_nat_eq
#print axioms OddPerfect.pade21_nat_eq
