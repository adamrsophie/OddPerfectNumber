import Mathlib.Tactic

/-!
Numerical checks for Ochem and Zelinsky, *On odd perfect numbers with exactly
one even exponent greater than 2*, Section 4 and the authors' update to Q9.
The tail bound uses 1.089 as an upper bound for the ordinary-prime product.
Verifying that the actual sieve gives a product below 1.089 is a separate task.
-/

namespace OPNNumeric

/-- For x ≥ 0 one has (1−mx)(1+x)^m ≤ 1, by induction on m. -/
theorem linear_times_pow_le_one (m : ℕ) {x : ℚ} (hx : 0 ≤ x) :
    (1 - (m : ℚ) * x) * (1 + x)^m ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : (1 - ((m : ℚ) + 1) * x) * (1 + x) ≤ 1 - (m : ℚ) * x := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (m : ℚ) + 1) (sq_nonneg x)]
      calc
        (1 - ((m + 1 : ℕ) : ℚ) * x) * (1 + x)^(m + 1)
            = ((1 - ((m : ℚ) + 1) * x) * (1+x)) * (1+x)^m := by
                push_cast
                rw [pow_succ]
                ring
        _ ≤ (1 - (m : ℚ) * x) * (1+x)^m := mul_le_mul_of_nonneg_right h (by positivity)
        _ ≤ 1 := ih

/-- A rational upper bound for one block of the tail product. -/
theorem block_bound (m : ℕ) {x : ℚ} (hx : 0 ≤ x) (hm : 0 < 1 - (m : ℚ) * x) :
    (1+x)^m ≤ 1 / (1 - (m : ℚ) * x) := by
  apply (le_div_iff₀ hm).2
  simpa [mul_comm] using linear_times_pow_le_one m hx

/-- Cross-multiplied check for 100 blocks, with z = 216171986291 and
block length 435000000. -/
theorem cross_multiplied :
    3 * 6000001 * 1089 * (216171986291 : ℕ)^100 <
    4 * 6000000 * 1000 * (216171986291 - 435000000 : ℕ)^100 := by
  decide +kernel

/-- For every rational `A` with `A ≤ 1.089`, the product
`(3/2) · (1 + 1/6000000) · A · (1 + 1/216171986291)^43500000000` is strictly smaller
than two.

The bound `A ≤ 1.089` is a hypothesis of this theorem, not a result of this file. The
file does not reconstruct the sieve of Ochem and Zelinsky that is meant to produce such a
bound, does not prove that the sieve's survivor list is exhaustive, and does not identify
any computed product with `A`. The theorem is only the final arithmetic step, valid for
whatever `A` satisfies the hypothesis. -/
theorem restrained_tail {A : ℚ} (hA : A ≤ 1089 / 1000) :
    (3/2 : ℚ) * (1+1/6000000) * A * (1+1/216171986291)^43500000000 < 2 := by
  let x : ℚ := 1 / 216171986291
  have hx : 0 ≤ x := by norm_num [x]
  have step := block_bound 435000000 hx (by norm_num [x])
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1+x)^435000000) step 100
  rw [← pow_mul] at hp
  change (1+x)^43500000000 ≤ _ at hp
  change (3/2 : ℚ) * (1+1/6000000) * A * (1+x)^43500000000 < 2
  calc
    _ ≤ (3/2 : ℚ) * (1+1/6000000) * (1089/1000) * (1+x)^43500000000 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) (by positivity)
    _ ≤ (3/2 : ℚ) * (1+1/6000000) * (1089/1000) *
          (1 / (1 - (435000000 : ℚ)*x))^100 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ < 2 := by norm_num [x]

/-- Exact factor identity in the reported square-full value for Q9. -/
theorem squarefull_factor_identity :
    let x : ℕ := 47116128896261596331524418282573
    x^2 + x + 1 =
      7^3 * 43^2 * 3416683^2 * 12353161^2 * 1401752363863729^2 := by
  decide +kernel

#print axioms linear_times_pow_le_one
#print axioms block_bound
#print axioms cross_multiplied
#print axioms restrained_tail
#print axioms squarefull_factor_identity

end OPNNumeric
