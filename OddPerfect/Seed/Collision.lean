import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Square ratios of values of the third cyclotomic polynomial

A restricted consequence for Question 10 in Ochem and Zelinsky,
arXiv:2607.19746. All statements use natural numbers and need no
primality assumptions. The exponent inequality applies to even gaps.
-/

namespace OPNCollision

/-- The third cyclotomic polynomial evaluated at a natural number. -/
def phi3 (n : ℕ) : ℕ := n ^ 2 + n + 1

/-- A nontrivial square ratio forces the smaller input below the square root
of the ratio. -/
theorem smaller_input_lt_scale {x y k : ℕ} (hk : 1 < k)
    (h : phi3 x = k ^ 2 * phi3 y) : y < k := by
  unfold phi3 at h
  let u := 2 * x + 1
  let v := k * (2 * y + 1)
  have hid : u ^ 2 + 3 = v ^ 2 + 3 * k ^ 2 := by
    dsimp [u, v]
    nlinarith only [h]
  have hk2 : 1 < k ^ 2 := by nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ k by omega)]
  have huv : v < u := by
    by_contra! hn
    have := Nat.mul_self_le_mul_self hn
    nlinarith only [hid, hk2, this]
  have hstep := Nat.mul_self_le_mul_self (show v + 1 ≤ u by omega)
  by_contra! hky
  have hprod := Nat.mul_le_mul_left k hky
  dsimp [v] at hstep
  dsimp [u, v] at hid
  dsimp [u] at hstep
  nlinarith only [hstep, hid, hprod]

/-- Two values with a common positive cofactor and a positive even exponent
gap must have the larger exponent strictly greater than twice the smaller.
The variables in Question 10 can be prime, but this inequality only needs
a base greater than one and a positive cofactor. -/
theorem even_gap_forces_exponent_bound {x y p r a b t : ℕ}
    (hp : 1 < p) (hr : 0 < r) (ht : 0 < t) (hgap : a = b + 2 * t)
    (hx : phi3 x = p ^ a * r) (hy : phi3 y = p ^ b * r) :
    2 * b < a := by
  have hpow : 1 < p ^ t := one_lt_pow₀ hp (by omega)
  have hratio : phi3 x = (p ^ t) ^ 2 * phi3 y := by
    rw [hx, hy, hgap, pow_add, Nat.mul_comm 2 t, pow_mul]
    ring
  have hylt := smaller_input_lt_scale hpow hratio
  have hsq := Nat.mul_self_le_mul_self (show y + 1 ≤ p ^ t by omega)
  have hysmall : phi3 y < (p ^ t) ^ 2 := by
    by_cases hz : y = 0
    · rw [hz]
      simpa [phi3] using (one_lt_pow₀ hpow (by decide : (2 : ℕ) ≠ 0))
    · unfold phi3
      nlinarith only [hsq, (show 0 < y by omega)]
  by_contra! hwrong
  have hexp : 2 * t ≤ b := by omega
  have hple : p ^ (2 * t) ≤ p ^ b := Nat.pow_le_pow_right (by omega) hexp
  have hbase : (p ^ t) ^ 2 ≤ phi3 y := by
    rw [hy, ← pow_mul, Nat.mul_comm t 2]
    exact hple.trans (Nat.le_mul_of_pos_right (p ^ b) hr)
  omega

end OPNCollision

#print axioms OPNCollision.smaller_input_lt_scale
#print axioms OPNCollision.even_gap_forces_exponent_bound
