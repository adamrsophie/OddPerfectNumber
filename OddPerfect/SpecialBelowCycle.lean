import OddPerfect.SpecialBelowRows

/-!
# `q < m` from a statement about one square

Let `N = q ^ k * m ^ 2` be an odd perfect number in Euler's form (`q` the special prime,
`q ∤ m`). The theorem `special_lt_of_noSquareCycle` proves `q < m` under its explicit
hypothesis `NoSquareCycle`. That hypothesis is a statement about one prime and one square: no
prime `p`, exponent `e ≥ 1` and odd `t` have `σ(t ^ 2) = p ^ e` and `2 t ^ 2 = 1 + σ(p ^ e)`. It
does not mention odd perfect numbers. The hypothesis is proved in another module; this module
only shows the reduction. The odd perfect number conjecture is open, and nothing here decides
it.

The argument: by `special_lt_or_shape`, either `q < m`, or `k = 1` and there is a prime `p ∣ m`
with `σ(p ^ e) = q`, `e = v_p(N)`, in the shape described by `shape_data`, which gives an odd `t`
with `q + 1 = 2 t ^ 2` and `σ(t ^ 2) = p ^ e`. These are the two equations that
`NoSquareCycle` excludes.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The statement about one square: no prime `p`, exponent `e ≥ 1` and odd `t` have
`σ(t ^ 2) = p ^ e` and `2 * t ^ 2 = 1 + σ(p ^ e)`. -/
def NoSquareCycle : Prop :=
  ∀ p e t : ℕ, p.Prime → 1 ≤ e → Odd t → σ 1 (t ^ 2) = p ^ e → 2 * t ^ 2 = 1 + σ 1 (p ^ e) → False

/-- If `NoSquareCycle` holds, then every odd perfect number `N = q ^ k * m ^ 2` in Euler's form
has `q < m`. -/
theorem special_lt_of_noSquareCycle (hcyc : NoSquareCycle) {N q k m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q < m := by
  rcases special_lt_or_shape h hq hN hqm with h1 | ⟨rfl, p, hp, hpm, h2, -, -⟩
  · exact h1
  have hN1 : N = q * m ^ 2 := by rw [hN, pow_one]
  obtain ⟨t, -, hqt2, -, -, -, htodd, hσt, hσp, -, he0⟩ := shape_data h hq hN1 hqm hp hpm h2
  exact (hcyc p (N.factorization p) t hp he0 htodd hσt (by rw [hσp]; omega)).elim

end OddPerfect

#print axioms OddPerfect.special_lt_of_noSquareCycle
