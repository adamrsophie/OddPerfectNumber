import OddPerfect.EulerIndexPairEmitterTwelve
import OddPerfect.EulerIndexPairReceiverBound

/-!
# Two prime Euler index: emitter exponent at least 12 in both branches

Restricted result; no published source was checked; novelty not verified.

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`, oriented by a frame `PairFrame N q r s t u`.

* `PairFrame.exponent_twelve`: the emitter exponent `e = v_t(N)` is at least `12`.
* `eulerIndex_pair_exponent_twelve`: the same for every member of the family.

Branch `v = 0`: `PairFrame.emitter_twelve`. Branch `v = 1`: `u = e + 1` and
`PairFrame.receiver_ge` gives `43 ≤ u`, so `e ≥ 42`.

The family of a two prime Euler index is not excluded; only the exponent of the emitter is
bounded below by `12`. The odd perfect number conjecture is open, and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q m r s t u : ℕ}

namespace PairFrame

/-- **Emitter exponent at least 12.** For a frame of the two prime Euler index family,
`v_t(N) ≥ 12`. Restricted result; no published source was checked; novelty not verified. The
family is not excluded here. -/
theorem exponent_twelve (F : PairFrame N q r s t u) (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) : 12 ≤ N.factorization t := by
  obtain ⟨-, -, v, j, hA, -, -, -, -, -, -, hcases⟩ :=
    F.emitter_ten_all h hq hN hqm hr hs hrs hJ
  rcases hcases with ⟨-, hv0, -⟩ | ⟨rfl, hu, -⟩
  · exact F.emitter_twelve h hq hN hqm hr hs hrs hJ hv0
  · rw [pow_one] at hA
    have := (F.receiver_ge h hq hN hqm hr hs hrs hJ hA).1
    omega

end PairFrame

/-- **Family form.** In the two prime Euler index family the emitter `t` satisfies
`v_t(N) ≥ 12`. Restricted result; no published source was checked; novelty not verified. The
family is not excluded here. -/
theorem eulerIndex_pair_exponent_twelve (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧ 12 ≤ N.factorization t := by
  obtain ⟨t, u, F⟩ := exists_pairFrame h hq hN hqm hr hs hrs hJ
  exact ⟨t, u, F.pair, F.ne, F.emit, F.exponent_twelve h hq hN hqm hr hs hrs hJ⟩

end OddPerfect

#print axioms OddPerfect.PairFrame.exponent_twelve
#print axioms OddPerfect.eulerIndex_pair_exponent_twelve
