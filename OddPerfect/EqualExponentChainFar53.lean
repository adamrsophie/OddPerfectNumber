import OddPerfect.EqualExponentChainFar53Spec
import OddPerfect.EqualExponentChainFar53Ord0
import OddPerfect.EqualExponentChainFar53Ord1

/-!
# Equal exponent chains: `l = 53`

The exponents other than the special prime of an odd perfect number cannot all equal `52`:
the pieces of the certificate are chained by `OddPerfect.EqChain.runC_sound_cuts` and
`OddPerfect.EqChain.split_sound`.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect

open EqChain in
/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `52`. Restricted family result; no published source was
checked; novelty not verified. -/
theorem not_all_exponents_eq_fifty_two {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 52) : False := by
  have hlP : Pratt.trialPrime 53 = true := by decide +kernel
  have hl := Pratt.trialPrime_sound hlP
  have h1 : Holds 53 N q cut53_1 → False :=
    runC_sound_cuts pc53_check hl (by decide) h hq hodd hexp ord53_run1
      (fun _ hs => by simp at hs)
  have h0 : Holds 53 N q ⟨[53], [53], none, 2⟩ → False :=
    runC_sound_cuts pc53_check hl (by decide) h hq hodd hexp ord53_run0
      (fun s hs => by rw [List.mem_singleton.mp hs]; exact h1)
  exact split_sound hlP (by decide) pc53_check spec53_run h hq hodd hexp h0

end OddPerfect

#print axioms OddPerfect.not_all_exponents_eq_fifty_two
