import OddPerfect.EqualExponentChainFar67Spec
import OddPerfect.EqualExponentChainFar67Ord0
import OddPerfect.EqualExponentChainFar67Ord1
import OddPerfect.EqualExponentChainFar67Ord2

/-!
# Equal exponent chains: `l = 67`

The exponents other than the special prime of an odd perfect number cannot all equal `66`:
the pieces of the certificate are chained by `OddPerfect.EqChain.runC_sound_cuts` and
`OddPerfect.EqChain.split_sound`.
The certificate was found by an untrusted search and is checked by `decide +kernel`.
Restricted family result; no published source was checked; novelty not verified.
-/

namespace OddPerfect

open EqChain in
/-- In an odd perfect number the exponents of the primes other than the special
prime cannot all equal `66`. Restricted family result; no published source was
checked; novelty not verified. -/
theorem not_all_exponents_eq_sixty_six {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 66) : False := by
  have hlP : Pratt.trialPrime 67 = true := by decide +kernel
  have hl := Pratt.trialPrime_sound hlP
  have h2 : Holds 67 N q cut67_2 → False :=
    runC_sound_cuts pc67_check hl (by decide) h hq hodd hexp ord67_run2
      (fun _ hs => by simp at hs)
  have h1 : Holds 67 N q cut67_1 → False :=
    runC_sound_cuts pc67_check hl (by decide) h hq hodd hexp ord67_run1
      (fun s hs => by rw [List.mem_singleton.mp hs]; exact h2)
  have h0 : Holds 67 N q ⟨[67], [67], none, 2⟩ → False :=
    runC_sound_cuts pc67_check hl (by decide) h hq hodd hexp ord67_run0
      (fun s hs => by rw [List.mem_singleton.mp hs]; exact h1)
  exact split_sound hlP (by decide) pc67_check spec67_run h hq hodd hexp h0

end OddPerfect

#print axioms OddPerfect.not_all_exponents_eq_sixty_six
