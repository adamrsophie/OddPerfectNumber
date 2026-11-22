import OddPerfect.OmegaSevenSplit

/-!
# A forcing step for the search states of `OddPerfect/OmegaSevenSplit.lean`

`closed_of_force`: if a state has an exact entry `p ^ k` and an odd prime `c`, not listed,
divides `σ (p ^ k) = 1 + p + ... + p ^ k`, then `c` divides `N` (since `σ (p ^ k) ∣ σ N = 2 N`),
so the state is closed when the state with `c` added (exponent at least `kmin c`, one fewer
further prime) is closed. This is the forcing step of the verified engine
`OmegaSevenEngine.solve`, stated as a lemma so that a cut plan can split a large state at a
forced prime. Used by `OddPerfect/NotThreeTen*.lean`.
-/

namespace OddPerfect.NotThreeTenForce

open OmegaSixSearch (Ent Holds kmin kmin_le)
open OmegaSevenSearch (Closed)
open Cert (geom)

/-- A forced prime: an odd prime `c`, not listed, dividing the divisor sum `geom p k` of an
exact entry `p ^ k`, may be added to the state. -/
theorem closed_of_force {l : List Ent} {j m p k c : ℕ} (hj : j ≠ 0) (hc : c.Prime)
    (hc2 : c ≠ 2) (he : (⟨p, k, true⟩ : Ent) ∈ l) (hd : c ∣ geom p k) (hn : c ∉ l.map Ent.p)
    (h : Closed (⟨c, kmin c, false⟩ :: l) (j - 1) m) : Closed l j m := by
  intro N H
  obtain ⟨hN, hnd, hent, hcard, hm⟩ := H
  have hE := hent _ he
  have hp := Nat.prime_of_mem_primeFactors hE.1
  have hcN : c ∣ N := OPNStarter.force_prime hN.perfect hp rfl hc hc2
    (by rw [hE.2.2 rfl, Cert.sigma_eq_geom hp]; exact hd)
  have hcm : c ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hc, hcN, hN.ne_zero⟩
  refine h N ⟨hN, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    exact ⟨hn, hnd⟩
  · intro e he'
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact ⟨hcm, kmin_le hN hcm, fun h => by simp at h⟩
    · exact hent e he'
  · simp only [List.length_cons]
    omega
  · intro q hq hql
    simp only [List.map_cons, List.mem_cons, not_or] at hql
    exact hm q hq hql.2

end OddPerfect.NotThreeTenForce

#print axioms OddPerfect.NotThreeTenForce.closed_of_force
