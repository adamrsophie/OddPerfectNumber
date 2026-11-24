import OddPerfect.Steps
import OddPerfect.PureRows
import OddPerfect.OmegaSevenFinal

/-!
Proof of the step `AllRowsPrimePower` (Levit 1947). If every ordinary row of an odd perfect
number `N` is a prime power, the fan-out inequality `|R| + D_q ≤ 2 d_q` of
`OddPerfect/PureRows.lean` holds, where `|R| ≥ ω(N) - 2`. If moreover `σ(q ^ e_q) = 2 * r ^ w`
with `r` prime, every prime factor of the odd number `N` dividing `σ(q ^ e_q)` is `r`, so
`d_q ≤ 1` and `ω(N) ≤ 4`, against `ω(N) ≥ 7`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.Proofs

theorem AllRowsPrimePower : OddPerfect.Steps.AllRowsPrimePower := by
  intro N q h hq hodd hpure ⟨r, w, hr, hrow⟩
  have hle := OddPerfect.card_add_inDegree_le_of_all_pure h hq hodd hpure
  have h7 := OddPerfect.seven_le_card_primeFactors h
  have hqP : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hd : (N.primeFactors.filter (fun t => t ∣ σ 1 (q ^ N.factorization q))).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    have key : ∀ t ∈ N.primeFactors.filter (fun t => t ∣ σ 1 (q ^ N.factorization q)),
        t = r := by
      intro t ht
      obtain ⟨htP, htd⟩ := Finset.mem_filter.mp ht
      have htp := Nat.prime_of_mem_primeFactors htP
      have ht2 : t ≠ 2 := by
        rintro rfl
        exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors htP)
      rw [hrow] at htd
      rcases (Nat.Prime.dvd_mul htp).mp htd with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq htp Nat.prime_two).mp h2) ht2
      · exact (Nat.prime_dvd_prime_iff_eq htp hr).mp (htp.dvd_of_dvd_pow h2)
    rw [key a ha, key b hb]
  have hsub : (N.primeFactors.erase q).erase 3 ⊆
      (N.primeFactors.erase q).filter (fun p => ¬ (p = 3 ∧ N.factorization 3 = 4)) := by
    intro p hp
    obtain ⟨hp3, hp⟩ := Finset.mem_erase.mp hp
    exact Finset.mem_filter.mpr ⟨hp, fun h3 => hp3 h3.1⟩
  have hc1 := Finset.pred_card_le_card_erase (s := N.primeFactors) (a := q)
  have hc2 := Finset.pred_card_le_card_erase (s := N.primeFactors.erase q) (a := 3)
  have hc3 := Finset.card_le_card hsub
  omega

end OddPerfect.Proofs
