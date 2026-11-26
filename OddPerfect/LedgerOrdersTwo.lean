import OddPerfect.Zsigmondy
import OddPerfect.ValuationBounds
import OddPerfect.SpecialPrime

/-!
# Order demands against receiver capacities

Let `N` be an odd perfect number, `A` a finite set of prime factors of `N` and, for every
`p ∈ A`, `D p` a finite set of integers `d ≥ 3` with `d ∣ e_p + 1`. For each `d ∈ D p`, Bang's
theorem (`Zsigmondy.lean`) gives a prime `t ∣ σ(p ^ e_p)` of exact order `d` modulo `t`; then
`t` divides `N`, `t ≠ p`, `d ∣ t - 1`, and different `d` give different `t`. A prime `t` serves
at most `v_t(N)` sources, since each source spends at least one unit of `v_t(σ(p ^ e_p))` and
these add up to at most `v_t(N)`, and it serves only compatible sources: `p ∈ A`, `p ≠ t`, and
some `d ∈ D p` divides `t - 1`.

* `sum_card_le_sum_min_compatible`:
  `∑_{p ∈ A} |D p| ≤ ∑_{t ∈ N.primeFactors} min (v_t(N), |compatible A D t|)`.
* `not_sum_min_compatible_lt`: the right side never falls strictly below the left side; a
  branch closer for case analyses.

The sum on the right runs over all prime factors of `N`. These are unconditional statements
about odd perfect numbers, used as conditional tools: they close a branch only when the demands
are known. Whether this is in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-- The sources `p ∈ A` that a prime `t` can serve: `p ≠ t` and some requested order `d ∈ D p`
divides `t - 1`. -/
def compatible (A : Finset ℕ) (D : ℕ → Finset ℕ) (t : ℕ) : Finset ℕ :=
  A.filter (fun p => p ≠ t ∧ ∃ d ∈ D p, d ∣ t - 1)

/-- The receivers of a source `p`: prime factors `t` of `N` dividing `σ(p ^ e_p)`, with
`t ≠ p` and some `d ∈ D p` dividing `t - 1`. -/
def orderReceivers (N : ℕ) (D : ℕ → Finset ℕ) (p : ℕ) : Finset ℕ :=
  N.primeFactors.filter (fun t => t ∣ σ 1 (p ^ N.factorization p) ∧ p ≠ t ∧ ∃ d ∈ D p, d ∣ t - 1)

/-- One source: the number of requested orders is at most the number of receivers. The map
`t ↦ ord_t(p)` covers `D p` by Bang's theorem. -/
theorem card_le_card_orderReceivers (h : OddPerfect N) {D : ℕ → Finset ℕ} {p : ℕ}
    (hp : p ∈ N.primeFactors) (hD : ∀ d ∈ D p, 3 ≤ d ∧ d ∣ N.factorization p + 1) :
    (D p).card ≤ (orderReceivers N D p).card := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  refine Finset.card_le_card_of_surjOn (fun t => orderOf (p : ZMod t)) ?_
  intro d hd
  obtain ⟨hd3, hdm⟩ := hD d hd
  obtain ⟨t, ht, htd, ho, hmod⟩ := exists_prime_dvd_sigma_orderOf_eq hpp hp3 hd3 hdm
  have ht2 : t ≠ 2 := by
    rintro rfl
    rw [Nat.mod_eq_of_lt (by omega : 2 < d)] at hmod
    omega
  have htN : t ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨ht, OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd,
      h.ne_zero⟩
  have hpt : p ≠ t := by
    rintro rfl
    exact hpp.one_lt.ne' ((coprime_sigma_prime_pow hpp _).symm.eq_one_of_dvd htd)
  have hdt : d ∣ t - 1 := by
    have := Nat.dvd_sub_mod (n := d) (k := t)
    rwa [hmod] at this
  refine ⟨t, ?_, ho⟩
  simp only [orderReceivers, Finset.coe_filter, Set.mem_ofPred_eq]
  exact ⟨htN, htd, hpt, d, hd, hdt⟩

/-- **Order demands against capacities.** Let `N` be an odd perfect number, `A` a set of prime
factors of `N` and, for `p ∈ A`, `D p` a set of integers `d ≥ 3` dividing `e_p + 1`. Then
`∑_{p ∈ A} |D p| ≤ ∑_{t ∈ N.primeFactors} min (e_t, |compatible A D t|)`.
Whether this is in the literature was not verified. -/
theorem sum_card_le_sum_min_compatible (h : OddPerfect N) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) {D : ℕ → Finset ℕ}
    (hD : ∀ p ∈ A, ∀ d ∈ D p, 3 ≤ d ∧ d ∣ N.factorization p + 1) :
    ∑ p ∈ A, (D p).card ≤
      ∑ t ∈ N.primeFactors, min (N.factorization t) (compatible A D t).card := by
  refine le_trans (Finset.sum_le_sum fun p hp => card_le_card_orderReceivers h (hA hp)
    (hD p hp)) ?_
  have hswap : ∑ p ∈ A, (orderReceivers N D p).card = ∑ t ∈ N.primeFactors,
      (A.filter (fun p => t ∣ σ 1 (p ^ N.factorization p) ∧ p ≠ t ∧
        ∃ d ∈ D p, d ∣ t - 1)).card := by
    simp only [orderReceivers, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum fun t ht => le_min ?_ ?_
  · have htp := Nat.prime_of_mem_primeFactors ht
    have ht2 : t ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors ht)
    have : Fact t.Prime := ⟨htp⟩
    set B := A.filter (fun p => t ∣ σ 1 (p ^ N.factorization p) ∧ p ≠ t ∧
      ∃ d ∈ D p, d ∣ t - 1)
    refine le_trans ?_ (sum_padicValNat_sigma_le_factorization h.perfect htp ht2 B)
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpA, hpd, -⟩ := Finset.mem_filter.mp hp
    rw [Nat.padicValNat_def]
    refine one_le_padicValNat_of_dvd ?_ hpd
    exact (sigma_pos 1 _ (pow_ne_zero _
      (Nat.prime_of_mem_primeFactors (hA hpA)).ne_zero)).ne'
  · refine Finset.card_le_card fun p hp => ?_
    obtain ⟨hpA, -, hpt, hex⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpA, hpt, hex⟩

/-- **Branch closer.** Under the hypotheses of `sum_card_le_sum_min_compatible`, a strict
overshoot of the demands over the capacities is impossible.
Whether this is in the literature was not verified. -/
theorem not_sum_min_compatible_lt (h : OddPerfect N) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) {D : ℕ → Finset ℕ}
    (hD : ∀ p ∈ A, ∀ d ∈ D p, 3 ≤ d ∧ d ∣ N.factorization p + 1) :
    ¬ ∑ t ∈ N.primeFactors, min (N.factorization t) (compatible A D t).card <
      ∑ p ∈ A, (D p).card :=
  not_lt.mpr (sum_card_le_sum_min_compatible h hA hD)

/-! ## Examples of the definition -/

/-- The prime 19 can serve both 7 and 13 for the order 3, since `3 ∣ 18`. -/
example : compatible {7, 13} (fun _ => {3}) 19 = {7, 13} := by decide

/-- A prime never serves itself. -/
example : compatible {7} (fun _ => {3, 9}) 7 = ∅ := by decide

/-- The prime 31 serves 5 (order 3) and 11 (order 5), but not 13 (order 7, and `7 ∤ 30`). -/
example : compatible {5, 11, 13} (fun p => if p = 5 then {3} else if p = 11 then {5} else {7})
    31 = {5, 11} := by decide

end OddPerfect

#print axioms OddPerfect.card_le_card_orderReceivers
#print axioms OddPerfect.sum_card_le_sum_min_compatible
#print axioms OddPerfect.not_sum_min_compatible_lt
