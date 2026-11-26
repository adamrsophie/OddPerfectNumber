import OddPerfect.Zsigmondy
import OddPerfect.ValuationBounds

/-!
# Distinct multiplicative orders inside one component

Let `N` be an odd perfect number and `p` a prime factor with exponent `e_p`, `m_p = e_p + 1`.
For each divisor `d` of `m_p` with `3 ∣ d`, Bang's theorem (`Zsigmondy.lean`) gives a prime `t`
dividing `σ(p ^ e_p)` of order exactly `d` modulo `t`; then `t ≡ 1 (mod d)`, so `t ≡ 1 (mod 3)`,
and different `d` give different `t`. Each pair `(p, t)` uses at least one unit of
`v_t(σ(p ^ e_p))`, and these units add up to at most `e_t` over `p`. Counting the pairs by `t`:

* `sum_card_three_dvd_divisors_le`: for every set `A` of prime factors of `N`,
  `∑_{p ∈ A} #{d ∣ m_p : 3 ∣ d} ≤ ∑_{t ∣ N prime, t ≡ 1 (mod 3)} min(e_t, |A|)`.
* `sum_card_three_dvd_divisors_sub_one_le`: the same with one order per component removed and
  a chosen prime `q` (in practice the special prime) removed from the right side.
* `card_nine_dvd_le`: the number of prime factors `p ≠ q` with `9 ∣ m_p` is at most the sum
  of `e_t` over the prime factors `t ≠ q` with `t ≡ 1 (mod 3)`.

Whether these results are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-- The divisors `d` of `m_p = e_p + 1` with `3 ∣ d`. -/
def threeOrders (N p : ℕ) : Finset ℕ :=
  (N.factorization p + 1).divisors.filter (3 ∣ ·)

/-- The prime factors `t ∈ T` of `N` that divide `σ(p ^ e_p)`. -/
def receiversIn (N p : ℕ) (T : Finset ℕ) : Finset ℕ :=
  T.filter (· ∣ σ 1 (p ^ N.factorization p))

/-- One component: the number of divisors `d` of `m_p` with `3 ∣ d` is at most the number of
prime factors `t ≡ 1 (mod 3)` of `N` dividing `σ(p ^ e_p)`. The map `t ↦ ord_t(p)` covers all
such `d`, by Bang's theorem. -/
theorem card_threeOrders_le (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    (threeOrders N p).card ≤
      (receiversIn N p (N.primeFactors.filter (· % 3 = 1))).card := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  refine Finset.card_le_card_of_surjOn (fun t => orderOf (p : ZMod t)) ?_
  intro d hd
  simp only [threeOrders, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
  obtain ⟨⟨hdm, -⟩, c, rfl⟩ := hd
  have hc : c ≠ 0 := by rintro rfl; simp at hdm
  obtain ⟨t, ht, htd, ho, hmod⟩ :=
    exists_prime_dvd_sigma_orderOf_eq hpp hp3 (by omega) hdm
  have ht3 : t % 3 = 1 := by
    rw [← Nat.mod_mod_of_dvd t (dvd_mul_right 3 c), hmod]
  have ht2 : t ≠ 2 := by rintro rfl; norm_num at ht3
  have htN : t ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨ht, OPNStarter.force_prime h.perfect hpp rfl ht ht2 htd,
      h.ne_zero⟩
  refine ⟨t, ?_, ho⟩
  simp only [receiversIn, Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq]
  exact ⟨⟨htN, ht3⟩, htd⟩

/-- Double counting: for a set `A` of prime factors and a set `T` of odd prime factors of `N`, the pairs
`(p, t) ∈ A × T` with `t ∣ σ(p ^ e_p)` number at most `∑_{t ∈ T} min(e_t, |A|)`. -/
theorem sum_card_receiversIn_le (h : OddPerfect N) {A : Finset ℕ} (hA : A ⊆ N.primeFactors)
    {T : Finset ℕ} (hT : ∀ t ∈ T, t.Prime ∧ t ≠ 2) :
    ∑ p ∈ A, (receiversIn N p T).card ≤ ∑ t ∈ T, min (N.factorization t) A.card := by
  have hswap : ∑ p ∈ A, (receiversIn N p T).card =
      ∑ t ∈ T, (A.filter (fun p => t ∣ σ 1 (p ^ N.factorization p))).card := by
    simp only [receiversIn, Finset.card_filter]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum fun t ht => le_min ?_ (Finset.card_filter_le _ _)
  obtain ⟨htp, ht2⟩ := hT t ht
  have : Fact t.Prime := ⟨htp⟩
  set B := A.filter (fun p => t ∣ σ 1 (p ^ N.factorization p))
  have hle := sum_padicValNat_sigma_le_factorization h.perfect htp ht2 B
  refine le_trans ?_ hle
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpd := (Finset.mem_filter.mp hp).2
  rw [Nat.padicValNat_def]
  refine one_le_padicValNat_of_dvd ?_ hpd
  exact (sigma_pos 1 _ (pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (hA (Finset.mem_filter.mp hp).1)).ne_zero)).ne'

/-- **Distinct orders inside one sender.** For an odd perfect number `N` and every set `A` of
prime factors of `N`, `∑_{p ∈ A} #{d ∣ e_p + 1 : 3 ∣ d}` is at most the sum of
`min(e_t, |A|)` over the prime factors `t ≡ 1 (mod 3)` of `N`.
Whether this result is new was not verified against the literature. -/
theorem sum_card_three_dvd_divisors_le (h : OddPerfect N) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) :
    ∑ p ∈ A, ((N.factorization p + 1).divisors.filter (3 ∣ ·)).card ≤
      ∑ t ∈ N.primeFactors.filter (· % 3 = 1), min (N.factorization t) A.card := by
  refine le_trans (Finset.sum_le_sum fun p hp => card_threeOrders_le h (hA hp)) ?_
  refine sum_card_receiversIn_le h hA fun t ht => ?_
  obtain ⟨htN, ht3⟩ := Finset.mem_filter.mp ht
  exact ⟨Nat.prime_of_mem_primeFactors htN, by rintro rfl; norm_num at ht3⟩

/-- **Distinct orders, one prime removed.** For an odd perfect number `N`, any number `q` (in
practice the special prime) and every set `A` of prime factors of `N`,
`∑_{p ∈ A} (#{d ∣ e_p + 1 : 3 ∣ d} - 1)` is at most the sum of `min(e_t, |A|)` over the prime
factors `t ≠ q` of `N` with `t ≡ 1 (mod 3)`: the prime `q` serves at most one order of each
component. Whether this result is new was not verified against the literature. -/
theorem sum_card_three_dvd_divisors_sub_one_le (h : OddPerfect N) (q : ℕ) {A : Finset ℕ}
    (hA : A ⊆ N.primeFactors) :
    ∑ p ∈ A, (((N.factorization p + 1).divisors.filter (3 ∣ ·)).card - 1) ≤
      ∑ t ∈ (N.primeFactors.erase q).filter (· % 3 = 1),
        min (N.factorization t) A.card := by
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (sum_card_receiversIn_le h hA ?_)
  · have h1 := card_threeOrders_le h (hA hp)
    have h2 := Finset.pred_card_le_card_erase
      (s := receiversIn N p (N.primeFactors.filter (· % 3 = 1))) (a := q)
    have h3 : (receiversIn N p (N.primeFactors.filter (· % 3 = 1))).erase q =
        receiversIn N p ((N.primeFactors.erase q).filter (· % 3 = 1)) := by
      simp only [receiversIn, Finset.filter_erase]
    rw [h3] at h2
    change (threeOrders N p).card - 1 ≤ _
    omega
  · intro t ht
    obtain ⟨htN, ht3⟩ := Finset.mem_filter.mp ht
    exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase htN),
      by rintro rfl; norm_num at ht3⟩

/-- **Components with `9 ∣ m_p`.** For an odd perfect number `N` and any number `q` (in practice
the special prime), the number of prime factors `p ≠ q` with `9 ∣ e_p + 1` is at most the sum
of `e_t` over the prime factors `t ≠ q` of `N` with `t ≡ 1 (mod 3)`. Each such component has the
two orders `3` and `9`, and `q` can serve only one of them.
Whether this result is new was not verified against the literature. -/
theorem card_nine_dvd_le (h : OddPerfect N) (q : ℕ) :
    ((N.primeFactors.erase q).filter (9 ∣ N.factorization · + 1)).card ≤
      ∑ t ∈ (N.primeFactors.erase q).filter (· % 3 = 1), N.factorization t := by
  set A := (N.primeFactors.erase q).filter (9 ∣ N.factorization · + 1)
  have hA : A ⊆ N.primeFactors :=
    (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hmain := sum_card_three_dvd_divisors_sub_one_le h q hA
  have hlow : A.card ≤ ∑ p ∈ A, (((N.factorization p + 1).divisors.filter (3 ∣ ·)).card - 1) := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => ?_
    have h9 : 9 ∣ N.factorization p + 1 := (Finset.mem_filter.mp hp).2
    have hsub : ({3, 9} : Finset ℕ) ⊆ (N.factorization p + 1).divisors.filter (3 ∣ ·) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨⟨(by norm_num : 3 ∣ 9).trans h9, by omega⟩, dvd_refl 3⟩
      · exact ⟨⟨h9, by omega⟩, by norm_num⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (by norm_num)] at this
    omega
  refine le_trans hlow (le_trans hmain (Finset.sum_le_sum fun t _ => min_le_left _ _))

end OddPerfect

#print axioms OddPerfect.card_threeOrders_le
#print axioms OddPerfect.sum_card_receiversIn_le
#print axioms OddPerfect.sum_card_three_dvd_divisors_le
#print axioms OddPerfect.sum_card_three_dvd_divisors_sub_one_le
#print axioms OddPerfect.card_nine_dvd_le
