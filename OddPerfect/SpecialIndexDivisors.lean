import OddPerfect.LedgerOrders
import OddPerfect.SpecialIndexWitness

/-!
# Divisors of the special index when `3` divides it

Let `N` be an odd perfect number with special prime `q` of exponent `a`, and let
`T = ∑_{p ∣ N, p ≠ q} (v_p(N) / 2 - 1)` be the total excess. Write
`D = {d ∣ a + 1 : 3 ∣ d}` and `v = v_3(a + 1)`.

* `card_divisors_filter_three_add_le`: `|D| + v ≤ 2 T + 2`.
* `card_divisors_special_index_le_four_mul_excess`: if `3 ∣ a + 1`, then
  `τ(a + 1) ≤ 4 T`.

This removes no unbounded family outright. For each fixed total excess `T` it bounds the number
of divisors of the special index `a + 1` on the branch `3 ∣ a + 1`; the primes dividing `a + 1`
stay unbounded, and the branch `3 ∤ a + 1` is untouched.

Proof idea. By Bang's theorem every `d ∈ D` is the order of `q` modulo some prime factor of
`σ(q ^ a)`; these primes are distinct, `1` modulo `3`, different from `q` and divide `N`
(`card_threeOrders_le`). Those whose index `v_r(N) + 1` is divisible by `3` each use one factor
`3` of `v_3(N)`, and the special row uses at least `v` of them (`special_index_budget`,
`padicValNat_three_succ_le_sigma`). The others have exponent at least `4`, so each carries
excess at least `1`; the prime `3` carries excess `v_3(N) / 2 - 1` when it divides `N`. Hence
`|D| + v ≤ v_3(N) + b₀ ≤ 2 T + 2`. Finally `a + 1 = 3 ^ v * m` with `m ≡ 2 (mod 4)`, so
`τ(a + 1) = (v + 1) τ(m)`, `|D| = v τ(m)` and `τ(m)` is even, which gives `τ(a + 1) ≤ 4 T`.

Whether these inequalities are in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The divisors `d` of `a + 1` with `3 ∣ d` are at most as many as the prime factors `p ≠ q`
of `N` with `p ≡ 1 (mod 3)`, where `a` is the exponent of the special prime `q`. -/
theorem card_divisors_filter_three_le_card {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ((N.factorization q + 1).divisors.filter (3 ∣ ·)).card ≤
      (N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1).card := by
  have hqN : q ∈ N.primeFactors := by
    have : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
    exact Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_of_factorization_pos this, h.ne_zero⟩
  refine (card_threeOrders_le h hqN).trans (Finset.card_le_card ?_)
  intro t ht
  simp only [receiversIn, Finset.mem_filter] at ht ⊢
  obtain ⟨⟨htN, ht3⟩, htd⟩ := ht
  refine ⟨htN, ?_, ht3⟩
  rintro rfl
  exact hq.one_lt.ne' ((coprime_sigma_prime_pow hq _).symm.eq_one_of_dvd htd)

/-- The excess bridge: `v_3(N) + b₀ ≤ 2 T + 2`, where `b₀` counts the prime factors `p ≠ q`
with `p ≡ 1 (mod 3)` and `3 ∤ v_p(N) + 1`, and `T` is the total excess. -/
theorem factorization_three_add_card_le_excess {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    N.factorization 3 + (N.primeFactors.filter fun p =>
        p ≠ q ∧ p % 3 = 1 ∧ ¬ 3 ∣ N.factorization p + 1).card ≤
      2 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 2 := by
  set G := N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1 ∧ ¬ 3 ∣ N.factorization p + 1
  have hq3 : q ≠ 3 := by have := (special_mod_four h hq hodd).1; omega
  have hGsub : G ⊆ N.primeFactors.erase q := by
    intro p hp
    simp only [G, Finset.mem_filter] at hp
    exact Finset.mem_erase.mpr ⟨hp.2.1, hp.1⟩
  have h3G : (3 : ℕ) ∉ G := by simp [G]
  have hone : ∀ p ∈ G, 1 ≤ N.factorization p / 2 - 1 := by
    intro p hp
    simp only [G, Finset.mem_filter] at hp
    obtain ⟨hpN, hpq, -, hp3⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd hpp hpq
    have hpos := hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpN)
    have hne : N.factorization p ≠ 2 := fun h2 => hp3 (by rw [h2])
    omega
  have hc : G.card ≤ ∑ p ∈ G, (N.factorization p / 2 - 1) := by
    simpa using Finset.card_nsmul_le_sum G _ 1 hone
  by_cases h3N : 3 ∈ N.primeFactors
  · have h3e : (3 : ℕ) ∈ N.primeFactors.erase q := Finset.mem_erase.mpr ⟨Ne.symm hq3, h3N⟩
    have hle := Finset.sum_le_sum_of_subset (f := fun p => N.factorization p / 2 - 1)
      (Finset.insert_subset h3e hGsub)
    rw [Finset.sum_insert h3G] at hle
    obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd Nat.prime_three (Ne.symm hq3)
    have hpos := Nat.prime_three.factorization_pos_of_dvd h.ne_zero
      (Nat.dvd_of_mem_primeFactors h3N)
    omega
  · have h0 : N.factorization 3 = 0 := by
      by_contra hne
      exact h3N (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_three, Nat.dvd_of_factorization_pos hne, h.ne_zero⟩)
    have hle := Finset.sum_le_sum_of_subset (f := fun p => N.factorization p / 2 - 1) hGsub
    beta_reduce at hle
    omega

/-- **Orders of the special row and the excess.** For an odd perfect number `N` with special
prime `q` of exponent `a`, the number of divisors `d` of `a + 1` with `3 ∣ d`, plus
`v_3(a + 1)`, is at most `2 T + 2`, where `T = ∑_{p ∣ N, p ≠ q} (v_p(N) / 2 - 1)` is the total
excess. Whether this inequality is in the literature was not verified. -/
theorem card_divisors_filter_three_add_le {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ((N.factorization q + 1).divisors.filter (3 ∣ ·)).card +
        padicValNat 3 (N.factorization q + 1) ≤
      2 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) + 2 := by
  have hA := card_divisors_filter_three_le_card h hq hodd
  have hb := special_index_budget h hq hodd Nat.prime_three (by decide)
  have hq3 : q ≠ 3 := by have := (special_mod_four h hq hodd).1; omega
  have hv := padicValNat_three_succ_le_sigma hq hq3 hodd
  have hs := Finset.card_filter_add_card_filter_not
    (s := N.primeFactors.filter fun p => p ≠ q ∧ p % 3 = 1)
    (fun p => 3 ∣ N.factorization p + 1)
  simp only [Finset.filter_filter, and_assoc] at hs
  have hD := factorization_three_add_card_le_excess h hq hodd
  omega

/-- Arithmetic step: if `1 ≤ v` and `v (2 W) + v ≤ 2 T + 2`, then `(v + 1) (2 W) ≤ 4 T`. -/
private theorem succ_mul_two_le_four_mul {v W T : ℕ} (hv : 1 ≤ v)
    (h : v * (2 * W) + v ≤ 2 * T + 2) : (v + 1) * (2 * W) ≤ 4 * T := by
  rcases Nat.lt_or_ge v 2 with hv2 | hv2
  · obtain rfl : v = 1 := by omega
    rw [show 1 * (2 * W) = 2 * W by ring] at h
    rw [show (1 + 1) * (2 * W) = 4 * W by ring]
    omega
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
    rw [show (w + 2) * (2 * W) = 2 * (w * W) + 4 * W by ring] at h
    rw [show (w + 2 + 1) * (2 * W) = 2 * (w * W) + 6 * W by ring]
    omega

/-- Divisor count step: if `n ≡ 2 (mod 4)`, `3 ∣ n` and the divisors `d` of `n` with `3 ∣ d`
together with `v_3(n)` number at most `2 T + 2`, then `τ(n) ≤ 4 T`. -/
theorem card_divisors_le_four_mul_of_card_filter_three {n T : ℕ} (hn4 : n % 4 = 2)
    (h3 : 3 ∣ n) (hD : (n.divisors.filter (3 ∣ ·)).card + padicValNat 3 n ≤ 2 * T + 2) :
    n.divisors.card ≤ 4 * T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : n ≠ 0 := by omega
  have hv1 : 1 ≤ padicValNat 3 n := by
    rw [Nat.padicValNat_def]; exact one_le_padicValNat_of_dvd hn0 h3
  have hns : ¬ 3 ^ (padicValNat 3 n + 1) ∣ n := by
    rw [Nat.padicValNat_def]; exact pow_succ_padicValNat_not_dvd (p := 3) hn0
  obtain ⟨v, hvdef⟩ : ∃ v, padicValNat 3 n = v := ⟨_, rfl⟩
  rw [hvdef] at hv1 hns hD
  obtain ⟨m, hm⟩ : 3 ^ v ∣ n := by
    rw [← hvdef, Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _
  have hm3 : ¬ 3 ∣ m := by
    rintro ⟨c, rfl⟩
    exact hns ⟨c, by rw [hm, pow_succ]; ring⟩
  have hcop3 : Nat.Coprime (3 ^ v) m :=
    Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hn0 hm
  have h2m : 2 ∣ m := by
    have h2n : 2 ∣ 3 ^ v * m := by rw [← hm]; omega
    exact (Nat.Coprime.pow_right v (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_left h2n
  obtain ⟨u, rfl⟩ := h2m
  have hu : ¬ 2 ∣ u := by
    rintro ⟨w, rfl⟩
    have : 4 ∣ n := ⟨3 ^ v * w, by rw [hm]; ring⟩
    omega
  have hcop2 : Nat.Coprime 2 u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hu
  have h2 : (Nat.divisors 2).card = 2 := by decide
  have hτm : (2 * u).divisors.card = 2 * u.divisors.card := by
    rw [Nat.Coprime.card_divisors_mul hcop2, h2]
  have h3pow : (3 ^ v).divisors.card = v + 1 := by
    rw [← sigma_zero_apply, sigma_zero_apply_prime_pow Nat.prime_three]
  have hτn : n.divisors.card = (v + 1) * (2 * u).divisors.card := by
    rw [hm, Nat.Coprime.card_divisors_mul hcop3, h3pow]
  have hfilt : n.divisors.filter (fun d => ¬ 3 ∣ d) = (2 * u).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hd3⟩
      refine ⟨?_, hm0⟩
      have hc : Nat.Coprime d (3 ^ v) := Nat.Coprime.pow_right v
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hd3))
      rw [hm] at hd
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨hd, -⟩
      refine ⟨⟨by rw [hm]; exact Dvd.dvd.mul_left hd _, hn0⟩, fun h3d => hm3 (h3d.trans hd)⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => 3 ∣ d)
  rw [hfilt] at hsplit
  rw [hτm] at hτn hsplit
  have hDv : (n.divisors.filter (3 ∣ ·)).card = v * (2 * u.divisors.card) := by
    have : (v + 1) * (2 * u.divisors.card) = v * (2 * u.divisors.card) + 2 * u.divisors.card :=
      by ring
    omega
  rw [hDv] at hD
  rw [hτn]
  exact succ_mul_two_le_four_mul hv1 hD

/-- **Divisors of the special index.** For an odd perfect number `N` with special prime `q` of
exponent `a`, if `3 ∣ a + 1`, then `τ(a + 1) ≤ 4 T`, where
`T = ∑_{p ∣ N, p ≠ q} (v_p(N) / 2 - 1)` is the total excess.

This removes no unbounded family outright. For each fixed total excess `T` it bounds the number
of divisors of the special index `a + 1` on the branch `3 ∣ a + 1`; the primes dividing `a + 1`
stay unbounded, and the branch `3 ∤ a + 1` is untouched. Whether this inequality is in the
literature was not verified. -/
theorem card_divisors_special_index_le_four_mul_excess {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : 3 ∣ N.factorization q + 1) :
    (N.factorization q + 1).divisors.card ≤
      4 * (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) := by
  have h4 := (special_mod_four h hq hodd).2
  exact card_divisors_le_four_mul_of_card_filter_three (by omega) h3
    (card_divisors_filter_three_add_le h hq hodd)

end OddPerfect

#print axioms OddPerfect.card_divisors_filter_three_le_card
#print axioms OddPerfect.factorization_three_add_card_le_excess
#print axioms OddPerfect.card_divisors_filter_three_add_le
#print axioms OddPerfect.card_divisors_le_four_mul_of_card_filter_three
#print axioms OddPerfect.card_divisors_special_index_le_four_mul_excess
