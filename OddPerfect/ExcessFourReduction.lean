import OddPerfect.RestrainedEight
import OddPerfect.TwoExceptionTwoThree
import OddPerfect.ThreeFreeThree
import OddPerfect.Steuerwald

/-!
# Total excess at least 4, modulo three exclusions

Let `N` be an odd perfect number with special prime `q`. Every other prime factor `p` has an
even exponent `e_p ≥ 2`; call `e_p / 2 - 1` its excess. This module shows that the total excess
is at least 4 (`four_le_excess_of_exclusions`), equivalently `ω(m) + 4 ≤ Ω(m)` in Euler's form
`N = q ^ a * m ^ 2` (`four_le_cardFactors_sub_of_exclusions`), provided three exclusions hold:

* `ExcessS1`: exponent 6 at 3, at most one further prime of exponent 4, all others 2;
* `ExcessS2a`: exponent 4 at 3, at most two further primes of exponent 4, all others 2;
* `ExcessS2b`: exponent 2 at 3, at most three primes of exponent 4, all others 2.

The three exclusions are hypotheses here; this module proves nothing about odd perfect numbers
without them.

Proof. Let `X` be the set of primes `p ≠ q` with positive excess and suppose the total is at
most 3, so `|X| ≤ 3`. If `|X| ≤ 1`, `restrained_twelve_le_three` gives `v_3(N) ≥ 12`, an excess
of at least 5 at 3. If `|X| = 2`, then `3 ∈ X` with `v_3(N) ≥ 6`, which forces exclusion S1. If
`|X| = 3`, every excess is 1 and `3 ∣ N`; the cases `3 ∈ X` and `3 ∉ X` are S2a and S2b.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- Exclusion S1: exponent 6 at 3, at most one further prime of exponent 4, all others 2. -/
def ExcessS1 : Prop :=
  ∀ {N q r : ℕ}, OddPerfect N → q.Prime → Odd (N.factorization q) → N.factorization 3 = 6 →
    (r ∈ N.primeFactors → N.factorization r = 4) →
    (∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ r → N.factorization p = 2) → False

/-- Exclusion S2a: exponent 4 at 3, at most two further primes of exponent 4, all others 2. -/
def ExcessS2a : Prop :=
  ∀ {N q r₁ r₂ : ℕ}, OddPerfect N → q.Prime → Odd (N.factorization q) → N.factorization 3 = 4 →
    (r₁ ∈ N.primeFactors → N.factorization r₁ = 4) →
    (r₂ ∈ N.primeFactors → N.factorization r₂ = 4) →
    (∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) → False

/-- Exclusion S2b: exponent 2 at 3, at most three primes of exponent 4, all others 2. -/
def ExcessS2b : Prop :=
  ∀ {N q r₁ r₂ r₃ : ℕ}, OddPerfect N → q.Prime → Odd (N.factorization q) →
    N.factorization 3 = 2 →
    (r₁ ∈ N.primeFactors → N.factorization r₁ = 4) →
    (r₂ ∈ N.primeFactors → N.factorization r₂ = 4) →
    (r₃ ∈ N.primeFactors → N.factorization r₃ = 4) →
    (∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2) → False

/-- Under the three exclusions, the total excess `∑ (v_p(N) / 2 - 1)` over the prime factors
`p ≠ q` of an odd perfect number is at least 4. The exclusions are unproved hypotheses. -/
theorem four_le_excess_of_exclusions (h1 : ExcessS1) (h2a : ExcessS2a) (h2b : ExcessS2b)
    {N q : ℕ} (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) :
    4 ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  by_contra hlt
  push Not at hlt
  have hN0 := h.ne_zero
  have hq3 : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  obtain ⟨S, hS⟩ : ∃ S, S = N.primeFactors.erase q := ⟨_, rfl⟩
  rw [← hS] at hlt
  have hexp : ∀ p ∈ S, N.factorization p = 2 * ((N.factorization p / 2 - 1) + 1) := by
    intro p hp
    rw [hS] at hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have h1 := (hpp.dvd_iff_one_le_factorization hN0).mp (Nat.dvd_of_mem_primeFactors hpN)
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
    omega
  have hle : ∀ p ∈ S, N.factorization p / 2 - 1 ≤ 3 := fun p hp =>
    (Finset.single_le_sum (f := fun p => N.factorization p / 2 - 1)
      (fun _ _ => Nat.zero_le _) hp).trans (by omega)
  have h3S : 3 ∣ N → 3 ∈ S := fun h3 => by
    rw [hS]
    exact Finset.mem_erase.mpr ⟨hq3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hN0⟩⟩
  obtain ⟨X, hX⟩ : ∃ X, X = S.filter (fun p => N.factorization p / 2 - 1 ≠ 0) := ⟨_, rfl⟩
  have hsumX : ∑ p ∈ X, (N.factorization p / 2 - 1) < 4 := by
    rw [hX, Finset.sum_filter_ne_zero]; exact hlt
  have hmemX : ∀ p ∈ X, p ∈ S ∧ 1 ≤ N.factorization p / 2 - 1 := fun p hp => by
    rw [hX, Finset.mem_filter] at hp
    exact ⟨hp.1, Nat.one_le_iff_ne_zero.mpr hp.2⟩
  have hcard : X.card ≤ 3 := by
    have : X.card ≤ ∑ p ∈ X, (N.factorization p / 2 - 1) := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun p hp => (hmemX p hp).2
    omega
  have hout : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ X → N.factorization p = 2 := by
    intro p hp hpq hpX
    have hpS : p ∈ S := by rw [hS]; exact Finset.mem_erase.mpr ⟨hpq, hp⟩
    have he := hexp p hpS
    have : N.factorization p / 2 - 1 = 0 := by
      by_contra hne
      exact hpX (by rw [hX]; exact Finset.mem_filter.mpr ⟨hpS, hne⟩)
    omega
  have hpS : ∀ p ∈ S, p.Prime ∧ p ≠ q := fun p hp => by
    rw [hS] at hp
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    exact ⟨Nat.prime_of_mem_primeFactors hpN, hpq⟩
  have h3dvd : ∀ k, 1 ≤ k → k ≤ N.factorization 3 → 3 ∣ N := fun k hk hk3 =>
    (Nat.prime_three.dvd_iff_one_le_factorization hN0).mpr (by omega)
  rcases (by omega : X.card ≤ 1 ∨ X.card = 2 ∨ X.card = 3) with hc | hc | hc
  · -- At most one prime of positive excess: the exponent of 3 is at least 12.
    obtain ⟨r, hr, hrq, hrX⟩ : ∃ r, r.Prime ∧ r ≠ q ∧ ∀ p ∈ X, p = r := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h0
      · exact ⟨3, Nat.prime_three, hq3, fun p hp => by simp [Finset.card_eq_zero.mp h0] at hp⟩
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h0
        obtain ⟨ha, haq⟩ := hpS a (hmemX a (Finset.mem_singleton_self a)).1
        exact ⟨a, ha, haq, fun p hp => Finset.mem_singleton.mp hp⟩
    have h12 := restrained_twelve_le_three h hq hodd hr hrq
      fun p hp hpq hpr => hout p hp hpq fun hpX => hpr (hrX p hpX)
    have h3 := h3S (h3dvd 12 (by omega) h12)
    have := hle 3 h3
    omega
  · -- Two primes of positive excess: one is 3 with exponent 6, the other has exponent 4.
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    have hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ a → p ≠ b → N.factorization p = 2 :=
      fun p hp hpq ha hb => hout p hp hpq (by simp [ha, hb])
    have h6 := two_exceptions_six_le_three h hq hodd hsq
    rw [Finset.sum_pair hab] at hsumX
    have ha := hmemX a (by simp)
    have hb := hmemX b (by simp)
    have hea := hexp a ha.1
    have heb := hexp b hb.1
    rcases two_exceptions_three_exceptional h hq hodd hsq with rfl | rfl
    · exact @h1 N q b h hq hodd (by omega) (fun _ => by omega)
        fun p hp hpq hp3 hpb => hsq p hp hpq hp3 hpb
    · exact @h1 N q a h hq hodd (by omega) (fun _ => by omega)
        fun p hp hpq hp3 hpa => hsq p hp hpq hpa hp3
  · -- Three primes of positive excess: each has exponent 4.
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    have hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ a → p ≠ b → p ≠ c → N.factorization p = 2 :=
      fun p hp hpq ha hb hc => hout p hp hpq (by simp [ha, hb, hc])
    have h3 := three_dvd_of_three_exceptions h hq hodd hsq
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hsumX
    have ha := hmemX a (by simp)
    have hb := hmemX b (by simp)
    have hc := hmemX c (by simp)
    have hea := hexp a ha.1
    have heb := hexp b hb.1
    have hec := hexp c hc.1
    by_cases h3X : 3 = a ∨ 3 = b ∨ 3 = c
    · rcases h3X with rfl | rfl | rfl
      · exact @h2a N q b c h hq hodd (by omega) (fun _ => by omega) (fun _ => by omega)
          fun p hp hpq hp3 hpb hpc => hsq p hp hpq hp3 hpb hpc
      · exact @h2a N q a c h hq hodd (by omega) (fun _ => by omega) (fun _ => by omega)
          fun p hp hpq hp3 hpa hpc => hsq p hp hpq hpa hp3 hpc
      · exact @h2a N q a b h hq hodd (by omega) (fun _ => by omega) (fun _ => by omega)
          fun p hp hpq hp3 hpa hpb => hsq p hp hpq hpa hpb hp3
    · push Not at h3X
      have he3 := hsq 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, hN0⟩) hq3
        h3X.1 h3X.2.1 h3X.2.2
      exact @h2b N q a b c h hq hodd he3 (fun _ => by omega) (fun _ => by omega)
        (fun _ => by omega) hsq

/-- Under the three exclusions, in Euler's form `N = q ^ a * m ^ 2` with `q ∤ m` of an odd
perfect number, `ω(m) + 4 ≤ Ω(m)`. The exclusions are unproved hypotheses. -/
theorem four_le_cardFactors_sub_of_exclusions (h1 : ExcessS1) (h2a : ExcessS2a)
    (h2b : ExcessS2b) {N q a m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hN : N = q ^ a * m ^ 2) :
    ArithmeticFunction.cardDistinctFactors m + 4 ≤ ArithmeticFunction.cardFactors m := by
  have hN0 := h.ne_zero
  have hm0 : m ≠ 0 := by rintro rfl; simp [hN] at hN0
  have hq0 : q ^ a ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hfac : ∀ p, N.factorization p = a * q.factorization p + 2 * m.factorization p := by
    intro p
    rw [hN, Nat.factorization_mul hq0 (pow_ne_zero _ hm0), Finsupp.add_apply,
      Nat.factorization_pow, Nat.factorization_pow]
    rfl
  have hmq : m.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqm
  have hkq : N.factorization q = a := by
    rw [hfac, hq.factorization_self, hmq]
    ring
  have hk : Odd a := by
    by_contra hk
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hk
    exact not_isSquare h ⟨q ^ j * m, by rw [hN]; ring⟩
  have hne : ∀ p, p ≠ q → N.factorization p = 2 * m.factorization p := by
    intro p hpq
    rw [hfac, hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq)]
    ring
  have hset : N.primeFactors.erase q = m.primeFactors := by
    ext p
    rw [Finset.mem_erase, ← Nat.support_factorization, ← Nat.support_factorization,
      Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hpq, hp⟩
      rw [hne p hpq] at hp
      omega
    · intro hp
      have hpq : p ≠ q := by rintro rfl; exact hp hmq
      exact ⟨hpq, by rw [hne p hpq]; omega⟩
  have key := four_le_excess_of_exclusions h1 h2a h2b h hq (hkq ▸ hk)
  rw [hset] at key
  have hsum : ∑ p ∈ m.primeFactors, (N.factorization p / 2 - 1)
      = ∑ p ∈ m.primeFactors, (m.factorization p - 1) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpq : p ≠ q := by rintro rfl; exact (Nat.dvd_of_mem_primeFactors hp |> hqm)
    rw [hne p hpq]
    omega
  have hOm : Ω m = ∑ p ∈ m.primeFactors, (m.factorization p - 1) + m.primeFactors.card := by
    rw [cardFactors_eq_sum_primeFactors, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hm0
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  rw [cardDistinctFactors_eq_card_primeFactors, hOm]
  omega

end OddPerfect

#print axioms OddPerfect.four_le_excess_of_exclusions
#print axioms OddPerfect.four_le_cardFactors_sub_of_exclusions
