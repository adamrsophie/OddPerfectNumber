import OddPerfect.EulerIndexPairAll
import OddPerfect.OmegaSevenFinal

/-!
# Two prime Euler index: the other primes sit inside `q + 1`

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_rows_all` (in `OddPerfect/EulerIndexPairAll.lean`) shows that
`p ^ v_p(N) ∣ q + 1` for every prime `p ∣ N` outside `{q, r, s}`. This module collects these
divisibilities into one product and draws two consequences.

* `eulerIndex_pair_outside_prod_dvd`: `2 ∏ p ^ v_p(N) ∣ q + 1`, the product over the primes of
  `N` outside `{q, r, s}`.
* `eulerIndex_pair_outside_sq_le`: every such `p` has `p ^ 2 ≤ q + 1` and `p < q`.
* `eulerIndex_pair_card_above_le_two`: at most two prime factors of `N` exceed `q`.
* `eulerIndex_pair_special_ge`: `2668049 ≤ q`. With `seven_le_card_primeFactors` there are at
  least four outside primes, their product is at least `3 * 5 * 7 * 11 = 1155`, each exponent
  is at least 2, so `q + 1 ≥ 2 * 1155 ^ 2`.

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). They do not exclude this case. Their novelty has not been verified.
-/

namespace OddPerfect

namespace EulerIndexPairOutside

/-- A product of prime powers over distinct primes divides `z` when each factor does. -/
private lemma epo_prod_dvd {O : Finset ℕ} {f : ℕ → ℕ} {z : ℕ} (hp : ∀ p ∈ O, p.Prime)
    (hd : ∀ p ∈ O, p ^ f p ∣ z) : ∏ p ∈ O, p ^ f p ∣ z := by
  induction O using Finset.induction_on with
  | empty => simp
  | insert a O ha ih =>
    rw [Finset.prod_insert ha]
    have hpa : a.Prime := hp a (Finset.mem_insert_self _ _)
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd a (Finset.mem_insert_self _ _))
      (ih (fun p h => hp p (Finset.mem_insert_of_mem h))
        (fun p h => hd p (Finset.mem_insert_of_mem h)))
    refine Nat.Coprime.prod_right fun i hi => ?_
    exact Nat.coprime_pow_primes _ _ hpa (hp i (Finset.mem_insert_of_mem hi))
      (fun h => ha (h ▸ hi))

/-- Four or more distinct odd primes have product at least `3 * 5 * 7 * 11 = 1155`. -/
private lemma epo_prod_ge {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (h2 : ∀ p ∈ S, p ≠ 2)
    (hc : 4 ≤ S.card) : 1155 ≤ ∏ p ∈ S, p := by
  have key : ∀ T ∈ ({3, 5, 7} : Finset ℕ).powerset,
      1155 ≤ (∏ p ∈ T, p) * 11 ^ (4 - T.card) := by decide
  have hsub : S.filter (· < 11) ∈ ({3, 5, 7} : Finset ℕ).powerset := by
    rw [Finset.mem_powerset]
    intro p hpS
    rw [Finset.mem_filter] at hpS
    have hpp := hp p hpS.1
    have hp2 := h2 p hpS.1
    have h1 := hpS.2
    have := hpp.two_le
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases p
    all_goals first
      | (left; rfl)
      | (right; left; rfl)
      | (right; right; rfl)
      | exact (hp2 rfl).elim
      | (exfalso; norm_num at hpp)
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p => p < 11)
  have hbig : 11 ^ (S.filter (fun p => ¬ p < 11)).card ≤
      ∏ p ∈ S.filter (fun p => ¬ p < 11), p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp' => by
      rw [Finset.mem_filter] at hp'; omega)
  have hmono : 11 ^ (4 - (S.filter (· < 11)).card) ≤
      11 ^ (S.filter (fun p => ¬ p < 11)).card :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p < 11)]
  exact (key _ hsub).trans (Nat.mul_le_mul_left _ (hmono.trans hbig))

end EulerIndexPairOutside

open EulerIndexPairOutside

variable {N q m r s : ℕ}

/-- The facts used for one outside prime: it is an odd prime, its exponent is at least 2,
and its prime power divides `q + 1`. -/
private lemma epo_outside_facts (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∀ p ∈ N.primeFactors \ {q, r, s}, p.Prime ∧ p ≠ 2 ∧ 2 ≤ N.factorization p ∧
      p ^ N.factorization p ∣ q + 1 := by
  obtain ⟨t, u, htu, -, -, -, -, -, -, -, -, -, -, hall⟩ :=
    eulerIndex_pair_rows_all h hq hN hqm hr hs hrs hJ
  intro p hp
  rw [Finset.mem_sdiff] at hp
  obtain ⟨hpN, hpO⟩ := hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpO
  obtain ⟨hpq, hpr, hps⟩ := hpO
  have ht : t ∈ ({r, s} : Finset ℕ) := htu ▸ by simp
  have hu : u ∈ ({r, s} : Finset ℕ) := htu ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht hu
  have hpt : p ≠ t := by rcases ht with rfl | rfl <;> assumption
  have hpu : p ≠ u := by rcases hu with rfl | rfl <;> assumption
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hp2 : p ≠ 2 := by
    rintro rfl; exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hpN)
  refine ⟨hpp, hp2, ?_, (hall p hpN hpq hpt hpu).2.1⟩
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hpm : p ∣ m := by
    rcases (Nat.Prime.dvd_mul hpp).mp (hN ▸ Nat.dvd_of_mem_primeFactors hpN) with hd | hd
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hd) hpq
    · exact hpp.dvd_of_dvd_pow hd
  have hpos := hpp.factorization_pos_of_dvd hm hpm
  rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
    hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  omega

/-- **Outside primes inside `q + 1`.** Let `N = q m ^ 2` be an odd perfect number with special
prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly
the two prime factors `r ≠ s`. Then twice the product of `p ^ v_p(N)` over the primes `p ∣ N`
outside `{q, r, s}` divides `q + 1`. This is a restricted result (special exponent 1, index
supported on exactly two primes); it does not exclude this case. Its novelty has not been
verified. -/
theorem eulerIndex_pair_outside_prod_dvd (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    2 * ∏ p ∈ N.primeFactors \ {q, r, s}, p ^ N.factorization p ∣ q + 1 := by
  have F := epo_outside_facts h hq hN hqm hr hs hrs hJ
  have hq2 : ¬ 2 ∣ q := by
    intro h2
    have hqN : q ∣ N := hN ▸ dvd_mul_right q _
    exact h.not_two_dvd (h2.trans hqN)
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (by omega)
    (epo_prod_dvd (fun p hp => (F p hp).1) (fun p hp => (F p hp).2.2.2))
  refine Nat.Coprime.prod_right fun p hp => Nat.Coprime.pow_right _ ?_
  exact (Nat.coprime_primes Nat.prime_two (F p hp).1).mpr (F p hp).2.1.symm

/-- **Outside primes lie below `q`.** In the setting of `eulerIndex_pair_outside_prod_dvd`,
every prime `p ∣ N` outside `{q, r, s}` has `p ^ 2 ≤ q + 1` and `p < q`. This is a restricted
result (special exponent 1, index supported on exactly two primes); it does not exclude this
case. Its novelty has not been verified. -/
theorem eulerIndex_pair_outside_sq_le (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∀ p ∈ N.primeFactors \ {q, r, s}, p ^ 2 ≤ q + 1 ∧ p < q := by
  intro p hp
  obtain ⟨hpp, hp2, hg, hd⟩ := epo_outside_facts h hq hN hqm hr hs hrs hJ p hp
  have hle : p ^ 2 ≤ q + 1 :=
    Nat.le_of_dvd (by omega) ((pow_dvd_pow p hg).trans hd)
  have h3 : 3 ≤ p := by have := hpp.two_le; omega
  refine ⟨hle, ?_⟩
  nlinarith

/-- **At most two primes above `q`.** In the setting of `eulerIndex_pair_outside_prod_dvd`, at
most two prime factors of `N` exceed `q` (they lie in `{r, s}`). This is a restricted result
(special exponent 1, index supported on exactly two primes); it does not exclude this case.
Its novelty has not been verified. -/
theorem eulerIndex_pair_card_above_le_two (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    (N.primeFactors.filter (q < ·)).card ≤ 2 := by
  have H := eulerIndex_pair_outside_sq_le h hq hN hqm hr hs hrs hJ
  have hsub : N.primeFactors.filter (q < ·) ⊆ {r, s} := by
    intro p hp
    rw [Finset.mem_filter] at hp
    by_contra hrs'
    have hO : p ∈ N.primeFactors \ {q, r, s} := by
      rw [Finset.mem_sdiff]
      refine ⟨hp.1, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrs' ⊢
      exact ⟨by omega, hrs'.1, hrs'.2⟩
    have := (H p hO).2
    omega
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- **Lower bound on the special prime.** In the setting of `eulerIndex_pair_outside_prod_dvd`,
`2668049 ≤ q`. By `seven_le_card_primeFactors` at least four primes of `N` lie outside
`{q, r, s}`; four distinct odd primes have product at least `1155`, every exponent is at least
2, so `q + 1 ≥ 2 * 1155 ^ 2 = 2668050`. This is a restricted result (special exponent 1, index
supported on exactly two primes); it does not exclude this case. Its novelty has not been
verified. -/
theorem eulerIndex_pair_special_ge (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    2668049 ≤ q := by
  have F := epo_outside_facts h hq hN hqm hr hs hrs hJ
  have hD := eulerIndex_pair_outside_prod_dvd h hq hN hqm hr hs hrs hJ
  set O := N.primeFactors \ {q, r, s} with hOdef
  have hc : 4 ≤ O.card := by
    have h7 := seven_le_card_primeFactors h
    have h3 : ({q, r, s} : Finset ℕ).card ≤ 3 := Finset.card_le_three
    have := Finset.le_card_sdiff ({q, r, s} : Finset ℕ) N.primeFactors
    rw [← hOdef] at this
    omega
  have hP := epo_prod_ge (fun p hp => (F p hp).1) (fun p hp => (F p hp).2.1) hc
  have hsq : (∏ p ∈ O, p) ^ 2 ≤ ∏ p ∈ O, p ^ N.factorization p := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod' fun p hp =>
      Nat.pow_le_pow_right (F p hp).1.pos (F p hp).2.2.1
  have hle := Nat.le_of_dvd (by omega) hD
  have h1155 : 1155 ^ 2 ≤ (∏ p ∈ O, p) ^ 2 := Nat.pow_le_pow_left hP 2
  omega

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_outside_prod_dvd
#print axioms OddPerfect.eulerIndex_pair_outside_sq_le
#print axioms OddPerfect.eulerIndex_pair_card_above_le_two
#print axioms OddPerfect.eulerIndex_pair_special_ge
