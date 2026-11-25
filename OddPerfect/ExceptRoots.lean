import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.LedgerReceiver

/-!
# The roots of the small exceptional prime chain at three

Call a prime factor `p` of an odd perfect number `N` exceptional when its exponent is even and
at least `4`. The landed proof of `exceptSmall_three` uses the hypothesis "exponent exactly 2"
only at the primes of `R = {3, 7, 13, 19, 31, 61, 97, 127, 331}`. Restating that chain with the
hypothesis restricted to `R` gives:

* `exceptRoots_three`: if `3 ∣ N`, some exceptional prime of `N` lies in `R`.
* `exceptRoots_exceptSmall_three`: the landed statement as a corollary (every element of `R`
  is at most `331`).
* `not_three_dvd_of_exceptions_mod_three`: if every exceptional prime is `2` modulo `3`, then
  `3 ∤ N`, since every element of `R` is `0` or `1` modulo `3`.
* `thirtytwo_le_card_exceptions_of_mod_three`: under the same hypothesis, at least 32 ordinary
  primes have exponent at least `4`, `ω(N) ≥ 33` and `Ω(N) ≥ 2 ω(N) + 63`.

The chain is the landed one; related chains appear in the literature (Ochem and Zelinsky,
2026 preprint). The last result is a conditional family result. Novelty was not verified. The
odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma ArithmeticFunction.omega ArithmeticFunction.Omega

namespace OddPerfect

/-- If `3` divides an odd perfect number `N`, then some prime factor of `N` with even exponent
at least `4` lies in `{3, 7, 13, 19, 31, 61, 97, 127, 331}`. This is the chain of
`exceptSmall_three` with the square hypothesis used only at these primes. Related chains
appear in the literature (Ochem and Zelinsky, 2026 preprint); novelty was not verified. -/
theorem exceptRoots_three {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    ∃ p ∈ ({3, 7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ), p ∈ N.primeFactors ∧
      Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  set R : Finset ℕ := {3, 7, 13, 19, 31, 61, 97, 127, 331} with hR
  by_contra hne
  simp only [not_exists, not_and] at hne
  obtain ⟨q, hq, -, hq4, hk, hev⟩ := exists_special_prime h
  have sq : ∀ p, p.Prime → p ∣ N → p ≠ q → p ∈ R → N.factorization p = 2 := by
    intro p hp hpN hpq hR'
    have he := hev p hp hpq
    have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
    have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
    by_contra h2
    have h4 : 4 ≤ N.factorization p := by obtain ⟨j, hj⟩ := he; omega
    exact hne p hR' hmem he h4
  have hqodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have hcard := card_exact_sq_modEq_one_le h
  have h3q : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
  have v3 : N.factorization 3 = 2 := sq 3 Nat.prime_three h3 h3q (by simp [hR])
  have force : ∀ p r : ℕ, p.Prime → p ∣ N → p ≠ q → p ∈ R → r.Prime → r ≠ 2 →
      r ∣ phi3 p → r ∣ N := fun p r hp hpN hpq hle hr hr2 hd =>
    OPNStarter.force_prime h.perfect hp (sq p hp hpN hpq hle) hr hr2
      (by rw [sigma_prime_sq hp]; exact hd)
  have three : ∀ a b c : ℕ, a.Prime → b.Prime → c.Prime → a ∣ N → b ∣ N → c ∣ N →
      a ≠ q → b ≠ q → c ≠ q → a ∈ R → b ∈ R → c ∈ R → a % 3 = 1 → b % 3 = 1 →
      c % 3 = 1 → a ≠ b → a ≠ c → b ≠ c → False := by
    intro a b c ha hb hc haN hbN hcN haq hbq hcq ha3 hb3 hc3 ha1 hb1 hc1 hab hac hbc
    have hsub : ({a, b, c} : Finset ℕ) ⊆
        N.primeFactors.filter fun p => N.factorization p = 2 ∧ p % 3 = 1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨ha, haN, h.ne_zero⟩, sq x ha haN haq ha3, ha1⟩
      · exact ⟨⟨hb, hbN, h.ne_zero⟩, sq x hb hbN hbq hb3, hb1⟩
      · exact ⟨⟨hc, hcN, h.ne_zero⟩, sq x hc hcN hcq hc3, hc1⟩
    have h3c : ({a, b, c} : Finset ℕ).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac,
      hbc, rfl⟩
    have := Finset.card_le_card hsub
    omega
  have h13 : 13 ∣ N := OPNStarter.force_prime h.perfect Nat.prime_three v3 (by norm_num)
    (by norm_num) (by rw [sigma_prime_sq Nat.prime_three]; norm_num [phi3])
  by_cases hq13 : q = 13
  · subst hq13
    obtain ⟨h7, -⟩ := prime_dvd_of_dvd_succ_special h hq hqodd (r := 7) (by norm_num)
      (by norm_num) (by norm_num)
    have h19 := force 7 19 (by norm_num) h7 (by norm_num) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    have h127 := force 19 127 (by norm_num) h19 (by norm_num) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    exact three 7 19 127 (by norm_num) (by norm_num) (by norm_num) h7 h19 h127 (by norm_num)
      (by norm_num) (by norm_num) (by simp [hR]) (by simp [hR]) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h61 := force 13 61 (by norm_num) h13 (Ne.symm hq13) (by simp [hR]) (by norm_num)
    (by norm_num) (by norm_num [phi3])
  by_cases hq61 : q = 61
  · subst hq61
    obtain ⟨h31, -⟩ := prime_dvd_of_dvd_succ_special h hq hqodd (r := 31) (by norm_num)
      (by norm_num) (by norm_num)
    have h331 := force 31 331 (by norm_num) h31 (by norm_num) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    exact three 13 31 331 (by norm_num) (by norm_num) (by norm_num) h13 h31 h331 (by norm_num)
      (by norm_num) (by norm_num) (by simp [hR]) (by simp [hR]) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h97 := force 61 97 (by norm_num) h61 (Ne.symm hq61) (by simp [hR]) (by norm_num)
    (by norm_num) (by norm_num [phi3])
  by_cases hq97 : q = 97
  · subst hq97
    obtain ⟨h7, -⟩ := prime_dvd_of_dvd_succ_special h hq hqodd (r := 7) (by norm_num)
      (by norm_num) (by norm_num)
    exact three 13 61 7 (by norm_num) (by norm_num) (by norm_num) h13 h61 h7 (by norm_num)
      (by norm_num) (by norm_num) (by simp [hR]) (by simp [hR]) (by simp [hR]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact three 13 61 97 (by norm_num) (by norm_num) (by norm_num) h13 h61 h97 (Ne.symm hq13)
    (Ne.symm hq61) (Ne.symm hq97) (by simp [hR]) (by simp [hR]) (by simp [hR]) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Sanity check: the landed statement `exceptSmall_three` follows from `exceptRoots_three`. -/
theorem exceptRoots_exceptSmall_three {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 331 := by
  obtain ⟨p, hR, hp, he, h4⟩ := exceptRoots_three h h3
  exact ⟨p, hp, he, h4, by simp only [Finset.mem_insert, Finset.mem_singleton] at hR; omega⟩

/-- If every prime factor of an odd perfect number `N` with even exponent at least `4` is `2`
modulo `3`, then `3 ∤ N`. Every element of `{3, 7, 13, 19, 31, 61, 97, 127, 331}` is `0` or `1`
modulo `3`. Restricted result; novelty was not verified. -/
theorem not_three_dvd_of_exceptions_mod_three {N : ℕ} (h : OddPerfect N)
    (hmod : ∀ p ∈ N.primeFactors, Even (N.factorization p) → 4 ≤ N.factorization p →
      p % 3 = 2) :
    ¬ 3 ∣ N := by
  intro h3
  obtain ⟨p, hR, hp, he, h4⟩ := exceptRoots_three h h3
  have := hmod p hp he h4
  simp only [Finset.mem_insert, Finset.mem_singleton] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Let `N` be an odd perfect number with special prime `q` (odd exponent), and suppose every
prime factor with even exponent at least `4` is `2` modulo `3`. Then at least 32 prime factors
`p ≠ q` have exponent at least `4`, `ω(N) ≥ 33` and `Ω(N) ≥ 2 ω(N) + 63`.

Proof: `3 ∤ N` by `not_three_dvd_of_exceptions_mod_three`. A prime factor `t ≠ q` with
`t ≡ 1 (mod 3)` has even exponent; exponent at least `4` is excluded by the hypothesis, and
exponent `2` gives `3 ∣ t ^ 2 + t + 1 = σ(t ^ 2)`, so `3 ∣ N`. Hence every prime factor
`≡ 1 (mod 3)` is `q`, and `receiver_three_free` applies; a prime `p ≠ q` with `3 ∤ e_p + 1`
has even exponent other than `2`, hence at least `4`.

The hypothesis is the hypothesis `hH` of `five_le_card_budgetExceptions` in
`OddPerfect/ExcessBudget.lean` (the prime factors `r ≠ q` with exponent other than `2` are
exactly those with even exponent at least `4`). Both other hypotheses of that theorem are
dropped: `hA` (no exception `r` divides `e_q + 1`) and `hW` (no exception `r` has
`r ^ 2 ∣ p ^ (r - 1) - 1` for `p` in the exceptions or `q`, `p ≠ r`). The count rises from 5
to 32. Conditional family result; novelty was not verified. -/
theorem thirtytwo_le_card_exceptions_of_mod_three {N q : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hmod : ∀ p ∈ N.primeFactors, Even (N.factorization p) → 4 ≤ N.factorization p →
      p % 3 = 2) :
    32 ≤ ((N.primeFactors.erase q).filter (fun p => 4 ≤ N.factorization p)).card ∧
      33 ≤ ω N ∧ 2 * ω N + 63 ≤ Ω N := by
  have h3 := not_three_dvd_of_exceptions_mod_three h hmod
  have hrecv : ∀ t ∈ N.primeFactors, t % 3 = 1 → t = q := by
    intro t ht ht1
    by_contra htq
    obtain ⟨htp, htN, -⟩ := Nat.mem_primeFactors.mp ht
    have he := even_factorization_of_ne h hq hodd htp htq
    have h1 : 1 ≤ N.factorization t := htp.factorization_pos_of_dvd h.ne_zero htN
    by_cases h4 : 4 ≤ N.factorization t
    · have := hmod t ht he h4
      omega
    · have h2 : N.factorization t = 2 := by obtain ⟨j, hj⟩ := he; omega
      refine h3 (OPNStarter.force_prime h.perfect htp h2 Nat.prime_three (by norm_num) ?_)
      rw [sigma_prime_sq htp]
      apply Nat.dvd_of_mod_eq_zero
      simp [phi3, Nat.add_mod, Nat.pow_mod, ht1]
  obtain ⟨hX, hω, hΩ⟩ := receiver_three_free h hq hodd h3 hrecv
  refine ⟨hX.trans (Finset.card_le_card fun p hp => ?_), hω, hΩ⟩
  obtain ⟨hp1, hp3⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp1
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpN
  have h1 : 1 ≤ N.factorization p := hpp.factorization_pos_of_dvd h.ne_zero hpd
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hpp hpq
  have : N.factorization p ≠ 2 := fun h2 => hp3 (by rw [h2])
  exact Finset.mem_filter.mpr ⟨hp1, by omega⟩

end OddPerfect

#print axioms OddPerfect.exceptRoots_three
#print axioms OddPerfect.exceptRoots_exceptSmall_three
#print axioms OddPerfect.not_three_dvd_of_exceptions_mod_three
#print axioms OddPerfect.thirtytwo_le_card_exceptions_of_mod_three
