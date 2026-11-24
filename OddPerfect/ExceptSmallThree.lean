import OddPerfect.Phi3
import OddPerfect.SpecialPrime

/-!
# A small exceptional prime when three divides an odd perfect number

Call a prime factor `p` of an odd perfect number `N` exceptional when its exponent is even and
at least `4`. If `3 ∣ N`, then some exceptional prime is at most `331`.

Proof. Suppose not. Then every prime factor `p ≤ 331` other than the special prime has
exponent exactly `2`. In particular the exponent of `3` is `2`, so at most two exact square
primes are `1` modulo `3`. The row `σ(3 ^ 2) = 13` forces `13 ∣ N`, and four cases on the
special prime (`13`, `61`, `97`, or none of these) each force three exact square primes that
are `1` modulo `3`.

This is a restricted result whose novelty was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If `3` divides an odd perfect number `N`, then some prime factor of `N` with even exponent
at least `4` is at most `331`. A restricted result whose novelty was not verified. -/
theorem exceptSmall_three {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 331 := by
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  obtain ⟨q, hq, -, hq4, hk, hev⟩ := exists_special_prime h
  have hqodd : Odd (N.factorization q) := Nat.odd_iff.mpr (by omega)
  have sq : ∀ p, p.Prime → p ∣ N → p ≠ q → p ≤ 331 → N.factorization p = 2 := by
    intro p hp hpN hpq hle
    have he := hev p hp hpq
    have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
    have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
    by_contra h2
    have h4 : 4 ≤ N.factorization p := by obtain ⟨j, hj⟩ := he; omega
    have := hne p hmem he h4
    omega
  have hcard := card_exact_sq_modEq_one_le h
  have h3q : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
  have v3 : N.factorization 3 = 2 := sq 3 Nat.prime_three h3 h3q (by norm_num)
  have force : ∀ p r : ℕ, p.Prime → p ∣ N → p ≠ q → p ≤ 331 → r.Prime → r ≠ 2 →
      r ∣ phi3 p → r ∣ N := fun p r hp hpN hpq hle hr hr2 hd =>
    OPNStarter.force_prime h.perfect hp (sq p hp hpN hpq hle) hr hr2
      (by rw [sigma_prime_sq hp]; exact hd)
  have three : ∀ a b c : ℕ, a.Prime → b.Prime → c.Prime → a ∣ N → b ∣ N → c ∣ N →
      a ≠ q → b ≠ q → c ≠ q → a ≤ 331 → b ≤ 331 → c ≤ 331 → a % 3 = 1 → b % 3 = 1 →
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
    have h19 := force 7 19 (by norm_num) h7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    have h127 := force 19 127 (by norm_num) h19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    exact three 7 19 127 (by norm_num) (by norm_num) (by norm_num) h7 h19 h127 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h61 := force 13 61 (by norm_num) h13 (Ne.symm hq13) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [phi3])
  by_cases hq61 : q = 61
  · subst hq61
    obtain ⟨h31, -⟩ := prime_dvd_of_dvd_succ_special h hq hqodd (r := 31) (by norm_num)
      (by norm_num) (by norm_num)
    have h331 := force 31 331 (by norm_num) h31 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [phi3])
    exact three 13 31 331 (by norm_num) (by norm_num) (by norm_num) h13 h31 h331 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h97 := force 61 97 (by norm_num) h61 (Ne.symm hq61) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [phi3])
  by_cases hq97 : q = 97
  · subst hq97
    obtain ⟨h7, -⟩ := prime_dvd_of_dvd_succ_special h hq hqodd (r := 7) (by norm_num)
      (by norm_num) (by norm_num)
    exact three 13 61 7 (by norm_num) (by norm_num) (by norm_num) h13 h61 h7 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact three 13 61 97 (by norm_num) (by norm_num) (by norm_num) h13 h61 h97 (Ne.symm hq13)
    (Ne.symm hq61) (Ne.symm hq97) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end OddPerfect

#print axioms OddPerfect.exceptSmall_three
