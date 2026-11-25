import OddPerfect.Phi3
import OddPerfect.SpecialPrime

/-!
# The least exceptional prime at three, case by case in the special prime

Call a prime factor `p` of an odd perfect number `N` exceptional when its exponent is even and
at least `4`. The landed theorem `exceptRoots_three` finds an exceptional prime in
`{3, 7, 13, 19, 31, 61, 97, 127, 331}` when `3 ∣ N`. Its proof splits on the special prime `q`
(the prime of odd exponent), and each branch uses only four of the nine primes. This module
states the branches:

* `q = 13`: an exceptional prime lies in `{3, 7, 19, 127}`;
* `q = 61`: an exceptional prime lies in `{3, 13, 31, 331}`;
* `q = 97`: an exceptional prime lies in `{3, 7, 13, 61}`;
* otherwise: an exceptional prime lies in `{3, 13, 61, 97}`.

Corollaries bound the least exceptional prime by `97` when `q ∉ {13, 61}` and by `127` when
`q ≠ 61`. These results hold for every odd perfect number divisible by `3`. They bound the
least exceptional prime only: they do not bound the number of exceptional primes and exclude
nothing. Novelty was not verified. The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If no prime of `S` is exceptional, a prime factor `p ∈ S` other than the special prime has
exponent exactly `2`. -/
private theorem erc_sq {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) {S : Finset ℕ}
    (hne : ∀ x ∈ S, x ∈ N.primeFactors → Even (N.factorization x) →
      ¬ 4 ≤ N.factorization x)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q) (hS : p ∈ S) :
    N.factorization p = 2 := by
  have he := even_factorization_of_ne h hq hodd hp hpq
  have h1 := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  have hmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  have h4 := hne p hS hmem he
  obtain ⟨j, hj⟩ := he
  omega

/-- A prime `r ≠ 2` dividing `phi3 p`, where `p` has exponent `2`, divides `N`. -/
private theorem erc_force {N p r : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hsq : N.factorization p = 2) (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ phi3 p) : r ∣ N :=
  OPNStarter.force_prime h.perfect hp hsq hr hr2 (by rw [sigma_prime_sq hp]; exact hd)

/-- If `3` has exponent `2`, there are no three distinct prime factors `≡ 1 (mod 3)` of
exponent `2`. -/
private theorem erc_three {N a b c : ℕ} (h : OddPerfect N) (hv3 : N.factorization 3 = 2)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (haN : a ∣ N) (hbN : b ∣ N) (hcN : c ∣ N)
    (ha2 : N.factorization a = 2) (hb2 : N.factorization b = 2)
    (hc2 : N.factorization c = 2) (ha1 : a % 3 = 1) (hb1 : b % 3 = 1) (hc1 : c % 3 = 1)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆
      N.primeFactors.filter fun p => N.factorization p = 2 ∧ p % 3 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    rcases hx with rfl | rfl | rfl
    · exact ⟨⟨ha, haN, h.ne_zero⟩, ha2, ha1⟩
    · exact ⟨⟨hb, hbN, h.ne_zero⟩, hb2, hb1⟩
    · exact ⟨⟨hc, hcN, h.ne_zero⟩, hc2, hc1⟩
  have h3c : ({a, b, c} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have := Finset.card_le_card hsub
  have := card_exact_sq_modEq_one_le h
  omega

/-- Let `N` be an odd perfect number with `3 ∣ N` whose special prime is `13`. Then some prime
of `{3, 7, 19, 127}` divides `N` with even exponent at least `4`. Valid for every odd perfect
number divisible by `3`; it bounds the least exceptional prime, not the number of exceptional
primes, and excludes nothing. Novelty was not verified. -/
theorem exceptRoots_three_of_special_eq_13 {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hodd : Odd (N.factorization 13)) :
    ∃ p ∈ ({3, 7, 19, 127} : Finset ℕ), p ∈ N.primeFactors ∧
      Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hq : (13 : ℕ).Prime := by norm_num
  have sq := @erc_sq N 13 h hq hodd _ hne
  have v3 := sq Nat.prime_three h3 (by norm_num) (by simp)
  obtain ⟨h7, -⟩ := prime_dvd_of_dvd_succ_special h hq hodd (r := 7) (by norm_num)
    (by norm_num) (by norm_num)
  have s7 := sq (by norm_num) h7 (by norm_num) (by simp)
  have h19 := erc_force h (by norm_num) s7 (r := 19) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s19 := sq (by norm_num) h19 (by norm_num) (by simp)
  have h127 := erc_force h (by norm_num) s19 (r := 127) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s127 := sq (by norm_num) h127 (by norm_num) (by simp)
  exact erc_three h v3 (by norm_num) (by norm_num) (by norm_num) h7 h19 h127 s7 s19 s127
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Let `N` be an odd perfect number with `3 ∣ N` whose special prime is `61`. Then some prime
of `{3, 13, 31, 331}` divides `N` with even exponent at least `4`. Valid for every odd perfect
number divisible by `3`; it bounds the least exceptional prime, not the number of exceptional
primes, and excludes nothing. Novelty was not verified. -/
theorem exceptRoots_three_of_special_eq_61 {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hodd : Odd (N.factorization 61)) :
    ∃ p ∈ ({3, 13, 31, 331} : Finset ℕ), p ∈ N.primeFactors ∧
      Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hq : (61 : ℕ).Prime := by norm_num
  have sq := @erc_sq N 61 h hq hodd _ hne
  have v3 := sq Nat.prime_three h3 (by norm_num) (by simp)
  have h13 := erc_force h Nat.prime_three v3 (r := 13) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s13 := sq (by norm_num) h13 (by norm_num) (by simp)
  obtain ⟨h31, -⟩ := prime_dvd_of_dvd_succ_special h hq hodd (r := 31) (by norm_num)
    (by norm_num) (by norm_num)
  have s31 := sq (by norm_num) h31 (by norm_num) (by simp)
  have h331 := erc_force h (by norm_num) s31 (r := 331) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s331 := sq (by norm_num) h331 (by norm_num) (by simp)
  exact erc_three h v3 (by norm_num) (by norm_num) (by norm_num) h13 h31 h331 s13 s31 s331
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Let `N` be an odd perfect number with `3 ∣ N` whose special prime is `97`. Then some prime
of `{3, 7, 13, 61}` divides `N` with even exponent at least `4`. Valid for every odd perfect
number divisible by `3`; it bounds the least exceptional prime, not the number of exceptional
primes, and excludes nothing. Novelty was not verified. -/
theorem exceptRoots_three_of_special_eq_97 {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hodd : Odd (N.factorization 97)) :
    ∃ p ∈ ({3, 7, 13, 61} : Finset ℕ), p ∈ N.primeFactors ∧
      Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hq : (97 : ℕ).Prime := by norm_num
  have sq := @erc_sq N 97 h hq hodd _ hne
  have v3 := sq Nat.prime_three h3 (by norm_num) (by simp)
  have h13 := erc_force h Nat.prime_three v3 (r := 13) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s13 := sq (by norm_num) h13 (by norm_num) (by simp)
  have h61 := erc_force h (by norm_num) s13 (r := 61) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s61 := sq (by norm_num) h61 (by norm_num) (by simp)
  obtain ⟨h7, -⟩ := prime_dvd_of_dvd_succ_special h hq hodd (r := 7) (by norm_num)
    (by norm_num) (by norm_num)
  have s7 := sq (by norm_num) h7 (by norm_num) (by simp)
  exact erc_three h v3 (by norm_num) (by norm_num) (by norm_num) h13 h61 h7 s13 s61 s7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Let `N` be an odd perfect number with `3 ∣ N` whose special prime `q` (the prime of odd
exponent) is none of `13`, `61`, `97`. Then some prime of `{3, 13, 61, 97}` divides `N` with
even exponent at least `4`. Valid for every odd perfect number divisible by `3`; it bounds the
least exceptional prime, not the number of exceptional primes, and excludes nothing. Novelty
was not verified. -/
theorem exceptRoots_three_of_special_ne {N q : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h13 : q ≠ 13) (h61 : q ≠ 61)
    (h97 : q ≠ 97) :
    ∃ p ∈ ({3, 13, 61, 97} : Finset ℕ), p ∈ N.primeFactors ∧
      Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have sq := @erc_sq N q h hq hodd _ hne
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    norm_num at this
  have v3 := sq Nat.prime_three h3 h3q (by simp)
  have h13N := erc_force h Nat.prime_three v3 (r := 13) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s13 := sq (by norm_num) h13N (Ne.symm h13) (by simp)
  have h61N := erc_force h (by norm_num) s13 (r := 61) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s61 := sq (by norm_num) h61N (Ne.symm h61) (by simp)
  have h97N := erc_force h (by norm_num) s61 (r := 97) (by norm_num) (by norm_num)
    (by norm_num [phi3])
  have s97 := sq (by norm_num) h97N (Ne.symm h97) (by simp)
  exact erc_three h v3 (by norm_num) (by norm_num) (by norm_num) h13N h61N h97N s13 s61 s97
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The four branches of `exceptRoots_three` in one statement: for an odd perfect number `N`
with `3 ∣ N` and special prime `q` (the prime of odd exponent), some prime of the four element
set chosen by `q` divides `N` with even exponent at least `4`. Valid for every odd perfect
number divisible by `3`; it bounds the least exceptional prime, not the number of exceptional
primes, and excludes nothing. Novelty was not verified. -/
theorem exceptRoots_three_cases {N q : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    ∃ p ∈ (if q = 13 then ({3, 7, 19, 127} : Finset ℕ) else if q = 61 then {3, 13, 31, 331}
        else if q = 97 then {3, 7, 13, 61} else {3, 13, 61, 97}),
      p ∈ N.primeFactors ∧ Even (N.factorization p) ∧ 4 ≤ N.factorization p := by
  split_ifs with h13 h61 h97
  · subst h13; exact exceptRoots_three_of_special_eq_13 h h3 hodd
  · subst h61; exact exceptRoots_three_of_special_eq_61 h h3 hodd
  · subst h97; exact exceptRoots_three_of_special_eq_97 h h3 hodd
  · exact exceptRoots_three_of_special_ne h h3 hq hodd h13 h61 h97

/-- For an odd perfect number `N` with `3 ∣ N` whose special prime is neither `13` nor `61`,
some prime factor `p ≤ 97` has even exponent at least `4`. Bounds the least exceptional prime
only; it excludes nothing. Novelty was not verified. -/
theorem exceptRoots_le_97_of_special_ne {N q : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h13 : q ≠ 13) (h61 : q ≠ 61) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 97 := by
  by_cases h97 : q = 97
  · subst h97
    obtain ⟨p, hS, hp, he, h4⟩ := exceptRoots_three_of_special_eq_97 h h3 hodd
    exact ⟨p, hp, he, h4, by simp only [Finset.mem_insert, Finset.mem_singleton] at hS; omega⟩
  · obtain ⟨p, hS, hp, he, h4⟩ := exceptRoots_three_of_special_ne h h3 hq hodd h13 h61 h97
    exact ⟨p, hp, he, h4, by simp only [Finset.mem_insert, Finset.mem_singleton] at hS; omega⟩

/-- For an odd perfect number `N` with `3 ∣ N` whose special prime is not `61`, some prime
factor `p ≤ 127` has even exponent at least `4`. Bounds the least exceptional prime only; it
excludes nothing. Novelty was not verified. -/
theorem exceptRoots_le_127_of_special_ne {N q : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h61 : q ≠ 61) :
    ∃ p ∈ N.primeFactors, Even (N.factorization p) ∧ 4 ≤ N.factorization p ∧ p ≤ 127 := by
  by_cases h13 : q = 13
  · subst h13
    obtain ⟨p, hS, hp, he, h4⟩ := exceptRoots_three_of_special_eq_13 h h3 hodd
    exact ⟨p, hp, he, h4, by simp only [Finset.mem_insert, Finset.mem_singleton] at hS; omega⟩
  · obtain ⟨p, hp, he, h4, hle⟩ := exceptRoots_le_97_of_special_ne h h3 hq hodd h13 h61
    exact ⟨p, hp, he, h4, by omega⟩

end OddPerfect

#print axioms OddPerfect.exceptRoots_three_of_special_eq_13
#print axioms OddPerfect.exceptRoots_three_of_special_eq_61
#print axioms OddPerfect.exceptRoots_three_of_special_eq_97
#print axioms OddPerfect.exceptRoots_three_of_special_ne
#print axioms OddPerfect.exceptRoots_three_cases
#print axioms OddPerfect.exceptRoots_le_97_of_special_ne
#print axioms OddPerfect.exceptRoots_le_127_of_special_ne
