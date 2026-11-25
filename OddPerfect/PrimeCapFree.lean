import OddPerfect.PrimeCapFamily
import OddPerfect.Zsigmondy

/-!
# The largest prime caps without the hypothesis `e_q = 1`

Restricted family results; no novelty is claimed, and whether they are in the literature was
not verified.

The results of `OddPerfect.PrimeCapFamily` assume that the special exponent is `1`, and use it
only to show that the special row `σ(q ^ e_q)` is not divisible by the largest prime factor
`P`. Here that step is proved under the weaker hypothesis `gcd(e_q + 1, P - 1) ≤ 2`: if
`P ∣ σ(q ^ a)` then `q ^ (a + 1) ≡ 1` and `q ^ (P - 1) ≡ 1` modulo `P`, so the order of `q`
modulo `P` is `1` or `2`, and both are impossible for odd primes `q < P`.

The case `e_q = 1` is the case `gcd(2, P - 1) = 2`, so these theorems contain the landed
theorems of `OddPerfect.PrimeCapFamily`. The special exponent itself is still not bounded by
these results: they bound `e_P` only.

`largest_not_dvd_succ_factorization`: the largest prime factor `P` divides no `e_u + 1`, since
a prime factor `r ≡ 1 (mod P)` of `N` would exceed `P`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Special row. Let `q < P` be odd primes and `a` a natural number with
`gcd(a + 1, P - 1) ≤ 2`. Then `P ∤ σ(q ^ a)`. Restricted result; novelty not verified. -/
theorem not_dvd_sigma_prime_pow_of_gcd {q P a : ℕ} (hq : q.Prime) (hP : P.Prime)
    (hq2 : q ≠ 2) (hP2 : P ≠ 2) (hqP : q < P) (hg : Nat.gcd (a + 1) (P - 1) ≤ 2) :
    ¬ P ∣ σ 1 (q ^ a) := by
  have := Fact.mk hP
  intro hd
  rw [sigma_one_apply_prime_pow hq] at hd
  have hsum : ∑ i ∈ Finset.range (a + 1), (q : ZMod P) ^ i = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ P).mpr hd
  have hpow : (q : ZMod P) ^ (a + 1) = 1 := by
    have := geom_sum_mul (q : ZMod P) (a + 1)
    rw [hsum, zero_mul] at this
    exact sub_eq_zero.mp this.symm
  have hx0 : (q : ZMod P) ≠ 0 := by
    intro h0
    have := Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff q P).mp h0)
    omega
  have hferm : (q : ZMod P) ^ (P - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hgd : (q : ZMod P) ^ Nat.gcd (a + 1) (P - 1) = 1 := pow_gcd_eq_one.mpr ⟨hpow, hferm⟩
  have hx1 : (q : ZMod P) ≠ 1 := by
    intro h1
    have h1' : ((q : ℕ) : ZMod P) = ((1 : ℕ) : ZMod P) := by rw [h1, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hqP, Nat.mod_eq_of_lt hP.one_lt] at h1'
    exact hq.one_lt.ne' h1'
  have hgpos : 0 < Nat.gcd (a + 1) (P - 1) := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos a)
  have hqo := hq.eq_two_or_odd.resolve_left hq2
  have hPo := hP.eq_two_or_odd.resolve_left hP2
  rcases (by omega : Nat.gcd (a + 1) (P - 1) = 1 ∨ Nat.gcd (a + 1) (P - 1) = 2) with h1 | h2
  · rw [h1, pow_one] at hgd
    exact hx1 hgd
  · rw [h2, pow_two] at hgd
    rcases mul_self_eq_one_iff.mp hgd with h | h
    · exact hx1 h
    · have h0 : ((q + 1 : ℕ) : ZMod P) = 0 := by
        push_cast
        rw [h]
        ring
      have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ P).mp h0)
      omega

private theorem sigmaWeight_special_eq_zero_of_gcd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hg : Nat.gcd (N.factorization q + 1) (P - 1) ≤ 2)
    (hP : P ∈ N.primeFactors) (hqm : q ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) : sigmaWeight N q P = 0 := by
  have hodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have := hodd q hqm
  have := hodd P hP
  have hnd := not_dvd_sigma_prime_pow_of_gcd hq (Nat.prime_of_mem_primeFactors hP)
    (by omega) (by omega) (lt_of_le_of_ne (hmax q hqm) hPq.symm) hg
  unfold sigmaWeight
  exact Nat.factorization_eq_zero_of_not_dvd hnd

/-- Family bound for prime senders, without `e_q = 1`. Let `N` be an odd perfect number, `q` a
prime with `gcd(e_q + 1, P - 1) ≤ 2`, and `P ≠ q` the largest prime factor. Let `E` be a
finite set of exponents `e` with `3 ≤ e + 1 ≤ 11` and `P ∤ e + 1`. If every prime factor
other than `q` and `P` has its exponent in `E`, then `e_P ≤ ∑ e ∈ E, primeSenderCap (e + 1)`.
Restricted family result; novelty not verified. -/
theorem factorization_largest_le_sum_primeSenderCap_of_gcd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hg : Nat.gcd (N.factorization q + 1) (P - 1) ≤ 2)
    (hP : P ∈ N.primeFactors) (hPq : P ≠ q)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (E : Finset ℕ)
    (hE : ∀ e ∈ E, 3 ≤ e + 1 ∧ e + 1 ≤ 11 ∧ ¬ P ∣ e + 1)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P → N.factorization p ∈ E) :
    N.factorization P ≤ ∑ e ∈ E, primeSenderCap (e + 1) := by
  refine factorization_le_sum_of_cap h hP hmax E (fun e => primeSenderCap (e + 1))
    (fun e he U hU => ?_) (fun p hp hpP => ?_)
  · obtain ⟨h3, h11, hPe⟩ := hE e he
    exact sum_factorization_geom_sum_le_primeSenderCap (Nat.prime_of_mem_primeFactors hP)
      hPe h3 h11 U hU
  · by_cases hpq : p = q
    · subst hpq
      exact Or.inl (sigmaWeight_special_eq_zero_of_gcd h hq hg hP hp hPq hmax)
    · exact Or.inr (hexp p hp hpq hpP)

private theorem largest_gt_200000' {N P : ℕ} (h : OddPerfect N)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ P) : 200000 < P := by
  obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
  exact lt_of_lt_of_le hlt (hmax p hp)

private theorem not_dvd_small' {P n : ℕ} (hP : 200000 < P) (hn : 0 < n) (hn11 : n ≤ 11) :
    ¬ P ∣ n := fun hd => by
  have := Nat.le_of_dvd hn hd
  omega

/-- Exponents `2`, `4`, `6`, prime senders, without `e_q = 1`. Let `N` be an odd perfect
number with special prime `q` (`e_q` odd), `gcd(e_q + 1, P - 1) ≤ 2`, and largest prime factor
`P ≠ q`. If every prime factor other than `q` and `P` has exponent `2`, `4` or `6`, then
`e_P ≤ 18`. Restricted family result; novelty not verified. -/
theorem factorization_largest_le_eighteen_of_gcd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hg : Nat.gcd (N.factorization q + 1) (P - 1) ≤ 2) (hP : P ∈ N.primeFactors)
    (hPq : P ≠ q) (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4 ∨ N.factorization p = 6) :
    N.factorization P ≤ 18 := by
  have hbig := largest_gt_200000' h hmax
  have hb := factorization_largest_le_sum_primeSenderCap_of_gcd h hq hg hP hPq hmax {2, 4, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small' hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4, 6} : Finset ℕ), primeSenderCap (e + 1) = 19 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hP) hPq
  omega

/-- Exponents `2`, `6`, prime senders, without `e_q = 1`. Let `N` be an odd perfect number
with special prime `q` (`e_q` odd), `gcd(e_q + 1, P - 1) ≤ 2`, and largest prime factor
`P ≠ q`. If every prime factor other than `q` and `P` has exponent `2` or `6`, then
`e_P ≤ 12`. Restricted family result; novelty not verified. -/
theorem factorization_largest_le_twelve_of_gcd {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hg : Nat.gcd (N.factorization q + 1) (P - 1) ≤ 2) (hP : P ∈ N.primeFactors)
    (hPq : P ≠ q) (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 6) :
    N.factorization P ≤ 12 := by
  have hbig := largest_gt_200000' h hmax
  have hb := factorization_largest_le_sum_primeSenderCap_of_gcd h hq hg hP hPq hmax {2, 6}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small' hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 6} : Finset ℕ), primeSenderCap (e + 1) = 13 := by decide
  obtain ⟨k, hk⟩ := even_factorization_of_ne h hq hodd (Nat.prime_of_mem_primeFactors hP) hPq
  omega

/-- Exponents `2`, `4`, prime senders, without `e_q = 1`: the conclusion `e_P ≤ 8` of
`factorization_largest_le_eight_of_primeSenderCap` under `gcd(e_q + 1, P - 1) ≤ 2`.
Restricted family result; novelty not verified. -/
theorem factorization_largest_le_eight_of_primeSenderCap_of_gcd {N q P : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hg : Nat.gcd (N.factorization q + 1) (P - 1) ≤ 2)
    (hP : P ∈ N.primeFactors) (hPq : P ≠ q) (hmax : ∀ p ∈ N.primeFactors, p ≤ P)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ P →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization P ≤ 8 := by
  have hbig := largest_gt_200000' h hmax
  have hb := factorization_largest_le_sum_primeSenderCap_of_gcd h hq hg hP hPq hmax {2, 4}
    (by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;>
        exact ⟨by norm_num, by norm_num, not_dvd_small' hbig (by norm_num) (by norm_num)⟩)
    (fun p hp hpq hpP => by simpa using hexp p hp hpq hpP)
  have hc : ∑ e ∈ ({2, 4} : Finset ℕ), primeSenderCap (e + 1) = 8 := by decide
  omega

/-- Largest prime and indices. Let `P` be a prime factor of an odd perfect number `N` that is
at least every prime factor of `N`, and `u` a prime factor of `N`. Then `P ∤ e_u + 1`.
Restricted result; novelty not verified. -/
theorem largest_not_dvd_succ_factorization {N P u : ℕ} (h : OddPerfect N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ p ∈ N.primeFactors, p ≤ P) (hu : u ∈ N.primeFactors) :
    ¬ P ∣ N.factorization u + 1 := by
  intro hd
  have hPo := Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hP))
  have hP2 := (Nat.prime_of_mem_primeFactors hP).two_le
  obtain ⟨r, hr, -, hrP⟩ := exists_primeFactor_modEq_one h hu (by omega) hd
  have hr1 := (Nat.prime_of_mem_primeFactors hr).one_lt
  have hrle := hmax r hr
  have : r % P = r := Nat.mod_eq_of_lt (lt_of_le_of_ne hrle fun he => by
    rw [he, Nat.mod_self] at hrP
    omega)
  omega

end OddPerfect

#print axioms OddPerfect.not_dvd_sigma_prime_pow_of_gcd
#print axioms OddPerfect.factorization_largest_le_sum_primeSenderCap_of_gcd
#print axioms OddPerfect.factorization_largest_le_eighteen_of_gcd
#print axioms OddPerfect.factorization_largest_le_twelve_of_gcd
#print axioms OddPerfect.factorization_largest_le_eight_of_primeSenderCap_of_gcd
#print axioms OddPerfect.largest_not_dvd_succ_factorization
