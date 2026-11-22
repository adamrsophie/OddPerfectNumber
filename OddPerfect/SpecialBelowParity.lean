import OddPerfect.SpecialBelow
import OddPerfect.SquareRow

/-!
# Parity of the number of prime factors when the special prime is not below `m`

Let `N = q ^ k * m ^ 2` be an odd perfect number with special prime `q` and `q ∤ m`. The landed
`special_lt_or_index_prime_pow` proves `q < m` outside one shape:
`N = q * p ^ e * t ^ 2` with `σ(p ^ e) = q`, `q + 1 = 2 t ^ 2` and `σ(t ^ 2) = p ^ e`.
This module shows that in that shape the number of distinct prime factors of `N` is even.

The argument: `σ(t ^ 2)` is the product of the components `σ(r ^ (2 c_r))` over the primes
`r ∣ t`; each divides `p ^ e`, so it is `p ^ (w_r)`, and the `w_r` add up to `e`, which is even.
An even `w_r` makes `σ(r ^ (2 c_r))` a square, so `r = 3`, `2 c_r = 4` and `p ^ (w_r) = 121`,
`p = 11` (`isSquare_sigma_prime_pow_iff`); then `3 ∣ t` gives `q ≡ 2 (mod 3)` while
`q = σ(11 ^ e) ≡ 1 (mod 3)`. So every `w_r` is odd, `t` has an even number of prime factors,
and `N` has two more.

Literature: P. A. Brown (arXiv 1602.01591, 2016) claims `q < m` for every odd perfect number.
For `k = 1` his proof asserts, citing only that `m` has at least eight prime factors, that some
component `σ(r ^ (2 β))` with `r ≠ p` has a prime factor other than `p`; that assertion is
exactly the negation of the shape above; we found no proof of it in that paper. P. Starni
(Notes on Number Theory and Discrete Mathematics 24 (2018), 5 to 9) states `m ^ 2 > π ^ 9 / 2`;
as we read it, Corollary 2.2 derives `m ^ 2 > (3 / 2) π ^ (ω(N) - 1)` from a disjunction that
only gives `m ^ 2 > (3 / 2) π ^ k` when `σ(m ^ 2) ≠ q ^ k`, which again leaves the shape above
open. These remarks record our reading of the two papers and are not kernel checked.

This module does not prove `q < m`: the parity of the number of prime factors of an odd
perfect number is not known.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If `σ(n) = p ^ e` for a prime `p`, and every component `σ(r ^ v_r(n))` (necessarily a power
of `p`) is an odd power of `p`, then `e` and the number of distinct prime factors of `n` have
the same parity. -/
theorem mod_two_eq_card_primeFactors_of_sigma_eq_prime_pow {n p e : ℕ} (hp : p.Prime)
    (hn : n ≠ 0) (hσ : σ 1 n = p ^ e)
    (hodd : ∀ r ∈ n.primeFactors, ∀ w, σ 1 (r ^ n.factorization r) = p ^ w → Odd w) :
    e % 2 = n.primeFactors.card % 2 := by
  have hfac : σ 1 n = ∏ r ∈ n.primeFactors, σ 1 (r ^ n.factorization r) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
  have hdiv : ∀ r ∈ n.primeFactors, ∃ w, σ 1 (r ^ n.factorization r) = p ^ w := by
    intro r hr
    have hd : σ 1 (r ^ n.factorization r) ∣ p ^ e := by
      rw [← hσ, hfac]
      exact Finset.dvd_prod_of_mem _ hr
    obtain ⟨w, -, hw⟩ := (Nat.dvd_prime_pow hp).1 hd
    exact ⟨w, hw⟩
  choose! w hw using hdiv
  have hsum : e = ∑ r ∈ n.primeFactors, w r := by
    apply Nat.pow_right_injective hp.two_le
    show p ^ e = p ^ _
    rw [← Finset.prod_pow_eq_pow_sum, ← hσ, hfac]
    exact Finset.prod_congr rfl fun r hr => hw r hr
  rw [hsum, Finset.sum_nat_mod, Finset.card_eq_sum_ones, Finset.sum_nat_mod]
  congr 1
  exact Finset.sum_congr rfl fun r hr => by rw [Nat.odd_iff.1 (hodd r hr (w r) (hw r hr))]

/-- `σ(11 ^ (2 j)) ≡ 1 (mod 3)`. -/
theorem sigma_eleven_pow_two_mul_mod_three (j : ℕ) : σ 1 (11 ^ (2 * j)) % 3 = 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num)]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have h : 11 ^ (2 * j + 1) + 11 ^ (2 * j + 1 + 1) = 11 ^ (2 * j) * 44 * 3 := by ring
    rw [add_assoc, h, Nat.add_mul_mod_self_right]
    exact ih

/-- **Parity on the open branch.** If the special prime `q` of an odd perfect number
`N = q ^ k * m ^ 2` (with `q ∤ m`) is not below `m`, then `N` has an even number of distinct
prime factors. -/
theorem even_card_primeFactors_of_special_ge {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hge : m ≤ q) :
    Even N.primeFactors.card := by
  rcases special_lt_or_index_prime_pow h hq hN hqm with hlt | ⟨rfl, p, hp, hpm, hI, hσ, -⟩
  · omega
  obtain ⟨e, he⟩ : ∃ e, e = N.factorization p := ⟨_, rfl⟩
  rw [← he] at hI hσ
  have hN1 : N = q * m ^ 2 := by rw [hN, pow_one]
  have hmN : m ∣ N := hN1 ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have he0 : 0 < e := he ▸ hp.factorization_pos_of_dvd h.ne_zero (hpm.trans hmN)
  obtain ⟨t, hmt, hpt, htodd, ht1, hqt, -, hqt2, hσt, -, heven, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN1 hqm hp he0 hI
  have ht0 : t ≠ 0 := by omega
  have key : e % 2 = (t ^ 2).primeFactors.card % 2 := by
    refine mod_two_eq_card_primeFactors_of_sigma_eq_prime_pow hp (pow_ne_zero _ ht0) hσt ?_
    intro r hr w hw
    rw [Nat.primeFactors_pow t two_ne_zero] at hr
    have hr' := Nat.prime_of_mem_primeFactors hr
    have hrt := Nat.dvd_of_mem_primeFactors hr
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 htodd) (even_iff_two_dvd.2 hrt)
    rw [Nat.factorization_pow] at hw
    simp only [Finsupp.smul_apply, smul_eq_mul] at hw
    rcases Nat.even_or_odd w with ⟨j, rfl⟩ | hw'
    · exfalso
      have hsq : IsSquare (σ 1 (r ^ (2 * t.factorization r))) := ⟨p ^ j, by rw [hw, pow_add]⟩
      have hc0 : t.factorization r ≠ 0 := (hr'.factorization_pos_of_dvd ht0 hrt).ne'
      obtain ⟨rfl, h4⟩ :=
        (isSquare_sigma_prime_pow_iff hr' hr2 (even_two_mul _) (by omega)).1 hsq
      rw [h4] at hw
      have h121 : σ 1 (3 ^ 4) = 121 := by
        rw [sigma_one_apply_prime_pow (by norm_num)]
        norm_num [Finset.sum_range_succ]
      rw [h121] at hw
      have hp11 : p = 11 := by
        have hj : j + j ≠ 0 := by
          intro hj
          rw [hj, pow_zero] at hw
          omega
        have hd : p ∣ 11 ^ 2 := by
          rw [show (11 : ℕ) ^ 2 = 121 by norm_num, hw]
          exact dvd_pow_self p hj
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow hd)
      subst hp11
      obtain ⟨i, hi⟩ := heven
      have h1 := sigma_eleven_pow_two_mul_mod_three i
      rw [show 2 * i = e by omega, hσ] at h1
      have h3 : 3 ∣ t ^ 2 := dvd_pow hrt two_ne_zero
      omega
    · exact hw'
  rw [Nat.primeFactors_pow t two_ne_zero] at key
  have hNf : N.primeFactors = insert q (insert p t.primeFactors) := by
    rw [hN1, hmt, Nat.primeFactors_mul hq.ne_zero
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ ht0)),
      Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ ht0), hq.primeFactors,
      Nat.primeFactors_prime_pow he0.ne' hp, Nat.primeFactors_pow t two_ne_zero,
      Finset.insert_eq, Finset.insert_eq]
  have hqp : q ≠ p := by
    rintro rfl
    exact hqm hpm
  have hpt' : p ∉ t.primeFactors := fun hh => hpt (Nat.dvd_of_mem_primeFactors hh)
  have hqt' : q ∉ insert p t.primeFactors := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hqp, fun hh => hqt (Nat.dvd_of_mem_primeFactors hh)⟩
  rw [hNf, Finset.card_insert_of_notMem hqt', Finset.card_insert_of_notMem hpt']
  rw [Nat.even_iff] at heven ⊢
  omega

/-- If an odd perfect number `N = q ^ k * m ^ 2` (special prime `q`, `q ∤ m`) has an odd number
of distinct prime factors, then `q < m`. This does not prove `q < m` in general: the parity of
the number of prime factors of an odd perfect number is not known. -/
theorem special_lt_of_odd_card_primeFactors {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hodd : Odd N.primeFactors.card) : q < m := by
  by_contra hc
  exact (Nat.not_even_iff_odd.2 hodd)
    (even_card_primeFactors_of_special_ge h hq hN hqm (by omega))

end OddPerfect

#print axioms OddPerfect.mod_two_eq_card_primeFactors_of_sigma_eq_prime_pow
#print axioms OddPerfect.sigma_eleven_pow_two_mul_mod_three
#print axioms OddPerfect.even_card_primeFactors_of_special_ge
#print axioms OddPerfect.special_lt_of_odd_card_primeFactors
