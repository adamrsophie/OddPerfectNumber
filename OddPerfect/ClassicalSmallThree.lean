import OddPerfect.McDaniel
import OddPerfect.Valuation
import OddPerfect.SpecialPrime

/-!
# Three small known lemmas on odd perfect numbers

Throughout, `N` is an odd perfect number with special prime `q`. No novelty is claimed.

* `padicValNat_three_sigma_special_of_equal_exponents` (Starni, J. Number Theory 116 (2006),
  Theorem, p. 484): if every ordinary prime has exponent `2 β` and `3 ∣ N`, then
  `v_3(σ(q ^ a)) = 2 β`.
* `prime_dvd_sigma_special_of_succ_succ` (Starni, J. Number Theory 44 (1993), 58 to 59,
  statement (ii)): if the special exponent is `k`, the number `l = k + 2` is prime and
  `q % l ≠ 1`, then `l ∣ σ(q ^ k)` and `l ^ 2 ∣ N`.
* `five_special_exponent_mod_twelve` (Bërdëllima, Elem. Math. 81 (2026), Proposition 2,
  p. 106): if `5` is the special prime, its exponent is `1` or `9` modulo `12`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Starni, J. Number Theory 116 (2006), Theorem, p. 484; no novelty is claimed. Let `N` be an
odd perfect number with special prime `q`, let every other prime factor of `N` have exponent
`2 * β`, and let `3 ∣ N`. Then the special component sends the whole exponent of `3`:
`v_3(σ(q ^ a)) = 2 * β`. The ordinary components send nothing to `3`: a prime `2 (mod 3)` has
even exponent, and a prime `1 (mod 3)` sends `v_3(2 β + 1)`, which is `0` by McDaniel's theorem
(`mcdaniel`). For `2 β + 1` prime the same statement for every ordinary prime in place of `3`
is `padicValNat_sigma_special_eq`. -/
theorem padicValNat_three_sigma_special_of_equal_exponents {N q β : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p = 2 * β) (h3 : 3 ∣ N) :
    padicValNat 3 (σ 1 (q ^ N.factorization q)) = 2 * β := by
  have hq4 := (special_mod_four h hq hodd).1
  have h3q : (3 : ℕ) ≠ q := by rintro rfl; norm_num at hq4
  have h3N : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq,
    Nat.dvd_of_factorization_pos (by obtain ⟨k, hk⟩ := hodd; omega), h.ne_zero⟩
  have hv : padicValNat 3 (2 * β + 1) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    exact mcdaniel h hq hodd fun p hp hpq => by rw [hexp p hp hpq]; omega
  rw [← hexp 3 h3N h3q, factorization_eq_sum_erase h.perfect Nat.prime_three (by norm_num),
    Finset.sum_eq_single q]
  · intro r hr hrq
    obtain ⟨hr3, hrN⟩ := Finset.mem_erase.mp hr
    rw [hexp r hrN hrq, padicValNat_three_sigma_prime_pow (Nat.prime_of_mem_primeFactors hrN),
      threeWeight, if_neg hr3]
    split_ifs with h1 h2
    · exact hv
    · rfl
    · exact absurd (even_two_mul β) h2
  · intro hqn
    exact absurd (Finset.mem_erase.mpr ⟨h3q.symm, hqN⟩) hqn

/-- Starni, J. Number Theory 44 (1993), 58 to 59, statement (ii); no novelty is claimed. Let
`N` be an odd perfect number with special prime `q` of exponent `k`, let `k + 2` be prime and
`q % (k + 2) ≠ 1`. Then `k + 2` divides `σ(q ^ k)`, is a prime factor of `N`, and its square
divides `N`. By Fermat's little theorem `q ^ (k + 1) ≡ 1` modulo `k + 2`, and `k + 2` does not
divide `q - 1`. -/
theorem prime_dvd_sigma_special_of_succ_succ {N q k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hk : N.factorization q = k) (hodd : Odd k) (hl : (k + 2).Prime) (hql : q % (k + 2) ≠ 1) :
    k + 2 ∣ σ 1 (q ^ k) ∧ k + 2 ∈ N.primeFactors ∧ (k + 2) ^ 2 ∣ N := by
  have hodd' : Odd (N.factorization q) := hk ▸ hodd
  obtain ⟨hq4, hk4⟩ := special_mod_four h hq hodd'
  have hlq : k + 2 ≠ q := by intro e; omega
  have := Fact.mk hl
  have hq0 : (q : ZMod (k + 2)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hlq ((Nat.prime_dvd_prime_iff_eq hl hq).mp hd)
  have hferm : (q : ZMod (k + 2)) ^ (k + 1) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one hq0
    rwa [show k + 2 - 1 = k + 1 by omega] at this
  have hq1 : (q : ZMod (k + 2)) - 1 ≠ 0 := by
    intro e
    rw [sub_eq_zero, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (by omega : 1 < k + 2)] at e
    exact hql e
  have hdiv : k + 2 ∣ σ 1 (q ^ k) := by
    rw [← ZMod.natCast_eq_zero_iff, sigma_one_apply_prime_pow hq]
    push_cast
    have hg := geom_sum_mul (q : ZMod (k + 2)) (k + 1)
    rw [hferm, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right hq1
  have hlN : k + 2 ∣ N := OPNStarter.force_prime h.perfect hq hk hl (by omega) hdiv
  have hev := even_factorization_of_ne h hq hodd' hl hlq
  have hpos : 1 ≤ N.factorization (k + 2) :=
    (hl.pow_dvd_iff_le_factorization h.ne_zero).mp (by rwa [pow_one])
  refine ⟨hdiv, Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩,
    (hl.pow_dvd_iff_le_factorization h.ne_zero).mpr ?_⟩
  obtain ⟨j, hj⟩ := hev
  omega

/-- Bërdëllima, Elem. Math. 81 (2026), Proposition 2, p. 106; no novelty is claimed. If `5` has
odd exponent `k` in an odd perfect number `N`, then `k % 12` is `1` or `9`. Here `k ≡ 1 (mod 4)`,
`3 ∣ σ(5 ^ k) ∣ 2 N`, and `k ≡ 5 (mod 12)` would give `7 ∣ σ(5 ^ 5) ∣ σ(5 ^ k)`, so `105 ∣ N`,
which is impossible (`not_105_dvd`). This sharpens the `1` or at least `9` of
`MixedIndexTwo.five_exponent`. -/
theorem five_special_exponent_mod_twelve {N : ℕ} (h : OddPerfect N)
    (h5o : Odd (N.factorization 5)) :
    N.factorization 5 % 12 = 1 ∨ N.factorization 5 % 12 = 9 := by
  have hk4 := (special_mod_four h Nat.prime_five h5o).2
  have hsd : ∀ a, a + 1 ∣ N.factorization 5 + 1 → σ 1 (5 ^ a) ∣ σ 1 (5 ^ N.factorization 5) :=
    fun a ha => OPNExample.sigma_prime_pow_dvd Nat.prime_five ha
  have h3s : 3 ∣ σ 1 (5 ^ N.factorization 5) := by
    refine dvd_trans ?_ (hsd 1 (Nat.dvd_of_mod_eq_zero (by omega)))
    rw [sigma_one_apply_prime_pow Nat.prime_five]
    norm_num [Finset.sum_range_succ]
  have h3d : 3 ∣ N :=
    OPNStarter.force_prime h.perfect Nat.prime_five rfl Nat.prime_three (by norm_num) h3s
  have h5d : 5 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  by_contra hne
  have h7s : 7 ∣ σ 1 (5 ^ N.factorization 5) := by
    refine dvd_trans ?_ (hsd 5 (Nat.dvd_of_mod_eq_zero (by omega)))
    rw [sigma_one_apply_prime_pow Nat.prime_five]
    norm_num [Finset.sum_range_succ]
  exact not_seven_dvd_of_three_five h h3d h5d
    (OPNStarter.force_prime h.perfect Nat.prime_five rfl (by norm_num) (by norm_num) h7s)

end OddPerfect

#print axioms OddPerfect.padicValNat_three_sigma_special_of_equal_exponents
#print axioms OddPerfect.prime_dvd_sigma_special_of_succ_succ
#print axioms OddPerfect.five_special_exponent_mod_twelve
