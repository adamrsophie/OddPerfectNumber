import OddPerfect.SpecialRankFamily
import OddPerfect.PrimeCapSpecial

/-!
# The palette of exponents 2 and 4 with the capacity for prime senders

Restricted family results; no novelty is claimed, and whether they are in the literature was
not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, and
let every other prime factor have exponent `2` or `4`.

* `sum_sigmaWeight_below_special_le_eight`: the rows of the prime factors below `q` carry at
  most `8` at `q`. The senders are distinct primes below `q`, so the prime sender totals `2`
  (index `3`) and `6` (index `5`) of `OddPerfect.PrimeCap` apply in place of the totals `2` and
  `7` used by `sum_sigmaWeight_below_special_le_nine`.
* `special_exponent_le_41`: if moreover `q` is the second largest prime factor, then `a ≤ 41`,
  and `special_exponent_le_37_of_not_three_dvd`: `a ≤ 37` under the explicit hypothesis `3 ∤ N`.
* `not_dvd_geom_sum_of_not_dvd_sub_one`: for primes `q ≠ l` with `l ∤ q - 1`, no integer `u`
  has `q ∣ 1 + u + ⋯ + u ^ (l - 1)`. Indeed `u ^ l ≡ 1` and `u ^ (q - 1) ≡ 1 (mod q)` force
  `u ≡ 1`, and then the sum is `l (mod q)`.
* For `q` the largest prime factor: `special_exponent_le_of_mod`:
  `a ≤ [q % 3 = 1] 2 + [q % 5 = 1] 6`. Hence `special_mod_five_of_eq_five`: `a = 5` forces
  `q % 5 = 1` (refining `special_exponent_eq_one_or_five`), and
  `special_mod_three_or_mod_five`: `q % 3 = 1 ∨ q % 5 = 1`.

Remark on sharpness. The capacity bound of `OddPerfect.LargestPrimeCapGen` counts integer
senders, not only primes. The integers `3` and `9` are below `11`, and `11 ^ 2` divides both
`1 + 3 + 3 ^ 2 + 3 ^ 3 + 3 ^ 4 = 121` and `1 + 9 + 9 ^ 2 + 9 ^ 3 + 9 ^ 4 = 7381 = 121 * 61`
(the two examples below). So two integer senders can share level two at index `5`, which the
integer bound must allow; the improved bound uses that the senders are primes (here `9` is not).
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

example : 11 ^ 2 ∣ ∑ i ∈ Finset.range 5, 3 ^ i := by decide
example : 11 ^ 2 ∣ ∑ i ∈ Finset.range 5, 9 ^ i := by decide

/-! ## Capacity 8 at the special prime -/

private theorem sigmaWeight_eq_geom {N p q : ℕ} (hp : p.Prime) :
    sigmaWeight N p q =
      (∑ i ∈ Finset.range (N.factorization p + 1), p ^ i).factorization q := by
  unfold sigmaWeight
  rw [sigma_one_apply_prime_pow hp]

/-- Palette capacity at the special prime, for prime senders. Let `N` be an odd perfect number
with special prime `q` such that every other prime factor has exponent `2` or `4`. Then the rows
of the prime factors below `q` carry at most `8` at `q`. Restricted family result. -/
theorem sum_sigmaWeight_below_special_le_eight {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 8 := by
  classical
  set U := N.primeFactors.filter (· < q) with hU
  have hUp : ∀ s : Finset ℕ, s ⊆ U → ∀ u ∈ s, u.Prime ∧ u < q := fun s hs u hu =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hs hu)).1,
      (Finset.mem_filter.mp (hs hu)).2⟩
  by_cases hsmall : q = 3 ∨ q = 5
  · -- only the prime `3` lies below `q`, and its rows `13` and `121` are prime to `5`
    have hz : ∀ p ∈ U, sigmaWeight N p q = 0 := by
      intro p hp
      obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp')
      have hp3 : p = 3 ∧ q = 5 := by
        have := hpp.two_le
        rcases hsmall with rfl | rfl
        · omega
        · interval_cases p
          · exact absurd rfl hp2
          · exact ⟨rfl, rfl⟩
          · exact absurd hpp (by norm_num)
      obtain ⟨rfl, rfl⟩ := hp3
      rw [sigmaWeight_eq_geom hpp]
      rcases hexp 3 hp' (by norm_num) with hf | hf <;> rw [hf] <;>
        exact Nat.factorization_eq_zero_of_not_dvd (by decide)
    rw [Finset.sum_eq_zero hz]
    norm_num
  push Not at hsmall
  have hpt : ∀ p ∈ U, sigmaWeight N p q ≤
      (if N.factorization p = 2 then (∑ i ∈ Finset.range 3, p ^ i).factorization q else 0) +
      (if N.factorization p = 4 then (∑ i ∈ Finset.range 5, p ^ i).factorization q
        else 0) := by
    intro p hp
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    rw [sigmaWeight_eq_geom hpp]
    rcases hexp p hp' (by omega) with hf | hf
    · rw [if_pos hf, if_neg (by omega), add_zero, hf]
    · rw [if_neg (by omega), if_pos hf, zero_add, hf]
  have hle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hle
  have h2 := sum_factorization_geom_sum_three_le_two_of_primes hq hsmall.1
    (U.filter (fun p => N.factorization p = 2)) (hUp _ (Finset.filter_subset _ _))
  have h4 := sum_factorization_geom_sum_five_le_six_of_primes hq hsmall.2
    (U.filter (fun p => N.factorization p = 4)) (hUp _ (Finset.filter_subset _ _))
  omega

/-- Palette bound with prime senders. Let `N` be an odd perfect number with special prime `q`,
let every other prime factor have exponent `2` or `4`, and let `q` be the second largest prime
factor (some prime factor `P > q`, every prime factor other than `P` at most `q`). Then
`v_q(N) ≤ 41`. Restricted family result; novelty not verified. -/
theorem special_exponent_le_41 {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 41 :=
  special_exponent_le_41_of_le_eight h hq hodd hP hqP hsecond hexp
    (sum_sigmaWeight_below_special_le_eight h hq hexp)

/-- Palette bound with prime senders and without the prime `3`: in the setting of
`special_exponent_le_41`, under the explicit hypothesis `3 ∤ N`, `v_q(N) ≤ 37`. Restricted
family result; novelty not verified. -/
theorem special_exponent_le_37_of_not_three_dvd {N q P : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    N.factorization q ≤ 37 :=
  special_exponent_le_37_of_le_eight_of_not_three_dvd h hq hodd hP hqP hsecond hexp
    (sum_sigmaWeight_below_special_le_eight h hq hexp) h3

/-! ## Residue conditions when the special prime is the largest prime factor -/

/-- Let `q ≠ l` be primes with `l ∤ q - 1`. Then `q ∤ ∑ i < l, u ^ i` for every `u`: from
`u ^ l ≡ 1` and `u ^ (q - 1) ≡ 1 (mod q)` follows `u ≡ 1`, and then the sum is `l (mod q)`. -/
theorem not_dvd_geom_sum_of_not_dvd_sub_one {q l : ℕ} (hq : q.Prime) (hl : l.Prime)
    (hql : q ≠ l) (hdvd : ¬ l ∣ q - 1) (u : ℕ) :
    ¬ q ∣ ∑ i ∈ Finset.range l, u ^ i := by
  have : Fact q.Prime := ⟨hq⟩
  intro hd
  have hS : ∑ i ∈ Finset.range l, (u : ZMod q) ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ q).mpr hd
    push_cast at this
    exact this
  have hpow : (u : ZMod q) ^ l = 1 := by
    have := geom_sum_mul (u : ZMod q) l
    rw [hS, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  have hu0 : (u : ZMod q) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hl.ne_zero] at hpow
    exact zero_ne_one hpow
  have hferm := ZMod.pow_card_sub_one_eq_one hu0
  have hcop : Nat.Coprime l (q - 1) := (Nat.Prime.coprime_iff_not_dvd hl).mpr hdvd
  have hu1 : (u : ZMod q) = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hpow, hferm⟩
  rw [hu1] at hS
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hS
  have hql' : q ∣ l := (ZMod.natCast_eq_zero_iff _ _).mp hS
  exact hql ((Nat.prime_dvd_prime_iff_eq hq hl).mp hql')

/-- Let `N` be an odd perfect number with special prime `q` (odd exponent), where `q` is the
largest prime factor and every other prime factor has exponent `2` or `4`. Then
`v_q(N) ≤ (if q % 3 = 1 then 2 else 0) + (if q % 5 = 1 then 6 else 0)`: the rows of exponent
`2` give nothing at `q` unless `q % 3 = 1`, and those of exponent `4` nothing unless
`q % 5 = 1`. Restricted family result; novelty not verified. -/
theorem special_exponent_le_of_mod {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmax : ∀ p ∈ N.primeFactors, p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ (if q % 3 = 1 then 2 else 0) + (if q % 5 = 1 then 6 else 0) := by
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨k, hk⟩ := hodd; omega)
  have hbig : 200000 < q := by
    obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
    exact lt_of_lt_of_le hlt (hmax p hp)
  set c : ℕ → ℕ := fun e =>
    if e = 2 then (if q % 3 = 1 then 2 else 0) else (if q % 5 = 1 then 6 else 0) with hcdef
  have hb := factorization_le_sum_of_cap h hqm hmax {2, 4} c
    (by
      intro e he U hU
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · simp only [hcdef, if_pos rfl]
        split_ifs with h3
        · exact sum_factorization_geom_sum_three_le_two_of_primes hq (by omega) U hU
        · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
          exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_three (by omega)
            (by omega) u
      · simp only [hcdef, if_neg (show (4 : ℕ) ≠ 2 by norm_num)]
        split_ifs with h5
        · exact sum_factorization_geom_sum_five_le_six_of_primes hq (by omega) U hU
        · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
          exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_five (by omega)
            (by omega) u)
    (fun p hp hpq => Or.inr (by simpa using hexp p hp hpq))
  have hc : ∑ e ∈ ({2, 4} : Finset ℕ), c e = c 2 + c 4 := by
    rw [Finset.sum_pair (by norm_num)]
  rw [hc] at hb
  simpa [hcdef] using hb

/-- Refinement of `special_exponent_eq_one_or_five`. In its setting (`q` the largest prime
factor, every other exponent `2` or `4`), `v_q(N) = 5` forces `q % 5 = 1`. Restricted family
result; novelty not verified. -/
theorem special_mod_five_of_eq_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmax : ∀ p ∈ N.primeFactors, p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q = 5 → q % 5 = 1 := by
  intro h5
  have hb := special_exponent_le_of_mod h hq hodd hmax hexp
  by_contra hne
  rw [if_neg hne, h5] at hb
  split_ifs at hb <;> omega

/-- In the setting of `special_exponent_eq_one_or_five` (`q` the largest prime factor, every
other exponent `2` or `4`), `q % 3 = 1 ∨ q % 5 = 1`: otherwise no row gives anything at `q` and
the odd exponent `v_q(N)` would be `0`. Restricted family result; novelty not verified. -/
theorem special_mod_three_or_mod_five {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hmax : ∀ p ∈ N.primeFactors, p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    q % 3 = 1 ∨ q % 5 = 1 := by
  have hb := special_exponent_le_of_mod h hq hodd hmax hexp
  by_contra hne
  push Not at hne
  rw [if_neg hne.1, if_neg hne.2] at hb
  obtain ⟨k, hk⟩ := hodd
  omega

end OddPerfect

#print axioms OddPerfect.sum_sigmaWeight_below_special_le_eight
#print axioms OddPerfect.special_exponent_le_41
#print axioms OddPerfect.special_exponent_le_37_of_not_three_dvd
#print axioms OddPerfect.not_dvd_geom_sum_of_not_dvd_sub_one
#print axioms OddPerfect.special_exponent_le_of_mod
#print axioms OddPerfect.special_mod_five_of_eq_five
#print axioms OddPerfect.special_mod_three_or_mod_five
