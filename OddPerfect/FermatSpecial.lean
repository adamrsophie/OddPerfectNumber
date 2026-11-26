import OddPerfect.Valuation
import OddPerfect.ValuationBounds

/-!
# Excess bounds for Fermat special primes

For a Fermat prime, the valuation of an even prime power's divisor sum is bounded by
the valuation of the exponent plus one. Summing these bounds in the valuation ledger
gives a lower bound on the total excess when the special prime is a Fermat prime at least 5.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Let `f` be a prime with `f - 1` a power of 2, `p` a prime other than `f`, and `e` even.
The `f`-adic valuation of the divisor sum of `p ^ e` is at most that of `e + 1`. -/
theorem padicValNat_sigma_prime_pow_le_of_fermat {f p e k : ℕ} (hf : f.Prime)
    (hfk : f = 2 ^ k + 1) (hp : p.Prime) (hpf : p ≠ f) (he : Even e) :
    padicValNat f (σ 1 (p ^ e)) ≤ padicValNat f (e + 1) := by
  rcases eq_or_ne f 2 with rfl | hf2
  · rw [padicValNat_two_sigma_prime_pow hp hpf e, if_pos he]
    exact Nat.zero_le _
  by_cases hd : f ∣ σ 1 (p ^ e)
  · have hfk' : f - 1 = 2 ^ k := by rw [hfk, Nat.add_sub_cancel]
    have hm := mod_eq_one_of_dvd_sigma_of_even hp hf hfk' he hd
    have hpred : f ∣ p - 1 := by
      apply (Nat.modEq_iff_dvd' hp.one_lt.le).mp
      rw [Nat.ModEq, hm, Nat.mod_eq_of_lt hf.one_lt]
    exact (padicValNat_sigma_prime_pow_of_dvd_pred hp hf hf2 hpred).le
  · rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- If the special prime `q` of an odd perfect number is a Fermat prime (at least 5), then
`(q - 3) / 2` times its exponent is at most the total excess. -/
theorem fermat_special_mul_le_excess {N q k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hqk : q = 2 ^ k + 1) (hq5 : 5 ≤ q) :
    (q - 3) / 2 * N.factorization q ≤
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  let c := (q - 3) / 2
  change c * N.factorization q ≤ _
  have hq2 : q ≠ 2 := by omega
  have hc : 1 + (2 * c + 2) ≤ q := by
    dsimp [c]
    omega
  have hcost (e : ℕ) : c * padicValNat q (e + 1) ≤ e / 2 - 1 := by
    let m := padicValNat q (e + 1)
    change c * m ≤ e / 2 - 1
    by_cases hm : m = 0
    · rw [hm, mul_zero]
      exact Nat.zero_le _
    have hm1 : 1 ≤ m := by omega
    have hpow : q ^ m ≤ e + 1 :=
      Nat.le_of_dvd e.succ_pos (show q ^ padicValNat q (e + 1) ∣ e + 1 by
        rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
    have hbernoulli : 1 + m * (2 * c + 2) ≤ q ^ m :=
      calc
        _ ≤ (1 + (2 * c + 2)) ^ m :=
          one_add_le_pow_of_two_add_nonneg (a := 2 * c + 2) (Nat.zero_le _) m
        _ ≤ q ^ m := Nat.pow_le_pow_left hc m
    have hmul : m * (2 * c + 2) = 2 * (c * m) + 2 * m := by ring
    rw [hmul] at hbernoulli
    omega
  rw [factorization_eq_sum_erase h.perfect hq hq2, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro p hp
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have he := even_factorization_of_ne h hq hodd hpp hpq
  exact (Nat.mul_le_mul_left c
    (padicValNat_sigma_prime_pow_le_of_fermat hq hqk hpp hpq he)).trans (hcost _)

/-- With special prime 5, the special exponent is at most the total excess. -/
theorem special_five_exponent_le_excess {N : ℕ} (h : OddPerfect N)
    (hodd : Odd (N.factorization 5)) :
    N.factorization 5 ≤ ∑ p ∈ N.primeFactors.erase 5, (N.factorization p / 2 - 1) := by
  simpa only [show (5 - 3 : ℕ) / 2 = 1 by decide, one_mul] using
    fermat_special_mul_le_excess (k := 2) h Nat.prime_five hodd rfl (Nat.le_refl 5)

end OddPerfect

#print axioms OddPerfect.padicValNat_sigma_prime_pow_le_of_fermat
#print axioms OddPerfect.fermat_special_mul_le_excess
#print axioms OddPerfect.special_five_exponent_le_excess
