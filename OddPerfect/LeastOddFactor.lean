import OddPerfect.Valuation
import OddPerfect.SpecialPrime

/-!
# Least odd factors and total excess

A prime dividing the divisor sum of an even prime power constrains the odd factors of
its exponent plus one. This gives a lower bound on the total excess of an odd perfect number.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- If a prime `q` divides the divisor sum of an even power `r ^ e` of another prime, then
`e + 1` has an odd prime factor that divides `q - 1` or equals `q`. -/
theorem exists_odd_prime_dvd_succ_of_dvd_sigma {q r e : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hrq : r ≠ q) (he : Even e) (h : q ∣ σ 1 (r ^ e)) :
    ∃ d, d.Prime ∧ d ≠ 2 ∧ d ∣ e + 1 ∧ (d ∣ q - 1 ∨ d = q) := by
  have hnot : ¬ 2 ∣ e + 1 := he.add_one.not_two_dvd_nat
  have hdiv := (dvd_sigma_prime_pow_iff hr hq hrq).mp h
  by_cases ho : orderOf (r : ZMod q) = 1
  · rw [if_pos ho] at hdiv
    exact ⟨q, hq, fun hq2 => hnot (hq2 ▸ hdiv), hdiv, Or.inr rfl⟩
  · rw [if_neg ho] at hdiv
    have : Fact q.Prime := ⟨hq⟩
    have hr0 : (r : ZMod q) ≠ 0 := by
      intro hz
      have hd : q ∣ r := (ZMod.natCast_eq_zero_iff r q).mp hz
      exact hrq ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd).symm
    obtain ⟨d, hd, hdo⟩ := Nat.exists_prime_and_dvd ho
    have hde : d ∣ e + 1 := hdo.trans hdiv
    exact ⟨d, hd, fun hd2 => hnot (hd2 ▸ hde), hde,
      Or.inl (hdo.trans (ZMod.orderOf_dvd_card_sub_one hr0))⟩

/-- Let `L` be a lower bound for the special prime `q` of an odd perfect number and for every
odd prime factor of `q - 1`. Then `(L - 3) / 2` is at most the total excess. -/
theorem least_odd_factor_le_excess {N q L : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hL : ∀ d, d.Prime → d ≠ 2 → d ∣ q - 1 → L ≤ d)
    (hLq : L ≤ q) :
    (L - 3) / 2 ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  have ha : N.factorization q ≠ 0 := hodd.pos.ne'
  have hqN : q ∣ N :=
    (hq.dvd_iff_one_le_factorization h.ne_zero).mpr (Nat.one_le_iff_ne_zero.mpr ha)
  have hq2 : q ≠ 2 := fun hq2 => h.not_two_dvd (hq2 ▸ hqN)
  rw [factorization_eq_sum_erase h.perfect hq hq2] at ha
  obtain ⟨r, hr, hval⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hrq, hrN⟩ := Finset.mem_erase.mp hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrN
  have hdiv : q ∣ σ 1 (r ^ N.factorization r) := by
    by_contra hn
    exact hval (by rw [Nat.padicValNat_def]; exact padicValNat.eq_zero_of_not_dvd hn)
  have he := even_factorization_of_ne h hq hodd hrp hrq
  obtain ⟨d, hd, hd2, hde, hcase⟩ := exists_odd_prime_dvd_succ_of_dvd_sigma hq hrp hrq he hdiv
  have hLd : L ≤ d := by
    rcases hcase with hdq | rfl
    · exact hL d hd hd2 hdq
    · exact hLq
  have hLe : L ≤ N.factorization r + 1 := hLd.trans (Nat.le_of_dvd (by omega) hde)
  calc
    (L - 3) / 2 ≤ N.factorization r / 2 - 1 := by omega
    _ ≤ ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) :=
      Finset.single_le_sum (f := fun p => N.factorization p / 2 - 1) (fun _ _ => Nat.zero_le _) hr

end OddPerfect

#print axioms OddPerfect.exists_odd_prime_dvd_succ_of_dvd_sigma
#print axioms OddPerfect.least_odd_factor_le_excess
