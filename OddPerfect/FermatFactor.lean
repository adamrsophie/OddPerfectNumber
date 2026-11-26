import OddPerfect.FermatSpecial

/-!
# Excess bounds for Fermat prime factors

A Fermat prime cannot divide the special prime's divisor sum under the stated residue exclusions.
The other prime powers bound its exponent through the valuation ledger, yielding a lower bound
on the total excess when the Fermat prime divides the odd perfect number.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Let `F = 2 ^ k + 1` be a prime, `q` a prime that is neither `1` nor `-1` modulo `F`, and
`a ≡ 1 (mod 4)`. Then `F` does not divide the divisor sum of `q ^ a`. -/
theorem not_fermat_dvd_sigma_special {F q a k : ℕ} (hF : F.Prime) (hFk : F = 2 ^ k + 1)
    (hq : q.Prime) (h1 : q % F ≠ 1) (h2 : q % F ≠ F - 1) (ha : a % 4 = 1) :
    ¬ F ∣ σ 1 (q ^ a) := by
  intro hdvd
  have : Fact F.Prime := ⟨hF⟩
  rcases (prime_dvd_sigma_prime_pow hq hF hdvd).2 with ⟨hm, -⟩ | ⟨ho, hd, hpow⟩
  · exact h1 hm
  have hpred : F - 1 = 2 ^ k := by rw [hFk, Nat.add_sub_cancel]
  rw [hpred] at hpow
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
  have hi0 : i ≠ 0 := by
    intro hz
    rw [hi, hz, pow_zero] at ho
    exact lt_irrefl _ ho
  have hi2 : i < 2 := by
    by_contra! hge
    have hfour : (2 : ℕ) ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 hge
    rw [hi] at hd
    have hbad : 4 ∣ a + 1 := hfour.trans hd
    omega
  have hi1 : i = 1 := by omega
  have horder : orderOf (q : ZMod F) = 2 := by rw [hi, hi1, pow_one]
  have hsq : (q : ZMod F) ^ 2 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one (q : ZMod F)
  rcases sq_eq_one_iff.mp hsq with hone | hneg
  · apply h1
    have hmod := (ZMod.natCast_eq_natCast_iff' q 1 F).mp
      (by simpa only [Nat.cast_one] using hone)
    rwa [Nat.mod_eq_of_lt hF.one_lt] at hmod
  · apply h2
    have hcast : ((F - 1 : ℕ) : ZMod F) = -1 := by
      rw [Nat.cast_sub hF.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    have hmod := (ZMod.natCast_eq_natCast_iff' q (F - 1) F).mp (hneg.trans hcast.symm)
    have hlt : F - 1 < F := by have := hF.pos; omega
    rwa [Nat.mod_eq_of_lt hlt] at hmod

/-- For `F ≥ 5`, the valuation of `e + 1` times `(F - 3) / 2` is bounded by the excess of `e`. -/
private theorem fermat_factor_cost {F : ℕ} (hF5 : 5 ≤ F) (e : ℕ) :
    (F - 3) / 2 * padicValNat F (e + 1) ≤ e / 2 - 1 := by
  let c := (F - 3) / 2
  let m := padicValNat F (e + 1)
  change c * m ≤ e / 2 - 1
  by_cases hm : m = 0
  · rw [hm, mul_zero]
    exact Nat.zero_le _
  have hm1 : 1 ≤ m := by omega
  have hc : 1 + (2 * c + 2) ≤ F := by
    dsimp [c]
    omega
  have hpow : F ^ m ≤ e + 1 :=
    Nat.le_of_dvd e.succ_pos
      (show F ^ padicValNat F (e + 1) ∣ e + 1 by
        rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
  have hbernoulli : 1 + m * (2 * c + 2) ≤ F ^ m :=
    calc
      _ ≤ (1 + (2 * c + 2)) ^ m :=
        one_add_le_pow_of_two_add_nonneg (a := 2 * c + 2) (Nat.zero_le _) m
      _ ≤ F ^ m := Nat.pow_le_pow_left hc m
  have hmul : m * (2 * c + 2) = 2 * (c * m) + 2 * m := by ring
  rw [hmul] at hbernoulli
  omega

/-- A Fermat prime `F ≥ 5` other than the special prime `q`, with `q` not `±1` modulo `F`:
`(F - 3) / 2` times the exponent of `F` is at most the excess of the remaining primes. -/
theorem fermat_factor_mul_le_excess {N q F k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hF : F.Prime) (hFk : F = 2 ^ k + 1) (hF5 : 5 ≤ F)
    (hFq : F ≠ q) (h1 : q % F ≠ 1) (h2 : q % F ≠ F - 1) :
    (F - 3) / 2 * N.factorization F ≤
      ∑ p ∈ (N.primeFactors.erase q).erase F, (N.factorization p / 2 - 1) := by
  let v (p : ℕ) := padicValNat F (σ 1 (p ^ N.factorization p))
  have hqa := (special_mod_four h hq hodd).2
  have hqmem : q ∈ N.primeFactors.erase F := by
    refine Finset.mem_erase.mpr ⟨hFq.symm, ?_⟩
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    omega
  have hvq : v q = 0 := by
    simp only [v, Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (not_fermat_dvd_sigma_special hF hFk hq h1 h2 hqa)
  have hledger : N.factorization F = ∑ p ∈ (N.primeFactors.erase q).erase F, v p :=
    calc
      _ = ∑ p ∈ N.primeFactors.erase F, v p :=
        factorization_eq_sum_erase h.perfect hF (by omega)
      _ = ∑ p ∈ (N.primeFactors.erase F).erase q, v p := by
        rw [← Finset.add_sum_erase _ v hqmem, hvq, zero_add]
      _ = _ := by rw [Finset.erase_right_comm]
  rw [hledger, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro p hp
  obtain ⟨hpF, hpq'⟩ := Finset.mem_erase.mp hp
  obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hpq'
  have hpp := Nat.prime_of_mem_primeFactors hpN
  have he := even_factorization_of_ne h hq hodd hpp hpq
  exact (Nat.mul_le_mul_left ((F - 3) / 2)
    (padicValNat_sigma_prime_pow_le_of_fermat hF hFk hpp hpF he)).trans (fermat_factor_cost hF5 _)

/-- The same with `F ∣ N`: the total excess is at least `(F - 2) * t + (F - 3)`, where `t` is
the excess of `F`. -/
theorem fermat_factor_excess_le {N q F k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hF : F.Prime) (hFk : F = 2 ^ k + 1) (hF5 : 5 ≤ F)
    (hFq : F ≠ q) (h1 : q % F ≠ 1) (h2 : q % F ≠ F - 1) (hFN : F ∣ N) :
    (F - 2) * (N.factorization F / 2 - 1) + (F - 3) ≤
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
  have hFmem : F ∈ N.primeFactors.erase q :=
    Finset.mem_erase.mpr ⟨hFq, Nat.mem_primeFactors.mpr ⟨hF, hFN, h.ne_zero⟩⟩
  let t := N.factorization F / 2 - 1
  let c := (F - 3) / 2
  have hpos := hF.factorization_pos_of_dvd h.ne_zero hFN
  have he : N.factorization F = 2 * (t + 1) := by
    obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd hF hFq
    dsimp [t]
    omega
  have hc : 2 * c = F - 3 := by
    obtain ⟨j, hj⟩ := hF.odd_of_ne_two (by omega)
    dsimp [c]
    omega
  have hmul : c * N.factorization F = (F - 3) * (t + 1) := by
    calc
      _ = (2 * c) * (t + 1) := by rw [he]; ring
      _ = _ := by rw [hc]
  have hbound := fermat_factor_mul_le_excess h hq hodd hF hFk hF5 hFq h1 h2
  change c * N.factorization F ≤ _ at hbound
  rw [hmul] at hbound
  have hsucc : F - 2 = (F - 3) + 1 := by omega
  calc
    (F - 2) * t + (F - 3) = t + (F - 3) * (t + 1) := by rw [hsucc]; ring
    _ ≤ t + ∑ p ∈ (N.primeFactors.erase q).erase F, (N.factorization p / 2 - 1) :=
      Nat.add_le_add_left hbound t
    _ = _ := Finset.add_sum_erase _ (fun p => N.factorization p / 2 - 1) hFmem

end OddPerfect

#print axioms OddPerfect.not_fermat_dvd_sigma_special
#print axioms OddPerfect.fermat_factor_mul_le_excess
#print axioms OddPerfect.fermat_factor_excess_le
