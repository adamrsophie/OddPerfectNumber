import OddPerfect.LedgerPrimeThree

/-! # Parity of ordinary prime factors with divisor sum three modulo four

For an odd perfect number, the parity of this count determines whether the special
prime and its exponent agree modulo eight.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- In an odd perfect number with special prime `q`, the number of other prime factors `p` with
`p ≡ 1 (mod 4)` and exponent `≡ 2 (mod 4)` is even exactly when `q` and its exponent agree
modulo 8. -/
theorem even_card_one_mod_four_iff {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    Even ((N.primeFactors.erase q).filter
      fun p => p % 4 = 1 ∧ N.factorization p % 4 = 2).card ↔
      q % 8 = N.factorization q % 8 := by
  let P := N.primeFactors.erase q
  let selected (p : ℕ) := p % 4 = 1 ∧ N.factorization p % 4 = 2
  let f (p : ℕ) := σ 1 (p ^ N.factorization p)
  let D := ∏ p ∈ P, f p
  change Even (P.filter selected).card ↔ q % 8 = N.factorization q % 8
  have hres (p : ℕ) (hp : p ∈ P) : f p % 4 = if selected p then 3 else 1 := by
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hpN)
    have he := even_factorization_of_ne h hq hodd hpp hpq
    change σ 1 (p ^ N.factorization p) % 4 = _
    rcases sigma_prime_pow_even_mod_four hpp hp2 he with ⟨hp4, hs⟩ | ⟨hp4, hs⟩
    · have hn : ¬ selected p := by
        intro hb
        have hp1 : p % 4 = 1 := hb.1
        omega
      rw [if_neg hn, hs]
    · have he2 := Nat.even_iff.mp he
      by_cases hb : N.factorization p % 4 = 2
      · rw [if_pos (show selected p from ⟨hp4, hb⟩), hs]
        omega
      · rw [if_neg (show ¬ selected p from fun hs' => hb hs'.2), hs]
        omega
  have hDmod : D % 4 = (3 : ℕ) ^ (P.filter selected).card % 4 := by
    change (∏ p ∈ P, f p) % 4 = _
    rw [Finset.prod_nat_mod]
    have hprod : (∏ p ∈ P, f p % 4) = ∏ p ∈ P, if selected p then 3 else 1 :=
      Finset.prod_congr rfl hres
    rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hparity : Even (P.filter selected).card ↔ D % 4 = 1 := by
    rw [Nat.even_iff, hDmod]
    let c := (P.filter selected).card
    change c % 2 = 0 ↔ (3 : ℕ) ^ c % 4 = 1
    have hpow : (3 : ℕ) ^ c % 4 = 3 ^ (c % 2) % 4 := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ 4).mp
      push_cast
      exact pow_eq_pow_mod c (show (3 : ZMod 4) ^ 2 = 1 by decide)
    rw [hpow]
    have hc : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases hc with hc | hc <;> rw [hc] <;> decide
  have hqN : q ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hsplit : f q * D = σ 1 N := by
    change f q * (∏ p ∈ N.primeFactors.erase q, f p) = σ 1 N
    rw [Finset.mul_prod_erase _ _ hqN,
      isMultiplicative_sigma.multiplicative_factorization _ h.ne_zero,
      Nat.prod_factorization_eq_prod_primeFactors]
  obtain ⟨r, k, m, hr, hN, hrm, -, hk4⟩ := exists_euler_form h
  have hm : m ≠ 0 := by
    rintro rfl
    exact hrm (dvd_zero r)
  have hfac : N.factorization r = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hr.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd hrm]
    simp
  have hrOdd : Odd (N.factorization r) := Nat.odd_iff.mpr (by omega)
  have hrq : r = q := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hrOdd) (even_factorization_of_ne h hq hodd hr hne)
  subst r
  subst k
  have hcop : (q ^ N.factorization q).Coprime (m ^ 2) :=
    (hq.coprime_iff_not_dvd.mpr hrm).pow _ _
  have hD : D = σ 1 (m ^ 2) := by
    have hfq : 0 < f q := sigma_pos 1 _ (pow_ne_zero _ hq.ne_zero)
    apply Nat.eq_of_mul_eq_mul_left hfq
    calc
      f q * D = σ 1 N := hsplit
      _ = σ 1 (q ^ N.factorization q * m ^ 2) := congrArg (fun n => σ 1 n) hN
      _ = f q * σ 1 (m ^ 2) := isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hparity, hD]
  exact sigma_sq_mod_four_eq_one_iff h hq hN hrm

end OddPerfect

#print axioms OddPerfect.even_card_one_mod_four_iff
