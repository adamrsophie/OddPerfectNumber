import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact components of a perfect number

Checked with the Lean version in `lean-toolchain` and the Mathlib commit in `lake-manifest.json`.
For a prime `p`, `n.factorization p = e` says that the exponent is exactly `e`.
All lemmas here apply to every perfect number.
-/

namespace OPNStarter

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem sigma_eq_two_mul {n : ℕ} (hn : n.Perfect) : σ 1 n = 2 * n := by
  rw [sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).mp hn

/-- The divisor sum of an entire prime-power component divides the full divisor sum. -/
theorem component_sigma_dvd {n p e : ℕ} (hn : n.Perfect) (hp : p.Prime)
    (he : n.factorization p = e) : σ 1 (p ^ e) ∣ 2 * n := by
  subst e
  have hcop := (Nat.coprime_ordCompl hp hn.2.ne').pow_left (n.factorization p)
  rw [← sigma_eq_two_mul hn]
  calc
    σ 1 (ordProj[p] n) ∣ σ 1 (ordProj[p] n) * σ 1 (ordCompl[p] n) :=
      dvd_mul_right _ _
    _ = σ 1 (ordProj[p] n * ordCompl[p] n) :=
      (isMultiplicative_sigma.map_mul_of_coprime hcop).symm
    _ = σ 1 n := by rw [Nat.ordProj_mul_ordCompl_eq_self]

/-- Any odd prime dividing the divisor sum of an exact component must divide the number. -/
theorem force_prime {n p e q : ℕ} (hn : n.Perfect) (hp : p.Prime)
    (he : n.factorization p = e) (hq : q.Prime) (hodd : q ≠ 2)
    (hdiv : q ∣ σ 1 (p ^ e)) : q ∣ n := by
  have hd : q ∣ 2 * n := hdiv.trans (component_sigma_dvd hn hp he)
  exact (hq.dvd_mul.mp hd).resolve_left (fun h => hodd ((Nat.dvd_prime Nat.prime_two).mp h
    |>.resolve_left hq.ne_one))

/-- A prime can occur several times among different component sums. This equality
counts all incidences, including repeated factors, with the extra factor of two on the left. -/
theorem valuation_balance {n : ℕ} (hn : n.Perfect) (q : ℕ) :
    Nat.factorization 2 q + n.factorization q =
      ∑ p ∈ n.primeFactors, (σ 1 (p ^ n.factorization p)).factorization q := by
  calc
    Nat.factorization 2 q + n.factorization q = (2 * n).factorization q := by
      rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hn.2.ne', Finsupp.add_apply]
    _ = (σ 1 n).factorization q := by rw [sigma_eq_two_mul hn]
    _ = _ := by
      rw [isMultiplicative_sigma.multiplicative_factorization _ hn.2.ne',
        Nat.prod_factorization_eq_prod_primeFactors]
      apply Nat.factorization_prod_apply
      intro p hp
      exact (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne'

/-- A certified first link of a factor chain. -/
theorem thirteen_dvd_of_three_sq {n : ℕ} (hn : n.Perfect) (he : n.factorization 3 = 2) :
    13 ∣ n := by
  apply force_prime hn (by decide : Nat.Prime 3) he (by decide) (by decide)
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 3)]
  decide

/-- The second link requires its own exact-exponent hypothesis. -/
theorem sixty_one_dvd_of_thirteen_sq {n : ℕ} (hn : n.Perfect) (he : n.factorization 13 = 2) :
    61 ∣ n := by
  apply force_prime hn (by decide : Nat.Prime 13) he (by decide) (by decide)
  rw [sigma_one_apply_prime_pow (by decide : Nat.Prime 13)]
  decide

/-- Three distinct exact squares each contribute a factor 3. Together they contradict
an exponent of exactly two at 3, regardless of which other primes divide the number. -/
theorem exclude_four_exact_squares {n : ℕ} (hn : n.Perfect)
    (h3 : n.factorization 3 = 2) (h7 : n.factorization 7 = 2)
    (h13 : n.factorization 13 = 2) (h19 : n.factorization 19 = 2) : False := by
  let incoming := fun p => (σ 1 (p ^ n.factorization p)).factorization 3
  have hmem (p : ℕ) (hp : n.factorization p = 2) : p ∈ n.primeFactors :=
    Finsupp.mem_support_iff.mpr (show n.factorization p ≠ 0 by rw [hp]; decide)
  have hsub : ({7, 13, 19} : Finset ℕ) ⊆ n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hmem _ h7
    · exact hmem _ h13
    · exact hmem _ h19
  have hle : ∑ p ∈ ({7, 13, 19} : Finset ℕ), incoming p ≤
      ∑ p ∈ n.primeFactors, incoming p := Finset.sum_le_sum_of_subset hsub
  have heval (p : ℕ) (hp : p.Prime) (he : n.factorization p = 2) :
      incoming p = (1 + p + p ^ 2).factorization 3 := by
    simp [incoming, he, sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have hpos (x : ℕ) (hx : x ≠ 0) (hd : 3 ∣ x) : 1 ≤ x.factorization 3 :=
    ((show Nat.Prime 3 by decide).pow_dvd_iff_le_factorization hx).mp (by simpa using hd)
  have hm : 3 ≤ ∑ p ∈ ({7, 13, 19} : Finset ℕ), incoming p := by
    simp only [Finset.sum_insert (by decide : 7 ∉ ({13, 19} : Finset ℕ)),
      Finset.sum_insert (by decide : 13 ∉ ({19} : Finset ℕ)), Finset.sum_singleton,
      heval 7 (by decide) h7, heval 13 (by decide) h13, heval 19 (by decide) h19]
    have h57 := hpos (1 + 7 + 7 ^ 2) (by decide) (by decide)
    have h183 := hpos (1 + 13 + 13 ^ 2) (by decide) (by decide)
    have h381 := hpos (1 + 19 + 19 ^ 2) (by decide) (by decide)
    omega
  have hbalance := valuation_balance hn 3
  change (2 : ℕ).factorization 3 + n.factorization 3 =
    ∑ p ∈ n.primeFactors, incoming p at hbalance
  rw [h3, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)] at hbalance
  omega

end OPNStarter

#print axioms OPNStarter.sigma_eq_two_mul
#print axioms OPNStarter.component_sigma_dvd
#print axioms OPNStarter.force_prime
#print axioms OPNStarter.valuation_balance
#print axioms OPNStarter.thirteen_dvd_of_three_sq
#print axioms OPNStarter.sixty_one_dvd_of_thirteen_sq
#print axioms OPNStarter.exclude_four_exact_squares
