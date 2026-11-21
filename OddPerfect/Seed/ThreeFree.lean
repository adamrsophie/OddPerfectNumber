import OddPerfect.Seed.Starter
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# Where the divisor sum of an exact square can go

If 3 does not divide a perfect number, prime factors with exponent exactly
two are congruent to 2 modulo 3. Every prime dividing the divisor sum of one
of those squares is congruent to 1 modulo 3 and has a different exponent.
The result holds without an oddness assumption on the perfect number.
-/

namespace OPNThreeFree

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem sigma_square {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

/-- An exact-square prime in a perfect number coprime to 3 has residue 2 modulo 3. -/
theorem source_mod_three {n p : ℕ} (hn : n.Perfect) (h3 : ¬ 3 ∣ n)
    (hp : p.Prime) (he : n.factorization p = 2) : p % 3 = 2 := by
  have hmem : p ∈ n.primeFactors :=
    Finsupp.mem_support_iff.mpr (show n.factorization p ≠ 0 by omega)
  have h0 : p % 3 ≠ 0 := fun h =>
    h3 ((Nat.dvd_iff_mod_eq_zero.mpr h).trans (Nat.mem_primeFactors.mp hmem).2.1)
  have h1 : p % 3 ≠ 1 := by
    intro h
    apply h3
    apply OPNStarter.force_prime hn hp he Nat.prime_three (by decide)
    rw [sigma_square hp]
    have hcast : (p : ZMod 3) = 1 := (ZMod.natCast_eq_natCast_iff' p 1 3).2 h
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [hcast]
    decide
  omega

/-- A prime divisor other than 3 of the third cyclotomic value has residue 1 mod 3. -/
theorem target_mod_three {p q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hdiv : q ∣ 1 + p + p ^ 2) : q % 3 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hz : (1 : ZMod q) + p + (p : ZMod q) ^ 2 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    simp [h] at hz
  have hp1 : (p : ZMod q) ≠ 1 := by
    intro h
    have hthree : (3 : ZMod q) = 0 := by
      rw [h] at hz
      convert hz using 1
      ring
    have hd : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).mp hthree
    exact hq3 ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hq.ne_one)
  have hpow : (p : ZMod q) ^ 3 = 1 := by
    calc
      (p : ZMod q) ^ 3 = ((1 : ZMod q) + p + (p : ZMod q) ^ 2) * (p - 1) + 1 := by ring
      _ = 1 := by rw [hz]; simp
  have horder : orderOf (p : ZMod q) = 3 := orderOf_eq_prime hpow hp1
  have hd := ZMod.orderOf_dvd_card_sub_one hp0
  rw [horder] at hd
  have := hq.one_lt
  omega

/-- Every prime forced by an exact square belongs to the support of the perfect
number, is 1 modulo 3, and cannot itself be an exact-square component. -/
theorem exact_square_transfer {n p q : ℕ} (hn : n.Perfect) (h3 : ¬ 3 ∣ n)
    (hp : p.Prime) (he : n.factorization p = 2) (hq : q.Prime)
    (hdiv : q ∣ σ 1 (p ^ 2)) :
    p % 3 = 2 ∧ q ∣ n ∧ q ≠ 3 ∧ q % 3 = 1 ∧ n.factorization q ≠ 2 := by
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact h3 (OPNStarter.force_prime hn hp he hq (by decide) hdiv)
  have hm : q % 3 = 1 := target_mod_three hq hq3 (by simpa [sigma_square hp] using hdiv)
  refine ⟨source_mod_three hn h3 hp he, OPNStarter.force_prime hn hp he hq (by omega) hdiv,
    hq3, hm, ?_⟩
  intro heq
  have := source_mod_three hn h3 hq heq
  omega

end OPNThreeFree

#print axioms OPNThreeFree.source_mod_three
#print axioms OPNThreeFree.target_mod_three
#print axioms OPNThreeFree.exact_square_transfer
