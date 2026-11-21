import OddPerfect.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic structure of component divisor sums

For a prime `p`, the divisor sum `σ 1 (p ^ a)` is the geometric sum
`1 + p + ⋯ + p ^ a`. This file records its cyclotomic factorization, its closed
form, and the arithmetic of the primes dividing it: order dichotomy, the prime
length corollary, the converse forcing direction, and the exact valuation in the
non-primitive case via lifting the exponent.
-/

namespace OddPerfect

open ArithmeticFunction Polynomial
open scoped ArithmeticFunction.sigma

/-- The divisor sum of a prime power factors as a product of cyclotomic values. -/
theorem sigma_prime_pow_eq_prod_cyclotomic {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ((σ 1 (p ^ a) : ℕ) : ℤ) =
      ∏ d ∈ (a + 1).divisors.erase 1, (Polynomial.cyclotomic d ℤ).eval (p : ℤ) := by
  rw [← eval_prod, prod_cyclotomic_eq_geom_sum a.succ_pos, eval_geom_sum,
    sigma_one_apply_prime_pow hp]
  push_cast
  rfl

/-- Closed form of the divisor sum of a prime power. -/
theorem sigma_prime_pow_mul_pred {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) * (p - 1) = p ^ (a + 1) - 1 := by
  zify [hp.one_lt.le, Nat.one_le_pow _ _ hp.pos]
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

/-- The divisor sum of `p ^ a`, read in `ZMod q`, times `p - 1`. -/
private theorem sigma_cast_mul {p : ℕ} (hp : p.Prime) (a q : ℕ) :
    ((σ 1 (p ^ a) : ℕ) : ZMod q) * ((p : ZMod q) - 1) = (p : ZMod q) ^ (a + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

/-- A prime divisor `q` of `σ 1 (p ^ a)` differs from `p`, and either `p ≡ 1 (mod q)`
with `q ∣ a + 1`, or the order of `p` modulo `q` exceeds 1 and divides both
`a + 1` and `q - 1`. -/
theorem prime_dvd_sigma_prime_pow {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdiv : q ∣ σ 1 (p ^ a)) :
    q ≠ p ∧
    ((p % q = 1 ∧ q ∣ a + 1) ∨
     (1 < orderOf (p : ZMod q) ∧ orderOf (p : ZMod q) ∣ a + 1 ∧
       orderOf (p : ZMod q) ∣ q - 1)) := by
  have : Fact q.Prime := ⟨hq⟩
  have hz : ((σ 1 (p ^ a) : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [sigma_one_apply_prime_pow hp] at hz
    push_cast at hz
    simp [Finset.sum_range_succ'] at hz
  by_cases h1 : p % q = 1
  · left
    refine ⟨h1, ?_⟩
    have hc : (p : ZMod q) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff' p 1 q).mpr
        (by rw [h1, Nat.mod_eq_of_lt hq.one_lt])
    rw [sigma_one_apply_prime_pow hp] at hz
    push_cast at hz
    simp only [hc, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hz
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast hz)
  · right
    have hne : (p : ZMod q) ≠ 1 := by
      intro h
      have := (ZMod.natCast_eq_natCast_iff' p 1 q).mp (by simpa using h)
      rw [Nat.mod_eq_of_lt hq.one_lt] at this
      exact h1 this
    have hpow : (p : ZMod q) ^ (a + 1) = 1 := by
      have := sigma_cast_mul hp a q
      rw [hz, zero_mul] at this
      exact (sub_eq_zero.mp this.symm)
    have hdvd : orderOf (p : ZMod q) ∣ a + 1 := orderOf_dvd_of_pow_eq_one hpow
    have hp0 : (p : ZMod q) ≠ 0 := by
      intro h
      rw [h, zero_pow a.succ_ne_zero] at hpow
      exact zero_ne_one hpow
    have hpos : 0 < orderOf (p : ZMod q) := Nat.pos_of_dvd_of_pos hdvd a.succ_pos
    have hne1 : orderOf (p : ZMod q) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    exact ⟨by omega, hdvd, ZMod.orderOf_dvd_card_sub_one hp0⟩

/-- Every prime divisor of `σ 1 (p ^ (l - 1))`, for a prime length `l`, is `l`
itself or congruent to 1 modulo `l`. -/
theorem prime_dvd_sigma_prime_pow_of_prime_length {p q l : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hl : l.Prime) (hdiv : q ∣ σ 1 (p ^ (l - 1))) : q = l ∨ q % l = 1 := by
  have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.one_lt.le
  rcases (prime_dvd_sigma_prime_pow hp hq hdiv).2 with ⟨-, h⟩ | ⟨h1, hd, hq1⟩
  · rw [hl1] at h
    exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hl).mp h)
  · rw [hl1] at hd
    have ho : orderOf (p : ZMod q) = l :=
      ((Nat.dvd_prime hl).mp hd).resolve_left (by omega)
    rw [ho] at hq1
    right
    have := ((Nat.modEq_iff_dvd' hq.one_lt.le).mpr hq1)
    rw [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at this
    exact this.symm

/-- If the order of `p` modulo a prime `q` exceeds 1 and divides `a + 1`, then
`q` divides `σ 1 (p ^ a)`. -/
theorem dvd_sigma_prime_pow_of_orderOf_dvd {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h1 : 1 < orderOf (p : ZMod q)) (hd : orderOf (p : ZMod q) ∣ a + 1) :
    q ∣ σ 1 (p ^ a) := by
  have : Fact q.Prime := ⟨hq⟩
  have hpow : (p : ZMod q) ^ (a + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have hne : (p : ZMod q) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    rw [h, orderOf_one] at h1
    exact lt_irrefl _ h1
  have h := sigma_cast_mul hp a q
  rw [hpow, sub_self] at h
  exact (ZMod.natCast_eq_zero_iff _ _).mp ((mul_eq_zero.mp h).resolve_right hne)

/-- Lifting the exponent: for an odd prime `q` dividing `p - 1`, the `q`-adic
valuation of `σ 1 (p ^ a)` equals that of `a + 1`. -/
theorem padicValNat_sigma_prime_pow_of_dvd_pred {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q ∣ p - 1) :
    padicValNat q (σ 1 (p ^ a)) = padicValNat q (a + 1) := by
  have : Fact q.Prime := ⟨hq⟩
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hp1 : p - 1 ≠ 0 := by have := hp.one_lt; omega
  have hσ : σ 1 (p ^ a) ≠ 0 := by
    intro h0
    have := sigma_prime_pow_mul_pred hp a
    rw [h0, zero_mul] at this
    have h2 : 1 < p ^ (a + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hqp : ¬ q ∣ p := by
    intro hqp
    have := (Nat.dvd_sub_iff_right (Nat.sub_le p 1) hqp).mpr h
    rw [Nat.sub_sub_self hp.one_lt.le] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hlte := padicValNat.pow_sub_pow (p := q) (x := p) (y := 1) hodd hp.one_lt
    (by simpa using h) hqp (n := a + 1) (by omega)
  rw [one_pow, ← sigma_prime_pow_mul_pred hp a, padicValNat.mul hσ hp1] at hlte
  omega

/-- If a prime `q` not dividing `d` divides the `d`th cyclotomic value at `p`, then
the order of `p` modulo `q` is exactly `d`, and hence `d ∣ q - 1`. -/
theorem orderOf_eq_of_dvd_cyclotomic_eval {p q d : ℕ} (hq : q.Prime)
    (hdiv : (q : ℤ) ∣ (Polynomial.cyclotomic d ℤ).eval (p : ℤ)) (hqd : ¬ q ∣ d) :
    orderOf (p : ZMod q) = d ∧ d ∣ q - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero (d : ZMod q) := NeZero.of_not_dvd (ZMod q) hqd
  have hroot : IsRoot (cyclotomic d (ZMod q)) (p : ZMod q) := by
    rw [IsRoot.def, ← map_cyclotomic_int d (ZMod q), eval_map, ← Int.cast_natCast]
    change eval₂ _ (Int.castRingHom (ZMod q) (p : ℤ)) _ = 0
    rw [eval₂_hom, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdiv
  have hprim := isRoot_cyclotomic_iff.mp hroot
  have hord : orderOf (p : ZMod q) = d := hprim.eq_orderOf.symm
  have hd0 : d ≠ 0 := fun h => hqd (h ▸ dvd_zero q)
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.mpr] at hord
    · exact hd0 hord.symm
    · intro n hn h0
      rw [zero_pow hn.ne'] at h0
      exact zero_ne_one h0
  exact ⟨hord, hord ▸ ZMod.orderOf_dvd_card_sub_one hp0⟩

end OddPerfect

#print axioms OddPerfect.sigma_prime_pow_eq_prod_cyclotomic
#print axioms OddPerfect.sigma_prime_pow_mul_pred
#print axioms OddPerfect.prime_dvd_sigma_prime_pow
#print axioms OddPerfect.prime_dvd_sigma_prime_pow_of_prime_length
#print axioms OddPerfect.dvd_sigma_prime_pow_of_orderOf_dvd
#print axioms OddPerfect.padicValNat_sigma_prime_pow_of_dvd_pred
#print axioms OddPerfect.orderOf_eq_of_dvd_cyclotomic_eval
