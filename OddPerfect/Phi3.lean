import OddPerfect.Network
import OddPerfect.Seed.ThreeFree
import OddPerfect.Seed.Collision
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The divisor sum of the square of a prime

For a prime `p`, `σ(p ^ 2) = p ^ 2 + p + 1`. This file collects arithmetic of
`phi3 x = x ^ 2 + x + 1`: parity, coprimality, the exact power of `3`, residues of the
other prime divisors, the root structure modulo a prime, and the resulting bound on
exact-square primes that are `1` modulo `3` in an odd perfect number.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The value `x^2 + x + 1`. -/
def phi3 (x : ℕ) : ℕ := x ^ 2 + x + 1

/-- Agreement with the copy in `OPNCollision`. -/
theorem phi3_eq_collision (x : ℕ) : phi3 x = OPNCollision.phi3 x := rfl

/-- The divisor sum of the square of a prime. -/
theorem sigma_prime_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = phi3 p := by
  simp [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, phi3]
  ring

/-- `phi3 x` is odd. -/
theorem phi3_odd (x : ℕ) : Odd (phi3 x) := by
  unfold phi3
  have : Even (x ^ 2 + x) := by
    rw [show x ^ 2 + x = x * (x + 1) by ring]
    exact Nat.even_mul_succ_self x
  exact this.add_one

/-- `phi3 x` is coprime to `x`. -/
theorem phi3_coprime_self (x : ℕ) : Nat.Coprime (phi3 x) x := by
  rw [show phi3 x = x * (x + 1) + 1 by unfold phi3; ring, Nat.coprime_mul_left_add_left]
  exact Nat.coprime_one_left _

/-- `phi3 x` is coprime to `x + 1`. -/
theorem phi3_coprime_succ (x : ℕ) : Nat.Coprime (phi3 x) (x + 1) := by
  rw [show phi3 x = x * (x + 1) + 1 by unfold phi3; ring, Nat.coprime_mul_right_add_left]
  exact Nat.coprime_one_left _

/-- `3` divides `phi3 x` exactly when `x ≡ 1 (mod 3)`. -/
theorem three_dvd_phi3_iff (x : ℕ) : 3 ∣ phi3 x ↔ x % 3 = 1 := by
  unfold phi3
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod (x ^ 2), Nat.pow_mod]
  have h := Nat.mod_lt x (show 3 > 0 by norm_num)
  interval_cases x % 3 <;> simp

/-- `9` never divides `phi3 x`. -/
theorem not_nine_dvd_phi3 (x : ℕ) : ¬ 9 ∣ phi3 x := by
  unfold phi3
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.add_mod (x ^ 2), Nat.pow_mod]
  have h := Nat.mod_lt x (show 9 > 0 by norm_num)
  interval_cases x % 9 <;> simp

/-- The exponent of `3` in `phi3 x`. -/
theorem padicValNat_three_phi3 (x : ℕ) :
    padicValNat 3 (phi3 x) = if x % 3 = 1 then 1 else 0 := by
  have hpos : phi3 x ≠ 0 := by unfold phi3; omega
  split_ifs with h
  · have h3 : 3 ∣ phi3 x := (three_dvd_phi3_iff x).2 h
    have hle : padicValNat 3 (phi3 x) ≤ 1 := by
      by_contra hc
      have : 3 ^ 2 ∣ phi3 x :=
        (pow_dvd_pow 3 (show 2 ≤ padicValNat 3 (phi3 x) by omega)).trans
          (by rw [Nat.padicValNat_def]; exact pow_multiplicity_dvd _ _)
      exact not_nine_dvd_phi3 x (by simpa using this)
    have : 1 ≤ padicValNat 3 (phi3 x) := by
      have := Fact.mk Nat.prime_three
      rw [Nat.padicValNat_def]; exact (one_le_multiplicity_of_dvd hpos h3)
    omega
  · rw [Nat.padicValNat_def]
    exact multiplicity_eq_zero_of_not_dvd (fun h3 => h ((three_dvd_phi3_iff x).1 h3))

/-- The exponent of `3` in `phi3 x`, via `Nat.factorization`. -/
theorem factorization_three_phi3 (x : ℕ) :
    (phi3 x).factorization 3 = if x % 3 = 1 then 1 else 0 := by
  rw [Nat.factorization_def _ Nat.prime_three, ← Nat.padicValNat_def, padicValNat_three_phi3]

/-- A prime divisor of `phi3 x` other than `3` is `1` modulo `3`. -/
theorem prime_dvd_phi3_mod_three {q x : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ phi3 x) : q % 3 = 1 :=
  OPNThreeFree.target_mod_three hq hq3 (by
    unfold phi3 at hd; rwa [show 1 + x + x ^ 2 = x ^ 2 + x + 1 by ring])

/-- A prime divisor of `phi3 x` other than `3` is `1` modulo `6`. -/
theorem prime_dvd_phi3_mod_six {q x : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ phi3 x) : q % 6 = 1 := by
  have h3 := prime_dvd_phi3_mod_three hq hq3 hd
  have hodd : Odd q := (phi3_odd x).of_dvd_nat hd
  rcases hodd with ⟨k, rfl⟩
  omega

/-- A prime divisor of `phi3 x` other than `3` is at least `7`. -/
theorem seven_le_of_prime_dvd_phi3 {q x : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ phi3 x) : 7 ≤ q := by
  have h6 := prime_dvd_phi3_mod_six hq hq3 hd
  have h1 := hq.one_lt
  omega

/-- `phi3 x` lies strictly above `x ^ 2`. -/
theorem sq_lt_phi3 (x : ℕ) : x ^ 2 < phi3 x := by unfold phi3; omega

/-- `phi3 x` lies strictly below `(x + 1) ^ 2` once `x ≥ 1`. -/
theorem phi3_lt_succ_sq {x : ℕ} (hx : 1 ≤ x) : phi3 x < (x + 1) ^ 2 := by
  unfold phi3; nlinarith

/-- `phi3 x` is not a square once `x ≥ 1`. -/
theorem not_isSquare_phi3 {x : ℕ} (hx : 1 ≤ x) : ¬ IsSquare (phi3 x) := by
  rintro ⟨t, ht⟩
  exact Nat.not_exists_sq (sq_lt_phi3 x |>.trans_eq' (by ring))
    ((phi3_lt_succ_sq hx).trans_eq (by ring)) ⟨t, ht.symm⟩

/-- `phi3` is strictly monotone. -/
theorem phi3_strictMono : StrictMono phi3 := by
  intro a b hab
  unfold phi3
  have := Nat.pow_lt_pow_left hab (two_ne_zero)
  omega

/-- Two inputs with a common prime divisor of `phi3` are congruent or sum to `-1`
modulo that prime. -/
theorem phi3_two_roots {q x y : ℕ} (hq : q.Prime) (hx : q ∣ phi3 x) (hy : q ∣ phi3 y) :
    (x : ZMod q) = y ∨ (x : ZMod q) + y + 1 = 0 := by
  have := Fact.mk hq
  have hx' : ((phi3 x : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hx
  have hy' : ((phi3 y : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hy
  unfold phi3 at hx' hy'
  push_cast at hx' hy'
  have h : ((x : ZMod q) - y) * ((x : ZMod q) + y + 1) = 0 := by
    linear_combination hx' - hy'
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr h

/-- Two distinct inputs below a prime `q` with `q ∣ phi3` of both sum to `q - 1`. -/
theorem phi3_roots_sum {q x y : ℕ} (hq : q.Prime) (hx : q ∣ phi3 x) (hy : q ∣ phi3 y)
    (hxy : x < y) (hyq : y < q) : x + y + 1 = q := by
  rcases phi3_two_roots hq hx hy with h | h
  · have := (ZMod.natCast_eq_natCast_iff' x y q).1 h
    rw [Nat.mod_eq_of_lt (hxy.trans hyq), Nat.mod_eq_of_lt hyq] at this
    omega
  · have hd : q ∣ x + y + 1 := (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h)
    obtain ⟨k, hk⟩ := hd
    rcases k with _ | _ | k
    · omega
    · omega
    · nlinarith

/-- At most two residues below a prime `q` are roots of `phi3` modulo `q`. -/
theorem not_three_roots {q x y z : ℕ} (hq : q.Prime) (hx : q ∣ phi3 x) (hy : q ∣ phi3 y)
    (hz : q ∣ phi3 z) (hxq : x < q) (hyq : y < q) (hzq : z < q)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have key : ∀ a b, q ∣ phi3 a → q ∣ phi3 b → a < q → b < q → a ≠ b →
      a + b + 1 = q := by
    intro a b ha hb haq hbq hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact phi3_roots_sum hq ha hb h hbq
    · have := phi3_roots_sum hq hb ha h haq
      omega
  have := key x y hx hy hxq hyq hxy
  have := key x z hx hz hxq hzq hxz
  omega

/-- An exact-square prime that is `1` modulo `3` sends weight exactly one to `3`. -/
theorem sigmaWeight_three_of_sq_mod_one {N p : ℕ} (hp : p.Prime)
    (he : N.factorization p = 2) (h1 : p % 3 = 1) : sigmaWeight N p 3 = 1 := by
  rw [sigmaWeight, he, sigma_prime_sq hp, factorization_three_phi3, if_pos h1]

/-- An exact-square prime that is `2` modulo `3` sends no weight to `3`. -/
theorem sigmaWeight_three_of_sq_mod_two {N p : ℕ} (hp : p.Prime)
    (he : N.factorization p = 2) (h2 : p % 3 = 2) : sigmaWeight N p 3 = 0 := by
  rw [sigmaWeight, he, sigma_prime_sq hp, factorization_three_phi3, if_neg (by omega)]

/-- In a perfect number, an exact-square prime that is `1` modulo `3` forces `3 ∣ N`. -/
theorem three_dvd_of_sq_mod_one {N p : ℕ} (hN : N.Perfect) (hp : p.Prime)
    (he : N.factorization p = 2) (h1 : p % 3 = 1) : 3 ∣ N :=
  OPNStarter.force_prime hN hp he Nat.prime_three (by decide)
    (by rw [sigma_prime_sq hp]; exact (three_dvd_phi3_iff p).2 h1)

/-- The number of exact-square primes that are `1` modulo `3` is at most the exponent
of `3` in an odd perfect number. -/
theorem card_exact_sq_modEq_one_le {N : ℕ} (h : OddPerfect N) :
    ((N.primeFactors.filter fun p => N.factorization p = 2 ∧ p % 3 = 1).card)
      ≤ N.factorization 3 := by
  rw [← sigmaWeight_sum_eq h.perfect Nat.prime_three (by decide), Finset.card_eq_sum_ones]
  calc ∑ p ∈ N.primeFactors.filter (fun p => N.factorization p = 2 ∧ p % 3 = 1), 1
      = ∑ p ∈ N.primeFactors.filter (fun p => N.factorization p = 2 ∧ p % 3 = 1),
          sigmaWeight N p 3 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_filter] at hp
        exact (sigmaWeight_three_of_sq_mod_one (Nat.prime_of_mem_primeFactors hp.1)
          hp.2.1 hp.2.2).symm
    _ ≤ ∑ p ∈ N.primeFactors, sigmaWeight N p 3 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end OddPerfect

#print axioms OddPerfect.phi3_eq_collision
#print axioms OddPerfect.sigma_prime_sq
#print axioms OddPerfect.phi3_odd
#print axioms OddPerfect.phi3_coprime_self
#print axioms OddPerfect.phi3_coprime_succ
#print axioms OddPerfect.three_dvd_phi3_iff
#print axioms OddPerfect.not_nine_dvd_phi3
#print axioms OddPerfect.padicValNat_three_phi3
#print axioms OddPerfect.factorization_three_phi3
#print axioms OddPerfect.prime_dvd_phi3_mod_three
#print axioms OddPerfect.prime_dvd_phi3_mod_six
#print axioms OddPerfect.seven_le_of_prime_dvd_phi3
#print axioms OddPerfect.sq_lt_phi3
#print axioms OddPerfect.phi3_lt_succ_sq
#print axioms OddPerfect.not_isSquare_phi3
#print axioms OddPerfect.phi3_strictMono
#print axioms OddPerfect.phi3_two_roots
#print axioms OddPerfect.phi3_roots_sum
#print axioms OddPerfect.not_three_roots
#print axioms OddPerfect.sigmaWeight_three_of_sq_mod_one
#print axioms OddPerfect.sigmaWeight_three_of_sq_mod_two
#print axioms OddPerfect.three_dvd_of_sq_mod_one
#print axioms OddPerfect.card_exact_sq_modEq_one_le
