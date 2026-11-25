import OddPerfect.Reciprocity
import OddPerfect.RestrainedFiveModTwelve

/-!
# The special prime is a square modulo the primes 1 mod 4 of its row

The landed `legendreSym_eq_one_of_dvd_sigma_even` covers rows `σ(p ^ e)` with `e` even. This
module treats the row of exponent `a ≡ 1 (mod 4)`, the shape of the special row of an odd
perfect number.

* `isSquare_of_dvd_geom_sum_of_mod_four` (arithmetic): if `a % 4 = 1`, `p` is a prime with
  `p % 4 = 1` and `p ∣ ∑ i ∈ range (a + 1), q ^ i`, then `q` is a square modulo `p`. Write
  `a + 1 = 2 L` with `L = 2 t + 1` odd. Then `q ^ (2 L) ≡ 1`, so `y = q ^ L ≡ ±1`, and
  `q * y = (q ^ (t + 1)) ^ 2`. If `y ≡ 1` this shows that `q` is a square; if `y ≡ -1`, then
  `-q` is a square and so is `-1` (as `p ≡ 1 (mod 4)`), hence `q` is a square.
* `isSquare_of_dvd_sigma_of_mod_four`: the same for `σ(q ^ a)` with `q` prime.
* `isSquare_of_dvd_sigma_special`: in an odd perfect number with special prime `q`, every
  prime `p ≡ 1 (mod 4)` dividing `σ(q ^ v_q(N))` has `q` a square modulo `p` and, by quadratic
  reciprocity, `p` a square modulo `q`. This is a necessary condition only.
* `restrained_five_mod_twelve_isSquare`: a restricted family result. In the setting of
  `restrained_five_mod_twelve_sq_dvd`, every prime factor `p ≡ 5 (mod 12)` of `N` has `q` a
  square modulo `p` and `p` a square modulo `q`. The family is not excluded.

Both hypotheses of the arithmetic statement are needed. For `a ≡ 1 (mod 4)`: `q = 37`, `a = 3`,
`p = 5` has `5 ∣ σ(37 ^ 3) = 52060`, and `37 ≡ 2` is not a square modulo 5. For
`p ≡ 1 (mod 4)`: `q = 13`, `a = 1`, `p = 7` has `7 ∣ 14`, and `13 ≡ 6` is not a square
modulo 7.

Novelty not verified. Wallace's product formula for the special vertex is in
`OddPerfect/Reciprocity.lean`; this is the statement for one prime of the special row. The odd
perfect number conjecture is open and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- **Arithmetic.** If `a % 4 = 1` and a prime `p ≡ 1 (mod 4)` divides
`∑ i ∈ range (a + 1), q ^ i`, then `q` is a square modulo `p`. Here `q` is any natural number.
Both congruence hypotheses are needed: `(q, a, p) = (37, 3, 5)` and `(13, 1, 7)`. -/
theorem isSquare_of_dvd_geom_sum_of_mod_four {q a p : ℕ} [Fact p.Prime] (ha : a % 4 = 1)
    (hp4 : p % 4 = 1) (hd : p ∣ ∑ i ∈ Finset.range (a + 1), q ^ i) :
    IsSquare ((q : ℕ) : ZMod p) := by
  set x : ZMod p := (q : ZMod p) with hxdef
  have h0 : ∑ i ∈ Finset.range (a + 1), x ^ i = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    push_cast at this
    exact this
  have h1 : x ^ (a + 1) = 1 := by
    have := geom_sum_mul x (a + 1)
    rw [h0, zero_mul] at this
    exact (sub_eq_zero.mp this.symm)
  obtain ⟨t, rfl⟩ : ∃ t, a = 4 * t + 1 := ⟨a / 4, by omega⟩
  have hy : (x ^ (2 * t + 1) - 1) * (x ^ (2 * t + 1) + 1) = 0 := by
    have he : (x ^ (2 * t + 1) - 1) * (x ^ (2 * t + 1) + 1) = x ^ (4 * t + 1 + 1) - 1 := by
      ring
    rw [he, h1, sub_self]
  have hsq : x * x ^ (2 * t + 1) = x ^ (t + 1) * x ^ (t + 1) := by ring
  rcases mul_eq_zero.mp hy with hy | hy
  · rw [sub_eq_zero.mp hy, mul_one] at hsq
    exact ⟨_, hsq⟩
  · rw [eq_neg_of_add_eq_zero_left hy] at hsq
    obtain ⟨c, hc⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    refine ⟨c * x ^ (t + 1), ?_⟩
    linear_combination c ^ 2 * hsq - x * hc

/-- **Arithmetic, divisor sum form.** If `q` is prime, `a % 4 = 1` and a prime `p ≡ 1 (mod 4)`
divides `σ(q ^ a)`, then `q` is a square modulo `p`. -/
theorem isSquare_of_dvd_sigma_of_mod_four {q a p : ℕ} [Fact p.Prime] (hq : q.Prime)
    (ha : a % 4 = 1) (hp4 : p % 4 = 1) (hd : p ∣ σ 1 (q ^ a)) :
    IsSquare ((q : ℕ) : ZMod p) :=
  isSquare_of_dvd_geom_sum_of_mod_four ha hp4 (by rwa [sigma_one_apply_prime_pow hq] at hd)

/-- **Odd perfect numbers: the primes 1 mod 4 of the special row.** Let `N` be an odd perfect
number with special prime `q` (odd exponent `a = v_q(N)`, so `a ≡ 1 (mod 4)` by
`special_mod_four`). Every prime `p ≡ 1 (mod 4)` dividing `σ(q ^ a)` has `q` a square modulo
`p` and, by quadratic reciprocity, `p` a square modulo `q`. A necessary condition only. -/
theorem isSquare_of_dvd_sigma_special {N q p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hd : p ∣ σ 1 (q ^ N.factorization q)) :
    IsSquare ((q : ℕ) : ZMod p) ∧ IsSquare ((p : ℕ) : ZMod q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  have hsq := isSquare_of_dvd_sigma_of_mod_four hq ha4 hp4 hd
  exact ⟨hsq, (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 (by omega)).mp hsq⟩

/-- **Restrained family: the primes 5 modulo 12.** In the setting of
`restrained_five_mod_twelve_sq_dvd` (every prime factor other than `q` and `r` has exponent 2),
a prime factor `p ≡ 5 (mod 12)` of `N` divides `σ(q ^ v_q(N))`, so `q` is a square modulo `p`
and `p` is a square modulo `q`. A restricted family result; the family is not excluded. -/
theorem restrained_five_mod_twelve_isSquare {N q r p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hp : p ∈ N.primeFactors) (h12 : p % 12 = 5) :
    IsSquare ((q : ℕ) : ZMod p) ∧ IsSquare ((p : ℕ) : ZMod q) := by
  have h2 := restrained_five_mod_twelve_sq_dvd h hq hodd hr hrq hsq hp h12
  have h2q : 2 ∣ σ 1 (q ^ N.factorization q) := RestrainedFifteen.two_dvd_sigma_odd hq
    (by have := (special_mod_four h hq hodd).1; omega) hodd
  have hd : p ∣ σ 1 (q ^ N.factorization q) :=
    (dvd_pow_self p two_ne_zero).trans (h2.trans (Nat.div_dvd_of_dvd h2q))
  exact isSquare_of_dvd_sigma_special h hq hodd (Nat.prime_of_mem_primeFactors hp)
    (by omega) hd

end OddPerfect

#print axioms OddPerfect.isSquare_of_dvd_geom_sum_of_mod_four
#print axioms OddPerfect.isSquare_of_dvd_sigma_of_mod_four
#print axioms OddPerfect.isSquare_of_dvd_sigma_special
#print axioms OddPerfect.restrained_five_mod_twelve_isSquare
