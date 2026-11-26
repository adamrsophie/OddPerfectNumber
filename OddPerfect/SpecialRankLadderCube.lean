import OddPerfect.SpecialRankLadder
import OddPerfect.SpecialBelowCapacity

/-!
# The special exponent ladder for an arbitrary cap on the ordinary exponents

Restricted result; no published source was checked; novelty not verified.

Let `N` be an odd perfect number with special prime `q`, let every other prime factor have
exponent at most `E`, and let `k` prime factors of `N` exceed `q`. The module
`SpecialRankLadder` bounds the special exponent in terms of a bound `β` for the weight that
the rows of the primes below `q` carry at `q`; the module `SpecialBelowCapacity` shows that
`β = E ^ 3` always works. This module joins the two.

* `special_exponent_ladder_cube`: if `k ≤ (q - 2) q ^ t`, then
  `E v_q(N) + E t + E - 1 ≤ (E + 1) ^ k (E E ^ 3 + E t + E - 1)`.
* `special_exponent_ladder_cube_card`: the same with `t = k`, valid for every `k`.

So for a fixed cap `E` on the ordinary exponents and a fixed number `k` of prime factors
above the special prime, the special exponent is bounded by a number that depends on `E` and
`k` only. The bound grows with `k`, and no bound on `k` is proved, so no family is excluded.
The odd perfect number conjecture is open, and nothing here decides it.
-/

namespace OddPerfect

/-- The ladder with the general capacity `E ^ 3`: ordinary exponents at most `E`, and
`k ≤ (q - 2) q ^ t` prime factors above the special prime `q`. Restricted result; no
published source was checked; novelty not verified. -/
theorem special_exponent_ladder_cube {N q E t k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E)
    (hk : (N.primeFactors.filter (q < ·)).card = k) (ht : k ≤ (q - 2) * q ^ t) :
    E * N.factorization q + E * t + E - 1 ≤ (E + 1) ^ k * (E * E ^ 3 + E * t + E - 1) :=
  special_exponent_ladder h hq hodd hE
    (sum_sigmaWeight_below_special_le_cube h hq fun p hp hpq => hE p hp hpq.ne)
    ((Nat.le_self_pow (by norm_num) E).trans (Nat.le_succ _)) hk ht

/-- The ladder with the general capacity and `t = k`, valid for every number `k` of prime
factors above the special prime. Restricted result; no published source was checked;
novelty not verified. -/
theorem special_exponent_ladder_cube_card {N q E k : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hE : ∀ p ∈ N.primeFactors, p ≠ q → N.factorization p ≤ E)
    (hk : (N.primeFactors.filter (q < ·)).card = k) :
    E * N.factorization q + E * k + E - 1 ≤ (E + 1) ^ k * (E * E ^ 3 + E * k + E - 1) := by
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    omega
  have h1 : k < q ^ k := Nat.lt_pow_self (by omega)
  have h2 : q ^ k ≤ (q - 2) * q ^ k := Nat.le_mul_of_pos_left _ (by omega)
  exact special_exponent_ladder_cube h hq hodd hE hk (by omega)

end OddPerfect

#print axioms OddPerfect.special_exponent_ladder_cube
#print axioms OddPerfect.special_exponent_ladder_cube_card
