import OddPerfect.Cyclotomic
import OddPerfect.Network

/-!
# Exact valuations of component divisor sums

For primes `p` and `q`, this file computes the exact `q`-adic valuation of
`σ 1 (p ^ a)` at every exponent `a`: through the order of `p` modulo an odd prime `q`,
in closed form at `q = 2` and `q = 3`, and at `q = p`. It then reads off consequences
for the divisor sum network of a perfect number.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private theorem sigma_ne_zero' {p : ℕ} (hp : p.Prime) (a : ℕ) : σ 1 (p ^ a) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

/-- `q ∣ x - 1` exactly when `x` is `1` in `ZMod q` (for `x ≥ 1`). -/
private theorem dvd_sub_one_iff {q x : ℕ} (hx : 1 ≤ x) : q ∣ x - 1 ↔ (x : ZMod q) = 1 := by
  rw [← Nat.modEq_iff_dvd' hx, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one, eq_comm]

/-- The valuation of `σ 1 (p ^ a)` plus that of `p - 1` is that of `p ^ (a + 1) - 1`. -/
private theorem padicValNat_sigma_add {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a : ℕ) :
    padicValNat q (σ 1 (p ^ a)) + padicValNat q (p - 1) = padicValNat q (p ^ (a + 1) - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [← sigma_prime_pow_mul_pred hp a, padicValNat.mul (sigma_ne_zero' hp a)
    (by have := hp.one_lt; omega)]

/-- `q = p`: the prime `p` never divides `σ 1 (p ^ a)`. -/
theorem padicValNat_sigma_prime_pow_self {p : ℕ} (hp : p.Prime) (a : ℕ) :
    padicValNat p (σ 1 (p ^ a)) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => (prime_dvd_sigma_prime_pow hp hp h).1 rfl

/-- Odd `q`, general order: if the order `d` of `p` modulo `q` exceeds 1 and divides
`a + 1`, then `v_q(σ(p ^ a)) = v_q(p ^ d - 1) + v_q((a + 1) / d)`. -/
theorem padicValNat_sigma_prime_pow_of_orderOf_dvd {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (h1 : 1 < orderOf (p : ZMod q))
    (hd : orderOf (p : ZMod q) ∣ a + 1) :
    padicValNat q (σ 1 (p ^ a)) =
      padicValNat q (p ^ orderOf (p : ZMod q) - 1) +
        padicValNat q ((a + 1) / orderOf (p : ZMod q)) := by
  have : Fact q.Prime := ⟨hq⟩
  set d := orderOf (p : ZMod q) with hdd
  have hqp1 : ¬ q ∣ p - 1 := by
    rw [dvd_sub_one_iff hp.one_lt.le]
    intro h
    rw [hdd, h, orderOf_one] at h1
    exact lt_irrefl _ h1
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hpd : 1 < p ^ d := Nat.one_lt_pow (by omega) hp.one_lt
  have hqd : q ∣ p ^ d - 1 := by
    rw [dvd_sub_one_iff hpd.le, Nat.cast_pow, hdd]
    exact pow_orderOf_eq_one _
  obtain ⟨m, hm⟩ := hd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hlte := padicValNat.pow_sub_pow (p := q) (x := p ^ d) (y := 1)
    (hq.odd_of_ne_two hq2) hpd (by simpa using hqd)
    (fun h => hqp (hq.dvd_of_dvd_pow h)) hm0
  have hsum := padicValNat_sigma_add hp hq a
  rw [padicValNat.eq_zero_of_not_dvd hqp1, hm, pow_mul] at hsum
  rw [one_pow] at hlte
  rw [hm, Nat.mul_div_cancel_left _ (by omega)]
  omega

/-- If a prime `q` divides `σ 1 (p ^ a)`, then the order of `p` modulo `q` divides
`a + 1`. -/
private theorem orderOf_dvd_of_dvd_sigma {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : q ∣ σ 1 (p ^ a)) : orderOf (p : ZMod q) ∣ a + 1 := by
  rcases (prime_dvd_sigma_prime_pow hp hq h).2 with ⟨h1, -⟩ | ⟨-, hd, -⟩
  · have : (p : ZMod q) = 1 := by
      rw [← dvd_sub_one_iff hp.one_lt.le]
      exact (Nat.modEq_iff_dvd' hp.one_lt.le).mp
        (by rw [Nat.ModEq, h1, Nat.mod_eq_of_lt hq.one_lt])
    rw [this, orderOf_one]
    exact one_dvd _
  · exact hd

/-- If the order of `p` modulo a prime `q` does not divide `a + 1`, then `q` does not
divide `σ 1 (p ^ a)`. -/
theorem padicValNat_sigma_prime_pow_of_not_orderOf_dvd {p q a : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hd : ¬ orderOf (p : ZMod q) ∣ a + 1) :
    padicValNat q (σ 1 (p ^ a)) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h => hd (orderOf_dvd_of_dvd_sigma hp hq h)

/-- Unified divisibility criterion: with `d` the order of `p` modulo a prime `q ≠ p`,
`q ∣ σ 1 (p ^ a)` iff `q ∣ a + 1` when `d = 1`, and iff `d ∣ a + 1` otherwise. -/
theorem dvd_sigma_prime_pow_iff {p q a : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    q ∣ σ 1 (p ^ a) ↔
      (if orderOf (p : ZMod q) = 1 then q ∣ a + 1 else orderOf (p : ZMod q) ∣ a + 1) := by
  split_ifs with hd1
  · have hc : (p : ZMod q) = 1 := orderOf_eq_one_iff.mp hd1
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, sigma_one_apply_prime_pow hp]
    push_cast
    simp [hc]
  · refine ⟨orderOf_dvd_of_dvd_sigma hp hq, fun hd => ?_⟩
    have h0 : orderOf (p : ZMod q) ≠ 0 := fun h => by rw [h] at hd; simp at hd
    exact dvd_sigma_prime_pow_of_orderOf_dvd hp hq hpq (by omega) hd

/-- `q = 2`: for an odd prime `p`, `σ 1 (p ^ a)` is odd for even `a`, and for odd `a`
its `2`-adic valuation is `v_2(p + 1) + v_2(a + 1) - 1`. -/
theorem padicValNat_two_sigma_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    padicValNat 2 (σ 1 (p ^ a)) =
      if Even a then 0 else padicValNat 2 (p + 1) + padicValNat 2 (a + 1) - 1 := by
  have hpo : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  split_ifs with ha
  · refine padicValNat.eq_zero_of_not_dvd fun h => ?_
    rcases (prime_dvd_sigma_prime_pow hp Nat.prime_two h).2 with ⟨-, h2⟩ | ⟨h1, -, h2⟩
    · obtain ⟨k, hk⟩ := ha
      omega
    · have := Nat.le_of_dvd one_pos h2
      omega
  · have hsum := padicValNat_sigma_add hp Nat.prime_two a
    have hlte := padicValNat.pow_two_sub_one hp.one_lt hpo (n := a + 1) (by omega)
      (by rw [Nat.not_even_iff_odd] at ha; exact ha.add_one)
    have h1 : 1 ≤ padicValNat 2 (p + 1) :=
      one_le_padicValNat_of_dvd (by omega) (by omega)
    omega

/-- `q = 3`, `p ≡ 1 (mod 3)`: `v_3(σ(p ^ a)) = v_3(a + 1)`. -/
theorem padicValNat_three_sigma_prime_pow_of_mod_one {p : ℕ} (hp : p.Prime) (h : p % 3 = 1)
    (a : ℕ) : padicValNat 3 (σ 1 (p ^ a)) = padicValNat 3 (a + 1) :=
  padicValNat_sigma_prime_pow_of_dvd_pred hp Nat.prime_three (by norm_num) (by omega)

/-- `q = 3`, `p ≡ 2 (mod 3)`: `v_3(σ(p ^ a))` is `0` for even `a` and
`v_3(p + 1) + v_3(a + 1)` for odd `a`. -/
theorem padicValNat_three_sigma_prime_pow_of_mod_two {p : ℕ} (hp : p.Prime) (h : p % 3 = 2)
    (a : ℕ) : padicValNat 3 (σ 1 (p ^ a)) =
      if Even a then 0 else padicValNat 3 (p + 1) + padicValNat 3 (a + 1) := by
  have hord : orderOf (p : ZMod 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← ZMod.natCast_mod, h]
    exact orderOf_eq_prime (by decide) (by decide)
  have hp3 : p ≠ 3 := by rintro rfl; norm_num at h
  split_ifs with ha
  · refine padicValNat_sigma_prime_pow_of_not_orderOf_dvd hp Nat.prime_three ?_
    rw [hord]
    obtain ⟨k, hk⟩ := ha
    omega
  · rw [Nat.not_even_iff_odd] at ha
    obtain ⟨k, hk⟩ := ha
    have hd : orderOf (p : ZMod 3) ∣ a + 1 := by rw [hord]; exact ⟨k + 1, by omega⟩
    rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hp Nat.prime_three (by norm_num) hp3
      (by omega) hd, hord]
    have h1 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
      have := hp.one_lt
      zify [Nat.one_le_pow 2 p hp.pos, this.le]
      ring
    have h2 : a + 1 = 2 * (k + 1) := by omega
    rw [h1, padicValNat.mul (by omega) (by have := hp.one_lt; omega),
      padicValNat.eq_zero_of_not_dvd (n := p - 1) (by omega), h2,
      Nat.mul_div_cancel_left _ (by norm_num),
      padicValNat.mul (by norm_num) (by omega),
      padicValNat.eq_zero_of_not_dvd (n := 2) (by norm_num)]
    simp

/-- `q = 3`, `p = 3`: `3` never divides `σ 1 (3 ^ a)`. -/
theorem padicValNat_three_sigma_three_pow (a : ℕ) : padicValNat 3 (σ 1 (3 ^ a)) = 0 :=
  padicValNat_sigma_prime_pow_self Nat.prime_three a

/-- Closed form of `v_3(σ(p ^ a))` for a prime `p`. -/
def threeWeight (p a : ℕ) : ℕ :=
  if p = 3 then 0
  else if p % 3 = 1 then padicValNat 3 (a + 1)
  else if Even a then 0
  else padicValNat 3 (p + 1) + padicValNat 3 (a + 1)

/-- `v_3(σ(p ^ a)) = threeWeight p a` for every prime `p` and every exponent `a`. -/
theorem padicValNat_three_sigma_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    padicValNat 3 (σ 1 (p ^ a)) = threeWeight p a := by
  unfold threeWeight
  split_ifs with h3 h1 ha
  · subst h3; exact padicValNat_three_sigma_three_pow a
  · exact padicValNat_three_sigma_prime_pow_of_mod_one hp h1 a
  all_goals
    have h2 : p % 3 = 2 := by
      have : p % 3 ≠ 0 := fun h0 =>
        h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
      omega
    rw [padicValNat_three_sigma_prime_pow_of_mod_two hp h2 a]
  · rw [if_pos ha]
  · rw [if_neg ha]

/-- The network weight is the `q`-adic valuation of the component divisor sum. -/
theorem sigmaWeight_eq_padicValNat (N p : ℕ) {q : ℕ} (hq : q.Prime) :
    sigmaWeight N p q = padicValNat q (σ 1 (p ^ N.factorization p)) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [sigmaWeight, Nat.factorization_def _ hq]

/-- The special prime `s` of an odd perfect number, with odd exponent `k`, satisfies
`v_2(s + 1) = 1` and `v_2(k + 1) = 1`: the special component alone supplies the single
unit of the `2`-adic ledger. -/
theorem padicValNat_two_special {N s : ℕ} (h : OddPerfect N) (hs : s.Prime)
    (hodd : Odd (N.factorization s)) :
    padicValNat 2 (s + 1) = 1 ∧ padicValNat 2 (N.factorization s + 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN : s ∈ N.primeFactors :=
    Nat.support_factorization N ▸ Finsupp.mem_support_iff.mpr (by rintro h0; simp [h0] at hodd)
  have hs2 : s ≠ 2 := fun h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hsN)
  have hle : sigmaWeight N s 2 ≤ 1 := by
    rw [← sigmaWeight_sum_two h]
    exact Finset.single_le_sum (f := fun r => sigmaWeight N r 2) (fun _ _ => Nat.zero_le _) hsN
  rw [sigmaWeight_eq_padicValNat N s Nat.prime_two, padicValNat_two_sigma_prime_pow hs hs2,
    if_neg (Nat.not_even_iff_odd.mpr hodd)] at hle
  have hso : s % 2 = 1 := Nat.odd_iff.mp (hs.odd_of_ne_two hs2)
  have h1 : 1 ≤ padicValNat 2 (s + 1) := one_le_padicValNat_of_dvd (by omega) (by omega)
  have h2 : 1 ≤ padicValNat 2 (N.factorization s + 1) := by
    obtain ⟨j, hj⟩ := hodd
    exact one_le_padicValNat_of_dvd (by omega) (by omega)
  omega

/-- Consistency with Euler: the special prime and its exponent are both `≡ 1 (mod 4)`,
derived from the `2`-adic ledger. -/
theorem mod_four_special {N s : ℕ} (h : OddPerfect N) (hs : s.Prime)
    (hodd : Odd (N.factorization s)) : s % 4 = 1 ∧ N.factorization s % 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := padicValNat_two_special h hs hodd
  have key : ∀ n : ℕ, padicValNat 2 (n + 1) = 1 → n % 4 = 1 := by
    intro n hn
    have h2d : 2 ∣ n + 1 := by
      have := pow_padicValNat_dvd (p := 2) (n := n + 1)
      rwa [hn, pow_one] at this
    have h4d : ¬ 4 ∣ n + 1 := by
      intro h4
      have := (padicValNat_dvd_iff_le (p := 2) (n := 2) (a := n + 1) (by omega)).mp
        (by norm_num; exact h4)
      omega
    omega
  exact ⟨key s h1, key _ h2⟩

/-- The `3`-adic ledger of a perfect number in closed form. -/
theorem factorization_three_eq_sum_threeWeight {N : ℕ} (hN : N.Perfect) :
    N.factorization 3 = ∑ p ∈ N.primeFactors, threeWeight p (N.factorization p) := by
  rw [← sigmaWeight_sum_eq hN Nat.prime_three (by norm_num)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [sigmaWeight_eq_padicValNat N p Nat.prime_three,
    padicValNat_three_sigma_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-- The `q`-adic ledger of a perfect number at an odd prime `q`, with the vanishing self
term removed. -/
theorem factorization_eq_sum_erase {N q : ℕ} (hN : N.Perfect) (hq : q.Prime) (hq2 : q ≠ 2) :
    N.factorization q =
      ∑ p ∈ N.primeFactors.erase q, padicValNat q (σ 1 (p ^ N.factorization p)) := by
  rw [← sigmaWeight_sum_eq hN hq hq2, Finset.sum_erase N.primeFactors
    (f := fun p => padicValNat q (σ 1 (p ^ N.factorization p)))
    (padicValNat_sigma_prime_pow_self hq _)]
  exact Finset.sum_congr rfl fun p _ => sigmaWeight_eq_padicValNat N p hq

/-- Lower bound: if a prime factor `p ≠ q` has order `d > 1` modulo an odd prime `q` and
`d ∣ v_p(N) + 1`, then `v_q(p ^ d - 1) ≤ v_q(N)`. -/
theorem padicValNat_pow_orderOf_sub_one_le {N p q : ℕ} (hN : N.Perfect) (hq : q.Prime)
    (hq2 : q ≠ 2) (hp : p ∈ N.primeFactors) (hpq : p ≠ q) (h1 : 1 < orderOf (p : ZMod q))
    (hd : orderOf (p : ZMod q) ∣ N.factorization p + 1) :
    padicValNat q (p ^ orderOf (p : ZMod q) - 1) ≤ N.factorization q := by
  rw [factorization_eq_sum_erase hN hq hq2]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun r => padicValNat q (σ 1 (r ^ N.factorization r))) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.mpr ⟨hpq, hp⟩))
  rw [padicValNat_sigma_prime_pow_of_orderOf_dvd (Nat.prime_of_mem_primeFactors hp) hq hq2
    hpq h1 hd]
  exact Nat.le_add_right _ _

end OddPerfect

#print axioms OddPerfect.padicValNat_sigma_prime_pow_self
#print axioms OddPerfect.padicValNat_sigma_prime_pow_of_orderOf_dvd
#print axioms OddPerfect.padicValNat_sigma_prime_pow_of_not_orderOf_dvd
#print axioms OddPerfect.dvd_sigma_prime_pow_iff
#print axioms OddPerfect.padicValNat_two_sigma_prime_pow
#print axioms OddPerfect.padicValNat_three_sigma_prime_pow_of_mod_one
#print axioms OddPerfect.padicValNat_three_sigma_prime_pow_of_mod_two
#print axioms OddPerfect.padicValNat_three_sigma_three_pow
#print axioms OddPerfect.padicValNat_three_sigma_prime_pow
#print axioms OddPerfect.sigmaWeight_eq_padicValNat
#print axioms OddPerfect.padicValNat_two_special
#print axioms OddPerfect.mod_four_special
#print axioms OddPerfect.factorization_three_eq_sum_threeWeight
#print axioms OddPerfect.factorization_eq_sum_erase
#print axioms OddPerfect.padicValNat_pow_orderOf_sub_one_le
