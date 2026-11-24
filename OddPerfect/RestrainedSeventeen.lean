import OddPerfect.RestrainedThirteen

/-!
# Restrained odd perfect numbers: the special exponent and saturated receivers

Setting of `restrained_big_special`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent exactly 2
(so `r = 3`). Write `E = v_3(N)`, `m = E + 1` and `a = v_q(N)`.

* `restrained_big_special_fermat`: if every prime factor `p` satisfies `2 p + 1 ≤ 3 q`, then
  `a ≤ 2 + v_q(3 ^ (q - 1) - 1)`. The order `d` of 3 modulo `q` divides both `m` and `q - 1`,
  and `q` divides neither, so lifting the exponent gives
  `v_q(3 ^ m - 1) = v_q(3 ^ d - 1) = v_q(3 ^ (q - 1) - 1)`.
* `restrained_big_pow_dvd`: under the same hypothesis, `q ^ (a - 2) ∣ 3 ^ (q - 1) - 1`.
* `saturated_receiver`: for an odd perfect number with `3 ∣ N` and a prime `t ∉ {2, 3}` whose
  order of 3 divides `E + 1`, if `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = v_t(N)`, then no prime
  factor `p ≠ 3` has `t ∣ σ(p ^ v_p(N))`.
* `restrained_tight_square`, `restrained_tight_special`: the restrained form, for a prime `t`
  with `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = 2`.

The hypothesis `2 p + 1 ≤ 3 q` is a real hypothesis; it is not proved for every member of the
family. The bounds on `a` hold for each fixed `q`; they are not uniform bounds on `a`.
Conditional family results in a restricted setting; no novelty is claimed, and whether they are
in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open RestrainedSeven RestrainedThirteen

/-- **Special exponent, Fermat form.** In the restrained family, if every prime factor `p` of
`N` satisfies `2 p + 1 ≤ 3 q`, then `a ≤ 2 + v_q(3 ^ (q - 1) - 1)`. The order `d` of 3 modulo
`q` divides `E + 1` (when `a > 2`) and `q - 1`; since `E + 1 < q`, lifting the exponent gives
`v_q(3 ^ (E + 1) - 1) = v_q(3 ^ d - 1) = v_q(3 ^ (q - 1) - 1)`. The hypothesis `2 p + 1 ≤ 3 q`
is not proved for every member of the family, and the bound depends on `q`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_special_fermat {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) :
    N.factorization q ≤ 2 + padicValNat q (3 ^ (q - 1) - 1) := by
  by_cases ha : N.factorization q ≤ 2
  · omega
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hF : Fact q.Prime := ⟨hq⟩
  have h12 := F.mod12
  have hC := restrained_big_special h hq hodd hr hrq hsq hbig
  have hlt := restrained_big_succ_lt h hq hodd hr hrq hsq hbig
  have hqd : q ∣ 3 ^ (N.factorization 3 + 1) - 1 := dvd_of_one_le_padicValNat (by omega)
  have hord : orderOf (3 : ZMod q) ∣ N.factorization 3 + 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h0 := (ZMod.natCast_eq_zero_iff (3 ^ (N.factorization 3 + 1) - 1) q).2 hqd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), sub_eq_zero] at h0
    push_cast at h0
    exact h0
  have h30 : (3 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : ZMod q) = 0 := by rw [Nat.cast_ofNat]; exact h0
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff _ _).1 h0')
    omega
  have hfer : orderOf (3 : ZMod q) ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one h30
  have hq2 := hq.two_le
  have hA := padicValNat_three_pow_sub_one_eq hq (by omega) (by omega) hord (by omega)
  have hB := padicValNat_three_pow_sub_one_eq hq (by omega) (by omega) hfer (by omega)
  have hm0 : padicValNat q (N.factorization 3 + 1) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  have hq0 : padicValNat q (q - 1) = 0 := padicValNat.eq_zero_of_not_dvd
    (fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega))
  omega

/-- In the restrained family, if every prime factor of `N` is at most `q`, then
`a ≤ 2 + v_q(3 ^ (q - 1) - 1)` (from `restrained_big_special_fermat`).
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_special_fermat {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) :
    N.factorization q ≤ 2 + padicValNat q (3 ^ (q - 1) - 1) :=
  restrained_big_special_fermat h hq hodd hr hrq hsq fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega

/-- **Special exponent, divisibility form.** In the restrained family, if every prime factor
`p` of `N` satisfies `2 p + 1 ≤ 3 q`, then `q ^ (a - 2) ∣ 3 ^ (q - 1) - 1`. The landed cube
condition `restrained_big_pow_modEq_of_one_lt` is the case `a ≥ 5`. For `a ≤ 2` the statement
is trivial. The hypothesis `2 p + 1 ≤ 3 q` is not proved for every member of the family.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_pow_dvd {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) :
    q ^ (N.factorization q - 2) ∣ 3 ^ (q - 1) - 1 := by
  have hF : Fact q.Prime := ⟨hq⟩
  have hC := restrained_big_special_fermat h hq hodd hr hrq hsq hbig
  exact (pow_dvd_pow q (by omega)).trans
    (pow_padicValNat_dvd (p := q) (n := 3 ^ (q - 1) - 1))

/-- In the restrained family, if every prime factor of `N` is at most `q`, then
`q ^ (a - 2) ∣ 3 ^ (q - 1) - 1` (from `restrained_big_pow_dvd`).
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_pow_dvd {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) :
    q ^ (N.factorization q - 2) ∣ 3 ^ (q - 1) - 1 :=
  restrained_big_pow_dvd h hq hodd hr hrq hsq fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega

/-- **Saturated receiver, weight form.** Let `N` be an odd perfect number with `3 ∣ N`, and `t`
a prime other than 2 and 3 whose order of 3 divides `E + 1`. If the row of 3 already sends the
full exponent, `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = v_t(N)`, then every other prime factor
sends nothing to `t`: the weights over all prime factors sum to `v_t(N)`. -/
theorem saturated_receiver_sigmaWeight {N t : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1)
    (hsat : padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
      padicValNat t (N.factorization 3 + 1) = N.factorization t) :
    ∀ p ∈ N.primeFactors, p ≠ 3 → sigmaWeight N p t = 0 := by
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩
  have hsum := sigmaWeight_sum_eq h.perfect ht ht2
  rw [← Finset.add_sum_erase _ _ h3m, sigmaWeight_eq_padicValNat _ _ ht,
    padicValNat_sigma_three_pow ht ht2, padicValNat_three_pow_sub_one_eq ht ht2 ht3 hd
      (by omega)] at hsum
  have h0 : ∑ p ∈ N.primeFactors.erase 3, sigmaWeight N p t = 0 := by omega
  intro p hp hp3
  exact (Finset.sum_eq_zero_iff.mp h0) p (Finset.mem_erase.mpr ⟨hp3, hp⟩)

/-- **Saturated receiver.** Let `N` be an odd perfect number with `3 ∣ N`, and `t` a prime other
than 2 and 3 whose order of 3 divides `E + 1`. If
`v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = v_t(N)`, then `t` divides `σ(p ^ v_p(N))` for no prime
factor `p ≠ 3`. -/
theorem saturated_receiver {N t : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (ht : t.Prime)
    (ht2 : t ≠ 2) (ht3 : t ≠ 3)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1)
    (hsat : padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
      padicValNat t (N.factorization 3 + 1) = N.factorization t) :
    ∀ p ∈ N.primeFactors, p ≠ 3 → ¬ t ∣ σ 1 (p ^ N.factorization p) := by
  intro p hp hp3 hdvd
  have hF : Fact t.Prime := ⟨ht⟩
  have hw := saturated_receiver_sigmaWeight h h3 ht ht2 ht3 hd hsat p hp hp3
  rw [sigmaWeight_eq_padicValNat _ _ ht] at hw
  have := one_le_padicValNat_of_dvd
    (sigma_pos 1 _ (pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)).ne' hdvd
  omega

/-- **Tight clock.** In the restrained family, if a prime `t ∉ {2, 3, q}` has order of 3
dividing `E + 1` and `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = 2`, then `t` divides `N` with
exponent exactly 2.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_tight_factorization {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1)
    (htight : padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
      padicValNat t (N.factorization 3 + 1) = 2) :
    N.factorization t = 2 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have key := clock_le_factorization h (restrained_three_dvd h hq hodd hr hrq hsq) ht ht2 ht3 hd
  have htN : t ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨ht, Nat.dvd_of_factorization_pos (by omega), h.ne_zero⟩
  exact F.sq t htN htq ht3

/-- **Tight clock, square rows.** In the restrained family, if a prime `t ∉ {2, 3, q}` has order
of 3 dividing `E + 1` and `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = 2`, then `t ∤ p ^ 2 + p + 1`
for every prime factor `p ∉ {3, q}` (all of these have exponent 2).
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_tight_square {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1)
    (htight : padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
      padicValNat t (N.factorization 3 + 1) = 2) :
    ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → ¬ t ∣ p ^ 2 + p + 1 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hfac := restrained_tight_factorization h hq hodd hr hrq hsq ht ht2 ht3 htq hd htight
  intro p hp hpq hp3
  have hs := saturated_receiver h (restrained_three_dvd h hq hodd hr hrq hsq) ht ht2 ht3 hd
    (by omega) p hp hp3
  rwa [F.sq p hp hpq hp3, sigma_prime_sq (Nat.prime_of_mem_primeFactors hp)] at hs

/-- **Tight clock, special row.** In the restrained family, if a prime `t ∉ {2, 3, q}` has order
of 3 dividing `E + 1` and `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) = 2`, then `t ∤ σ(q ^ a)`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_tight_special {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1)
    (htight : padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
      padicValNat t (N.factorization 3 + 1) = 2) :
    ¬ t ∣ σ 1 (q ^ N.factorization q) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have h12 := F.mod12
  have hfac := restrained_tight_factorization h hq hodd hr hrq hsq ht ht2 ht3 htq hd htight
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hq, Nat.dvd_of_factorization_pos (by obtain ⟨j, hj⟩ := hodd; omega), h.ne_zero⟩
  exact saturated_receiver h (restrained_three_dvd h hq hodd hr hrq hsq) ht ht2 ht3 hd
    (by omega) q hqN (by omega)

end OddPerfect

#print axioms OddPerfect.restrained_big_special_fermat
#print axioms OddPerfect.restrained_largest_special_fermat
#print axioms OddPerfect.restrained_big_pow_dvd
#print axioms OddPerfect.restrained_largest_pow_dvd
#print axioms OddPerfect.saturated_receiver_sigmaWeight
#print axioms OddPerfect.saturated_receiver
#print axioms OddPerfect.restrained_tight_factorization
#print axioms OddPerfect.restrained_tight_square
#print axioms OddPerfect.restrained_tight_special
