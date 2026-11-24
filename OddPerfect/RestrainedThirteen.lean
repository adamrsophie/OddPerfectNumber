import OddPerfect.RestrainedEight
import OddPerfect.Phi3Algebra
import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic

/-!
# Restrained odd perfect numbers: the exponent of 3 as a clock

Setting of `restrained_exception_eq_three`: `N` is an odd perfect number with special prime `q`,
`r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent exactly 2
(so `r = 3`). Write `E = v_3(N)` and `a = v_q(N)`.

* `padicValNat_pow_sub_one_eq`: lifting the exponent for a base `b` and an odd prime `t ∤ b`
  with `d = ord_t(b) ∣ m`: `v_t(b ^ m - 1) = v_t(b ^ d - 1) + v_t(m)`.
* `restrained_clock`: for a prime `t ∉ {2, 3, q}` with `ord_t(3) ∣ E + 1`,
  `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) ≤ 2`; the same with `a` in place of 2 for `t = q`
  (`restrained_clock_special`).
* `restrained_big_special`: if every prime factor `p` satisfies `2 p + 1 ≤ 3 q` (for instance
  if `q` is the largest prime factor, `restrained_largest_special`), then
  `a ≤ 2 + v_q(3 ^ (E + 1) - 1)`.
* `restrained_big_succ_lt`: under the same hypothesis, `E + 1 < q`.
* `restrained_big_pow_modEq_of_one_lt`: under the same hypothesis, `1 < a` forces
  `3 ^ (q - 1) ≡ 1 (mod q ^ 3)`, a condition stronger than the Wieferich condition to the
  base 3. The `largest` forms are corollaries.

Conditional family results; whether they are in the literature was not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedThirteen

/-- `2 σ(3 ^ E) + 1 = 3 ^ (E + 1)`. -/
theorem two_mul_sigma_three_pow_add_one' (E : ℕ) : 2 * σ 1 (3 ^ E) + 1 = 3 ^ (E + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_three]
  induction E with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, mul_add, pow_succ 3 (k + 1)]; omega

/-- For an odd prime `t`, `v_t(σ(3 ^ E)) = v_t(3 ^ (E + 1) - 1)`. -/
theorem padicValNat_sigma_three_pow {t : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (E : ℕ) :
    padicValNat t (σ 1 (3 ^ E)) = padicValNat t (3 ^ (E + 1) - 1) := by
  have : Fact t.Prime := ⟨ht⟩
  have h := two_mul_sigma_three_pow_add_one' E
  rw [show 3 ^ (E + 1) - 1 = 2 * σ 1 (3 ^ E) by omega,
    padicValNat.mul two_ne_zero (sigma_pos 1 _ (by positivity)).ne',
    padicValNat.eq_zero_of_not_dvd
      (fun hd => ht2 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp hd)), zero_add]

/-- For a prime `t ∤ b`, the order of `b` modulo `t` is positive and below `t`, and
`t ∣ b ^ ord_t(b) - 1`. -/
theorem orderOf_natCast_facts {t b : ℕ} (ht : t.Prime) (htb : ¬ t ∣ b) :
    0 < orderOf (b : ZMod t) ∧ orderOf (b : ZMod t) < t ∧
      t ∣ b ^ orderOf (b : ZMod t) - 1 := by
  have hF : Fact t.Prime := ⟨ht⟩
  have hb0 : (b : ZMod t) ≠ 0 := fun h => htb ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hdt : orderOf (b : ZMod t) ∣ t - 1 := ZMod.orderOf_dvd_card_sub_one hb0
  have ht1 := ht.two_le
  have hd0 : 0 < orderOf (b : ZMod t) := Nat.pos_of_dvd_of_pos hdt (by omega)
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · exact absurd (h ▸ dvd_zero t) htb
    · exact h
  refine ⟨hd0, lt_of_le_of_lt (Nat.le_of_dvd (by omega) hdt) (by omega), ?_⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hb1)]
  push_cast
  rw [pow_orderOf_eq_one, sub_self]

/-- **Lifting the exponent.** Let `t` be an odd prime, `b ≥ 2` with `t ∤ b`, and
`d = ord_t(b)`. If `d ∣ m` and `1 ≤ m`, then `v_t(b ^ m - 1) = v_t(b ^ d - 1) + v_t(m)`. -/
theorem padicValNat_pow_sub_one_eq {t b m : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (hb : 2 ≤ b)
    (htb : ¬ t ∣ b) (hd : orderOf (b : ZMod t) ∣ m) (hm : 1 ≤ m) :
    padicValNat t (b ^ m - 1) =
      padicValNat t (b ^ orderOf (b : ZMod t) - 1) + padicValNat t m := by
  have hF : Fact t.Prime := ⟨ht⟩
  obtain ⟨hd0, hdlt, hdvd⟩ := orderOf_natCast_facts ht htb
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by
    rintro rfl
    omega
  have hx1 : 1 < b ^ orderOf (b : ZMod t) := Nat.one_lt_pow hd0.ne' (by omega)
  have hndvd : ¬ t ∣ b ^ orderOf (b : ZMod t) := fun h => htb (ht.dvd_of_dvd_pow h)
  have key := padicValNat.pow_sub_pow (p := t) (ht.odd_of_ne_two ht2) hx1 hdvd hndvd hk
  rw [one_pow] at key
  rw [pow_mul, key, padicValNat.mul hd0.ne' hk,
    padicValNat.eq_zero_of_not_dvd (fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)),
    zero_add]

/-- The order of 3 modulo a prime `t ≠ 3`: positive, below `t`, and `t ∣ 3 ^ ord_t(3) - 1`. -/
theorem orderOf_three_facts {t : ℕ} (ht : t.Prime) (ht3 : t ≠ 3) :
    0 < orderOf (3 : ZMod t) ∧ orderOf (3 : ZMod t) < t ∧
      t ∣ 3 ^ orderOf (3 : ZMod t) - 1 := by
  have h := orderOf_natCast_facts (b := 3) ht
    (fun h => ht3 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_three).mp h))
  rwa [Nat.cast_ofNat] at h

/-- **Lifting the exponent, base 3.** For an odd prime `t ≠ 3` with `ord_t(3) ∣ m`, `1 ≤ m`:
`v_t(3 ^ m - 1) = v_t(3 ^ ord_t(3) - 1) + v_t(m)`. -/
theorem padicValNat_three_pow_sub_one_eq {t m : ℕ} (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3)
    (hd : orderOf (3 : ZMod t) ∣ m) (hm : 1 ≤ m) :
    padicValNat t (3 ^ m - 1) = padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) + padicValNat t m := by
  have h := padicValNat_pow_sub_one_eq (b := 3) ht ht2 (by norm_num)
    (fun h => ht3 ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_three).mp h))
    (by rwa [Nat.cast_ofNat]) hm
  rwa [Nat.cast_ofNat] at h

/-- For every odd perfect number with `3 ∣ N` and every prime `t ∉ {2, 3}` whose order of 3
divides `E + 1`, where `E = v_3(N)`: `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) ≤ v_t(N)`. -/
theorem clock_le_factorization {N t : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (ht : t.Prime)
    (ht2 : t ≠ 2) (ht3 : t ≠ 3) (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1) :
    padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) + padicValNat t (N.factorization 3 + 1) ≤
      N.factorization t := by
  rw [← padicValNat_three_pow_sub_one_eq ht ht2 ht3 hd (by omega),
    ← padicValNat_sigma_three_pow ht ht2, ← sigmaWeight_eq_padicValNat _ _ ht,
    ← sigmaWeight_sum_eq h.perfect ht ht2]
  exact Finset.single_le_sum (f := fun p => sigmaWeight N p t) (fun _ _ => Nat.zero_le _)
    (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, h.ne_zero⟩)

end RestrainedThirteen

open RestrainedSeven RestrainedThirteen

/-- **Clock restriction.** In the restrained family, for every prime `t ∉ {2, 3, q}` whose
order of 3 divides `E + 1` (`E = v_3(N)`): `v_t(3 ^ ord_t(3) - 1) + v_t(E + 1) ≤ 2`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_clock {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1) :
    padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) + padicValNat t (N.factorization 3 + 1) ≤ 2 := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have key := clock_le_factorization h (restrained_three_dvd h hq hodd hr hrq hsq) ht ht2 ht3 hd
  by_cases htN : t ∈ N.primeFactors
  · rwa [F.sq t htN htq ht3] at key
  · have h0 : N.factorization t = 0 :=
      Finsupp.notMem_support_iff.mp (by rwa [Nat.support_factorization])
    omega

/-- In the restrained family, if the order of 3 modulo a prime `t ∉ {2, 3, q}` divides `E + 1`,
then `v_t(E + 1) ≤ 1`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_clock_padicValNat_le_one {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hd : orderOf (3 : ZMod t) ∣ N.factorization 3 + 1) :
    padicValNat t (N.factorization 3 + 1) ≤ 1 := by
  have hF : Fact t.Prime := ⟨ht⟩
  have key := restrained_clock h hq hodd hr hrq hsq ht ht2 ht3 htq hd
  obtain ⟨hd0, -, hdvd⟩ := orderOf_three_facts ht ht3
  have h1 : 1 ≤ padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) := one_le_padicValNat_of_dvd
    (by have := Nat.one_lt_pow hd0.ne' (by norm_num : 1 < 3); omega) hdvd
  omega

/-- In the restrained family, if `t ^ 3 ∣ 3 ^ ord_t(3) - 1` for a prime `t ∉ {2, 3, q}`, then
the order of 3 modulo `t` does not divide `E + 1`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_clock_not_dvd {N q r t : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (ht : t.Prime) (ht2 : t ≠ 2) (ht3 : t ≠ 3) (htq : t ≠ q)
    (hcube : t ^ 3 ∣ 3 ^ orderOf (3 : ZMod t) - 1) :
    ¬ orderOf (3 : ZMod t) ∣ N.factorization 3 + 1 := by
  intro hd
  have hF : Fact t.Prime := ⟨ht⟩
  have key := restrained_clock h hq hodd hr hrq hsq ht ht2 ht3 htq hd
  obtain ⟨hd0, -, -⟩ := orderOf_three_facts ht ht3
  have h3 := (padicValNat_dvd_iff_le
    (by have := Nat.one_lt_pow hd0.ne' (by norm_num : 1 < 3); omega)).mp hcube
  omega

/-- **Clock restriction at the special prime.** In the restrained family, if the order `d` of 3
modulo `q` divides `E + 1`, then `v_q(3 ^ d - 1) + v_q(E + 1) ≤ a` with `a = v_q(N)`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_clock_special {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hd : orderOf (3 : ZMod q) ∣ N.factorization 3 + 1) :
    padicValNat q (3 ^ orderOf (3 : ZMod q) - 1) + padicValNat q (N.factorization 3 + 1) ≤
      N.factorization q := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have := F.mod12
  exact clock_le_factorization h (restrained_three_dvd h hq hodd hr hrq hsq) hq (by omega)
    (by omega) hd

namespace RestrainedThirteen

/-- Two odd numbers below `2 q` that are congruent modulo an odd `q` are equal. -/
theorem eq_of_natCast_eq_of_odd {q x y : ℕ} (hq : q % 2 = 1) (hx : x < 2 * q) (hy : y < 2 * q)
    (hxo : x % 2 = 1) (hyo : y % 2 = 1) (h : (x : ZMod q) = y) : x = y := by
  have hm := (ZMod.natCast_eq_natCast_iff x y q).1 h
  have key : ∀ u v : ℕ, u ≤ v → v < 2 * q → u % 2 = 1 → v % 2 = 1 → q ∣ v - u → u = v := by
    intro u v huv hv hu hv' hd
    obtain ⟨k, hk⟩ := hd
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simp at hk
      omega
    · have : q * 2 ≤ q * (k + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
  rcases le_total x y with hxy | hxy
  · exact key x y hxy hy hxo hyo ((Nat.modEq_iff_dvd' hxy).1 hm)
  · exact (key y x hxy hx hyo hxo ((Nat.modEq_iff_dvd' hxy).1 hm.symm)).symm

/-- A finite set of numbers `x ≡ 1 (mod 6)` with `1 < x ≤ M` has at most `M / 6` elements. -/
theorem card_le_of_mod_six {T : Finset ℕ} {M : ℕ} (hT : ∀ x ∈ T, x % 6 = 1 ∧ 1 < x ∧ x ≤ M) :
    T.card ≤ M / 6 := by
  have h := Finset.card_le_card_of_injOn (fun x => x / 6) (t := Finset.Icc 1 (M / 6))
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := hT x hx
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega)
    (fun x hx y hy hxy => by
      have := (hT x hx).1
      have := (hT y hy).1
      simp only at hxy
      omega)
  rw [Nat.card_Icc] at h
  omega

/-- `2 m + 3 < 3 ^ (m + 1)` for `m ≥ 1`. -/
theorem two_mul_add_three_lt_three_pow {m : ℕ} (hm : 1 ≤ m) : 2 * m + 3 < 3 ^ (m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

end RestrainedThirteen

/-- **The special prime against the other primes.** In the restrained family, if every prime
factor `p` of `N` satisfies `2 p + 1 ≤ 3 q`, then `a ≤ 2 + v_q(3 ^ (E + 1) - 1)`. The row of 3
sends `v_q(σ(3 ^ E)) = v_q(3 ^ (E + 1) - 1)`. Every other row is a square prime `s`, with
`s ^ 2 + s + 1 < 3 q ^ 2`; an odd quotient below 3 would give `s ^ 2 + s + 1 = q ^ 2`, which is
not a square, so the row sends at most 1. The senders are odd and below `2 q`, so distinct
senders have distinct residues modulo `q`, and at most two residues are roots of
`x ^ 2 + x + 1`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_special {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) :
    N.factorization q ≤ 2 + padicValNat q (3 ^ (N.factorization 3 + 1) - 1) := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hF : Fact q.Prime := ⟨hq⟩
  have h12 := F.mod12
  have hq2 : q ≠ 2 := by omega
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three, restrained_three_dvd h hq hodd hr hrq hsq, h.ne_zero⟩
  rw [← sigmaWeight_sum_eq h.perfect hq hq2, ← Finset.add_sum_erase _ _ h3m,
    sigmaWeight_eq_padicValNat _ _ hq, padicValNat_sigma_three_pow hq hq2]
  have hmemS : ∀ x ∈ (N.primeFactors.erase 3).filter (fun p => p ≠ q ∧ q ∣ phi3 p),
      x < 2 * q ∧ x % 2 = 1 ∧ q ∣ phi3 x := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_erase] at hx
    obtain ⟨⟨-, hxN⟩, -, hd⟩ := hx
    have := hbig x hxN
    have hxo : x % 2 = 1 := by
      rcases (Nat.prime_of_mem_primeFactors hxN).eq_two_or_odd with h2 | h2
      · have hdN : x ∣ N := Nat.dvd_of_mem_primeFactors hxN
        rw [h2] at hdN
        exact absurd hdN h.not_two_dvd
      · exact h2
    exact ⟨by omega, hxo, hd⟩
  have hcard : ((N.primeFactors.erase 3).filter (fun p => p ≠ q ∧ q ∣ phi3 p)).card ≤ 2 := by
    rw [← Finset.card_image_of_injOn (f := fun x : ℕ => (x : ZMod q))
      (fun x hx y hy hxy => eq_of_natCast_eq_of_odd (by omega) (hmemS x hx).1 (hmemS y hy).1
        (hmemS x hx).2.1 (hmemS y hy).2.1 hxy)]
    exact card_image_zmod_le_two_of_dvd_phi3 hq _ (fun x hx => (hmemS x hx).2.2)
  have hle : ∑ p ∈ N.primeFactors.erase 3, sigmaWeight N p q ≤
      ∑ p ∈ N.primeFactors.erase 3, if (p ≠ q ∧ q ∣ phi3 p) then 1 else 0 := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hp3, hpN⟩ := Finset.mem_erase.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hpN
    by_cases hpq : p = q
    · rw [hpq, sigmaWeight_self hq]
      exact Nat.zero_le _
    · rw [sigmaWeight_eq_padicValNat _ _ hq, F.sq p hpN hpq hp3, sigma_prime_sq hpp]
      split_ifs with hc
      · by_contra hgt
        have hpos : phi3 p ≠ 0 := by unfold phi3; omega
        obtain ⟨c, hc'⟩ : q ^ 2 ∣ phi3 p := (padicValNat_dvd_iff_le hpos).mpr (by omega)
        have hb := hbig p hpN
        have hq1 := hq.two_le
        have hsmall : phi3 p < 3 * q ^ 2 := by
          unfold phi3
          nlinarith [Nat.mul_le_mul hb hb]
        have hc3 : c < 3 := by
          by_contra h3
          have : q ^ 2 * 3 ≤ q ^ 2 * c := Nat.mul_le_mul_left _ (by omega)
          omega
        obtain ⟨j, hj⟩ := phi3_odd p
        interval_cases c
        · omega
        · exact not_isSquare_phi3 hpp.one_lt.le ⟨q, by rw [hc']; ring⟩
        · omega
      · exact (padicValNat.eq_zero_of_not_dvd (fun hd => hc ⟨hpq, hd⟩)).le
  have hle2 : ∑ p ∈ N.primeFactors.erase 3, sigmaWeight N p q ≤ 2 :=
    hle.trans (by rw [← Finset.card_filter]; exact hcard)
  omega

/-- **The special prime as largest prime.** In the restrained family, if every prime factor of
`N` is at most `q`, then `a ≤ 2 + v_q(3 ^ (E + 1) - 1)` (from `restrained_big_special`).
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_special {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) :
    N.factorization q ≤ 2 + padicValNat q (3 ^ (N.factorization 3 + 1) - 1) :=
  restrained_big_special h hq hodd hr hrq hsq fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega

/-- **Cube condition.** In the restrained family, if every prime factor `p` of `N` satisfies
`2 p + 1 ≤ 3 q`, `5 ≤ a` and `q ∤ E + 1`, then `3 ^ (q - 1) ≡ 1 (mod q ^ 3)`. This condition
is stronger than the Wieferich condition to the base 3.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_pow_modEq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) (h5 : 5 ≤ N.factorization q)
    (hndvd : ¬ q ∣ N.factorization 3 + 1) :
    3 ^ (q - 1) ≡ 1 [MOD q ^ 3] := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hF : Fact q.Prime := ⟨hq⟩
  have h12 := F.mod12
  have hC := restrained_big_special h hq hodd hr hrq hsq hbig
  have hv : 3 ≤ padicValNat q (3 ^ (N.factorization 3 + 1) - 1) := by omega
  have hqd : q ∣ 3 ^ (N.factorization 3 + 1) - 1 := dvd_of_one_le_padicValNat (by omega)
  have hord : orderOf (3 : ZMod q) ∣ N.factorization 3 + 1 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have h0 := (ZMod.natCast_eq_zero_iff (3 ^ (N.factorization 3 + 1) - 1) q).2 hqd
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), sub_eq_zero] at h0
    push_cast at h0
    exact h0
  have hA := padicValNat_three_pow_sub_one_eq hq (by omega) (by omega) hord (by omega)
  rw [padicValNat.eq_zero_of_not_dvd hndvd, add_zero] at hA
  obtain ⟨hd0, -, -⟩ := orderOf_three_facts hq (by omega)
  have hne : 3 ^ orderOf (3 : ZMod q) - 1 ≠ 0 := by
    have := Nat.one_lt_pow hd0.ne' (by norm_num : 1 < 3)
    omega
  have h3d : q ^ 3 ∣ 3 ^ orderOf (3 : ZMod q) - 1 := (padicValNat_dvd_iff_le hne).mpr (by omega)
  have hmod : 3 ^ orderOf (3 : ZMod q) ≡ 1 [MOD q ^ 3] :=
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h3d).symm
  have h30 : (3 : ZMod q) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : ZMod q) = 0 := by rw [Nat.cast_ofNat]; exact h0
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff _ _).1 h0')
    omega
  obtain ⟨k, hk⟩ := ZMod.orderOf_dvd_card_sub_one h30
  rw [hk, pow_mul]
  simpa using hmod.pow k

/-- **Largest special prime, cube condition.** In the restrained family, if every prime factor
of `N` is at most `q`, `5 ≤ a` and `q ∤ E + 1`, then `3 ^ (q - 1) ≡ 1 (mod q ^ 3)`. This
condition is stronger than the Wieferich condition to the base 3.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_pow_modEq {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) (h5 : 5 ≤ N.factorization q)
    (hndvd : ¬ q ∣ N.factorization 3 + 1) :
    3 ^ (q - 1) ≡ 1 [MOD q ^ 3] :=
  restrained_big_pow_modEq h hq hodd hr hrq hsq (fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega) h5 hndvd

/-- **The exponent of 3 is below the special prime.** In the restrained family, if every prime
factor `p` of `N` satisfies `2 p + 1 ≤ 3 q`, then `E + 1 < q`. With `E = 2 m`:
`v_q(3 ^ (E + 1) - 1) ≤ E` as `q > 3`, so `a + 1 ≤ 2 m + 3 < 3 ^ (m + 1)` and `v_3(a + 1) ≤ m`.
The column of 3 gives `E ≤ v_3(a + 1) + #T`, where `T` is the set of square primes
`s ≡ 1 (mod 3)`; these are `1` modulo 6 and at most `(3 q - 1) / 2`, so `#T ≤ (3 q - 1) / 12`,
and `m ≤ #T` gives `q ≥ 4 m + 1 = 2 E + 1`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_succ_lt {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) :
    N.factorization 3 + 1 < q := by
  obtain ⟨F, -, -⟩ := fam_of h hq hodd hr hrq hsq
  have hF : Fact q.Prime := ⟨hq⟩
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h12 := F.mod12
  have h6 := restrained_six_le_three h hq hodd hr hrq hsq
  obtain ⟨-, -, ⟨m, hm⟩, -⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  have hC := restrained_big_special h hq hodd hr hrq hsq hbig
  have hv : padicValNat q (3 ^ (N.factorization 3 + 1) - 1) ≤ N.factorization 3 := by
    by_contra hlt
    have h1 : 1 < 3 ^ (N.factorization 3 + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    have hd := Nat.le_of_dvd (by omega)
      (pow_padicValNat_dvd (p := q) (n := 3 ^ (N.factorization 3 + 1) - 1))
    have h2 : 3 ^ (N.factorization 3 + 1) ≤ q ^ (N.factorization 3 + 1) :=
      Nat.pow_le_pow_left (by have := hq.two_le; omega) _
    have h3 : q ^ (N.factorization 3 + 1) ≤
        q ^ padicValNat q (3 ^ (N.factorization 3 + 1) - 1) :=
      Nat.pow_le_pow_right hq.pos (by omega)
    omega
  have hw : padicValNat 3 (N.factorization q + 1) ≤ m := by
    by_contra hlt
    have hd := Nat.le_of_dvd (by omega)
      (pow_padicValNat_dvd (p := 3) (n := N.factorization q + 1))
    have h2 : 3 ^ (m + 1) ≤ 3 ^ padicValNat 3 (N.factorization q + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 := two_mul_add_three_lt_three_pow (m := m) (by omega)
    omega
  have hqN : q ∣ N := Nat.dvd_of_factorization_pos (by obtain ⟨j, hj⟩ := hodd; omega)
  have h3m : 3 ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_three, restrained_three_dvd h hq hodd hr hrq hsq, h.ne_zero⟩
  have hqm : q ∈ N.primeFactors.erase 3 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩⟩
  have hsum := sigmaWeight_sum_eq h.perfect Nat.prime_three (by decide)
  rw [← Finset.add_sum_erase _ _ h3m, sigmaWeight_self Nat.prime_three, zero_add,
    ← Finset.add_sum_erase _ _ hqm, sigmaWeight_eq_padicValNat N q Nat.prime_three,
    padicValNat_three_sigma_prime_pow_of_mod_one hq (by omega)] at hsum
  have hrest : ∑ p ∈ (N.primeFactors.erase 3).erase q, sigmaWeight N p 3 =
      (((N.primeFactors.erase 3).erase q).filter (fun p => p % 3 = 1)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpq, hp'⟩ := Finset.mem_erase.mp hp
    obtain ⟨hp3, hpN⟩ := Finset.mem_erase.mp hp'
    rw [sigmaWeight_eq_padicValNat _ _ Nat.prime_three, F.sq p hpN hpq hp3,
      sigma_prime_sq (Nat.prime_of_mem_primeFactors hpN), padicValNat_three_phi3]
  have hTc : (((N.primeFactors.erase 3).erase q).filter (fun p => p % 3 = 1)).card ≤
      (3 * q - 1) / 2 / 6 := by
    refine card_le_of_mod_six fun x hx => ?_
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_erase] at hx
    obtain ⟨⟨-, -, hxN⟩, hx1⟩ := hx
    have hb := hbig x hxN
    have hxp := Nat.prime_of_mem_primeFactors hxN
    have := hxp.two_le
    rcases hxp.eq_two_or_odd with h2 | h2
    · omega
    · omega
  omega

/-- In the restrained family, if every prime factor of `N` is at most `q`, then `E + 1 < q`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_succ_lt {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) :
    N.factorization 3 + 1 < q :=
  restrained_big_succ_lt h hq hodd hr hrq hsq fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega

/-- **Cube condition without the divisibility hypothesis.** In the restrained family, if every
prime factor `p` of `N` satisfies `2 p + 1 ≤ 3 q` and `1 < a`, then
`3 ^ (q - 1) ≡ 1 (mod q ^ 3)`: `a ≡ 1 (mod 4)` gives `5 ≤ a`, and `E + 1 < q` gives `q ∤ E + 1`.
This condition is stronger than the Wieferich condition to the base 3.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_big_pow_modEq_of_one_lt {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hbig : ∀ p ∈ N.primeFactors, 2 * p + 1 ≤ 3 * q) (ha : 1 < N.factorization q) :
    3 ^ (q - 1) ≡ 1 [MOD q ^ 3] := by
  have h4 := (special_mod_four h hq hodd).2
  have hlt := restrained_big_succ_lt h hq hodd hr hrq hsq hbig
  exact restrained_big_pow_modEq h hq hodd hr hrq hsq hbig (by omega)
    fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- In the restrained family, if every prime factor of `N` is at most `q` and `1 < a`, then
`3 ^ (q - 1) ≡ 1 (mod q ^ 3)`.
Conditional family result; whether this is in the literature was not verified. -/
theorem restrained_largest_pow_modEq_of_one_lt {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hmax : ∀ p ∈ N.primeFactors, p ≤ q) (ha : 1 < N.factorization q) :
    3 ^ (q - 1) ≡ 1 [MOD q ^ 3] :=
  restrained_big_pow_modEq_of_one_lt h hq hodd hr hrq hsq (fun p hp => by
    have := hmax p hp
    have := hq.two_le
    omega) ha

end OddPerfect

#print axioms OddPerfect.RestrainedThirteen.two_mul_sigma_three_pow_add_one'
#print axioms OddPerfect.RestrainedThirteen.padicValNat_sigma_three_pow
#print axioms OddPerfect.RestrainedThirteen.orderOf_natCast_facts
#print axioms OddPerfect.RestrainedThirteen.padicValNat_pow_sub_one_eq
#print axioms OddPerfect.RestrainedThirteen.orderOf_three_facts
#print axioms OddPerfect.RestrainedThirteen.padicValNat_three_pow_sub_one_eq
#print axioms OddPerfect.RestrainedThirteen.clock_le_factorization
#print axioms OddPerfect.RestrainedThirteen.eq_of_natCast_eq_of_odd
#print axioms OddPerfect.RestrainedThirteen.card_le_of_mod_six
#print axioms OddPerfect.RestrainedThirteen.two_mul_add_three_lt_three_pow
#print axioms OddPerfect.restrained_clock
#print axioms OddPerfect.restrained_clock_padicValNat_le_one
#print axioms OddPerfect.restrained_clock_not_dvd
#print axioms OddPerfect.restrained_clock_special
#print axioms OddPerfect.restrained_big_special
#print axioms OddPerfect.restrained_largest_special
#print axioms OddPerfect.restrained_big_pow_modEq
#print axioms OddPerfect.restrained_largest_pow_modEq
#print axioms OddPerfect.restrained_big_succ_lt
#print axioms OddPerfect.restrained_largest_succ_lt
#print axioms OddPerfect.restrained_big_pow_modEq_of_one_lt
#print axioms OddPerfect.restrained_largest_pow_modEq_of_one_lt
