import OddPerfect.AttackPrimality
import OddPerfect.ExponentCap

/-!
# The largest prime factor through the orders of its senders

Let `N` be an odd perfect number. A *sender* into a prime factor `q` is a prime factor
`p ≠ q` with `q ∣ σ(p ^ e_p)`; its order `d = ord_q(p)` divides `e_p + 1` and `q - 1`. For
ordinary `p` (even exponent) `d` is odd, and for the special prime `e_p + 1 ≡ 2 (mod 4)`; in
either case `4 ∤ d`. The weight of the edge is `v_q(σ(p ^ e_p))`, and the column identity
`e_q = Σ_p v_q(σ(p ^ e_p))` (`factorization_eq_sum_erase`) adds them up.

Primes of the form `q = 3 · 2 ^ j + 1` are rigid: a sender has order `3` or `6`. Order `3`
means `q ∣ p ^ 2 + p + 1`, order `6` means `q ∣ p ^ 2 - p + 1` and forces the sender to be
special. For `q = 3 · 4 ^ t + 1 = 12 y ^ 2 + 1` with `y = 2 ^ (t - 1)` the two roots of
`X ^ 2 + X + 1` modulo `q` are `a = 3 y (2 y - 1)` and `b = 3 y (2 y + 1)` (`a + b = q - 1`,
`a b - 1 = q (3 y ^ 2 - 1)`), and for `t ≥ 2` both are even.

Main results.

* `false_of_senders_odd`: no prime factor `q` can have all its senders of odd exponent and
  weight at most `1` (then `e_q ≤ 1` and `q` is special, or `q` is special and has no sender).
* `false_of_largest_of_cube_roots_even`: the largest prime factor `P` is not of the form
  `3 · 2 ^ j + 1` with both roots of `X ^ 2 + X + 1` below `P` even.
* `largest_prime_ne_three_mul_four_pow` (Target A): `P ≠ 3 · 4 ^ t + 1` for `t ≥ 2`.
* `le_largest_of_three_mul_four_pow_mem` (Target B): if `q = 3 · 4 ^ t + 1` (`t ≥ 2`) is any
  prime factor, then `P ≥ q + 3 · 2 ^ t (2 ^ t - 1) / 2`.
* `largest_prime_sub_one_ne_two_pow`: the largest prime factor is not a Fermat prime.
* `factorization_largest_le_two`: if `P - 1 = 3 · 2 ^ j`, then `e_P ≤ 2`.
* `largest_cube_roots_odd`: if moreover both roots are odd, every sender has order `3` and
  weight `1`, and either `e_P = 1` (so `P` is special) or `e_P = 2` and every root is a prime
  factor `r` of `N` with `3 ∣ e_r + 1`.
* `largest_three_mul_two_pow`: the roots share one parity, so the previous conclusion holds
  for every largest prime factor `P = 3 · 2 ^ j + 1`, with no parity hypothesis.

Controls. At `t = 1`, `P = 13` and the root `a = 3` is odd: `3 → 13` is a genuine edge
(`σ(3 ^ 2) = 13`), so `t ≥ 2` is needed in Target A. At `t = 3`, `P = 193` with roots `84` and
`108`. At `P = 19` (not of the form `3 · 2 ^ j + 1`) the two smaller primes `7` and `11` both
have order `3` (`Φ₃(7) = 3 · 19`, `Φ₃(11) = 7 · 19`); and `11` receives weight `2` from `3`
(`σ(3 ^ 4) = 121`), so the weight of an edge is not always `1`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-! ## Roots of `X ^ 2 ± X + 1` in `ZMod q` -/

section Roots

variable {q : ℕ} [Fact q.Prime]

private theorem sq_add_add_one_of_orderOf_eq_three {x : ZMod q} (h : orderOf x = 3) :
    x ^ 2 + x + 1 = 0 := by
  have h3 : x ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
  have h1 : x - 1 ≠ 0 := by
    rw [sub_ne_zero]; rintro rfl; rw [orderOf_one] at h; omega
  have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left h1

private theorem sq_sub_add_one_of_orderOf_eq_six {x : ZMod q} (h : orderOf x = 6) :
    x ^ 2 - x + 1 = 0 := by
  have h6 : x ^ 6 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
  have h3 : x ^ 3 + 1 = 0 := by
    have : (x ^ 3 - 1) * (x ^ 3 + 1) = 0 := by linear_combination h6
    refine (mul_eq_zero.mp this).resolve_left fun h0 => ?_
    have := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h0)
    rw [h] at this; norm_num at this
  have hx1 : x + 1 ≠ 0 := fun h0 => by
    have hx : x = -1 := eq_neg_of_add_eq_zero_left h0
    have : x ^ 2 = 1 := by rw [hx]; ring
    have := orderOf_dvd_of_pow_eq_one this
    rw [h] at this; norm_num at this
  have : (x + 1) * (x ^ 2 - x + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left hx1

private theorem cast_q_eq_zero {y : ℕ} (hq : q = 12 * y ^ 2 + 1) :
    12 * (y : ZMod q) ^ 2 + 1 = 0 := by
  have : ((12 * y ^ 2 + 1 : ℕ) : ZMod q) = 0 := by rw [← hq]; exact ZMod.natCast_self q
  exact_mod_cast this

private theorem cast_a {y : ℕ} (hy : 1 ≤ y) :
    ((3 * y * (2 * y - 1) : ℕ) : ZMod q) = 3 * y * (2 * y - 1) := by
  rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring

/-- With `q = 12 y ^ 2 + 1`, the roots of `X ^ 2 + X + 1` modulo `q` are `3 y (2 y - 1)` and
`3 y (2 y + 1)`. -/
private theorem cube_root_cases {y : ℕ} (hy : 1 ≤ y) (hq : q = 12 * y ^ 2 + 1) {x : ZMod q}
    (hx : x ^ 2 + x + 1 = 0) :
    x = ((3 * y * (2 * y - 1) : ℕ) : ZMod q) ∨ x = ((3 * y * (2 * y + 1) : ℕ) : ZMod q) := by
  have hq0 := cast_q_eq_zero hq
  have key : (x - ((3 * y * (2 * y - 1) : ℕ) : ZMod q)) *
      (x - ((3 * y * (2 * y + 1) : ℕ) : ZMod q)) = 0 := by
    rw [cast_a hy]; push_cast
    linear_combination hx + (-x + 3 * (y : ZMod q) ^ 2 - 1) * hq0
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- With `q = 12 y ^ 2 + 1`, the roots of `X ^ 2 - X + 1` modulo `q` are `3 y (2 y - 1) + 1`
and `3 y (2 y + 1) + 1`. -/
private theorem sixth_root_cases {y : ℕ} (hy : 1 ≤ y) (hq : q = 12 * y ^ 2 + 1) {x : ZMod q}
    (hx : x ^ 2 - x + 1 = 0) :
    x = ((3 * y * (2 * y - 1) + 1 : ℕ) : ZMod q) ∨
      x = ((3 * y * (2 * y + 1) + 1 : ℕ) : ZMod q) := by
  have hq0 := cast_q_eq_zero hq
  have key : (x - ((3 * y * (2 * y - 1) + 1 : ℕ) : ZMod q)) *
      (x - ((3 * y * (2 * y + 1) + 1 : ℕ) : ZMod q)) = 0 := by
    rw [Nat.cast_add (3 * y * (2 * y - 1)), cast_a hy]; push_cast
    linear_combination hx + (-x + 3 * (y : ZMod q) ^ 2) * hq0
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Two roots of `X ^ 2 + X + 1` in a field that are distinct add up to `-1`. -/
private theorem add_eq_neg_one_of_roots {x z : ZMod q} (hx : x ^ 2 + x + 1 = 0)
    (hz : z ^ 2 + z + 1 = 0) (hxz : x ≠ z) : x + z = -1 := by
  have : (x - z) * (x + z + 1) = 0 := by linear_combination hx - hz
  have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hxz)
  linear_combination this

end Roots

/-! ## Order and weight of a sender -/

private theorem eq_three_or_six {d : ℕ} (h6 : d ∣ 6) (h1 : d ≠ 1) (h2 : d ≠ 2) :
    d = 3 ∨ d = 6 := by
  have := Nat.le_of_dvd (by norm_num) h6
  interval_cases d <;> simp_all

/-- A sender into a prime `q` with `q - 1 = 3 · 2 ^ j` has order `3` or `6`, provided
`e + 1 < q`, `e` is even or `≡ 1 (mod 4)`, and `q ∤ p + 1`. Order `6` forces `e` odd. -/
theorem orderOf_eq_three_or_six {p q e j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hj : q - 1 = 3 * 2 ^ j) (hpq : p ≠ q) (hd : q ∣ σ 1 (p ^ e)) (he : e + 1 < q)
    (hpar : Even e ∨ e % 4 = 1) (hp1 : ¬ q ∣ p + 1) :
    orderOf (p : ZMod q) = 3 ∨ (orderOf (p : ZMod q) = 6 ∧ Odd e) := by
  have : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have hdq := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hj] at hdq
  have hde : orderOf (p : ZMod q) ∣ e + 1 ∧ orderOf (p : ZMod q) ≠ 1 := by
    have := (dvd_sigma_prime_pow_iff hp hq hpq).mp hd
    split_ifs at this with h1
    · exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · exact ⟨this, h1⟩
  have h4 : ¬ 4 ∣ orderOf (p : ZMod q) := fun h4 => by
    obtain ⟨c, hc⟩ := h4.trans hde.1
    rcases hpar with ⟨k, hk⟩ | hk <;> omega
  have h6 : orderOf (p : ZMod q) ∣ 6 := by
    obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hdq
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hz
    have hi : i ≤ 1 := by
      by_contra hi
      exact h4 (hyz ▸ Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega : 2 ≤ i)) y)
    rw [← hyz, show (6 : ℕ) = 3 * 2 ^ 1 by norm_num]
    exact mul_dvd_mul hy (pow_dvd_pow 2 hi)
  have h2 : orderOf (p : ZMod q) ≠ 2 := fun h2 => by
    have hsq : (p : ZMod q) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
    have hne1 : (p : ZMod q) ≠ 1 := fun h => hde.2 (by rw [h, orderOf_one])
    have : ((p : ZMod q) - 1) * ((p : ZMod q) + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact hne1 (sub_eq_zero.mp h)
    · exact hp1 ((ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact h))
  rcases eq_three_or_six h6 hde.2 h2 with h3 | h3
  · exact Or.inl h3
  · refine Or.inr ⟨h3, ?_⟩
    have := hde.1
    rw [h3] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨3 * c - 1, by omega⟩

private theorem padicValNat_quot_eq_zero {q e d : ℕ} (hd : d ∣ e + 1) (hd0 : 0 < d)
    (he : e + 1 < q) : padicValNat q ((e + 1) / d) = 0 := by
  rw [Nat.padicValNat_def]
  exact padicValNat.eq_zero_of_not_dvd fun h => by
    have := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (by omega) hd) hd0) h
    have := Nat.div_le_self (e + 1) d
    omega

/-- Weight of an order `3` sender: `v_q(σ(p ^ e)) = v_q(p ^ 2 + p + 1)` when `e + 1 < q`. -/
theorem padicValNat_sigma_of_orderOf_eq_three {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (h3 : orderOf (p : ZMod q) = 3) (hd : 3 ∣ e + 1)
    (he : e + 1 < q) :
    padicValNat q (σ 1 (p ^ e)) = padicValNat q (p ^ 2 + p + 1) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hp hq hq2 hpq (by rw [h3]; norm_num)
    (by rw [h3]; exact hd), h3, padicValNat_quot_eq_zero hd (by norm_num) he, add_zero]
  have hfac : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
    have := hp.one_lt
    zify [Nat.one_le_pow 3 p hp.pos, this.le]
    ring
  have hp1 : ¬ q ∣ p - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hp.one_lt.le, Nat.cast_one, sub_eq_zero]
    intro h; rw [h, orderOf_one] at h3; omega
  rw [hfac, Nat.padicValNat_def, Nat.padicValNat_def (n := p ^ 2 + p + 1),
    padicValNat.mul (by have := hp.one_lt; omega) (by positivity),
    padicValNat.eq_zero_of_not_dvd hp1, zero_add]

/-- Weight of an order `6` sender: `v_q(σ(p ^ e)) = v_q(p ^ 2 - p + 1)` when `e + 1 < q`. -/
theorem padicValNat_sigma_of_orderOf_eq_six {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (h6 : orderOf (p : ZMod q) = 6) (hd : 6 ∣ e + 1)
    (he : e + 1 < q) :
    padicValNat q (σ 1 (p ^ e)) = padicValNat q (p ^ 2 - p + 1) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [padicValNat_sigma_prime_pow_of_orderOf_dvd hp hq hq2 hpq (by rw [h6]; norm_num)
    (by rw [h6]; exact hd), h6, padicValNat_quot_eq_zero hd (by norm_num) he, add_zero]
  have hpp : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  have hfac : p ^ 6 - 1 = (p - 1) * (p + 1) * (p ^ 2 + p + 1) * (p ^ 2 - p + 1) := by
    have := hp.one_lt
    zify [Nat.one_le_pow 6 p hp.pos, this.le, hpp]
    ring
  have hA : ¬ q ∣ (p - 1) * (p + 1) * (p ^ 2 + p + 1) := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hp.one_lt.le]
    intro h0
    have h0' : ((p : ZMod q) ^ 3 - 1) * ((p : ZMod q) + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp h0' with h | h
    · have := orderOf_dvd_of_pow_eq_one (sub_eq_zero.mp h)
      rw [h6] at this; norm_num at this
    · have : (p : ZMod q) ^ 2 = 1 := by rw [eq_neg_of_add_eq_zero_left h]; ring
      have := orderOf_dvd_of_pow_eq_one this
      rw [h6] at this; norm_num at this
  have hp1 := hp.one_lt
  rw [hfac, Nat.padicValNat_def, Nat.padicValNat_def (n := p ^ 2 - p + 1),
    padicValNat.mul (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
    (by positivity)) (by omega), padicValNat.eq_zero_of_not_dvd hA,
    zero_add]

private theorem padicValNat_le_one {q n : ℕ} [Fact q.Prime] (hn : 0 < n) (hlt : n < q ^ 2) :
    padicValNat q n ≤ 1 := by
  by_contra hc
  have := (multiplicity_dvd_iff_le (p := q) hn.ne').mpr
    (show 2 ≤ multiplicity q n by rw [← Nat.padicValNat_def]; omega)
  exact absurd (Nat.le_of_dvd hn this) (by omega)

private theorem sq_sub_add_one_lt {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) :
    p ^ 2 - p + 1 < q ^ 2 := by
  have : p ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hpq (by norm_num)
  have : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  omega

private theorem sq_add_add_one_lt {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q) :
    p ^ 2 + p + 1 < q ^ 2 := by
  have h1 : p + 1 ≤ q := hpq
  have := Nat.mul_le_mul h1 h1
  rw [sq, sq]
  nlinarith

/-! ## The column of a prime factor -/

variable {N : ℕ}

private theorem ne_two_of_mem' (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p ≠ 2 := by
  rintro rfl
  exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)

private theorem mod_two_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    p % 2 = 1 :=
  Nat.odd_iff.mp (h.odd.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))

private theorem parity_of_mem (h : OddPerfect N) {p : ℕ} (hp : p ∈ N.primeFactors) :
    Even (N.factorization p) ∨ N.factorization p % 4 = 1 := by
  rcases Nat.even_or_odd (N.factorization p) with he | ho
  · exact Or.inl he
  · exact Or.inr (special_mod_four h (Nat.prime_of_mem_primeFactors hp) ho).2

/-- A column with only odd exponent senders of weight at most one is impossible. Let `q` be a
prime factor of the odd perfect number `N` such that every sender `p` (a prime factor
`p ≠ q` with `q ∣ σ(p ^ e_p)`) has odd exponent and `v_q(σ(p ^ e_p)) ≤ 1`. If `q` is special,
nothing sends into it and `e_q = 0`; otherwise only the special prime sends, so `e_q ≤ 1`,
against `e_q` even and positive. -/
theorem false_of_senders_odd (h : OddPerfect N) {q : ℕ} (hq : q ∈ N.primeFactors)
    (hsend : ∀ p ∈ N.primeFactors, p ≠ q → q ∣ σ 1 (p ^ N.factorization p) →
      Odd (N.factorization p) ∧ padicValNat q (σ 1 (p ^ N.factorization p)) ≤ 1) :
    False := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hsum := factorization_eq_sum_erase h.perfect hqp (ne_two_of_mem' h hq)
  have he1 : N.factorization q ≠ 0 := Finsupp.mem_support_iff.mp hq
  obtain ⟨s, hs, hsN, -, hs4, hev⟩ := exists_special_prime h
  -- a prime factor with even exponent contributes nothing
  have hzero : ∀ p ∈ N.primeFactors.erase q, Even (N.factorization p) →
      padicValNat q (σ 1 (p ^ N.factorization p)) = 0 := by
    intro p hp hpe
    obtain ⟨hpq, hpN⟩ := Finset.mem_erase.mp hp
    rw [Nat.padicValNat_def]
    refine padicValNat.eq_zero_of_not_dvd fun hd => ?_
    exact (Nat.not_even_iff_odd.mpr (hsend p hpN hpq hd).1) hpe
  by_cases hqs : q = s
  · subst hqs
    rw [Finset.sum_eq_zero fun p hp => hzero p hp
      (hev p (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
        (Finset.ne_of_mem_erase hp))] at hsum
    exact he1 hsum
  · have hqe := hev q hqp hqs
    have hsmem : s ∈ N.primeFactors.erase q :=
      Finset.mem_erase.mpr ⟨Ne.symm hqs, Nat.mem_primeFactors.mpr ⟨hs, hsN, h.ne_zero⟩⟩
    rw [Finset.sum_eq_single s (fun p hp hps => hzero p hp
      (hev p (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)) hps))
      (fun hn => absurd hsmem hn)] at hsum
    have hle : padicValNat q (σ 1 (s ^ N.factorization s)) ≤ 1 := by
      by_cases hd : q ∣ σ 1 (s ^ N.factorization s)
      · exact (hsend s (Finset.mem_of_mem_erase hsmem) (Ne.symm hqs) hd).2
      · rw [Nat.padicValNat_def, padicValNat.eq_zero_of_not_dvd hd]; exact Nat.zero_le _
    obtain ⟨k, hk⟩ := hqe
    omega

/-! ## The largest prime factor -/

/-- The largest prime factor `P` of an odd perfect number is not of the form
`3 · 2 ^ j + 1` with every root `r < P` of `X ^ 2 + X + 1` modulo `P` even. Senders have
order `3` or `6`; order `3` would make the sender a root, so all senders have order `6`, odd
exponent, and weight `v_P(p ^ 2 - p + 1) ≤ 1` (as `p < P`); `false_of_senders_odd` ends it. -/
theorem false_of_largest_of_cube_roots_even (h : OddPerfect N) {P j : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hj : P - 1 = 3 * 2 ^ j)
    (hev : ∀ r < P, P ∣ r ^ 2 + r + 1 → Even r) : False := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hP2 := mod_two_of_mem h hP
  refine false_of_senders_odd h hP fun p hp hpP hd => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hlt : p < P := lt_of_le_of_ne (hmax p hp) hpP
  have hp2 := mod_two_of_mem h hp
  have he := two_mul_factorization_add_three_le h hp hmax
  have hp1 : ¬ P ∣ p + 1 := fun hd1 => by
    have := Nat.le_of_dvd (by omega) hd1
    omega
  rcases orderOf_eq_three_or_six hpp hPp hj hpP hd (by omega) (parity_of_mem h hp) hp1 with
    h3 | ⟨h6, hodd⟩
  · have hx := sq_add_add_one_of_orderOf_eq_three h3
    have : P ∣ p ^ 2 + p + 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact hx)
    obtain ⟨k, hk⟩ := hev p hlt this
    omega
  · refine ⟨hodd, ?_⟩
    have hd6 : 6 ∣ N.factorization p + 1 := by
      have := (dvd_sigma_prime_pow_iff hpp hPp hpP).mp hd
      rw [if_neg (by rw [h6]; norm_num), h6] at this
      exact this
    rw [padicValNat_sigma_of_orderOf_eq_six hpp hPp (ne_two_of_mem' h hP) hpP h6 hd6
      (by omega)]
    exact padicValNat_le_one (by omega) (sq_sub_add_one_lt hpp.one_lt.le hlt)

private theorem three_mul_four_pow {t : ℕ} (ht : 1 ≤ t) :
    3 * 4 ^ t + 1 = 12 * (2 ^ (t - 1)) ^ 2 + 1 := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← pow_mul, pow_succ, mul_comm u 2, pow_mul]
  norm_num
  ring

private theorem even_y {t : ℕ} (ht : 2 ≤ t) : Even (2 ^ (t - 1)) :=
  (Nat.even_pow' (by omega)).mpr even_two

/-- Target A. For `t ≥ 2`, the largest prime factor of an odd perfect number is not
`3 · 4 ^ t + 1`. With `y = 2 ^ (t - 1)` the roots of `X ^ 2 + X + 1` modulo `P = 12 y ^ 2 + 1`
are `3 y (2 y - 1)` and `3 y (2 y + 1)`, both even since `y` is even. -/
theorem largest_prime_ne_three_mul_four_pow {N P t : ℕ} (h : OddPerfect N)
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (ht : 2 ≤ t) :
    P ≠ 3 * 4 ^ t + 1 := by
  intro hPt
  have : Fact P.Prime := ⟨Nat.prime_of_mem_primeFactors hP⟩
  set y := 2 ^ (t - 1) with hy
  have hy1 : 1 ≤ y := Nat.one_le_two_pow
  have hPy : P = 12 * y ^ 2 + 1 := by rw [hPt, three_mul_four_pow (by omega)]
  have hj : P - 1 = 3 * 2 ^ (2 * t) := by rw [hPt, pow_mul]; norm_num
  refine false_of_largest_of_cube_roots_even h hP hmax hj fun r hr hdr => ?_
  have hx : (r : ZMod P) ^ 2 + r + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hdr
    push_cast at this; exact this
  obtain ⟨c, hc⟩ := even_y ht
  rw [← hy] at hc
  have hb : 3 * y * (2 * y + 1) < P := by rw [hPy]; nlinarith
  have ha : 3 * y * (2 * y - 1) < P := lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (by omega)) hb
  rcases cube_root_cases hy1 hPy hx with hr' | hr' <;>
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by assumption)]
      at hr' <;> rw [hr', hc]
  · exact ⟨3 * c * (2 * (c + c) - 1), by ring⟩
  · exact ⟨3 * c * (2 * (c + c) + 1), by ring⟩

/-- Target B. If `q = 3 · 4 ^ t + 1` with `t ≥ 2` is a prime factor of an odd perfect number,
then the largest prime factor `P` satisfies `P ≥ q + 3 · 2 ^ t (2 ^ t - 1) / 2`. Otherwise
every sender into `q` lies below `q + a` with `a = 3 · 2 ^ t (2 ^ t - 1) / 2`: order `2` would
give `p = q - 1`, order `3` gives `p ∈ {a, b}` (even), and order `6` gives
`p ∈ {a + 1, b + 1}`, so `p < q` and the weight is at most one. -/
theorem le_largest_of_three_mul_four_pow_mem {N P q t : ℕ} (h : OddPerfect N)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hq : q ∈ N.primeFactors) (hqt : q = 3 * 4 ^ t + 1) (ht : 2 ≤ t) :
    q + 3 * 2 ^ t * (2 ^ t - 1) / 2 ≤ P := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  set y := 2 ^ (t - 1) with hy
  have hy1 : 1 ≤ y := Nat.one_le_two_pow
  have hqy : q = 12 * y ^ 2 + 1 := by rw [hqt, three_mul_four_pow (by omega)]
  have h2t : 2 ^ t = 2 * y := by
    rw [hy, ← pow_succ']; congr 1; omega
  have ha' : 3 * 2 ^ t * (2 ^ t - 1) / 2 = 3 * y * (2 * y - 1) := by
    rw [h2t, show 3 * (2 * y) * (2 * y - 1) = 2 * (3 * y * (2 * y - 1)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [ha']
  set a := 3 * y * (2 * y - 1) with ha
  set b := 3 * y * (2 * y + 1) with hb
  have hab : a + b + 1 = q := by
    rw [hqy, ha, hb]
    have h2y : 1 ≤ 2 * y := by omega
    zify [h2y]
    ring
  have hab' : a ≤ b := Nat.mul_le_mul_left _ (by omega)
  have hblt : b + 1 < q := by
    have : 1 ≤ a := by
      rw [ha]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨c, hc⟩ := even_y ht
  rw [← hy] at hc
  have haev : Even a := ⟨3 * c * (2 * (c + c) - 1), by rw [ha, hc]; ring⟩
  have hbev : Even b := ⟨3 * c * (2 * (c + c) + 1), by rw [hb, hc]; ring⟩
  by_contra hlt
  push Not at hlt
  have hq2 := mod_two_of_mem h hq
  refine false_of_senders_odd h hq fun p hp hpq hd => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpP := hmax p hp
  have hp2 := mod_two_of_mem h hp
  have he := two_mul_factorization_add_three_le h hp hmax
  have hp1 : ¬ q ∣ p + 1 := fun hd1 => by
    obtain ⟨k, hk⟩ := hd1
    rcases k with _ | _ | k
    · omega
    · omega
    · have := Nat.mul_le_mul_left q (show 2 ≤ k + 1 + 1 by omega); omega
  have hj : q - 1 = 3 * 2 ^ (2 * t) := by rw [hqt, pow_mul]; norm_num
  -- `p` as `q * (p / q) + p % q`
  have hdiv := Nat.div_add_mod p q
  have hpmod : ∀ m < q, (p : ZMod q) = (m : ℕ) → p % q = m := fun m hm hpm => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm] at hpm; exact hpm
  rcases orderOf_eq_three_or_six hpp hqp hj hpq hd (by omega) (parity_of_mem h hp) hp1 with
    h3 | ⟨h6, hodd⟩
  · exfalso
    rcases cube_root_cases hy1 hqy (sq_add_add_one_of_orderOf_eq_three h3) with hr | hr
    · have hm := hpmod a (by omega) hr
      rcases Nat.eq_zero_or_pos (p / q) with h0 | h0
      · rw [h0, hm] at hdiv; obtain ⟨k, hk⟩ := haev; omega
      · have := Nat.le_mul_of_pos_right q h0; omega
    · have hm := hpmod b (by omega) hr
      rcases Nat.eq_zero_or_pos (p / q) with h0 | h0
      · rw [h0, hm] at hdiv; obtain ⟨k, hk⟩ := hbev; omega
      · have := Nat.le_mul_of_pos_right q h0; omega
  · refine ⟨hodd, ?_⟩
    have hd6 : 6 ∣ N.factorization p + 1 := by
      have := (dvd_sigma_prime_pow_iff hpp hqp hpq).mp hd
      rw [if_neg (by rw [h6]; norm_num), h6] at this
      exact this
    have hplt : p < q := by
      rcases sixth_root_cases hy1 hqy (sq_sub_add_one_of_orderOf_eq_six h6) with hr | hr
      · have hm := hpmod (a + 1) (by omega) hr
        rcases Nat.eq_zero_or_pos (p / q) with h0 | h0
        · rw [h0, hm] at hdiv; omega
        · have := Nat.le_mul_of_pos_right q h0; omega
      · have hm := hpmod (b + 1) (by omega) hr
        rcases Nat.eq_zero_or_pos (p / q) with h0 | h0
        · rw [h0, hm] at hdiv; omega
        · have := Nat.le_mul_of_pos_right q h0; omega
    rw [padicValNat_sigma_of_orderOf_eq_six hpp hqp (ne_two_of_mem' h hq) hpq h6 hd6
      (by omega)]
    exact padicValNat_le_one (by omega) (sq_sub_add_one_lt hpp.one_lt.le hplt)

/-- The largest prime factor of an odd perfect number is not a Fermat prime: `P - 1` is not
a power of two. A sender `p < P` has order `d ≥ 3` (`exists_upward_edge_into_largest`) with
`d ∣ P - 1`, so `4 ∣ d ∣ e_p + 1`, impossible since `e_p` is even or `≡ 1 (mod 4)`. -/
theorem largest_prime_sub_one_ne_two_pow (h : OddPerfect N) {P : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (j : ℕ) :
    P - 1 ≠ 2 ^ j := by
  intro hj
  obtain ⟨p, hp, hlt, -, h3, hdv, -, -⟩ := exists_upward_edge_into_largest h hP hmax
  have : Fact P.Prime := ⟨Nat.prime_of_mem_primeFactors hP⟩
  have hp0 : (p : ZMod P) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hh
    have := Nat.le_of_dvd (Nat.prime_of_mem_primeFactors hp).pos hh
    omega
  have hdq := ZMod.orderOf_dvd_card_sub_one hp0
  rw [hj] at hdq
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdq
  have hi2 : 2 ≤ i := by
    by_contra hi2
    interval_cases i <;> rw [hi] at h3 <;> norm_num at h3
  have h4 : 4 ∣ N.factorization p + 1 := by
    refine dvd_trans ?_ hdv
    rw [hi, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact pow_dvd_pow 2 hi2
  obtain ⟨c, hc⟩ := h4
  rcases parity_of_mem h hp with ⟨k, hk⟩ | hk <;> omega

private theorem eq_of_natCast_eq {P a b : ℕ} (ha : a < P) (hb : b < P)
    (hab : (a : ZMod P) = b) : a = b := by
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab

/-- Data of a sender `p` into the largest prime factor `P` with `P - 1 = 3 · 2 ^ j`. -/
private theorem sender_largest (h : OddPerfect N) {P j p : ℕ} (hP : P ∈ N.primeFactors)
    (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hj : P - 1 = 3 * 2 ^ j) (hp : p ∈ N.primeFactors)
    (hpP : p ≠ P) (hd : P ∣ σ 1 (p ^ N.factorization p)) :
    p < P ∧ p % 2 = 1 ∧
      ((orderOf (p : ZMod P) = 3 ∧ 3 ∣ N.factorization p + 1 ∧
          padicValNat P (σ 1 (p ^ N.factorization p)) = padicValNat P (p ^ 2 + p + 1)) ∨
        (orderOf (p : ZMod P) = 6 ∧ Odd (N.factorization p) ∧
          padicValNat P (σ 1 (p ^ N.factorization p)) = padicValNat P (p ^ 2 - p + 1))) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hP2 := mod_two_of_mem h hP
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hlt : p < P := lt_of_le_of_ne (hmax p hp) hpP
  have hp2 := mod_two_of_mem h hp
  have he := two_mul_factorization_add_three_le h hp hmax
  have hp1 : ¬ P ∣ p + 1 := fun hd1 => by
    have := Nat.le_of_dvd (by omega) hd1
    omega
  have hdd := (dvd_sigma_prime_pow_iff hpp hPp hpP).mp hd
  refine ⟨hlt, hp2, ?_⟩
  rcases orderOf_eq_three_or_six hpp hPp hj hpP hd (by omega) (parity_of_mem h hp) hp1 with
    h3 | ⟨h6, hodd⟩
  · rw [if_neg (by rw [h3]; norm_num), h3] at hdd
    exact Or.inl ⟨h3, hdd, padicValNat_sigma_of_orderOf_eq_three hpp hPp
      (ne_two_of_mem' h hP) hpP h3 hdd (by omega)⟩
  · rw [if_neg (by rw [h6]; norm_num), h6] at hdd
    exact Or.inr ⟨h6, hodd, padicValNat_sigma_of_orderOf_eq_six hpp hPp
      (ne_two_of_mem' h hP) hpP h6 hdd (by omega)⟩

/-- The column of `P` as a sum over its senders. -/
private theorem sum_senders (h : OddPerfect N) {P : ℕ} (hP : P ∈ N.primeFactors) :
    N.factorization P = ∑ p ∈ (N.primeFactors.erase P).filter
      (fun p => P ∣ σ 1 (p ^ N.factorization p)), padicValNat P (σ 1 (p ^ N.factorization p)) := by
  rw [factorization_eq_sum_erase h.perfect (Nat.prime_of_mem_primeFactors hP)
    (ne_two_of_mem' h hP), Finset.sum_filter_of_ne]
  intro p _ hne
  by_contra hd
  exact hne (by rw [Nat.padicValNat_def]; exact padicValNat.eq_zero_of_not_dvd hd)

private theorem mem_senders {P p : ℕ} (hp : p ∈ (N.primeFactors.erase P).filter
    (fun p => P ∣ σ 1 (p ^ N.factorization p))) :
    p ∈ N.primeFactors ∧ p ≠ P ∧ P ∣ σ 1 (p ^ N.factorization p) := by
  rw [Finset.mem_filter, Finset.mem_erase] at hp
  exact ⟨hp.1.2, hp.1.1, hp.2⟩

/-- Capacity of the largest prime factor when `P - 1 = 3 · 2 ^ j`: `e_P ≤ 2`. Each sender has
order `3` or `6` and weight at most one; sending an order `3` sender `p` to `p` and an order
`6` sender to `-p` maps the senders injectively into the roots of `X ^ 2 + X + 1` modulo `P`
(two odd numbers below `P` do not add up to `P`), and there are at most two roots. -/
theorem factorization_largest_le_two (h : OddPerfect N) {P j : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hj : P - 1 = 3 * 2 ^ j) :
    N.factorization P ≤ 2 := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hP2 := mod_two_of_mem h hP
  have hsum := sum_senders h hP
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p)) with hS
  let f : ℕ → ZMod P := fun p =>
    if orderOf (p : ZMod P) = 3 then (p : ZMod P) else -(p : ZMod P)
  have hf : ∀ p ∈ S, f p ^ 2 + f p + 1 = 0 := by
    intro p hp
    obtain ⟨hpN, hpP, hd⟩ := mem_senders hp
    obtain ⟨-, -, h3 | h6⟩ := sender_largest h hP hmax hj hpN hpP hd
    · simp only [f, if_pos h3.1]; exact sq_add_add_one_of_orderOf_eq_three h3.1
    · simp only [f, if_neg (show orderOf (p : ZMod P) ≠ 3 by rw [h6.1]; norm_num)]
      linear_combination sq_sub_add_one_of_orderOf_eq_six h6.1
  have key2 : ∀ a b : ℕ, a < P → b < P → a % 2 = 1 → b % 2 = 1 →
      (a : ZMod P) = -(b : ZMod P) → False := by
    intro a b ha hb ha2 hb2 hab
    have : P ∣ a + b := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; rw [hab]; ring)
    obtain ⟨c, hc⟩ := this
    rcases c with _ | _ | c
    · omega
    · omega
    · have := Nat.mul_le_mul_left P (show 2 ≤ c + 1 + 1 by omega); omega
  have hinj : ∀ p ∈ S, ∀ p' ∈ S, f p = f p' → p = p' := by
    intro p hp p' hp' hff
    obtain ⟨hpN, hpP, hd⟩ := mem_senders hp
    obtain ⟨hp'N, hp'P, hd'⟩ := mem_senders hp'
    obtain ⟨hlt, hp2, -⟩ := sender_largest h hP hmax hj hpN hpP hd
    obtain ⟨hlt', hp2', -⟩ := sender_largest h hP hmax hj hp'N hp'P hd'
    simp only [f] at hff
    split_ifs at hff
    · exact eq_of_natCast_eq hlt hlt' hff
    · exact (key2 _ _ hlt hlt' hp2 hp2' hff).elim
    · exact (key2 _ _ hlt' hlt hp2' hp2 hff.symm).elim
    · exact eq_of_natCast_eq hlt hlt' (neg_inj.mp hff)
  have hcard : S.card ≤ 2 := by
    by_contra hc
    push Not at hc
    obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
    have e1 := add_eq_neg_one_of_roots (hf a ha) (hf b hb) fun e => hab (hinj a ha b hb e)
    have e2 := add_eq_neg_one_of_roots (hf a ha) (hf c hc') fun e => hac (hinj a ha c hc' e)
    exact hbc (hinj b hb c hc' (by linear_combination e1 - e2))
  have hle : ∑ p ∈ S, padicValNat P (σ 1 (p ^ N.factorization p)) ≤ S.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpN, hpP, hd⟩ := mem_senders hp
    obtain ⟨hlt, -, h3 | h6⟩ := sender_largest h hP hmax hj hpN hpP hd
    · rw [h3.2.2]
      exact padicValNat_le_one (by positivity)
        (sq_add_add_one_lt (Nat.prime_of_mem_primeFactors hpN).one_lt.le hlt)
    · rw [h6.2.2]
      exact padicValNat_le_one (by omega)
        (sq_sub_add_one_lt (Nat.prime_of_mem_primeFactors hpN).one_lt.le hlt)
  omega

/-- The odd root case. Let `P` be the largest prime factor, `P - 1 = 3 · 2 ^ j`, and suppose
every root `r < P` of `X ^ 2 + X + 1` modulo `P` is odd. Then every sender into `P` has order
`3`, `3 ∣ e_p + 1` and weight exactly `1` (an order `6` sender `p` would make the even number
`P - p` a root); and either `e_P = 1`, so `P` is the special prime, or `e_P = 2` and every
root `r < P` is a prime factor of `N` with `3 ∣ e_r + 1`. A sender may be the special prime
when `e_P = 2` (its exponent can be `≡ 5 (mod 12)`). -/
theorem largest_cube_roots_odd (h : OddPerfect N) {P j : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hj : P - 1 = 3 * 2 ^ j)
    (hodd : ∀ r < P, P ∣ r ^ 2 + r + 1 → Odd r) :
    (∀ p ∈ N.primeFactors, p ≠ P → P ∣ σ 1 (p ^ N.factorization p) →
      orderOf (p : ZMod P) = 3 ∧ 3 ∣ N.factorization p + 1 ∧
        padicValNat P (σ 1 (p ^ N.factorization p)) = 1) ∧
    (N.factorization P = 1 ∨ (N.factorization P = 2 ∧
      ∀ r < P, P ∣ r ^ 2 + r + 1 → r ∈ N.primeFactors ∧ 3 ∣ N.factorization r + 1)) := by
  have hPp := Nat.prime_of_mem_primeFactors hP
  have : Fact P.Prime := ⟨hPp⟩
  have hP2 := mod_two_of_mem h hP
  have hsend : ∀ p ∈ N.primeFactors, p ≠ P → P ∣ σ 1 (p ^ N.factorization p) →
      orderOf (p : ZMod P) = 3 ∧ 3 ∣ N.factorization p + 1 ∧
        padicValNat P (σ 1 (p ^ N.factorization p)) = 1 := by
    intro p hp hpP hd
    obtain ⟨hlt, hp2, h3 | ⟨h6, -, -⟩⟩ := sender_largest h hP hmax hj hp hpP hd
    · refine ⟨h3.1, h3.2.1, ?_⟩
      rw [h3.2.2]
      have hdv : P ∣ p ^ 2 + p + 1 := (ZMod.natCast_eq_zero_iff _ _).mp
        (by push_cast; exact sq_add_add_one_of_orderOf_eq_three h3.1)
      have := padicValNat_le_one (q := P) (by positivity) (sq_add_add_one_lt (by omega) hlt)
      have := one_le_padicValNat_of_dvd (by positivity) hdv
      rw [← Nat.padicValNat_def] at this
      omega
    · exfalso
      have hx := sq_sub_add_one_of_orderOf_eq_six h6
      have hdv : P ∣ (P - p) ^ 2 + (P - p) + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast [Nat.cast_sub hlt.le]
        rw [ZMod.natCast_self]
        linear_combination hx
      obtain ⟨k, hk⟩ := hodd (P - p) (by omega) hdv
      omega
  refine ⟨hsend, ?_⟩
  have hsum := sum_senders h hP
  set S := (N.primeFactors.erase P).filter (fun p => P ∣ σ 1 (p ^ N.factorization p)) with hS
  have hcardeq : N.factorization P = S.card := by
    rw [hsum, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpN, hpP, hd⟩ := mem_senders hp
    exact (hsend p hpN hpP hd).2.2
  have hle := factorization_largest_le_two h hP hmax hj
  have h0 : N.factorization P ≠ 0 := Finsupp.mem_support_iff.mp hP
  rcases (by omega : N.factorization P = 1 ∨ N.factorization P = 2) with h1 | h2
  · exact Or.inl h1
  · refine Or.inr ⟨h2, fun r hr hdr => ?_⟩
    obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp (show S.card = 2 by omega)
    have ha : a ∈ S := by rw [hSab]; simp
    have hb : b ∈ S := by rw [hSab]; simp
    have hroot : ∀ p ∈ S, (p : ZMod P) ^ 2 + p + 1 = 0 := fun p hp => by
      obtain ⟨hpN, hpP, hd⟩ := mem_senders hp
      exact sq_add_add_one_of_orderOf_eq_three (hsend p hpN hpP hd).1
    have hltS : ∀ p ∈ S, p < P := fun p hp => by
      obtain ⟨hpN, hpP, -⟩ := mem_senders hp
      exact lt_of_le_of_ne (hmax p hpN) hpP
    have hrr : (r : ZMod P) ^ 2 + r + 1 = 0 := by
      have := (ZMod.natCast_eq_zero_iff _ _).mpr hdr
      push_cast at this; exact this
    suffices hrS : r ∈ S by
      obtain ⟨hrN, hrP, hd⟩ := mem_senders hrS
      exact ⟨hrN, (hsend r hrN hrP hd).2.1⟩
    by_contra hrS
    have e1 := add_eq_neg_one_of_roots hrr (hroot a ha)
      fun e => hrS (eq_of_natCast_eq hr (hltS a ha) e ▸ ha)
    have e2 := add_eq_neg_one_of_roots hrr (hroot b hb)
      fun e => hrS (eq_of_natCast_eq hr (hltS b hb) e ▸ hb)
    exact hab (eq_of_natCast_eq (hltS a ha) (hltS b hb) (by linear_combination e1 - e2))

/-- Two roots `r, r' < P` of `X ^ 2 + X + 1` modulo an odd prime `P` have the same parity:
if they differ, `r + r' + 1 = P`. -/
private theorem roots_same_parity {P r r' : ℕ} [Fact P.Prime] (hP2 : P % 2 = 1) (hr : r < P)
    (hr' : r' < P) (h1 : P ∣ r ^ 2 + r + 1) (h2 : P ∣ r' ^ 2 + r' + 1) : r % 2 = r' % 2 := by
  by_cases hrr : r = r'
  · rw [hrr]
  have hx : (r : ZMod P) ^ 2 + r + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h1
    push_cast at this; exact this
  have hz : (r' : ZMod P) ^ 2 + r' + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr h2
    push_cast at this; exact this
  have hs := add_eq_neg_one_of_roots hx hz fun e => hrr (eq_of_natCast_eq hr hr' e)
  have : P ∣ r + r' + 1 :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; linear_combination hs)
  obtain ⟨c, hc⟩ := this
  rcases c with _ | _ | c
  · omega
  · omega
  · have := Nat.mul_le_mul_left P (show 2 ≤ c + 1 + 1 by omega); omega

/-- Structure of the largest prime factor `P` with `P - 1 = 3 · 2 ^ j`, with no parity
hypothesis. The roots below `P` of `X ^ 2 + X + 1` modulo `P` share one parity
(`roots_same_parity`); an even root is excluded by `false_of_largest_of_cube_roots_even`, so
they are all odd and `largest_cube_roots_odd` applies: every sender has order `3` and weight
`1`, and either `e_P = 1` or `e_P = 2` and every root is a prime factor `r` with
`3 ∣ e_r + 1`. -/
theorem largest_three_mul_two_pow (h : OddPerfect N) {P j : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P) (hj : P - 1 = 3 * 2 ^ j) :
    (∀ p ∈ N.primeFactors, p ≠ P → P ∣ σ 1 (p ^ N.factorization p) →
      orderOf (p : ZMod P) = 3 ∧ 3 ∣ N.factorization p + 1 ∧
        padicValNat P (σ 1 (p ^ N.factorization p)) = 1) ∧
    (N.factorization P = 1 ∨ (N.factorization P = 2 ∧
      ∀ r < P, P ∣ r ^ 2 + r + 1 → r ∈ N.primeFactors ∧ 3 ∣ N.factorization r + 1)) := by
  have : Fact P.Prime := ⟨Nat.prime_of_mem_primeFactors hP⟩
  have hP2 := mod_two_of_mem h hP
  refine largest_cube_roots_odd h hP hmax hj fun r hr hdr => ?_
  by_contra hno
  have hre : r % 2 = 0 := by
    rcases Nat.even_or_odd r with ⟨k, hk⟩ | ho
    · omega
    · exact absurd ho hno
  refine false_of_largest_of_cube_roots_even h hP hmax hj fun r' hr' hdr' => ?_
  have := roots_same_parity hP2 hr hr' hdr hdr'
  exact ⟨r' / 2, by omega⟩

/-! ## Controls -/

/-- `t = 1`: `P = 13`, the root `3` is odd and `σ(3 ^ 2) = 13`. -/
example : 13 = 3 * 4 ^ 1 + 1 ∧ 1 + 3 + 3 ^ 2 = 13 ∧ 13 ∣ 3 ^ 2 + 3 + 1 ∧ ¬ Even 3 := by decide

/-- `t = 3`: `P = 193` with the even roots `84 = 3 · 4 · 7` and `108 = 3 · 4 · 9`. -/
example : 193 = 3 * 4 ^ 3 + 1 ∧ 193 ∣ 84 ^ 2 + 84 + 1 ∧ 193 ∣ 108 ^ 2 + 108 + 1 := by
  norm_num

/-- Kill tests: `Φ₃(7) = 3 · 19`, `Φ₃(11) = 7 · 19`, and `σ(3 ^ 4) = 11 ^ 2`. -/
example : 7 ^ 2 + 7 + 1 = 3 * 19 ∧ 11 ^ 2 + 11 + 1 = 7 * 19 ∧
    1 + 3 + 3 ^ 2 + 3 ^ 3 + 3 ^ 4 = 11 ^ 2 := by norm_num

end OddPerfect

#print axioms OddPerfect.orderOf_eq_three_or_six
#print axioms OddPerfect.padicValNat_sigma_of_orderOf_eq_three
#print axioms OddPerfect.padicValNat_sigma_of_orderOf_eq_six
#print axioms OddPerfect.false_of_senders_odd
#print axioms OddPerfect.false_of_largest_of_cube_roots_even
#print axioms OddPerfect.largest_prime_ne_three_mul_four_pow
#print axioms OddPerfect.le_largest_of_three_mul_four_pow_mem
#print axioms OddPerfect.largest_prime_sub_one_ne_two_pow
#print axioms OddPerfect.factorization_largest_le_two
#print axioms OddPerfect.largest_cube_roots_odd
#print axioms OddPerfect.largest_three_mul_two_pow
