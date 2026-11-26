import OddPerfect.SpecialBelowRows
import OddPerfect.EqualExponentsBound

/-!
# Orders of the row primes in the open shape of `q < m`

Let `N = q * m ^ 2` be an odd perfect number in Euler's form with `k = 1` and `q ∤ m`, in the
one shape left open by `special_lt_or_shape`: a prime `p ∣ m` with `e = v_p(N)`,
`2 m ^ 2 = p ^ e (q + 1)`, `σ(p ^ e) = q` and `σ((q + 1) / 2) = p ^ e`. By
`sigma_row_eq_prime_pow_of_shape`, every prime `r ∣ (q + 1) / 2` has `σ(r ^ g) = p ^ w` with
`g = v_r(N)` and `w ≥ 1`. For such a row, with `d` the multiplicative order of `p` modulo `r`:

* `odd_weight_of_shape`: `w` is odd.
* `orderOf_dvd_weight_of_shape`: `d ∣ w` and `d` is odd.
* `dvd_index_add_two_of_shape_of_mod_one`: if `p ≡ 1 (mod r)`, then `r ∣ e + 2`.
* `three_le_orderOf_of_shape`: if `p ≢ 1 (mod r)`, then `3 ≤ d`, `d ∤ e` and `3 ≤ w`.
* `padicValNat_orderOf_of_shape` and `not_dvd_weight_of_shape`: `v_r(p ^ d - 1) = 1` and
  `r ∤ w`.
* `mod_eq_one_of_shape_of_fermat`: if `r = 2 ^ k + 1`, then `p ≡ 1 (mod r)` and `r ∣ e + 2`.
* `prod_dvd_index_add_two_of_shape`: the product of the primes `r ∣ (q + 1) / 2` with
  `p ≡ 1 (mod r)` divides `e + 2`.

These statements sharpen the description of the shape; they do not exclude it, and `q < m`
stays open in this shape. They are derived from a step of the published proof on closed loops
of divisor sums (Dandapat, Hunsucker and Pomerance; see the module `ClosedLoop`). Whether they
are new was not checked. The odd perfect number conjecture is open, and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma sigma_succ_eq_one_add_mul {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- `σ(p ^ e)` cast to `ZMod r` is the geometric sum. -/
private lemma cast_sigma_prime_pow {p : ℕ} (hp : p.Prime) (e r : ℕ) :
    ((σ 1 (p ^ e) : ℕ) : ZMod r) = ∑ i ∈ Finset.range (e + 1), (p : ZMod r) ^ i := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rfl

/-- For a prime `r`, `(p : ZMod r) = 1` exactly when `p % r = 1`. -/
private lemma natCast_eq_one_iff_mod {r : ℕ} (hr : r.Prime) (p : ℕ) :
    (p : ZMod r) = 1 ↔ p % r = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' p 1 r
  rwa [Nat.cast_one, Nat.mod_eq_of_lt hr.one_lt] at h

/-- If `σ(r ^ a) = p ^ w` with `a ≠ 0`, then `p ^ w ≡ 1 (mod r)`. -/
private lemma pow_weight_eq_one {r a p w : ℕ} (hr : r.Prime) (ha : a ≠ 0)
    (hrow : σ 1 (r ^ a) = p ^ w) : (p : ZMod r) ^ w = 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hc := congrArg (fun n : ℕ => (n : ZMod r)) hrow
  simp only [sigma_succ_eq_one_add_mul hr, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_one, ZMod.natCast_self, zero_mul, add_zero] at hc
  exact hc.symm

/-- The weight is odd: an even weight forces `σ(3 ^ 4) = 11 ^ 2`, and then
`q = σ(11 ^ e) ≡ 1 (mod 3)` contradicts `3 ∣ q + 1`. -/
private lemma odd_weight_aux {r p g w e q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime)
    (hg : Even g) (hg0 : g ≠ 0) (hrow : σ 1 (r ^ g) = p ^ w) (he : Even e)
    (hσ : σ 1 (p ^ e) = q) (hrq : r ∣ q + 1) : Odd w := by
  rcases odd_weight_or_three_pow_four hr hr2 hg hg0 hp hrow with hodd | ⟨rfl, -, rfl, -⟩
  · exact hodd
  · exfalso
    obtain ⟨i, rfl⟩ := he
    have h1 := sigma_eleven_pow_two_mul_mod_three i
    rw [← two_mul] at hσ
    rw [hσ] at h1
    omega

/-- If `p ≡ 1 (mod r)`, `σ(p ^ e) = q` and `r ∣ q + 1`, then `r ∣ e + 2`. -/
private lemma dvd_add_two_of_mod_one {r p e q : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hpr : p % r = 1) (hσ : σ 1 (p ^ e) = q) (hrq : r ∣ q + 1) : r ∣ e + 2 := by
  have h1 : (p : ZMod r) = 1 := (natCast_eq_one_iff_mod hr p).mpr hpr
  have hq : (q : ZMod r) = ((e + 1 : ℕ) : ZMod r) := by
    rw [← hσ, cast_sigma_prime_pow hp, h1]
    simp
  rw [← ZMod.natCast_eq_zero_iff] at hrq ⊢
  push_cast at hrq hq ⊢
  rw [hq] at hrq
  rw [← hrq]
  ring

/-- If `p ≢ 1 (mod r)` for an odd prime `r`, `σ(p ^ e) = q` and `r ∣ q + 1`, then the order of
`p` modulo `r` does not divide `e`. -/
private lemma not_orderOf_dvd_index {r p e q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime)
    (hpr : p % r ≠ 1) (hσ : σ 1 (p ^ e) = q) (hrq : r ∣ q + 1) :
    ¬ orderOf (p : ZMod r) ∣ e := by
  have : Fact r.Prime := ⟨hr⟩
  intro hd
  have hpe : (p : ZMod r) ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have hp1 : (p : ZMod r) - 1 ≠ 0 := fun h =>
    hpr ((natCast_eq_one_iff_mod hr p).mp (sub_eq_zero.mp h))
  have hq : (q : ZMod r) * ((p : ZMod r) - 1) = 1 * ((p : ZMod r) - 1) := by
    rw [← hσ, cast_sigma_prime_pow hp, geom_sum_mul, pow_succ, hpe, one_mul, one_mul]
  have hq1 : (q : ZMod r) = 1 := mul_right_cancel₀ hp1 hq
  rw [← ZMod.natCast_eq_zero_iff] at hrq
  have h2 : ((2 : ℕ) : ZMod r) = 0 := by
    rw [← hrq]
    push_cast
    rw [hq1]
    norm_num
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)

/-- Lifting the exponent: if `σ(r ^ a) = p ^ w` with `a ≠ 0`, `w ≠ 0`, `r` an odd prime and
`r ≠ p`, then `v_r(p ^ d - 1) = 1` for the order `d` of `p` modulo `r`, and `r ∤ w`. -/
private lemma padicValNat_order_and_not_dvd {r p a w : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hp : p.Prime) (hrp : r ≠ p) (ha : a ≠ 0) (hrow : σ 1 (r ^ a) = p ^ w) (hw : w ≠ 0) :
    padicValNat r (p ^ orderOf (p : ZMod r) - 1) = 1 ∧ ¬ r ∣ w := by
  have : Fact r.Prime := ⟨hr⟩
  set d := orderOf (p : ZMod r) with hd
  have hdw : d ∣ w := orderOf_dvd_of_pow_eq_one (pow_weight_eq_one hr ha hrow)
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hdw
    exact hw hdw
  obtain ⟨u, hu⟩ := hdw
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hu
    exact hw hu
  have hrp' : ¬ r ∣ p := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp h)
  have hpz : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hrp'
  have hdr : d ∣ r - 1 := ZMod.orderOf_dvd_card_sub_one hpz
  have hdlt : d < r := by
    have := Nat.le_of_dvd (by have := hr.two_le; omega) hdr
    omega
  have hpd1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  have hrdvd : r ∣ p ^ d - 1 := by
    have h1 : ((p ^ d : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by
      push_cast
      exact pow_orderOf_eq_one _
    rw [ZMod.natCast_eq_natCast_iff] at h1
    exact (Nat.modEq_iff_dvd' hpd1.le).mp h1.symm
  have hrpd : ¬ r ∣ p ^ d := fun h => hrp' (hr.dvd_of_dvd_pow h)
  have hlte := padicValNat.pow_sub_pow (hr.odd_of_ne_two hr2) hpd1 hrdvd hrpd hu0
  rw [one_pow, ← pow_mul, ← hu] at hlte
  have hwne : p ^ w - 1 ≠ 0 := by
    have := Nat.one_lt_pow hw hp.one_lt
    omega
  have hle : padicValNat r (p ^ w - 1) < 2 := by
    by_contra hc
    push Not at hc
    apply not_sq_dvd_sigma_sub_one hr (a - 1)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha), hrow]
    exact (padicValNat_dvd_iff_le hwne).mpr (by rw [← Nat.padicValNat_def]; omega)
  have hpdne : p ^ d - 1 ≠ 0 := by omega
  have hv1 := one_le_padicValNat_of_dvd hpdne hrdvd
  simp only [Nat.padicValNat_def] at hle ⊢
  have hu' : multiplicity r u = 0 := by omega
  refine ⟨by omega, fun hrw => ?_⟩
  rw [hu] at hrw
  rcases (Nat.Prime.dvd_mul hr).mp hrw with h | h
  · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h) (by omega)
  · exact (dvd_iff_padicValNat_ne_zero hu0).mp h hu'

/-- The facts of the shape that the row lemmas use. -/
private theorem order_shape_facts {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2) :
    σ 1 (p ^ N.factorization p) = q ∧ Even (N.factorization p) ∧ r ≠ p ∧ r ≠ 2 ∧
      r ∣ q + 1 ∧ N.factorization r ≠ 0 ∧ Even (N.factorization r) := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hmN : m ∣ N := hN ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have he0 : 0 < N.factorization p := hp.factorization_pos_of_dvd h.ne_zero (hpm.trans hmN)
  have hI : eulerIndex q 1 m = p ^ N.factorization p := by
    have hi := sigma_special_mul_eulerIndex h hq hN1 hqm
    have hσq : σ 1 (q ^ 1) = q + 1 := by
      rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ, add_comm]
    rw [hσq, h2, mul_comm (p ^ _)] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega) hi
  obtain ⟨t, hmt, hpt, htodd, -, hqt, hσp, hqt2, -, -, heven, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hp he0 hI
  have hW : (q + 1) / 2 = t ^ 2 := by omega
  rw [hW] at hrW
  have ht0 : t ≠ 0 := htodd.pos.ne'
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hrt : r ∣ t := hr.dvd_of_dvd_pow hrW
  have hrp : r ≠ p := by rintro rfl; exact hpt hrt
  have hrq : r ≠ q := by rintro rfl; exact hqt hrt
  have hr2 : r ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr htodd) (even_iff_two_dvd.mpr hrt)
  have hrq' : ¬ r ∣ q := fun hd => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hd)
  have hrpe : ¬ r ∣ p ^ N.factorization p := fun hd =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd))
  have hpe0 : p ^ N.factorization p ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hNr : N.factorization r = 2 * t.factorization r := by
    have hN' : N = q * (p ^ N.factorization p * t ^ 2) := by rw [← hmt]; exact hN
    have hfa := congrArg (fun n => n.factorization r) hN'
    rw [hfa, Nat.factorization_mul hq.ne_zero (mul_ne_zero hpe0 ht2),
      Nat.factorization_mul hpe0 ht2, Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrq', Nat.factorization_eq_zero_of_not_dvd hrpe,
      zero_add, zero_add, Nat.factorization_pow]
    simp
  have hc0 : t.factorization r ≠ 0 := (hr.factorization_pos_of_dvd ht0 hrt).ne'
  exact ⟨hσp, heven, hrp, hr2, hrW.trans ⟨2, by omega⟩, by omega,
    ⟨t.factorization r, by omega⟩⟩

/-- **Odd weight.** In the exceptional shape of `special_lt_or_shape` (`N = q * m ^ 2`, `q ∤ m`,
a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`), a prime `r ∣ (q + 1) / 2`
with `σ(r ^ v_r(N)) = p ^ w` has `w` odd. A sharpening of the shape only; the shape is not
excluded. Derived from a step of the published proof on closed loops of divisor sums (module
`ClosedLoop`); novelty not verified. -/
theorem odd_weight_of_shape {N q m p r w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p ^ w) : Odd w := by
  obtain ⟨hσ, he, -, hr2, hrq, hg0, hg⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  exact odd_weight_aux hr hr2 hp hg hg0 hrow he hσ hrq

/-- **Order divides the weight.** In the exceptional shape of `special_lt_or_shape`, a prime
`r ∣ (q + 1) / 2` with `σ(r ^ v_r(N)) = p ^ w` has `ord_r(p) ∣ w`, and `ord_r(p)` is odd.
A sharpening of the shape only; the shape is not excluded. Derived from a step of the published
proof on closed loops of divisor sums (module `ClosedLoop`); novelty not verified. -/
theorem orderOf_dvd_weight_of_shape {N q m p r w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p ^ w) :
    orderOf (p : ZMod r) ∣ w ∧ Odd (orderOf (p : ZMod r)) := by
  obtain ⟨-, -, -, -, -, hg0, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  have hdw : orderOf (p : ZMod r) ∣ w := orderOf_dvd_of_pow_eq_one (pow_weight_eq_one hr hg0 hrow)
  exact ⟨hdw, (odd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow).of_dvd_nat hdw⟩

/-- **Rows with `p ≡ 1 (mod r)`.** In the exceptional shape of `special_lt_or_shape`, a prime
`r ∣ (q + 1) / 2` with `p % r = 1` divides `e + 2`, where `e = v_p(N)`. This holds for every
weight `w` of the row (it generalizes `dvd_index_add_two_of_shape` from `w = 1`), so no row
hypothesis is needed. A sharpening of the shape only; the shape is not excluded. Derived from a
step of the published proof on closed loops of divisor sums (module `ClosedLoop`); novelty not
verified. -/
theorem dvd_index_add_two_of_shape_of_mod_one {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hp1 : p % r = 1) : r ∣ N.factorization p + 2 := by
  obtain ⟨hσ, -, -, -, hrq, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  exact dvd_add_two_of_mod_one hr hp hp1 hσ hrq

/-- **Rows with `p ≢ 1 (mod r)`.** In the exceptional shape of `special_lt_or_shape`, a prime
`r ∣ (q + 1) / 2` with `σ(r ^ v_r(N)) = p ^ w` and `p % r ≠ 1` has `3 ≤ ord_r(p)`,
`ord_r(p) ∤ e` where `e = v_p(N)`, and `3 ≤ w`. A sharpening of the shape only; the shape is not
excluded. Derived from a step of the published proof on closed loops of divisor sums (module
`ClosedLoop`); novelty not verified. -/
theorem three_le_orderOf_of_shape {N q m p r w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p ^ w) (hp1 : p % r ≠ 1) :
    3 ≤ orderOf (p : ZMod r) ∧ ¬ orderOf (p : ZMod r) ∣ N.factorization p ∧ 3 ≤ w := by
  obtain ⟨hσ, -, -, hr2, hrq, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  obtain ⟨hdw, j, hj⟩ := orderOf_dvd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  have hw := odd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  have hd1 : orderOf (p : ZMod r) ≠ 1 := fun h1 =>
    hp1 ((natCast_eq_one_iff_mod hr p).mp (orderOf_eq_one_iff.mp h1))
  have hd3 : 3 ≤ orderOf (p : ZMod r) := by omega
  exact ⟨hd3, not_orderOf_dvd_index hr hr2 hp hp1 hσ hrq,
    hd3.trans (Nat.le_of_dvd hw.pos hdw)⟩

/-- **Valuation of the order power.** In the exceptional shape of `special_lt_or_shape`, a prime
`r ∣ (q + 1) / 2` with `σ(r ^ v_r(N)) = p ^ w` has `v_r(p ^ ord_r(p) - 1) = 1`. A sharpening of
the shape only; the shape is not excluded. Derived from a step of the published proof on closed
loops of divisor sums (module `ClosedLoop`); novelty not verified. -/
theorem padicValNat_orderOf_of_shape {N q m p r w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p ^ w) :
    padicValNat r (p ^ orderOf (p : ZMod r) - 1) = 1 := by
  obtain ⟨-, -, hrp, hr2, -, hg0, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  have hw := odd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  exact (padicValNat_order_and_not_dvd hr hr2 hp hrp hg0 hrow hw.pos.ne').1

/-- **The row prime does not divide the weight.** In the exceptional shape of
`special_lt_or_shape`, a prime `r ∣ (q + 1) / 2` with `σ(r ^ v_r(N)) = p ^ w` does not divide
`w`. A sharpening of the shape only; the shape is not excluded. Derived from a step of the
published proof on closed loops of divisor sums (module `ClosedLoop`); novelty not verified. -/
theorem not_dvd_weight_of_shape {N q m p r w : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p ^ w) : ¬ r ∣ w := by
  obtain ⟨-, -, hrp, hr2, -, hg0, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  have hw := odd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  exact (padicValNat_order_and_not_dvd hr hr2 hp hrp hg0 hrow hw.pos.ne').2

/-- **Fermat row primes.** In the exceptional shape of `special_lt_or_shape`, a prime
`r ∣ (q + 1) / 2` of the form `2 ^ k + 1` has `p % r = 1` and divides `e + 2`, where
`e = v_p(N)`. A sharpening of the shape only; the shape is not excluded. Derived from a step of
the published proof on closed loops of divisor sums (module `ClosedLoop`); novelty not
verified. -/
theorem mod_eq_one_of_shape_of_fermat {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hk : ∃ k, r = 2 ^ k + 1) : p % r = 1 ∧ r ∣ N.factorization p + 2 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, rfl⟩ := hk
  obtain ⟨-, -, hrp, -⟩ := order_shape_facts h hq hN hqm hp hpm h2 hr hrW
  obtain ⟨w, -, hrow⟩ := sigma_row_eq_prime_pow_of_shape h hq hN hqm hp hpm h2 hr hrW
  obtain ⟨-, hodd⟩ := orderOf_dvd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  have hpz : (p : ZMod (2 ^ k + 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp hd)
  have hdr := ZMod.orderOf_dvd_card_sub_one hpz
  rw [Nat.add_sub_cancel] at hdr
  have hcop : (orderOf (p : ZMod (2 ^ k + 1))).Coprime (2 ^ k) :=
    (Nat.coprime_two_right.mpr hodd).pow_right k
  have hd1 := Nat.Coprime.eq_one_of_dvd hcop hdr
  have hp1 : p % (2 ^ k + 1) = 1 := (natCast_eq_one_iff_mod hr p).mp (orderOf_eq_one_iff.mp hd1)
  exact ⟨hp1, dvd_index_add_two_of_shape_of_mod_one h hq hN hqm hp hpm h2 hr hrW hp1⟩

/-- **Product over the rows with `p ≡ 1 (mod r)`.** In the exceptional shape of
`special_lt_or_shape`, the product of the primes `r ∣ (q + 1) / 2` with `p % r = 1` divides
`e + 2`, where `e = v_p(N)`. A sharpening of the shape only; the shape is not excluded. Derived
from a step of the published proof on closed loops of divisor sums (module `ClosedLoop`);
novelty not verified. -/
theorem prod_dvd_index_add_two_of_shape {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    ∏ r ∈ ((q + 1) / 2).primeFactors.filter (fun r => p % r = 1), r ∣
      N.factorization p + 2 :=
  Finset.prod_primes_dvd _
    (fun r hr => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1).prime)
    (fun r hr => by
      obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp hr
      exact dvd_index_add_two_of_shape_of_mod_one h hq hN hqm hp hpm h2
        (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem) hpr)

end OddPerfect

#print axioms OddPerfect.odd_weight_of_shape
#print axioms OddPerfect.orderOf_dvd_weight_of_shape
#print axioms OddPerfect.dvd_index_add_two_of_shape_of_mod_one
#print axioms OddPerfect.three_le_orderOf_of_shape
#print axioms OddPerfect.padicValNat_orderOf_of_shape
#print axioms OddPerfect.not_dvd_weight_of_shape
#print axioms OddPerfect.mod_eq_one_of_shape_of_fermat
#print axioms OddPerfect.prod_dvd_index_add_two_of_shape
