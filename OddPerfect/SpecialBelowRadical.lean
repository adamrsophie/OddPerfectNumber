import OddPerfect.SpecialBelowOrder

/-!
# The radical of the row part in the open shape of `q < m`

Let `N = q * m ^ 2` be an odd perfect number in Euler's form with `k = 1` and `q ∤ m`, in the
one shape left open by `special_lt_or_shape`: a prime `p ∣ m` with `e = v_p(N)`,
`2 m ^ 2 = p ^ e (q + 1)`, `σ(p ^ e) = q` and `σ(W) = p ^ e` for `W = (q + 1) / 2`. Write
`rad W` for the product of the primes dividing `W`.

* `div_two_mod_of_shape`: `W ≡ 1 (mod p)`.
* `prod_primeFactors_mod_of_shape`: `rad W ≡ 1 (mod p)`.
* `two_mul_add_one_le_prod_primeFactors_of_shape`: `2 p + 1 ≤ rad W`.
* `exists_row_not_mod_one_of_shape`: some prime `r ∣ W` has `p % r ≠ 1`; for it
  `σ(r ^ v_r(N)) = p ^ w` with `3 ≤ w`, the order `d` of `p` modulo `r` has `3 ≤ d` and
  `d ∤ e`, and `7 ≤ r`.
* `special_lt_of_noOrderPureRow`: `q < m` under the hypothesis `NoOrderPureRow`, which asks
  less than `NoHighPureRow` (`noOrderPureRow_of_noHighPureRow`). Both are unproved hypotheses.

The argument: each prime `r ∣ W` has `σ(r ^ g) = p ^ w` with `g = v_r(N) = v_r(W)` and `w ≥ 1`,
and `(r - 1) σ(r ^ g) = r ^ (g + 1) - 1`, so `r ^ (g + 1) ≡ 1 (mod p)`. Multiplying over the
primes of `W` gives `W rad W ≡ 1 (mod p)`. Also `q = σ(p ^ e) ≡ 1 (mod p)` and `2 W = q + 1`
with `p` odd, so `W ≡ 1` and `rad W ≡ 1 (mod p)`. If every prime `r ∣ W` had `p ≡ 1 (mod r)`,
then `rad W ∣ p - 1`, so `1 < rad W < p`, against `rad W ≡ 1 (mod p)`. For a prime `r` with
`p ≢ 1 (mod r)`, the order `d` is odd, at least `3` and divides the even number `r - 1`, so
`2 d ∣ r - 1` and `r ≥ 7`.

These statements sharpen the description of the shape; they do not exclude it, and `q < m`
stays open in this shape. Whether they are new was not checked. The odd perfect number
conjecture is open, and nothing here decides it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma sigma_succ_eq_one_add_mul_rad {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- For a prime `p`, `(n : ZMod p) = 1` exactly when `n % p = 1`. -/
private lemma cast_eq_one_iff_mod_rad {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (n : ZMod p) = 1 ↔ n % p = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' n 1 p
  rwa [Nat.cast_one, Nat.mod_eq_of_lt hp.one_lt] at h

/-- If `σ(r ^ g) = p ^ w` with `w ≥ 1`, then `r ^ (g + 1) ≡ 1 (mod p)`. -/
private lemma pow_succ_eq_one_of_row {r g p w : ℕ} (hr : r.Prime) (hw : 1 ≤ w)
    (hrow : σ 1 (r ^ g) = p ^ w) : (r : ZMod p) ^ (g + 1) = 1 := by
  have hc : ((σ 1 (r ^ g) : ℕ) : ZMod p) = ((p ^ w : ℕ) : ZMod p) := by rw [hrow]
  rw [sigma_one_apply_prime_pow hr] at hc
  push_cast [ZMod.natCast_self] at hc
  rw [zero_pow (by omega)] at hc
  have hg := geom_sum_mul (r : ZMod p) (g + 1)
  rw [hc, zero_mul] at hg
  exact (sub_eq_zero.mp hg.symm)

/-- If `r ^ (v_r(W) + 1) ≡ 1 (mod p)` for every prime `r ∣ W`, then `W rad W ≡ 1 (mod p)`. -/
private lemma cast_mul_prod_primeFactors {W p : ℕ} (hW : W ≠ 0)
    (hrow : ∀ r ∈ W.primeFactors, (r : ZMod p) ^ (W.factorization r + 1) = 1) :
    (W : ZMod p) * ∏ r ∈ W.primeFactors, (r : ZMod p) = 1 := by
  have hWp : (W : ZMod p) = ∏ r ∈ W.primeFactors, (r : ZMod p) ^ W.factorization r := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hW]
    rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hWp, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun r hr => by rw [← pow_succ]; exact hrow r hr)

/-- The product of the primes dividing `W > 1` exceeds `1`. -/
private lemma one_lt_prod_primeFactors {W : ℕ} (hW : 1 < W) :
    1 < ∏ r ∈ W.primeFactors, r := by
  obtain ⟨r, hr, hrW⟩ := Nat.exists_prime_and_dvd (show W ≠ 1 by omega)
  have hmem : r ∈ W.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrW, by omega⟩
  have hpos : 0 < ∏ r ∈ W.primeFactors, r :=
    Finset.prod_pos (fun s hs => (Nat.prime_of_mem_primeFactors hs).pos)
  have hle := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem (fun s => s) hmem)
  have := hr.two_le
  omega

/-- The facts of the shape used here: `σ(p ^ e) = q`, `e > 0`, `2 W = q + 1`, `W` odd, `W > 1`,
`p` odd, and `v_r(N) = v_r(W)` for every prime `r ∣ W`. -/
private theorem radical_shape_facts {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    σ 1 (p ^ N.factorization p) = q ∧ 0 < N.factorization p ∧ q + 1 = 2 * ((q + 1) / 2) ∧
      Odd ((q + 1) / 2) ∧ 1 < (q + 1) / 2 ∧ p ≠ 2 ∧
      ∀ r, r.Prime → r ∣ (q + 1) / 2 → N.factorization r = ((q + 1) / 2).factorization r := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hmN : m ∣ N := hN ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have he0 : 0 < N.factorization p := hp.factorization_pos_of_dvd h.ne_zero (hpm.trans hmN)
  have hI : eulerIndex q 1 m = p ^ N.factorization p := by
    have hi := sigma_special_mul_eulerIndex h hq hN1 hqm
    have hσq : σ 1 (q ^ 1) = q + 1 := by
      rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ, add_comm]
    rw [hσq, h2, mul_comm (p ^ _)] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega) hi
  obtain ⟨t, hmt, hpt, htodd, ht1, hqt, hσp, hqt2, -, -, -, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hp he0 hI
  have hW : (q + 1) / 2 = t ^ 2 := by omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.odd) (even_iff_two_dvd.mpr (hpm.trans hmN))
  refine ⟨hσp, he0, by omega, by rw [hW]; exact htodd.pow, by
    rw [hW]; exact Nat.one_lt_pow two_ne_zero ht1, hp2, ?_⟩
  intro r hr hrW
  rw [hW] at hrW ⊢
  have ht0 : t ≠ 0 := htodd.pos.ne'
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hrt : r ∣ t := hr.dvd_of_dvd_pow hrW
  have hrp : r ≠ p := by rintro rfl; exact hpt hrt
  have hrq : r ≠ q := by rintro rfl; exact hqt hrt
  have hrq' : ¬ r ∣ q := fun hd => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hd)
  have hrpe : ¬ r ∣ p ^ N.factorization p := fun hd =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd))
  have hpe0 : p ^ N.factorization p ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hN' : N = q * (p ^ N.factorization p * t ^ 2) := by rw [← hmt]; exact hN
  have hfa := congrArg (fun n => n.factorization r) hN'
  rw [hfa, Nat.factorization_mul hq.ne_zero (mul_ne_zero hpe0 ht2),
    Nat.factorization_mul hpe0 ht2, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hrq', Nat.factorization_eq_zero_of_not_dvd hrpe,
    zero_add, zero_add]

/-- The two congruences of the shape, `W ≡ 1` and `rad W ≡ 1 (mod p)`, with `W` odd, `W > 1`
and `p` odd. -/
private theorem radical_of_shape {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    (q + 1) / 2 % p = 1 ∧ (∏ r ∈ ((q + 1) / 2).primeFactors, r) % p = 1 ∧
      Odd ((q + 1) / 2) ∧ 1 < (q + 1) / 2 ∧ p ≠ 2 := by
  obtain ⟨hσp, he0, hW2, hWodd, hW1, hp2, hfac⟩ := radical_shape_facts h hq hN hqm hp hpm h2
  have hrow : ∀ r ∈ ((q + 1) / 2).primeFactors,
      (r : ZMod p) ^ (((q + 1) / 2).factorization r + 1) = 1 := by
    intro r hr
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hrW := Nat.dvd_of_mem_primeFactors hr
    obtain ⟨w, hw, hσr⟩ := sigma_row_eq_prime_pow_of_shape h hq hN hqm hp hpm h2 hrp hrW
    rw [hfac r hrp hrW] at hσr
    exact pow_succ_eq_one_of_row hrp hw hσr
  have hprod := cast_mul_prod_primeFactors (show (q + 1) / 2 ≠ 0 by omega) hrow
  set W := (q + 1) / 2 with hWdef
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : (q : ZMod p) = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, N.factorization p = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos he0).symm⟩
    rw [← hσp, hj, sigma_succ_eq_one_add_mul_rad hp]
    simp
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h0')
  have hWc : (W : ZMod p) = 1 := by
    have hc : ((q + 1 : ℕ) : ZMod p) = ((2 * W : ℕ) : ZMod p) := by rw [← hW2]
    push_cast at hc
    rw [hq1] at hc
    apply mul_left_cancel₀ h2ne
    rw [← hc]
    norm_num
  have hRc : ((∏ r ∈ W.primeFactors, r : ℕ) : ZMod p) = 1 := by
    rw [hWc, one_mul] at hprod
    rw [Nat.cast_prod]
    exact hprod
  exact ⟨(cast_eq_one_iff_mod_rad hp _).mp hWc, (cast_eq_one_iff_mod_rad hp _).mp hRc, hWodd,
    hW1, hp2⟩

/-- **`W ≡ 1 (mod p)`.** In the exceptional shape of `special_lt_or_shape` (`N = q * m ^ 2`,
`q ∤ m`, a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`), `(q + 1) / 2` is
`1` modulo `p`. A sharpening of the shape only; the shape is not excluded. Novelty not
verified. -/
theorem div_two_mod_of_shape {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    (q + 1) / 2 % p = 1 :=
  (radical_of_shape h hq hN hqm hp hpm h2).1

/-- **The radical of `W` is `1` modulo `p`.** In the exceptional shape of `special_lt_or_shape`
(`N = q * m ^ 2`, `q ∤ m`, a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`),
the product of the primes dividing `(q + 1) / 2` is `1` modulo `p`. A sharpening of the shape
only; the shape is not excluded. Novelty not verified. -/
theorem prod_primeFactors_mod_of_shape {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    (∏ r ∈ ((q + 1) / 2).primeFactors, r) % p = 1 :=
  (radical_of_shape h hq hN hqm hp hpm h2).2.1

/-- **Size of the radical.** In the exceptional shape of `special_lt_or_shape`, the product of
the primes dividing `(q + 1) / 2` is at least `2 p + 1`: it is odd, above `1` and `1` modulo
`p`. A sharpening of the shape only; the shape is not excluded. Novelty not verified. -/
theorem two_mul_add_one_le_prod_primeFactors_of_shape {N q m p : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    2 * p + 1 ≤ ∏ r ∈ ((q + 1) / 2).primeFactors, r := by
  obtain ⟨-, hrad, hWodd, hW1, hp2⟩ := radical_of_shape h hq hN hqm hp hpm h2
  have hR1 := one_lt_prod_primeFactors hW1
  have hRodd : Odd (∏ r ∈ ((q + 1) / 2).primeFactors, r) :=
    hWodd.of_dvd_nat (Nat.prod_primeFactors_dvd _)
  set R := ∏ r ∈ ((q + 1) / 2).primeFactors, r with hR
  have hdm := Nat.div_add_mod R p
  rw [hrad] at hdm
  obtain ⟨c, hc⟩ : ∃ c, R / p = c := ⟨_, rfl⟩
  rw [hc] at hdm
  obtain ⟨a, ha⟩ := hRodd
  obtain ⟨b, hb⟩ := hp.odd_of_ne_two hp2
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · interval_cases c <;> omega
  · have := Nat.mul_le_mul_left p hc2
    omega

/-- Some prime `r ∣ (q + 1) / 2` has `p % r ≠ 1`. -/
private theorem exists_mem_not_mod_one {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    ∃ r ∈ ((q + 1) / 2).primeFactors, p % r ≠ 1 := by
  obtain ⟨-, hrad, -, hW1, -⟩ := radical_of_shape h hq hN hqm hp hpm h2
  have hR1 := one_lt_prod_primeFactors hW1
  by_contra hne
  push Not at hne
  have hdvd : ∏ r ∈ ((q + 1) / 2).primeFactors, r ∣ p - 1 :=
    Finset.prod_primes_dvd _ (fun r hr => (Nat.prime_of_mem_primeFactors hr).prime)
      (fun r hr => by
        have hd := Nat.dvd_sub_mod (n := r) p
        rwa [hne r hr] at hd)
  have hle := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
  rw [Nat.mod_eq_of_lt (by omega)] at hrad
  omega

/-- The row prime of `exists_row_not_mod_one_of_shape` with the further facts that the order of
`p` modulo `r` is odd and divides both `w` and `r - 1`. -/
private theorem exists_row_not_mod_one_aux {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    ∃ r w : ℕ, r.Prime ∧ r ∣ (q + 1) / 2 ∧ σ 1 (r ^ N.factorization r) = p ^ w ∧ p % r ≠ 1 ∧
      3 ≤ orderOf (p : ZMod r) ∧ ¬ orderOf (p : ZMod r) ∣ N.factorization p ∧ 3 ≤ w ∧
      7 ≤ r ∧ Odd (orderOf (p : ZMod r)) ∧ orderOf (p : ZMod r) ∣ w ∧
      orderOf (p : ZMod r) ∣ r - 1 := by
  obtain ⟨hWmod, -, hWodd, -, -⟩ := radical_of_shape h hq hN hqm hp hpm h2
  obtain ⟨r, hrmem, hpr⟩ := exists_mem_not_mod_one h hq hN hqm hp hpm h2
  have hr := Nat.prime_of_mem_primeFactors hrmem
  have hrW := Nat.dvd_of_mem_primeFactors hrmem
  obtain ⟨w, -, hrow⟩ := sigma_row_eq_prime_pow_of_shape h hq hN hqm hp hpm h2 hr hrW
  obtain ⟨hd3, hde, hw3⟩ := three_le_orderOf_of_shape h hq hN hqm hp hpm h2 hr hrW hrow hpr
  obtain ⟨hdw, hdodd⟩ := orderOf_dvd_weight_of_shape h hq hN hqm hp hpm h2 hr hrW hrow
  have : Fact r.Prime := ⟨hr⟩
  have hrp : ¬ r ∣ p := fun hd => by
    have hpr' := (Nat.prime_dvd_prime_iff_eq hr hp).mp hd
    rw [hpr'] at hrW
    have := Nat.mod_eq_zero_of_dvd hrW
    omega
  have hpz : (p : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hrp
  have hdr : orderOf (p : ZMod r) ∣ r - 1 := ZMod.orderOf_dvd_card_sub_one hpz
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hWodd) (even_iff_two_dvd.mpr hrW)
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have h2r : 2 ∣ r - 1 := ⟨k, by omega⟩
  have h2d : 2 * orderOf (p : ZMod r) ∣ r - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hdodd) h2r hdr
  have hle := Nat.le_of_dvd (by have := hr.two_le; omega) h2d
  exact ⟨r, w, hr, hrW, hrow, hpr, hd3, hde, hw3, by omega, hdodd, hdw, hdr⟩

/-- **A row prime with `p ≢ 1 (mod r)`.** In the exceptional shape of `special_lt_or_shape`
(`N = q * m ^ 2`, `q ∤ m`, a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`),
some prime `r ∣ (q + 1) / 2` has `p % r ≠ 1`. For it, `σ(r ^ v_r(N)) = p ^ w` with `3 ≤ w`,
the order `d` of `p` modulo `r` has `3 ≤ d` and `d ∤ e`, and `7 ≤ r` (since `d` is odd and
`2 d ∣ r - 1`). A sharpening of the shape only; the shape is not excluded. Novelty not
verified. -/
theorem exists_row_not_mod_one_of_shape {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    ∃ r w : ℕ, r.Prime ∧ r ∣ (q + 1) / 2 ∧ σ 1 (r ^ N.factorization r) = p ^ w ∧ p % r ≠ 1 ∧
      3 ≤ orderOf (p : ZMod r) ∧ ¬ orderOf (p : ZMod r) ∣ N.factorization p ∧ 3 ≤ w ∧
      7 ≤ r := by
  obtain ⟨r, w, h1, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    exists_row_not_mod_one_aux h hq hN hqm hp hpm h2
  exact ⟨r, w, h1, h3, h4, h5, h6, h7, h8, h9⟩

/-- Hypothesis, not proved in this library: for primes `r` and `p`, an even exponent `g ≠ 0` and
an odd prime `s ∣ r - 1`, the divisor sum `σ(r ^ g) = (r ^ (g + 1) - 1) / (r - 1)` is not
`p ^ (s u)` with `u ≥ 1`. It follows from `NoHighPureRow` (`noOrderPureRow_of_noHighPureRow`)
and asks less: only exponents with a prime factor dividing `r - 1`. This is a case of the
equation `(x ^ n - 1) / (x - 1) = y ^ s` of Nagell and Ljunggren. It is not known whether that
equation has finitely many solutions, and the published constraints on an unknown solution
require a prime factor of `x` that is `1` modulo the exponent (Bennett and Levin, The Nagell
and Ljunggren equation via Runge's method, 2015, Proposition 1, which combines earlier
results); for a prime `x` that is this case. A research target, not a published theorem. -/
def NoOrderPureRow : Prop :=
  ∀ r p g s u : ℕ, r.Prime → p.Prime → s.Prime → s ≠ 2 → s ∣ r - 1 → Even g → g ≠ 0 → 1 ≤ u →
    σ 1 (r ^ g) ≠ p ^ (s * u)

/-- `NoHighPureRow` implies `NoOrderPureRow`. Both are unproved hypotheses. -/
theorem noOrderPureRow_of_noHighPureRow (hrow : NoHighPureRow) : NoOrderPureRow := by
  intro r p g s u hr hp hs hs2 hsr hg hg0 hu hσ
  have hr2 : r ≠ 2 := by
    rintro rfl
    have := Nat.le_of_dvd (by norm_num) hsr
    have := hs.two_le
    omega
  have hw := hrow r p g (s * u) hr hr2 hp hg hg0 hσ
  have hs3 : 3 ≤ s := by have := hs.two_le; omega
  have := Nat.mul_le_mul hs3 hu
  omega

/-- Under `NoOrderPureRow`, the special prime is below `m`: in Euler's form
`N = q ^ k * m ^ 2` with `q ∤ m`, `q < m`. `NoOrderPureRow` is an unproved hypothesis, so this
is a conditional result; it asks less than `special_lt_of_noHighPureRow`. The odd perfect
number conjecture is open, and nothing here decides it. -/
theorem special_lt_of_noOrderPureRow (hrow : NoOrderPureRow) {N q k m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q < m := by
  rcases special_lt_or_shape h hq hN hqm with h1 | ⟨rfl, p, hp, hpm, h2, -, -⟩
  · exact h1
  exfalso
  have hN' : N = q * m ^ 2 := by rw [hN, pow_one]
  obtain ⟨r, w, hr, hrW, hσ, -, hd3, -, hw3, hr7, hdodd, hdw, hdr⟩ :=
    exists_row_not_mod_one_aux h hq hN' hqm hp hpm h2
  obtain ⟨-, -, hW2, -, -, -, -⟩ := radical_shape_facts h hq hN' hqm hp hpm h2
  have hm0 : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hmN : m ∣ N := hN' ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have hfq : N.factorization q = 1 := by
    rw [hN', Nat.factorization_mul hq.ne_zero (pow_ne_zero 2 hm0), Finsupp.add_apply,
      hq.factorization_self, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hrq : r ≠ q := by
    rintro rfl
    have := Nat.le_of_dvd (by omega) hrW
    omega
  have hrq1 : r ∣ q + 1 := hrW.trans (Nat.div_dvd_of_dvd ⟨(q + 1) / 2, hW2⟩)
  have hr2m : r ∣ 2 * m ^ 2 := by rw [h2]; exact hrq1.mul_left _
  have hrm : r ∣ m := by
    rcases (Nat.Prime.dvd_mul hr).mp hr2m with h' | h'
    · have := Nat.le_of_dvd two_pos h'
      omega
    · exact hr.dvd_of_dvd_pow h'
  have hg0 : N.factorization r ≠ 0 :=
    (hr.factorization_pos_of_dvd h.ne_zero (hrm.trans hmN)).ne'
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq (by rw [hfq]; exact odd_one) hr hrq
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd (show orderOf (p : ZMod r) ≠ 1 by omega)
  have hs2 : s ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hdodd) (even_iff_two_dvd.mpr hsd)
  obtain ⟨u, hu⟩ := hsd.trans hdw
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · rw [h0, mul_zero] at hu
      omega
    · exact h0
  rw [hu] at hσ
  exact hrow r p _ s u hr hp hs hs2 (hsd.trans hdr) ⟨j, hj⟩ hg0 hu1 hσ

end OddPerfect

#print axioms OddPerfect.div_two_mod_of_shape
#print axioms OddPerfect.prod_primeFactors_mod_of_shape
#print axioms OddPerfect.two_mul_add_one_le_prod_primeFactors_of_shape
#print axioms OddPerfect.exists_row_not_mod_one_of_shape
#print axioms OddPerfect.noOrderPureRow_of_noHighPureRow
#print axioms OddPerfect.special_lt_of_noOrderPureRow
