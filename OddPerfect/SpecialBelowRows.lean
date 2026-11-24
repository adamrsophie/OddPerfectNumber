import OddPerfect.SpecialBelow
import OddPerfect.PureRows
import OddPerfect.SpecialBelowParity

/-!
# The open shape of `q < m` and pure rows of weight at least three

Let `N = q ^ k * m ^ 2` be an odd perfect number in Euler's form (`q` the special prime,
`q ∤ m`). The landed `special_lt_or_shape` proves `q < m` except in one shape: `k = 1` and a
prime `p ∣ m` with exponent `e` in `N` such that `2 m ^ 2 = p ^ e (q + 1)`, `σ(p ^ e) = q` and
`σ((q + 1) / 2) = p ^ e`. This module does not exclude that shape. It shows that the shape
contains a prime `r` whose component has divisor sum `p ^ w` with `w` odd and `w ≥ 3`.

* `sigma_row_eq_prime_pow_of_shape`: in the shape, every prime `r ∣ (q + 1) / 2` has
  `σ(r ^ v_r(N)) = p ^ w` for some `w ≥ 1`.
* `dvd_index_add_two_of_shape`: in the shape, a prime `r ∣ (q + 1) / 2` with
  `σ(r ^ v_r(N)) = p` divides `e + 2`.
* `exists_high_pure_row_of_le_special`: if `m ≤ q`, there are primes `r` and `p` with
  `σ(r ^ v_r(N)) = p ^ w`, `w` odd, `w ≥ 3` and `σ(p ^ v_p(N)) = q`.
* `special_lt_of_noHighPureRow`: under the hypothesis `NoHighPureRow`, `q < m`.

`NoHighPureRow` is an unproved hypothesis and a research target: it is a case of the equation
of Nagell and Ljunggren, for which finiteness of the solutions is not known (see the docstring
of the definition). So `q < m` is proved here only conditionally. The
odd perfect number conjecture is open, and nothing here decides it.

The argument: put `W = (q + 1) / 2`, so `m ^ 2 = p ^ e W`. Each prime `r ∣ W` has a component
`σ(r ^ v_r(W)) = p ^ (w_r)` with `w_r ≥ 1`, and the `w_r` add up to `e`. A row of weight one
gives `p ≡ 1 (mod r)`, so `q = σ(p ^ e) ≡ e + 1 (mod r)`, and `r ∣ q + 1` gives `r ∣ e + 2`. If
every weight were one, `W` would have `e` distinct odd prime factors, all dividing `e + 2`, so
`3 ^ e ≤ e + 2`, which is false for `e ≥ 2`. So some weight is at least two; it is odd (hence at
least three) unless `σ(3 ^ 4) = 11 ^ 2`, and that case contradicts `q = σ(11 ^ e) ≡ 1 (mod 3)`
with `3 ∣ q + 1`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- Hypothesis, not proved in this library: for odd primes `r` and `p` and an even exponent
`g ≠ 0`, the divisor sum `σ(r ^ g) = (r ^ (g + 1) - 1) / (r - 1)` is not `p ^ w` with `w ≥ 3`.
This is a case of the equation `(x ^ n - 1) / (x - 1) = y ^ w` of Nagell and Ljunggren. It is
not known whether that equation has finitely many solutions (Bennett and Levin, The Nagell and
Ljunggren equation via Runge's method, 2015, introduction); four solutions are known, among
them `(3 ^ 5 - 1) / 2 = 11 ^ 2`. A research target, not a published theorem. -/
def NoHighPureRow : Prop :=
  ∀ r p g w : ℕ, r.Prime → r ≠ 2 → p.Prime → Even g → g ≠ 0 → σ 1 (r ^ g) = p ^ w → w ≤ 2

/-- `σ(p ^ (j + 1)) = 1 + p σ(p ^ j)`. -/
private lemma sigma_succ_eq_one_add' {p : ℕ} (hp : p.Prime) (j : ℕ) :
    σ 1 (p ^ (j + 1)) = 1 + p * σ 1 (p ^ j) := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

/-- `e + 2 < 3 ^ e` for `e ≥ 2`. -/
private lemma add_two_lt_three_pow {e : ℕ} (he : 2 ≤ e) : e + 2 < 3 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e _ ih => rw [pow_succ]; omega

/-- The normal form of the shape: `(q + 1) / 2 = t ^ 2` with `p ∤ t`, `q ∤ t`, `t` odd. -/
theorem shape_data {N q m p : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) :
    ∃ t, (q + 1) / 2 = t ^ 2 ∧ q + 1 = 2 * t ^ 2 ∧ m ^ 2 = p ^ N.factorization p * t ^ 2 ∧
      ¬ p ∣ t ∧ ¬ q ∣ t ∧ Odd t ∧ σ 1 (t ^ 2) = p ^ N.factorization p ∧
      σ 1 (p ^ N.factorization p) = q ∧ Even (N.factorization p) ∧ 0 < N.factorization p := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hmN : m ∣ N := hN ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have he0 : 0 < N.factorization p := hp.factorization_pos_of_dvd h.ne_zero (hpm.trans hmN)
  have hI : eulerIndex q 1 m = p ^ N.factorization p := by
    have hi := sigma_special_mul_eulerIndex h hq hN1 hqm
    have hσq : σ 1 (q ^ 1) = q + 1 := by
      rw [sigma_one_apply_prime_pow hq]; simp [Finset.sum_range_succ, add_comm]
    rw [hσq, h2, mul_comm (p ^ _)] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega) hi
  obtain ⟨t, hmt, hpt, htodd, -, hqt, hσp, hqt2, hσt, -, heven, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hp he0 hI
  exact ⟨t, by omega, hqt2, hmt, hpt, hqt, htodd, hσt, hσp, heven, he0⟩

/-- Facts about one prime `r ∣ (q + 1) / 2` in the shape. -/
private theorem row_data {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2) :
    r ≠ p ∧ r ≠ q ∧ r ≠ 2 ∧ N.factorization r = ((q + 1) / 2).factorization r ∧
      N.factorization r ≠ 0 ∧ Even (N.factorization r) := by
  obtain ⟨t, hW, -, hmt, hpt, hqt, htodd, -⟩ := shape_data h hq hN hqm hp hpm h2
  have ht0 : t ≠ 0 := htodd.pos.ne'
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  rw [hW] at hrW ⊢
  have hrt : r ∣ t := hr.dvd_of_dvd_pow hrW
  have hrp : r ≠ p := by rintro rfl; exact hpt hrt
  have hrq : r ≠ q := by rintro rfl; exact hqt hrt
  have hr2 : r ≠ 2 := by
    rintro rfl; exact (Nat.not_even_iff_odd.mpr htodd) (even_iff_two_dvd.mpr hrt)
  have hrq' : ¬ r ∣ q := fun hd => hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hd)
  have hrpe : ¬ r ∣ p ^ N.factorization p := fun hd =>
    hrp ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd))
  have hpe0 : p ^ N.factorization p ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hNr : N.factorization r = (t ^ 2).factorization r := by
    have hN' : N = q * (p ^ N.factorization p * t ^ 2) := by rw [← hmt]; exact hN
    have hfa := congrArg (fun n => n.factorization r) hN'
    rw [hfa, Nat.factorization_mul hq.ne_zero (mul_ne_zero hpe0 ht2),
      Nat.factorization_mul hpe0 ht2, Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrq', Nat.factorization_eq_zero_of_not_dvd hrpe,
      zero_add, zero_add]
  have ht2r : (t ^ 2).factorization r = 2 * t.factorization r := by
    rw [Nat.factorization_pow]; simp
  have hc0 : t.factorization r ≠ 0 := (hr.factorization_pos_of_dvd ht0 hrt).ne'
  refine ⟨hrp, hrq, hr2, hNr, ?_, ?_⟩
  · rw [hNr, ht2r]; omega
  · rw [hNr, ht2r]; exact even_two_mul _

/-- Step 1 in general form: if `σ(n) = p ^ e` for a prime `p`, then every component of `n` has
divisor sum `p ^ w` with `w ≥ 1`. -/
private theorem component_eq_prime_pow {n p e r : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hσ : σ 1 n = p ^ e) (hr : r ∈ n.primeFactors) :
    ∃ w, 1 ≤ w ∧ σ 1 (r ^ n.factorization r) = p ^ w := by
  have hfac : σ 1 n = ∏ s ∈ n.primeFactors, σ 1 (s ^ n.factorization s) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
  have hd : σ 1 (r ^ n.factorization r) ∣ p ^ e := by
    rw [← hσ, hfac]
    exact Finset.dvd_prod_of_mem _ hr
  obtain ⟨w, -, hw⟩ := (Nat.dvd_prime_pow hp).1 hd
  have hr' := Nat.prime_of_mem_primeFactors hr
  have ha : n.factorization r ≠ 0 :=
    (hr'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hr)).ne'
  have hlt := lt_sigma_prime_pow hr' ha
  refine ⟨w, ?_, hw⟩
  rcases Nat.eq_zero_or_pos w with h0 | h0
  · rw [hw, h0, pow_zero] at hlt; have := hr'.two_le; omega
  · exact h0


/-- Step 2 in general form: if `σ(r ^ a) = p` with `a ≠ 0`, `q = σ(p ^ e)` and `r ∣ q + 1`,
then `r ∣ e + 2`. -/
private theorem dvd_add_two_of_weight_one {r a p e q : ℕ} (hr : r.Prime) (hp : p.Prime)
    (ha : a ≠ 0) (hrow : σ 1 (r ^ a) = p) (hσ : σ 1 (p ^ e) = q) (hrq : r ∣ q + 1) :
    r ∣ e + 2 := by
  have hr1 : 1 % r = 1 := Nat.mod_eq_of_lt hr.one_lt
  have hpr : p % r = 1 := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [← hrow, sigma_succ_eq_one_add' hr, Nat.add_mul_mod_self_left, hr1]
  have hq : q % r = (e + 1) % r := by
    rw [← hσ, sigma_one_apply_prime_pow hp, Finset.sum_nat_mod,
      Finset.sum_congr rfl (fun i _ => by rw [Nat.pow_mod, hpr, one_pow, hr1])]
    simp
  apply Nat.dvd_of_mod_eq_zero
  calc (e + 2) % r = (e + 1 + 1) % r := rfl
    _ = ((e + 1) % r + 1 % r) % r := Nat.add_mod _ _ _
    _ = (q % r + 1 % r) % r := by rw [hq]
    _ = (q + 1) % r := (Nat.add_mod _ _ _).symm
    _ = 0 := Nat.mod_eq_zero_of_dvd hrq

/-- Steps 1 and 3 in general form: if `σ(n) = p ^ e` with `e` even and nonzero, every prime
factor of `n` is odd, and every prime factor `r` with `σ(r ^ v_r(n)) = p` divides `e + 2`, then
some component of `n` has divisor sum `p ^ w` with `w ≥ 2`. -/
private theorem exists_weight_ge_two {n p e : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hσ : σ 1 n = p ^ e) (he : Even e) (he0 : e ≠ 0) (hodd : ∀ r ∈ n.primeFactors, r ≠ 2)
    (hdiv : ∀ r ∈ n.primeFactors, σ 1 (r ^ n.factorization r) = p → r ∣ e + 2) :
    ∃ r ∈ n.primeFactors, ∃ w, 2 ≤ w ∧ σ 1 (r ^ n.factorization r) = p ^ w := by
  by_contra hne
  push Not at hne
  have hfac : σ 1 n = ∏ s ∈ n.primeFactors, σ 1 (s ^ n.factorization s) := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
  have hone : ∀ r ∈ n.primeFactors, σ 1 (r ^ n.factorization r) = p := by
    intro r hr
    obtain ⟨w, hw1, hw⟩ := component_eq_prime_pow hp hn hσ hr
    have h1 : w = 1 := by
      by_contra h1
      exact hne r hr w (by omega) hw
    rw [hw, h1, pow_one]
  have hpe : p ^ e = p ^ n.primeFactors.card := by
    rw [← hσ, hfac, Finset.prod_congr rfl hone, Finset.prod_const]
  have hcard : e = n.primeFactors.card := Nat.pow_right_injective hp.two_le hpe
  have hdvd : ∏ r ∈ n.primeFactors, r ∣ e + 2 :=
    Finset.prod_primes_dvd _ (fun r hr => (Nat.prime_of_mem_primeFactors hr).prime)
      (fun r hr => hdiv r hr (hone r hr))
  have hle : 3 ^ n.primeFactors.card ≤ ∏ r ∈ n.primeFactors, r :=
    Finset.pow_card_le_prod _ _ _ (fun r hr => by
      have := (Nat.prime_of_mem_primeFactors hr).two_le
      have := hodd r hr
      omega)
  have h2 : 2 ≤ e := by obtain ⟨j, hj⟩ := he; omega
  have h3 := add_two_lt_three_pow h2
  have h4 := Nat.le_of_dvd (by omega) hdvd
  rw [← hcard] at hle
  omega

/-- **Step 1.** In the exceptional shape of `special_lt_or_shape` (`N = q * m ^ 2`, `q ∤ m`,
a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`), every prime
`r ∣ (q + 1) / 2` has `σ(r ^ v_r(N)) = p ^ w` for some `w ≥ 1`. -/
theorem sigma_row_eq_prime_pow_of_shape {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2) :
    ∃ w, 1 ≤ w ∧ σ 1 (r ^ N.factorization r) = p ^ w := by
  obtain ⟨t, hW, -, -, -, -, htodd, hσt, -⟩ := shape_data h hq hN hqm hp hpm h2
  obtain ⟨-, -, -, hNr, -⟩ := row_data h hq hN hqm hp hpm h2 hr hrW
  have ht0 : t ≠ 0 := htodd.pos.ne'
  have hW0 : (q + 1) / 2 ≠ 0 := by rw [hW]; exact pow_ne_zero 2 ht0
  rw [hNr]
  exact component_eq_prime_pow hp hW0 (by rw [hW]; exact hσt)
    (Nat.mem_primeFactors.mpr ⟨hr, hrW, hW0⟩)

/-- **Step 2.** In the exceptional shape of `special_lt_or_shape` (`N = q * m ^ 2`, `q ∤ m`,
a prime `p ∣ m` with `2 m ^ 2 = p ^ e (q + 1)` where `e = v_p(N)`), a prime `r ∣ (q + 1) / 2`
with `σ(r ^ v_r(N)) = p` divides `e + 2`. -/
theorem dvd_index_add_two_of_shape {N q m p r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hp : p.Prime) (hpm : p ∣ m)
    (h2 : 2 * m ^ 2 = p ^ N.factorization p * (q + 1)) (hr : r.Prime) (hrW : r ∣ (q + 1) / 2)
    (hrow : σ 1 (r ^ N.factorization r) = p) : r ∣ N.factorization p + 2 := by
  obtain ⟨t, -, hqt2, -, -, -, -, -, hσp, -⟩ := shape_data h hq hN hqm hp hpm h2
  obtain ⟨-, -, -, -, ha, -⟩ := row_data h hq hN hqm hp hpm h2 hr hrW
  exact dvd_add_two_of_weight_one hr hp ha hrow hσp
    (hrW.trans (Nat.div_dvd_of_dvd ⟨t ^ 2, hqt2⟩))

/-- The main statement with the exponent of `r` recorded as even and nonzero. -/
private theorem exists_high_pure_row_aux {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hle : m ≤ q) :
    ∃ r p w : ℕ, r.Prime ∧ r ≠ 2 ∧ p.Prime ∧ r ∣ N ∧ p ∣ N ∧ r ≠ p ∧ r ≠ q ∧ p ≠ q ∧
      Odd w ∧ 3 ≤ w ∧ σ 1 (r ^ N.factorization r) = p ^ w ∧
      σ 1 (p ^ N.factorization p) = q ∧ Even (N.factorization r) ∧ N.factorization r ≠ 0 := by
  rcases special_lt_or_shape h hq hN hqm with hlt | ⟨rfl, p, hp, hpm, h2, -, -⟩
  · omega
  have hN1 : N = q * m ^ 2 := by rw [hN, pow_one]
  obtain ⟨t, hW, hqt2, -, -, -, htodd, hσt, hσp, heven, he0⟩ :=
    shape_data h hq hN1 hqm hp hpm h2
  have ht0 : t ≠ 0 := htodd.pos.ne'
  have hW0 : (q + 1) / 2 ≠ 0 := by rw [hW]; exact pow_ne_zero 2 ht0
  have hσW : σ 1 ((q + 1) / 2) = p ^ N.factorization p := by rw [hW]; exact hσt
  obtain ⟨r, hrmem, w, hw2, hrow⟩ := exists_weight_ge_two hp hW0 hσW heven he0.ne'
    (fun r hr => (row_data h hq hN1 hqm hp hpm h2 (Nat.prime_of_mem_primeFactors hr)
      (Nat.dvd_of_mem_primeFactors hr)).2.2.1)
    (fun r hr hrow => by
      obtain ⟨-, -, -, hNr, -⟩ := row_data h hq hN1 hqm hp hpm h2
        (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
      exact dvd_index_add_two_of_shape h hq hN1 hqm hp hpm h2
        (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
        (by rw [hNr]; exact hrow))
  have hr := Nat.prime_of_mem_primeFactors hrmem
  have hrW := Nat.dvd_of_mem_primeFactors hrmem
  obtain ⟨hrp, hrq, hr2, hNr, ha0, haev⟩ := row_data h hq hN1 hqm hp hpm h2 hr hrW
  rw [← hNr] at hrow
  have hmN : m ∣ N := hN1 ▸ (dvd_pow_self m two_ne_zero).mul_left q
  have hrN : r ∣ N := Nat.dvd_of_factorization_pos ha0
  have hpq : p ≠ q := by rintro rfl; exact hqm hpm
  have h3 : r ∣ q + 1 := hrW.trans (Nat.div_dvd_of_dvd ⟨t ^ 2, hqt2⟩)
  rcases odd_weight_or_three_pow_four hr hr2 haev ha0 hp hrow with hodd | ⟨rfl, -, rfl, rfl⟩
  · exact ⟨r, p, w, hr, hr2, hp, hrN, hpm.trans hmN, hrp, hrq, hpq, hodd,
      by obtain ⟨j, rfl⟩ := hodd; omega, hrow, hσp, haev, ha0⟩
  · exfalso
    obtain ⟨i, hi⟩ := heven
    have h1 := sigma_eleven_pow_two_mul_mod_three i
    rw [show 2 * i = N.factorization 11 by omega, hσp] at h1
    omega

/-- If `m ≤ q` in Euler's form of an odd perfect number, then some prime `r` has a component
whose divisor sum is `p ^ w` with `w` odd and at least 3, where `p` is the prime whose
component has divisor sum `q`. -/
theorem exists_high_pure_row_of_le_special {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hle : m ≤ q) :
    ∃ r p w : ℕ, r.Prime ∧ r ≠ 2 ∧ p.Prime ∧ r ∣ N ∧ p ∣ N ∧ r ≠ p ∧ r ≠ q ∧ p ≠ q ∧
      Odd w ∧ 3 ≤ w ∧ σ 1 (r ^ N.factorization r) = p ^ w ∧
      σ 1 (p ^ N.factorization p) = q := by
  obtain ⟨r, p, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ :=
    exists_high_pure_row_aux h hq hN hqm hle
  exact ⟨r, p, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- Under `NoHighPureRow`, the special prime is below `m`. `NoHighPureRow` is an unproved
hypothesis, so this is a conditional result. -/
theorem special_lt_of_noHighPureRow (hrow : NoHighPureRow) {N q k m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q < m := by
  by_contra hc
  obtain ⟨r, p, w, hr, hr2, hp, -, -, -, -, -, -, hw3, hσ, -, hev, h0⟩ :=
    exists_high_pure_row_aux h hq hN hqm (by omega)
  have := hrow r p _ w hr hr2 hp hev h0 hσ
  omega

end OddPerfect

#print axioms OddPerfect.sigma_row_eq_prime_pow_of_shape
#print axioms OddPerfect.dvd_index_add_two_of_shape
#print axioms OddPerfect.exists_high_pure_row_of_le_special
#print axioms OddPerfect.special_lt_of_noHighPureRow
