import OddPerfect.SpecialPrime
import OddPerfect.Network
import OddPerfect.Phi3

/-!
# Size bounds for the large prime factors of an odd perfect number

Elementary bounds in the style of Acquaah and Konyagin, Zelinsky (arXiv 1810.11734) and
Bibby, Vyncke and Zelinsky (arXiv 1908.09420). The basic tool: for a prime `p` with exact
exponent `e` in `N`, the numbers `p ^ e` and `σ(p ^ e)` are coprime divisors of `2 * N`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N : ℕ}

/-! ## Helpers -/

/-- Split off one full prime component of the divisor sum. -/
private lemma sigma_eq_component_mul {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    σ 1 n = σ 1 (p ^ n.factorization p) * σ 1 (ordCompl[p] n) := by
  have hcop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  exact isMultiplicative_sigma.map_mul_of_coprime hcop

/-- The divisor sums of two distinct full components together divide `2 * N`. -/
theorem sigma_mul_sigma_dvd (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    σ 1 (p ^ N.factorization p) * σ 1 (q ^ N.factorization q) ∣ 2 * N := by
  set M := ordCompl[p] N with hM
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos p h.ne_zero).ne'
  have hfq : M.factorization q = N.factorization q := by
    rw [hM, Nat.factorization_ordCompl, Finsupp.erase_ne (Ne.symm hpq)]
  rw [← h.sigma_eq, sigma_eq_component_mul h.ne_zero hp, ← hM,
    sigma_eq_component_mul hM0 hq, hfq, ← mul_assoc]
  exact dvd_mul_right _ _

/-- `p ^ e` and `σ(p ^ e)` are coprime divisors of `2 * N`, so their product divides `2 * N`. -/
theorem pow_mul_sigma_dvd (h : OddPerfect N) {p : ℕ} (hp : p.Prime) :
    p ^ N.factorization p * σ 1 (p ^ N.factorization p) ∣ 2 * N := by
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ((Nat.ordProj_dvd N p).trans (dvd_mul_left _ _))
    (OPNStarter.component_sigma_dvd h.perfect hp rfl)
  exact ((coprime_sigma_prime_pow hp _).pow_right _).symm

/-- `p ^ e < σ(p ^ e)` for `e ≥ 1`. -/
private lemma pow_lt_sigma {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) : p ^ e < σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have : 1 ≤ ∑ i ∈ Finset.range e, p ^ i := by
    calc 1 = p ^ 0 := (pow_zero p).symm
      _ ≤ ∑ i ∈ Finset.range e, p ^ i :=
        Finset.single_le_sum (f := fun i => p ^ i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr he)
  omega

/-- The geometric identity `(p - 1) * σ(p ^ e) + 1 = p ^ (e + 1)`. -/
private lemma pred_mul_sigma_add_one {p e : ℕ} (hp : p.Prime) :
    (p - 1) * σ 1 (p ^ e) + 1 = p ^ (e + 1) := by
  have h1 := hp.one_lt
  rw [sigma_one_apply_prime_pow hp, mul_comm]
  have := geom_sum_mul_add (p - 1) (e + 1)
  rwa [Nat.sub_add_cancel h1.le] at this

private lemma odd_of_dvd (h : OddPerfect N) {p : ℕ} (hpN : p ∣ N) : Odd p :=
  h.odd.of_dvd_nat hpN

private lemma factorization_pos (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    1 ≤ N.factorization p :=
  (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN

/-- `A * B ≤ gcd A B * M` when `A` and `B` divide `M > 0`. -/
private lemma mul_le_gcd_mul {A B M : ℕ} (hA : A ∣ M) (hB : B ∣ M) (hM : 0 < M) :
    A * B ≤ Nat.gcd A B * M := by
  rw [← Nat.gcd_mul_lcm A B]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd hM (Nat.lcm_dvd hA hB))

/-! ## Part 1: every prime factor -/

/-- For every prime `p` with exponent `e` in `N`: `p ^ (2 * e) < 2 * N`, if `p ∣ N`. -/
theorem pow_two_mul_factorization_lt (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    p ^ (2 * N.factorization p) < 2 * N := by
  have he := factorization_pos h hp hpN
  have hlt := pow_lt_sigma hp he
  have hle := Nat.le_of_dvd (by have := h.pos; omega) (pow_mul_sigma_dvd h hp)
  calc p ^ (2 * N.factorization p) = p ^ N.factorization p * p ^ N.factorization p := by
        rw [two_mul, pow_add]
    _ < p ^ N.factorization p * σ 1 (p ^ N.factorization p) :=
        Nat.mul_lt_mul_of_pos_left hlt (pow_pos hp.pos _)
    _ ≤ 2 * N := hle

/-- Every prime factor `p` satisfies `p ^ 2 < 2 * N`. -/
theorem sq_lt_two_mul (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    p ^ 2 < 2 * N :=
  lt_of_le_of_lt (Nat.pow_le_pow_right hp.pos (by have := factorization_pos h hp hpN; omega))
    (pow_two_mul_factorization_lt h hp hpN)

/-- A prime with exponent at least two satisfies `p ^ 4 < 2 * N`. -/
theorem pow_four_lt_of_two_le (h : OddPerfect N) {p : ℕ} (hp : p.Prime)
    (he : 2 ≤ N.factorization p) : p ^ 4 < 2 * N := by
  have hpN : p ∣ N := (hp.dvd_iff_one_le_factorization h.ne_zero).mpr (by omega)
  exact lt_of_le_of_lt (Nat.pow_le_pow_right hp.pos (by omega))
    (pow_two_mul_factorization_lt h hp hpN)

/-- Every prime factor with even exponent (every non special prime factor) satisfies
`p ^ 4 < 2 * N`. -/
theorem pow_four_lt_of_even (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hev : Even (N.factorization p)) : p ^ 4 < 2 * N := by
  have := factorization_pos h hp hpN
  obtain ⟨j, hj⟩ := hev
  exact pow_four_lt_of_two_le h hp (by omega)

/-! ## Part 2: two cycles -/

/-- Zelinsky's Lemma 1, for all natural numbers: if `q ∣ p ^ 2 + p + 1` and `p ∣ q + 1`,
then `p ∈ {1, 2, 4}`. The complete solution set is `(1, 1), (1, 3), (2, 1), (2, 7), (4, 3),
(4, 7)`; for odd `p` and `q` only `(1, 1)` and `(1, 3)` remain, as Zelinsky states. -/
theorem eq_one_or_two_or_four_of_dvd_phi3_of_dvd_succ {p q : ℕ} (h1 : q ∣ p ^ 2 + p + 1)
    (h2 : p ∣ q + 1) : p = 1 ∨ p = 2 ∨ p = 4 := by
  obtain ⟨m, hm⟩ := h2
  have hq0 : q ≠ 0 := by rintro rfl; simp at h1
  have hp0 : p ≠ 0 := by rintro rfl; simp at hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hcop : Nat.Coprime q p :=
    Nat.Coprime.coprime_dvd_right ⟨m, hm⟩ (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right q))
  have hdiv : q ∣ p * (p + m + 1) := by
    have : p * (p + m + 1) = (p ^ 2 + p + 1) + q := by nlinarith [hm]
    rw [this]
    exact dvd_add h1 dvd_rfl
  have hq' : q ∣ p + m + 1 := hcop.dvd_of_dvd_mul_left hdiv
  have hle : q ≤ p + m + 1 := Nat.le_of_dvd (by omega) hq'
  have hp4 : p ≤ 4 := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hm1 : m = 1 := by omega
      subst hm1
      have h3 : q ∣ 3 := by
        have : p + 1 + 1 = q + 3 := by omega
        rw [this] at hq'
        exact (Nat.dvd_add_right dvd_rfl).mp hq'
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · nlinarith
  interval_cases p
  · omega
  · left; rfl
  · right; left; rfl
  · exfalso
    have hq13 : q ≤ 13 := Nat.le_of_dvd (by norm_num) h1
    interval_cases q <;> omega
  · right; right; rfl

/-- For primes, the only solution of `q ∣ p ^ 2 + p + 1` and `p ∣ q + 1` is `(p, q) = (2, 7)`.
So there is no such pair of odd primes (no `σ_{1,2}` two cycle in an odd perfect number). -/
theorem prime_dvd_phi3_dvd_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : q ∣ phi3 p) (h2 : p ∣ q + 1) : p = 2 ∧ q = 7 := by
  have hp2 : p = 2 := by
    rcases eq_one_or_two_or_four_of_dvd_phi3_of_dvd_succ h1 h2 with rfl | rfl | rfl
    · exact absurd hp Nat.not_prime_one
    · rfl
    · exact absurd hp (by decide)
  subst hp2
  refine ⟨rfl, ?_⟩
  have h7 : q ∣ 7 := h1
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h7 with h | h
  · exact absurd h hq.one_lt.ne'
  · exact h

/-- The classical `σ_{2,2}` two cycle: `13 ∣ 3 ^ 2 + 3 + 1` and `3 ∣ 13 ^ 2 + 13 + 1`. So the
analogue of `prime_dvd_phi3_dvd_succ` with both exponents two is false. -/
theorem three_thirteen_two_cycle : 13 ∣ phi3 3 ∧ 3 ∣ phi3 13 := by
  unfold phi3; norm_num

/-- The `σ_{1,1}` two cycle: distinct primes with `p ∣ q + 1` and `q ∣ p + 1` are `2` and `3`. -/
theorem prime_two_cycle_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h1 : p ∣ q + 1) (h2 : q ∣ p + 1) : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2) := by
  have a := Nat.le_of_dvd (by omega) h1
  have b := Nat.le_of_dvd (by omega) h2
  have key : ∀ x : ℕ, x.Prime → (x + 1).Prime → x = 2 := by
    intro x hx hx1
    rcases hx.eq_two_or_odd' with h | h
    · exact h
    · rcases hx1.eq_two_or_odd' with h' | h'
      · have := hx.two_le; omega
      · exact absurd (h.add_one) (Nat.not_even_iff_odd.mpr h')
  rcases Nat.lt_or_gt_of_ne hpq with hlt | hlt
  · have hq' : q = p + 1 := by omega
    subst hq'
    left; have := key p hp hq; omega
  · have hp' : p = q + 1 := by omega
    subst hp'
    right; have := key q hq hp; omega

private lemma phi6_core : ∀ n x y : ℕ, x + y ≤ n → y ≤ x → x ∣ y * (y - 1) + 1 →
    y ∣ x * (x - 1) + 1 → x = 1 ∧ y = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y hn hyx h1 h2
  have hx0 : x ≠ 0 := by rintro rfl; simp at h1
  have hy0 : y ≠ 0 := by rintro rfl; simp at h2
  rcases Nat.eq_or_lt_of_le hyx with rfl | hlt
  · have := Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right y (y - 1))).mp h1)
    exact ⟨this, this⟩
  exfalso
  rcases Nat.lt_or_ge y 2 with hy2 | hy2
  · have hy1 : y = 1 := by omega
    subst hy1
    have := Nat.dvd_one.mp (by simpa using h1)
    omega
  obtain ⟨t, ht⟩ := h1
  have ht0 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at ht; simp at ht
    · exact h0
  have hty : t < y := by
    by_contra hc
    have : y * x ≤ x * t := by rw [mul_comm]; exact Nat.mul_le_mul_left x (by omega)
    have h3 : y * (y + 1) ≤ y * x := Nat.mul_le_mul_left y hlt
    have h5 : y * (y - 1) + 2 * y = y * (y + 1) := by
      obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    omega
  have h2' : y ∣ t * (t - 1) + 1 := by
    have hz2 : (y : ℤ) ∣ (x : ℤ) * ((x : ℤ) - 1) + 1 := by
      have := Int.natCast_dvd_natCast.mpr h2
      push_cast [Nat.cast_sub (show 1 ≤ x by omega)] at this
      exact this
    have hxt : (x : ℤ) * t = (y : ℤ) * ((y : ℤ) - 1) + 1 := by
      have := congrArg (fun n : ℕ => (n : ℤ)) ht
      push_cast [Nat.cast_sub (show 1 ≤ y by omega)] at this
      linarith
    have hz : (y : ℤ) ∣ (t : ℤ) * ((t : ℤ) - 1) + 1 := by
      have e : (t : ℤ) * ((t : ℤ) - 1) + 1 = (t : ℤ) ^ 2 * ((x : ℤ) * ((x : ℤ) - 1) + 1) -
          (y : ℤ) * (((y : ℤ) - 1) * ((x : ℤ) * t + 1 - t)) := by
        linear_combination (-(x : ℤ) * t - 1 + t) * hxt
      rw [e]
      exact (dvd_mul_of_dvd_right hz2 _).sub (dvd_mul_right _ _)
    have : ((t * (t - 1) + 1 : ℕ) : ℤ) = (t : ℤ) * ((t : ℤ) - 1) + 1 := by
      push_cast [Nat.cast_sub ht0]; ring
    rw [← this] at hz
    exact Int.natCast_dvd_natCast.mp hz
  have := ih (y + t) (by omega) y t le_rfl hty.le h2' ⟨x, by rw [ht, mul_comm]⟩
  omega

/-- The `Φ6` two cycle (Cai, Chen and Zhang, Lemma 8, by Vieta descent): positive integers
with `x ∣ y ^ 2 - y + 1` and `y ∣ x ^ 2 - x + 1` are `x = y = 1`. In contrast the `Φ3`
version has the infinite family `(1, 1), (1, 3), (3, 13), (13, 61), ...`. -/
theorem phi6_two_cycle {x y : ℕ} (h1 : x ∣ y ^ 2 - y + 1) (h2 : y ∣ x ^ 2 - x + 1) :
    x = 1 ∧ y = 1 := by
  have e : ∀ z : ℕ, z ^ 2 - z = z * (z - 1) := fun z => by
    rw [Nat.mul_sub, mul_one, sq]
  rw [e] at h1 h2
  rcases le_total y x with hyx | hxy
  · exact phi6_core (x + y) x y le_rfl hyx h1 h2
  · exact (phi6_core (y + x) y x le_rfl hxy h2 h1).symm

/-! ## Part 3: two prime factors -/

private lemma coprime_pow_mul_sigma {p a : ℕ} (hp : p.Prime) {X : ℕ} (hX : ¬ p ∣ X) :
    Nat.Coprime (p ^ a) (σ 1 (p ^ a) * X) :=
  Nat.Coprime.pow_left _ (Nat.Coprime.mul_right
    ((coprime_sigma_prime_pow hp a).symm) ((hp.coprime_iff_not_dvd).mpr hX))

/-- If `p ∤ σ(q ^ b)`, then `p ^ a * (σ(p ^ a) * σ(q ^ b)) ∣ 2 * N` (exact exponents). -/
theorem pow_mul_sigma_mul_sigma_dvd (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hnd : ¬ p ∣ σ 1 (q ^ N.factorization q)) :
    p ^ N.factorization p * (σ 1 (p ^ N.factorization p) * σ 1 (q ^ N.factorization q)) ∣
      2 * N :=
  Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_pow_mul_sigma hp hnd)
    ((Nat.ordProj_dvd N p).trans (dvd_mul_left _ _)) (sigma_mul_sigma_dvd h hp hq hpq)

/-- If a prime factor `q ≠ p` does not divide `σ(p ^ a)`, then
`p ^ a * σ(p ^ a) * q ∣ 2 * N`. -/
theorem pow_mul_sigma_mul_prime_dvd (h : OddPerfect N) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hqN : q ∣ N) (hnd : ¬ q ∣ σ 1 (p ^ N.factorization p)) :
    p ^ N.factorization p * σ 1 (p ^ N.factorization p) * q ∣ 2 * N := by
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (pow_mul_sigma_dvd h hp)
    (hqN.trans (dvd_mul_left _ _))
  refine Nat.Coprime.mul_left (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).mpr hpq)) ?_
  exact Nat.Coprime.symm ((hq.coprime_iff_not_dvd).mpr hnd)

private lemma sigma_prime_one {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 1) = p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ, add_comm]

/-- Exponents two and one: if `p ^ 2 ∥ N` and `q ∥ N` with `p ≠ q`, then
`p ^ 4 * q < 2 * N`. This uses `prime_dvd_phi3_dvd_succ`. -/
theorem pow_four_mul_lt_of_two_one (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hqN : q ∣ N) (ha : N.factorization p = 2) (hb : N.factorization q = 1) :
    p ^ 4 * q < 2 * N := by
  have hpN : p ∣ N := (hp.dvd_iff_one_le_factorization h.ne_zero).mpr (by omega)
  have hpodd := odd_of_dvd h hpN
  have hsq := sigma_prime_sq hp
  have hN := h.pos
  by_cases hd : p ∣ q + 1
  · have hnd : ¬ q ∣ σ 1 (p ^ N.factorization p) := by
      rw [ha, hsq]
      intro hq'
      have := (prime_dvd_phi3_dvd_succ hp hq hq' hd).1
      subst this
      exact absurd hpodd (by decide)
    have hle := Nat.le_of_dvd (by omega) (pow_mul_sigma_mul_prime_dvd h hp hq hpq hqN hnd)
    rw [ha, hsq] at hle
    unfold phi3 at hle
    have hq0 := hq.pos
    nlinarith [Nat.mul_le_mul_left q (show p ^ 4 ≤ p ^ 2 * p ^ 2 by ring_nf; rfl)]
  · have hnd : ¬ p ∣ σ 1 (q ^ N.factorization q) := by rwa [hb, sigma_prime_one hq]
    have hle := Nat.le_of_dvd (by omega) (pow_mul_sigma_mul_sigma_dvd h hp hq hpq hnd)
    rw [ha, hb, hsq, sigma_prime_one hq] at hle
    unfold phi3 at hle
    have hp0 := hp.pos
    nlinarith [sq_nonneg p, pow_pos hp0 4, pow_pos hp0 2]

/-- Bound for any two prime factors `p < q` of an odd perfect number: `p ^ 4 * q < 2 * N`.
In particular this holds for the second largest prime `Q` and the largest prime `P`:
`Q ^ 4 * P < 2 * N`. -/
theorem pow_four_mul_lt (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p < q) : p ^ 4 * q < 2 * N := by
  have hN := h.pos
  have ha1 := factorization_pos h hp hpN
  have hb1 := factorization_pos h hq hqN
  have hpo := odd_of_dvd h hpN
  have hqo := odd_of_dvd h hqN
  have hne : p ≠ q := hpq.ne
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | _
    · subst h2; exact absurd hpo (by decide)
    · have := hp.two_le
      obtain ⟨k, hk⟩ := hpo
      omega
  rcases Nat.lt_or_ge (N.factorization p) 3 with ha | ha
  · interval_cases ha2 : N.factorization p
    · -- `p` is special with exponent one; `q` has even exponent at least two.
      have hodd : Odd (N.factorization p) := by rw [ha2]; decide
      obtain ⟨j, hj⟩ := even_factorization_of_ne h hp hodd hq hne.symm
      have hb2 : 2 ≤ N.factorization q := by omega
      have hnd : ¬ q ∣ σ 1 (p ^ N.factorization p) := by
        rw [ha2, sigma_prime_one hp]
        intro hd
        have := Nat.le_of_dvd (by omega) hd
        have hq1 : q = p + 1 := by omega
        rw [hq1] at hqo
        exact (Nat.not_even_iff_odd.mpr hqo) hpo.add_one
      have hle := Nat.le_of_dvd (by omega) (pow_mul_sigma_mul_sigma_dvd h hq hp hne.symm hnd)
      rw [ha2, sigma_prime_one hp] at hle
      have hX : q ^ 2 ≤ q ^ N.factorization q := Nat.pow_le_pow_right hq.pos hb2
      have hY := pow_lt_sigma hq (show 1 ≤ N.factorization q by omega)
      have h3 : p ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hpq.le 3
      have hXY : q ^ 4 ≤ q ^ N.factorization q * σ 1 (q ^ N.factorization q) := by
        calc q ^ 4 = q ^ 2 * q ^ 2 := by ring
          _ ≤ _ := Nat.mul_le_mul hX (hX.trans hY.le)
      calc p ^ 4 * q = p ^ 3 * (p * q) := by ring
        _ ≤ q ^ 3 * (p * q) := Nat.mul_le_mul_right _ h3
        _ = q ^ 4 * p := by ring
        _ < q ^ 4 * (p + 1) := Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos hq.pos 4)
        _ ≤ (q ^ N.factorization q * σ 1 (q ^ N.factorization q)) * (p + 1) :=
            Nat.mul_le_mul_right _ hXY
        _ = _ := by ring
        _ ≤ 2 * N := hle
    · rcases Nat.lt_or_ge (N.factorization q) 2 with hb | hb
      · exact pow_four_mul_lt_of_two_one h hp hq hne hqN ha2 (by omega)
      · -- Both exponents at least two: `q ^ 2 ∤ σ(p ^ 2)` since `σ(p ^ 2) < q ^ 2`.
        set A := p ^ 2 * σ 1 (p ^ 2) with hA
        have hAd : A ∣ 2 * N := by
          have := pow_mul_sigma_dvd h hp; rwa [ha2] at this
        have hBd : q ^ 2 ∣ 2 * N :=
          ((hq.pow_dvd_iff_le_factorization h.ne_zero).mpr hb).trans (dvd_mul_left _ _)
        have hsq := sigma_prime_sq hp
        have hlt : σ 1 (p ^ 2) < q ^ 2 := by
          rw [hsq]; unfold phi3; nlinarith
        have hg : Nat.gcd A (q ^ 2) ≤ q := by
          obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hq).mp (Nat.gcd_dvd_right A (q ^ 2))
          interval_cases k
          · rw [hk']; simp; exact hq.pos
          · rw [hk', pow_one]
          · exfalso
            have hdA : q ^ 2 ∣ A := hk' ▸ Nat.gcd_dvd_left A (q ^ 2)
            have hcop : Nat.Coprime (q ^ 2) (p ^ 2) :=
              Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hp).mpr hne.symm)
            have := Nat.le_of_dvd (sigma_pos 1 _ (by positivity)) (hcop.dvd_of_dvd_mul_left hdA)
            omega
        have hm := mul_le_gcd_mul hAd hBd (by omega)
        have hAq : A * q ≤ 2 * N := by
          have h' : q * (A * q) ≤ q * (2 * N) := by
            calc q * (A * q) = A * q ^ 2 := by ring
              _ ≤ Nat.gcd A (q ^ 2) * (2 * N) := hm
              _ ≤ q * (2 * N) := Nat.mul_le_mul_right _ hg
          exact Nat.le_of_mul_le_mul_left h' hq.pos
        have hσ := pow_lt_sigma hp (show 1 ≤ 2 by omega)
        calc p ^ 4 * q = p ^ 2 * p ^ 2 * q := by ring
          _ < p ^ 2 * σ 1 (p ^ 2) * q :=
            Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hσ (by positivity)) hq.pos
          _ ≤ 2 * N := hAq
  · -- Exponent at least three, hence at least four (an odd exponent is `≡ 1 (mod 4)`).
    have ha4 : 4 ≤ N.factorization p := by
      by_contra hlt
      have h3 : N.factorization p = 3 := by omega
      have := (special_mod_four h hp (by rw [h3]; decide)).2
      omega
    have hd : p ^ 4 * q ∣ N :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (Nat.Coprime.pow_left _ ((Nat.coprime_primes hp hq).mpr hne))
        ((hp.pow_dvd_iff_le_factorization h.ne_zero).mpr ha4) hqN
    have := Nat.le_of_dvd hN hd
    omega

/-- Zelinsky: every prime factor `p` other than the largest one satisfies `p ^ 5 < 2 * N`;
in particular `p_{k-1} < (2N)^{1/5}`. -/
theorem pow_five_lt_of_lt (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p < q) : p ^ 5 < 2 * N := by
  have := pow_four_mul_lt h hp hq hpN hqN hpq
  calc p ^ 5 = p ^ 4 * p := by ring
    _ < p ^ 4 * q := Nat.mul_lt_mul_of_pos_left hpq (pow_pos hp.pos 4)
    _ < 2 * N := this

/-! ## Part 4: Acquaah and Konyagin -/

/-- Pure arithmetic step: `r ≥ 3`, `x ≥ 1`, `(r - 1) s ≥ (r - 2) x + 1` give
`3 (r - 1) s ^ 2 ≥ 2 r x` (written with `r = k + 1`). -/
private lemma ak_arith {k x s : ℕ} (hk : 2 ≤ k) (hx : 1 ≤ x) (hy : (k - 1) * x + 1 ≤ k * s) :
    2 * (k + 1) * x ≤ 3 * k * s ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hy' : (j + 1) * x + 1 ≤ (j + 2) * s := by
    simpa [show j + 2 - 1 = j + 1 by omega] using hy
  have hsq := Nat.mul_le_mul hy' hy'
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have key : 2 * (j + 3) * (j + 2) * (y + 1) ≤ 3 * ((j + 1) * (y + 1) + 1) * ((j + 1) * (y + 1) + 1) :=
    Nat.le.intro (k := 3 * (j + 1) ^ 2 * y ^ 2 + (4 * j ^ 2 + 8 * j) * y + (j ^ 2 + 2 * j))
      (by ring)
  have : (j + 2) * (2 * (j + 2 + 1) * (y + 1)) ≤ (j + 2) * (3 * (j + 2) * s ^ 2) := by
    calc (j + 2) * (2 * (j + 2 + 1) * (y + 1)) = 2 * (j + 3) * (j + 2) * (y + 1) := by ring
      _ ≤ 3 * (((j + 1) * (y + 1) + 1) * ((j + 1) * (y + 1) + 1)) := by rw [← mul_assoc]; exact key
      _ ≤ 3 * ((j + 2) * s * ((j + 2) * s)) := Nat.mul_le_mul_left 3 hsq
      _ = (j + 2) * (3 * (j + 2) * s ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- Acquaah and Konyagin: every prime factor `p` of an odd perfect number satisfies
`p ^ 3 < 3 * N`. For exponent at least two this follows from `p ^ 4 < 2 * N`. For `p ∥ N`,
take a component `r ^ c` with `p ∣ σ(r ^ c) = p * s`, let `r ^ e = gcd(p + 1, r ^ c)`; then
`r ^ c * σ(r ^ c) * (p + 1) ≤ 2 N r ^ e`, and `r ^ e ∣ s + (1 + r + ... + r ^ (e - 1))` forces
`s` large enough. -/
theorem pow_three_lt_three_mul (h : OddPerfect N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    p ^ 3 < 3 * N := by
  have hN := h.pos
  have ha1 := factorization_pos h hp hpN
  rcases Nat.lt_or_ge (N.factorization p) 2 with ha | ha
  swap
  · have := pow_four_lt_of_two_le h hp ha
    have : p ^ 3 ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have ha1' : N.factorization p = 1 := by omega
  have hpo := odd_of_dvd h hpN
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpo (by decide)
  have hpmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩
  obtain ⟨r, hrp, hrmem, -, hdvd⟩ := exists_sigmaEdge_into h.perfect hpmem hp2
  have hr := Nat.prime_of_mem_primeFactors hrmem
  have hrN := Nat.dvd_of_mem_primeFactors hrmem
  have hro := odd_of_dvd h hrN
  have hr3 : 3 ≤ r := by
    rcases hr.eq_two_or_odd' with h2 | _
    · subst h2; exact absurd hro (by decide)
    · have := hr.two_le; obtain ⟨k, hk⟩ := hro; omega
  set c := N.factorization r with hc
  set D := r ^ c with hD
  set S := σ 1 D with hS
  obtain ⟨s, hs⟩ := hdvd
  have hS0 : 0 < S := sigma_pos 1 _ (by positivity)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0] at hs; omega
    · exact h0
  -- The two divisors of `2 * N`.
  have hAd : D * p ∣ 2 * N :=
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (Nat.Coprime.pow_left _ ((Nat.coprime_primes hr hp).mpr hrp))
      (Nat.ordProj_dvd N r) hpN).trans (dvd_mul_left _ _)
  have hBd : S * (p + 1) ∣ 2 * N := by
    have := sigma_mul_sigma_dvd h hr hp hrp
    rwa [ha1', sigma_prime_one hp] at this
  set x := Nat.gcd (p + 1) D with hx
  have hgcd : Nat.gcd (D * p) (S * (p + 1)) ≤ x * p := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul _ ((Nat.coprime_primes hr hp).mpr hrp |>.pow_left c)]
    have h1 : Nat.gcd (S * (p + 1)) D = x := by
      have hcop : Nat.Coprime S D := (coprime_sigma_prime_pow hr c).pow_right c
      rw [Nat.Coprime.gcd_mul_left_cancel _ hcop]
    rw [h1]
    exact Nat.mul_le_mul_left _ (Nat.le_of_dvd hp.pos (Nat.gcd_dvd_right _ _))
  have hmain : D * S * (p + 1) ≤ 2 * N * x := by
    have hm := mul_le_gcd_mul hAd hBd (by omega)
    have : p * (D * S * (p + 1)) ≤ p * (2 * N * x) := by
      calc p * (D * S * (p + 1)) = D * p * (S * (p + 1)) := by ring
        _ ≤ Nat.gcd (D * p) (S * (p + 1)) * (2 * N) := hm
        _ ≤ x * p * (2 * N) := Nat.mul_le_mul_right _ hgcd
        _ = p * (2 * N * x) := by ring
    exact Nat.le_of_mul_le_mul_left this hp.pos
  -- The congruence: `x = r ^ e` with `e ≤ c` and `x ∣ s + (1 + r + ... + r ^ (e - 1))`.
  obtain ⟨e, he, hxe⟩ := (Nat.dvd_prime_pow hr).mp (Nat.gcd_dvd_right (p + 1) D)
  rw [← hx] at hxe
  set u := ∑ i ∈ Finset.range e, r ^ i with hu
  have hSsplit : S = u + x * ∑ i ∈ Finset.range (c + 1 - e), r ^ i := by
    rw [hS, hD, sigma_one_apply_prime_pow hr, hxe, Finset.mul_sum,
      show c + 1 = e + (c + 1 - e) by omega, Finset.sum_range_add]
    simp [pow_add]
    exact hu.symm
  have hxdvd : x ∣ u + s := by
    have h1 : x ∣ (p + 1) * s := (Nat.gcd_dvd_left _ _).mul_right s
    have h2 : (p + 1) * s = (u + s) + x * ∑ i ∈ Finset.range (c + 1 - e), r ^ i := by
      rw [add_mul, one_mul, ← hs, hSsplit]; ring
    rw [h2] at h1
    exact (Nat.dvd_add_left (dvd_mul_right _ _)).mp h1
  have hxle : x ≤ u + s := Nat.le_of_dvd (by omega) hxdvd
  have hx1 : 1 ≤ x := Nat.pos_of_ne_zero (by
    rw [hx]; exact (Nat.gcd_pos_of_pos_left _ (by omega)).ne')
  have hgu : (r - 1) * u + 1 = x := by
    have := geom_sum_mul_add (r - 1) e
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at this
    rw [hxe, ← this, hu, mul_comm]
  have hgS : (r - 1) * S + 1 = r * D := by
    rw [hS, hD, pred_mul_sigma_add_one hr, pow_succ, mul_comm]
  -- Arithmetic.
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel] at hgu hgS
  have hk2 : 2 ≤ k := by omega
  have hy : (k - 1) * x + 1 ≤ k * s := by
    have h1 : k * x ≤ k * u + k * s := by rw [← mul_add]; exact Nat.mul_le_mul_left k hxle
    have h2 : (k - 1) * x + x = k * x := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    omega
  have hq1 := ak_arith hk2 hx1 hy
  -- `3 D s > 2 x p`.
  have hDs : 2 * x * p < 3 * D * s := by
    have : (k + 1) * (2 * x * p) < (k + 1) * (3 * D * s) := by
      have e1 : (k + 1) * (3 * D * s) = 3 * s * (k * S + 1) := by
        rw [hgS]; ring
      rw [e1, hs]
      calc (k + 1) * (2 * x * p) = (2 * (k + 1) * x) * p := by ring
        _ ≤ (3 * k * s ^ 2) * p := Nat.mul_le_mul_right p hq1
        _ < (3 * k * s ^ 2) * p + 3 * s := by omega
        _ = 3 * s * (k * (p * s) + 1) := by ring
    exact Nat.lt_of_mul_lt_mul_left this
  have hfin : 2 * x * p ^ 3 < 2 * x * (3 * N) := by
    have h3 : 2 * x * p * p * (p + 1) < 3 * D * s * p * (p + 1) :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hDs hp.pos) (by omega)
    have h4 : 3 * (D * S * (p + 1)) ≤ 3 * (2 * N * x) := Nat.mul_le_mul_left 3 hmain
    calc 2 * x * p ^ 3 ≤ 2 * x * p * p * (p + 1) := by
          rw [show 2 * x * p * p * (p + 1) = 2 * x * p ^ 3 + 2 * x * p * p by ring]; omega
      _ < 3 * D * s * p * (p + 1) := h3
      _ = 3 * (D * S * (p + 1)) := by rw [hs]; ring
      _ ≤ 3 * (2 * N * x) := h4
      _ = 2 * x * (3 * N) := by ring
  exact Nat.lt_of_mul_lt_mul_left hfin

/-- The case of `pow_four_mul_pow_four_lt` where `p ∥ N`. -/
private lemma pow_four_mul_pow_four_lt_aux (h : OddPerfect N) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q) (ha : N.factorization p = 1) :
    (p * q) ^ 4 < 6 * N ^ 2 := by
  have hN := h.pos
  have hb1 := factorization_pos h hq hqN
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hp (by rw [ha]; decide) hq hpq.symm
  have h3 := pow_three_lt_three_mul h hp hpN
  rcases Nat.lt_or_ge (N.factorization q) 3 with hb | hb
  · have hq4 := pow_four_mul_lt_of_two_one h hq hp hpq.symm hpN (by omega) ha
    calc (p * q) ^ 4 = (q ^ 4 * p) * p ^ 3 := by ring
      _ < (2 * N) * (3 * N) := Nat.mul_lt_mul'' hq4 h3
      _ = 6 * N ^ 2 := by ring
  · have hq8 : q ^ 8 < 2 * N :=
      lt_of_le_of_lt (Nat.pow_le_pow_right hq.pos (by omega))
        (pow_two_mul_factorization_lt h hq hqN)
    have hp2 := sq_lt_two_mul h hp hpN
    have h8 : ((p * q) ^ 4) ^ 2 < (6 * N ^ 2) ^ 2 := by
      calc ((p * q) ^ 4) ^ 2 = q ^ 8 * (p ^ 3 * p ^ 3) * p ^ 2 := by ring
        _ < (2 * N) * ((3 * N) * (3 * N)) * (2 * N) :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hq8 (Nat.mul_lt_mul'' h3 h3)) hp2
        _ = (6 * N ^ 2) ^ 2 := by ring
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h8

/-- Zelinsky's Theorem 2 in integer form, for any two distinct prime factors `p ≠ q`:
`(p * q) ^ 4 < 6 * N ^ 2`. For the two largest primes this is `p_{k-1} p_k < 6^{1/4} N^{1/2}`. -/
theorem pow_four_mul_pow_four_lt (h : OddPerfect N) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpN : p ∣ N) (hqN : q ∣ N) (hpq : p ≠ q) : (p * q) ^ 4 < 6 * N ^ 2 := by
  have hN := h.pos
  have ha1 := factorization_pos h hp hpN
  have hb1 := factorization_pos h hq hqN
  by_cases ha : N.factorization p = 1
  · exact pow_four_mul_pow_four_lt_aux h hp hq hpN hqN hpq ha
  by_cases hb : N.factorization q = 1
  · rw [mul_comm]; exact pow_four_mul_pow_four_lt_aux h hq hp hqN hpN hpq.symm hb
  have h1 := pow_four_lt_of_two_le h hp (by omega)
  have h2 := pow_four_lt_of_two_le h hq (by omega)
  calc (p * q) ^ 4 = p ^ 4 * q ^ 4 := by ring
    _ < (2 * N) * (2 * N) := Nat.mul_lt_mul'' h1 h2
    _ ≤ 6 * N ^ 2 := by nlinarith

end OddPerfect

#print axioms OddPerfect.sigma_mul_sigma_dvd
#print axioms OddPerfect.pow_mul_sigma_dvd
#print axioms OddPerfect.pow_two_mul_factorization_lt
#print axioms OddPerfect.sq_lt_two_mul
#print axioms OddPerfect.pow_four_lt_of_two_le
#print axioms OddPerfect.pow_four_lt_of_even
#print axioms OddPerfect.eq_one_or_two_or_four_of_dvd_phi3_of_dvd_succ
#print axioms OddPerfect.prime_dvd_phi3_dvd_succ
#print axioms OddPerfect.three_thirteen_two_cycle
#print axioms OddPerfect.prime_two_cycle_succ
#print axioms OddPerfect.phi6_two_cycle
#print axioms OddPerfect.pow_mul_sigma_mul_sigma_dvd
#print axioms OddPerfect.pow_mul_sigma_mul_prime_dvd
#print axioms OddPerfect.pow_four_mul_lt_of_two_one
#print axioms OddPerfect.pow_four_mul_lt
#print axioms OddPerfect.pow_five_lt_of_lt
#print axioms OddPerfect.pow_three_lt_three_mul
#print axioms OddPerfect.pow_four_mul_pow_four_lt
