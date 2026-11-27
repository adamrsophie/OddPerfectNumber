import OddPerfect.SpecialPrime
import OddPerfect.TwoExceptionsGeneralCore

/-!
# Three prime power components of an odd perfect number

For every odd perfect number `N` and every set `C` of at most three prime factors of `N`, the
product of the abundancies `σ(c ^ e_c) / c ^ e_c` over `c ∈ C` is at most `52514 / 26325`.
The constant is the abundancy of `3 ^ 4 * 5 ^ 2 * 13`. The proof bounds each component by
`c / (c - 1)` and settles the remaining sets `{3, 5, 7}`, `{3, 5, 11}`, `{3, 5, 13}` by the
exponent facts (a prime `≡ 3 (mod 4)` has an even exponent) and by the fact that the
components over any set of prime factors multiply to at most two.

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace ThreeGap

open OddPerfect.TwoExcGen (ab ab_anti ab_nonneg prod_ab_le_pow)

theorem one_le_abundancy_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : 1 ≤ abundancy (p ^ k) := by
  rw [abundancy_prime_pow hp]
  have h := Finset.single_le_sum (f := fun i => ((p : ℚ)⁻¹) ^ i) (fun i _ => by positivity)
    (Finset.mem_range.mpr (Nat.succ_pos k))
  simpa using h

theorem lt_of_ab {p k : ℕ} (hp : p.Prime) {r : ℚ} (hr : (p : ℚ) / (p - 1) = r) :
    abundancy (p ^ k) < r := hr ▸ abundancy_prime_pow_lt hp k

theorem mul3_le {x y z a b c : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ha : x ≤ a)
    (hb : y ≤ b) (hc : z ≤ c) : x * y * z ≤ a * b * c :=
  mul_le_mul (mul_le_mul ha hb hy (hx.trans ha)) hc hz (mul_nonneg (hx.trans ha) (hy.trans hb))

/-- The components over a set of prime factors multiply to at most two. -/
theorem prod_le_two {N : ℕ} (h : OddPerfect N) {C : Finset ℕ} (hC : C ⊆ N.primeFactors) :
    ∏ c ∈ C, abundancy (c ^ N.factorization c) ≤ 2 := by
  have h2 : abundancy N = 2 := (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  rw [abundancy_eq_prod_primeFactors h.ne_zero, ← Finset.prod_sdiff hC] at h2
  have h1 : 1 ≤ ∏ c ∈ N.primeFactors \ C, abundancy (c ^ N.factorization c) :=
    Finset.one_le_prod₀ fun c hc =>
      one_le_abundancy_pow (Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hc)) _
  have h0 : 0 ≤ ∏ c ∈ C, abundancy (c ^ N.factorization c) := Finset.prod_nonneg fun c hc =>
    zero_le_one.trans (one_le_abundancy_pow (Nat.prime_of_mem_primeFactors (hC hc)) _)
  have := le_mul_of_one_le_left h0 h1
  linarith

theorem even_of_mod_four {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (h4 : p % 4 = 3) :
    Even (N.factorization p) := by
  by_contra hne
  have := (special_mod_four h hp (Nat.not_even_iff_odd.mp hne)).1
  omega

theorem one_le_fac {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N) :
    1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN

/-- Distinct odd numbers at least `7`, at most two of them. -/
theorem pair7 {s : Finset ℕ} (hs : ∀ p ∈ s, 7 ≤ p ∧ p % 2 = 1) (hk : s.card ≤ 2) :
    ∏ p ∈ s, ab p ≤ 21 / 16 := by
  have ab_7 : ab 7 = 7 / 6 := by norm_num [ab]
  have ab_9 : ab 9 = 9 / 8 := by norm_num [ab]
  rcases Nat.lt_or_ge s.card 2 with h | h
  · have := prod_ab_le_pow (a := 7) (k := 1) (by norm_num) (fun p hp => (hs p hp).1)
      (by omega)
    rw [ab_7, pow_one] at this
    linarith
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (le_antisymm hk h)
    rw [Finset.prod_pair hxy]
    have hx := hs x (by simp)
    have hy := hs y (by simp)
    have key : ∀ a b : ℕ, 7 ≤ a → a % 2 = 1 → b % 2 = 1 → a < b → ab a * ab b ≤ 21 / 16 := by
      intro a b ha _ hb hab
      have e1 := ab_anti (a := 7) (by norm_num) ha
      have e2 := ab_anti (a := 9) (by norm_num) (show 9 ≤ b by omega)
      rw [ab_7] at e1
      rw [ab_9] at e2
      have hb0 := ab_nonneg (p := b) (by omega)
      calc ab a * ab b ≤ 7 / 6 * (9 / 8) := mul_le_mul e1 e2 hb0 (by norm_num)
        _ = 21 / 16 := by norm_num
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact key x y hx.1 hx.2 hy.2 hlt
    · rw [mul_comm]
      exact key y x hy.1 hy.2 hx.2 hlt

/-- The sets `{3, 5, t}` with `t ≥ 7` prime. -/
theorem triple {N t : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N) (ht : t.Prime)
    (htN : t ∣ N) (h7 : 7 ≤ t)
    (h2 : abundancy (3 ^ N.factorization 3) * (abundancy (5 ^ N.factorization 5) *
      abundancy (t ^ N.factorization t)) ≤ 2) :
    abundancy (3 ^ N.factorization 3) * (abundancy (5 ^ N.factorization 5) *
      abundancy (t ^ N.factorization t)) ≤ 52514 / 26325 := by
  rw [← mul_assoc] at h2 ⊢
  have p3 := Nat.prime_three
  have p5 := Nat.prime_five
  have x1 := one_le_abundancy_pow p3 (N.factorization 3)
  have y1 := one_le_abundancy_pow p5 (N.factorization 5)
  have z1 := one_le_abundancy_pow ht (N.factorization t)
  have x2 : abundancy (3 ^ N.factorization 3) < 3 / 2 := lt_of_ab p3 (by norm_num)
  have y2 : abundancy (5 ^ N.factorization 5) < 5 / 4 := lt_of_ab p5 (by norm_num)
  have z2 := abundancy_prime_pow_lt ht (N.factorization t)
  have e3 := one_le_fac h p3 h3
  obtain ⟨j3, hj3⟩ := even_of_mod_four h p3 (by norm_num)
  have e5 := one_le_fac h p5 h5
  have et := one_le_fac h ht htN
  have v32 : abundancy (3 ^ 2) = 13 / 9 := by
    rw [abundancy_prime_pow p3]; norm_num [Finset.sum_range_succ]
  have v34 : abundancy (3 ^ 4) = 121 / 81 := by
    rw [abundancy_prime_pow p3]; norm_num [Finset.sum_range_succ]
  have v36 : abundancy (3 ^ 6) = 1093 / 729 := by
    rw [abundancy_prime_pow p3]; norm_num [Finset.sum_range_succ]
  have v51 : abundancy (5 ^ 1) = 6 / 5 := by
    rw [abundancy_prime_pow p5]; norm_num [Finset.sum_range_succ]
  have v52 : abundancy (5 ^ 2) = 31 / 25 := by
    rw [abundancy_prime_pow p5]; norm_num [Finset.sum_range_succ]
  have v53 : abundancy (5 ^ 3) = 156 / 125 := by
    rw [abundancy_prime_pow p5]; norm_num [Finset.sum_range_succ]
  rcases Nat.lt_or_ge t 17 with hlt | hge
  swap
  · have hz : abundancy (t ^ N.factorization t) ≤ 17 / 16 := by
      have := ab_anti (a := 17) (p := t) (by norm_num) hge
      have h17 : ab 17 = 17 / 16 := by norm_num [ab]
      rw [h17] at this
      exact z2.le.trans this
    have := mul3_le (by linarith) (by linarith) (by linarith) x2.le y2.le hz
    linarith
  have ht' : t = 7 ∨ t = 11 ∨ t = 13 := by
    interval_cases t <;> first | omega | (exfalso; revert ht; decide)
  -- the exponent of `3` is `2` or at least `4`
  have hx : abundancy (3 ^ N.factorization 3) = 13 / 9 ∨
      121 / 81 ≤ abundancy (3 ^ N.factorization 3) := by
    rcases Nat.lt_or_ge (N.factorization 3) 4 with h4 | h4
    · left
      rw [show N.factorization 3 = 2 by omega, v32]
    · right
      rw [← v34]
      exact abundancy_prime_pow_mono p3 h4
  have hx2 : 13 / 9 ≤ abundancy (3 ^ N.factorization 3) := by
    rw [← v32]
    exact abundancy_prime_pow_mono p3 (by omega)
  have hy1 : 6 / 5 ≤ abundancy (5 ^ N.factorization 5) := by
    rw [← v51]
    exact abundancy_prime_pow_mono p5 e5
  rcases ht' with rfl | rfl | rfl
  · -- `t = 7`: impossible
    obtain ⟨j7, hj7⟩ := even_of_mod_four h ht (by norm_num)
    have v72 : abundancy (7 ^ 2) = 57 / 49 := by
      rw [abundancy_prime_pow ht]; norm_num [Finset.sum_range_succ]
    have hz : 57 / 49 ≤ abundancy (7 ^ N.factorization 7) := by
      rw [← v72]
      exact abundancy_prime_pow_mono ht (by omega)
    have := mul3_le (by norm_num) (by norm_num) (by norm_num) hx2 hy1 hz
    linarith
  · -- `t = 11`
    replace z2 : abundancy (11 ^ N.factorization 11) < 11 / 10 := lt_of_ab ht (by norm_num)
    rcases hx with hx | hx
    · have := mul3_le (by linarith) (by linarith) (by linarith) hx.le y2.le z2.le
      linarith
    rcases Nat.lt_or_ge (N.factorization 5) 2 with h52 | h52
    · have hy : abundancy (5 ^ N.factorization 5) = 6 / 5 := by
        rw [show N.factorization 5 = 1 by omega, v51]
      have := mul3_le (by linarith) (by linarith) (by linarith) x2.le hy.le z2.le
      linarith
    · obtain ⟨j11, hj11⟩ := even_of_mod_four h ht (by norm_num)
      have v112 : abundancy (11 ^ 2) = 133 / 121 := by
        rw [abundancy_prime_pow ht]; norm_num [Finset.sum_range_succ]
      have hz : 133 / 121 ≤ abundancy (11 ^ N.factorization 11) := by
        rw [← v112]
        exact abundancy_prime_pow_mono ht (by omega)
      have hy : 31 / 25 ≤ abundancy (5 ^ N.factorization 5) := by
        rw [← v52]
        exact abundancy_prime_pow_mono p5 h52
      have := mul3_le (by norm_num) (by norm_num) (by norm_num) hx hy hz
      linarith
  · -- `t = 13`
    replace z2 : abundancy (13 ^ N.factorization 13) < 13 / 12 := lt_of_ab ht (by norm_num)
    rcases hx with hx | hx
    · have := mul3_le (by linarith) (by linarith) (by linarith) hx.le y2.le z2.le
      linarith
    rcases Nat.lt_or_ge (N.factorization 5) 2 with h52 | h52
    · have hy : abundancy (5 ^ N.factorization 5) = 6 / 5 := by
        rw [show N.factorization 5 = 1 by omega, v51]
      have := mul3_le (by linarith) (by linarith) (by linarith) x2.le hy.le z2.le
      linarith
    have hy : 31 / 25 ≤ abundancy (5 ^ N.factorization 5) := by
      rw [← v52]
      exact abundancy_prime_pow_mono p5 h52
    have v131 : abundancy (13 ^ 1) = 14 / 13 := by
      rw [abundancy_prime_pow ht]; norm_num [Finset.sum_range_succ]
    have v132 : abundancy (13 ^ 2) = 183 / 169 := by
      rw [abundancy_prime_pow ht]; norm_num [Finset.sum_range_succ]
    have hz1 : 14 / 13 ≤ abundancy (13 ^ N.factorization 13) := by
      rw [← v131]
      exact abundancy_prime_pow_mono ht et
    rcases Nat.lt_or_ge (N.factorization 13) 2 with h132 | h132
    swap
    · have hz : 183 / 169 ≤ abundancy (13 ^ N.factorization 13) := by
        rw [← v132]
        exact abundancy_prime_pow_mono ht h132
      have := mul3_le (by norm_num) (by norm_num) (by norm_num) hx hy hz
      linarith
    have hz : abundancy (13 ^ N.factorization 13) = 14 / 13 := by
      rw [show N.factorization 13 = 1 by omega, v131]
    rcases Nat.lt_or_ge (N.factorization 5) 3 with h53 | h53
    swap
    · have hy3 : 156 / 125 ≤ abundancy (5 ^ N.factorization 5) := by
        rw [← v53]
        exact abundancy_prime_pow_mono p5 h53
      have := mul3_le (by norm_num) (by norm_num) (by norm_num) hx hy3 hz1
      linarith
    have hy2 : abundancy (5 ^ N.factorization 5) = 31 / 25 := by
      rw [show N.factorization 5 = 2 by omega, v52]
    rcases Nat.lt_or_ge (N.factorization 3) 6 with h36 | h36
    swap
    · have hx6 : 1093 / 729 ≤ abundancy (3 ^ N.factorization 3) := by
        rw [← v36]
        exact abundancy_prime_pow_mono p3 h36
      have := mul3_le (by norm_num) (by norm_num) (by norm_num) hx6 hy hz1
      linarith
    have h4 : 4 ≤ N.factorization 3 := by
      by_contra h4
      have : abundancy (3 ^ N.factorization 3) = 13 / 9 := by
        rw [show N.factorization 3 = 2 by omega, v32]
      linarith
    have hx4 : abundancy (3 ^ N.factorization 3) = 121 / 81 := by
      rw [show N.factorization 3 = 4 by omega, v34]
    rw [hx4, hy2, hz]
    norm_num

theorem main {N : ℕ} (h : OddPerfect N) {C : Finset ℕ} (hC : C ⊆ N.primeFactors)
    (hcard : C.card ≤ 3) :
    ∏ c ∈ C, abundancy (c ^ N.factorization c) ≤ 52514 / 26325 := by
  have hpr : ∀ c ∈ C, c.Prime := fun c hc => Nat.prime_of_mem_primeFactors (hC hc)
  have hod : ∀ c ∈ C, 3 ≤ c ∧ c % 2 = 1 := by
    intro c hc
    rcases (hpr c hc).eq_two_or_odd with h2 | h2
    · subst h2
      exact absurd (Nat.dvd_of_mem_primeFactors (hC hc)) h.not_two_dvd
    · exact ⟨by have := (hpr c hc).two_le; omega, h2⟩
  have hFab : ∏ c ∈ C, abundancy (c ^ N.factorization c) ≤ ∏ c ∈ C, ab c :=
    Finset.prod_le_prod₀
      (fun c hc => zero_le_one.trans (one_le_abundancy_pow (hpr c hc) _))
      (fun c hc => (abundancy_prime_pow_lt (hpr c hc) _).le)
  by_cases h3 : 3 ∈ C
  swap
  · refine hFab.trans ((prod_ab_le_pow (a := 5) (k := 3) (by norm_num) ?_ hcard).trans ?_)
    · intro p hp
      have := hod p hp
      have : p ≠ 3 := by rintro rfl; exact h3 hp
      omega
    · norm_num [ab]
  by_cases h5 : 5 ∈ C
  swap
  · have hE : ∀ p ∈ C.erase 3, 7 ≤ p ∧ p % 2 = 1 := by
      intro p hp
      have hpC := Finset.mem_of_mem_erase hp
      have hp3 := Finset.ne_of_mem_erase hp
      have hp5 : p ≠ 5 := by rintro rfl; exact h5 hpC
      have := hod p hpC
      omega
    have hcE : (C.erase 3).card ≤ 2 := by rw [Finset.card_erase_of_mem h3]; omega
    refine hFab.trans ?_
    rw [← Finset.mul_prod_erase C _ h3]
    have := pair7 hE hcE
    have h3ab : ab 3 = 3 / 2 := by norm_num [ab]
    rw [h3ab]
    linarith
  have h53 : 5 ∈ C.erase 3 := Finset.mem_erase.mpr ⟨by norm_num, h5⟩
  have hDc : ((C.erase 3).erase 5).card ≤ 1 := by
    rw [Finset.card_erase_of_mem h53, Finset.card_erase_of_mem h3]; omega
  have hle2 := prod_le_two h hC
  rw [← Finset.mul_prod_erase C _ h3, ← Finset.mul_prod_erase (C.erase 3) _ h53] at hle2 ⊢
  have x2 : abundancy (3 ^ N.factorization 3) < 3 / 2 := lt_of_ab Nat.prime_three (by norm_num)
  have y2 : abundancy (5 ^ N.factorization 5) < 5 / 4 := lt_of_ab Nat.prime_five (by norm_num)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hDc with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty, mul_one]
    have y1 := one_le_abundancy_pow Nat.prime_five (N.factorization 5)
    have := mul_le_mul x2.le y2.le (by linarith) (by norm_num)
    linarith
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
    have htD : t ∈ (C.erase 3).erase 5 := by rw [ht]; exact Finset.mem_singleton_self t
    rw [ht, Finset.prod_singleton] at hle2 ⊢
    have ht5 := Finset.ne_of_mem_erase htD
    have ht3 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase htD)
    have htC := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase htD)
    have := hod t htC
    exact triple h (Nat.dvd_of_mem_primeFactors (hC h3)) (Nat.dvd_of_mem_primeFactors (hC h5))
      (hpr t htC) (Nat.dvd_of_mem_primeFactors (hC htC)) (by omega) hle2

end ThreeGap

/-- For every odd perfect number `N` and every set `C` of at most three prime factors of `N`,
the product of the component abundancies `σ(c ^ e_c) / c ^ e_c` over `c ∈ C` is at most
`52514 / 26325`, the abundancy of `3 ^ 4 * 5 ^ 2 * 13`. Restricted result; no published source
was checked; novelty not verified. The odd perfect number conjecture remains open. -/
theorem abundancy_three_components_le {N : ℕ} (h : OddPerfect N) {C : Finset ℕ}
    (hC : C ⊆ N.primeFactors) (hcard : C.card ≤ 3) :
    ∏ c ∈ C, ((σ 1 (c ^ N.factorization c) : ℚ) / ((c : ℚ) ^ N.factorization c)) ≤
      52514 / 26325 := by
  have hrw : ∏ c ∈ C, ((σ 1 (c ^ N.factorization c) : ℚ) / ((c : ℚ) ^ N.factorization c)) =
      ∏ c ∈ C, abundancy (c ^ N.factorization c) :=
    Finset.prod_congr rfl fun c _ => by rw [abundancy, Nat.cast_pow]
  rw [hrw]
  exact ThreeGap.main h hC hcard

end OddPerfect

#print axioms OddPerfect.abundancy_three_components_le
