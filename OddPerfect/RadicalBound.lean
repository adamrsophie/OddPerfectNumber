import OddPerfect.Abundancy
import OddPerfect.SmallestPrime
import OddPerfect.Euler
import OddPerfect.SpecialPrime

/-!
# Radical identities for perfect numbers

For `N` with prime factorization `∏ p ^ e_p`, write `H(N) = ∏_{p ∣ N} p/(p-1)`, `R = ∏_{p ∣ N} p`
(the radical) and `φ(R) = ∏_{p ∣ N} (p - 1)`. Following Zelinsky (arXiv 2005.12115) and
Zelinsky and Zhang (arXiv 2501.04209):

* `σ(N)/N = H(N) * ∏ (1 - p^{-(e_p+1)})` for every `N ≠ 0`; for a perfect `N` the left side is two.
* For a perfect `N`, `2 φ(R) < R`, so `H(N) - 2 ≥ 1/φ(R)`.
* Some component satisfies `p^(e_p+1) ≤ ω(N) (2 φ(R) + 1)`, and every component satisfies
  `R ≤ p^(e_p+1) (R - 2 φ(R))`, the cross multiplied form of `p^(e_p+1) ≥ H/(H - 2)`.

From Zelinsky (arXiv 2402.14234 and 2005.12118): the denominator lemma `q ≤ 2 ∏ (p_i - 1) - 1`,
the cap `h(p₁^a₁ p₂^a₂ p₃^a₃) < 255/128` for any three prime components of an odd perfect
number, and linear bounds on the second, third and fourth smallest prime factors.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- One prime power component: `σ(p^e)/p^e = p/(p-1) * (1 - 1/p^(e+1))`. -/
theorem abundancy_prime_pow_eq_mul {p : ℕ} (hp : p.Prime) (e : ℕ) :
    abundancy (p ^ e) = (p : ℚ) / (p - 1) * (1 - ((p : ℚ) ^ (e + 1))⁻¹) := by
  have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℚ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℚ) ≠ 0 := by linarith
  have hx : (1 : ℚ) - (p : ℚ)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; exact (inv_lt_one_of_one_lt₀ (by linarith)).ne'
  have key : (p : ℚ) / (p - 1) = 1 / (1 - (p : ℚ)⁻¹) := by field_simp
  rw [abundancy_prime_pow hp, key, ← inv_pow, ← geom_sum_mul_neg]
  field_simp

/-- The exact identity `σ(n)/n = H(n) * ∏_{p ∣ n} (1 - 1/p^(e_p+1))` for `n ≠ 0`. -/
theorem abundancy_eq_prod_mul_prod {n : ℕ} (hn : n ≠ 0) :
    abundancy n = (∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1)) *
      ∏ p ∈ n.primeFactors, (1 - ((p : ℚ) ^ (n.factorization p + 1))⁻¹) := by
  rw [abundancy_eq_prod_primeFactors hn, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p hp =>
    abundancy_prime_pow_eq_mul (Nat.prime_of_mem_primeFactors hp) _

/-- For a perfect `N`: `2 = H(N) * ∏_{p ∣ N} (1 - 1/p^(e_p+1))`. -/
theorem two_eq_prod_mul_prod {N : ℕ} (hN : N.Perfect) :
    2 = (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) *
      ∏ p ∈ N.primeFactors, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) := by
  rw [← abundancy_eq_prod_mul_prod hN.2.ne', (perfect_iff_abundancy_eq_two hN.2).mp hN]

/-- For a perfect `N`: `H(N) - 2 = H(N) * (1 - ∏_{p ∣ N} (1 - 1/p^(e_p+1)))`. -/
theorem prod_sub_two_eq {N : ℕ} (hN : N.Perfect) :
    (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) - 2 = (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) *
      (1 - ∏ p ∈ N.primeFactors, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹)) := by
  rw [mul_one_sub, ← two_eq_prod_mul_prod hN]

/-- `H(n) = R/φ(R)` with `R = ∏ p` and `φ(R) = ∏ (p - 1)` over the prime factors. -/
theorem prod_div_sub_one_eq_div (n : ℕ) :
    ∏ p ∈ n.primeFactors, (p : ℚ) / (p - 1) =
      ((∏ p ∈ n.primeFactors, p : ℕ) : ℚ) / ((∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) := by
  rw [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_prod]
  congr 1
  exact Finset.prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- The product `∏ (p - 1)` over the prime factors of `n` is the totient of the radical. -/
theorem totient_prod_primeFactors (n : ℕ) :
    (∏ p ∈ n.primeFactors, p).totient = ∏ p ∈ n.primeFactors, (p - 1) := by
  have hR : 0 < ∏ p ∈ n.primeFactors, p :=
    Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_prod_primeFactors,
    Nat.div_self hR, one_mul]

private theorem prod_sub_one_pos (n : ℕ) : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
  Finset.prod_pos fun p hp => by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega

private theorem one_lt_of_perfect {N : ℕ} (hN : N.Perfect) : 1 < N := by
  have := hN.2
  rcases Nat.lt_or_ge 1 N with h | h
  · exact h
  · have : N = 1 := by omega
    subst this; simp [Nat.Perfect] at hN

/-- Integrality: for a perfect `N`, `2 φ(R) < R`, that is `R - 2 φ(R)` is a positive integer. -/
theorem two_mul_prod_sub_one_lt_prod {N : ℕ} (hN : N.Perfect) :
    2 * ∏ p ∈ N.primeFactors, (p - 1) < ∏ p ∈ N.primeFactors, p := by
  have h := abundancy_lt_prod (one_lt_of_perfect hN)
  rw [(perfect_iff_abundancy_eq_two hN.2).mp hN, prod_div_sub_one_eq_div,
    lt_div_iff₀ (by exact_mod_cast prod_sub_one_pos N)] at h
  exact_mod_cast h

/-- The discreteness bound: for a perfect `N`, `H(N) - 2 ≥ 1/φ(R)`. -/
theorem inv_prod_sub_one_le_prod_sub_two {N : ℕ} (hN : N.Perfect) :
    ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ)⁻¹ ≤
      (∏ p ∈ N.primeFactors, (p : ℚ) / (p - 1)) - 2 := by
  have h := two_mul_prod_sub_one_lt_prod hN
  have hφ : (0 : ℚ) < ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast prod_sub_one_pos N
  have h' : (2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ)) + 1 ≤
      ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) := by exact_mod_cast h
  rw [prod_div_sub_one_eq_div, le_sub_iff_add_le, le_div_iff₀ hφ, add_mul, inv_mul_cancel₀ hφ.ne']
  linarith

/-- The Weierstrass product inequality `1 - ∑ x_i ≤ ∏ (1 - x_i)` for `x_i ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℚ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have ha0 := h0 a (Finset.mem_insert_self a s)
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have hP : ∏ i ∈ s, (1 - x i) ≤ 1 := Finset.prod_le_one
      (fun i hi => by linarith [h1 i (Finset.mem_insert_of_mem hi)])
      (fun i hi => by linarith [h0 i (Finset.mem_insert_of_mem hi)])
    have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    nlinarith

private theorem inv_pow_nonneg_le_one {p : ℕ} (hp : p.Prime) (e : ℕ) :
    0 ≤ ((p : ℚ) ^ (e + 1))⁻¹ ∧ ((p : ℚ) ^ (e + 1))⁻¹ ≤ 1 := by
  have : (1 : ℚ) ≤ (p : ℚ) ^ (e + 1) := one_le_pow₀ (by exact_mod_cast hp.one_le)
  exact ⟨by positivity, inv_le_one_of_one_le₀ this⟩

/-- For a perfect `N`, `∏_{p ∣ N} (1 - 1/p^(e_p+1)) = 2 φ(R)/R`. -/
private theorem prod_one_sub_eq {N : ℕ} (hN : N.Perfect) :
    ∏ p ∈ N.primeFactors, (1 - ((p : ℚ) ^ (N.factorization p + 1))⁻¹) =
      2 * ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) := by
  have h := two_eq_prod_mul_prod hN
  rw [prod_div_sub_one_eq_div] at h
  have hφ : (0 : ℚ) < ((∏ p ∈ N.primeFactors, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast prod_sub_one_pos N
  have hR : (0 : ℚ) < ((∏ p ∈ N.primeFactors, p : ℕ) : ℚ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  rw [eq_div_iff hR.ne', h]
  field_simp

/-- Some component is small: a perfect `N` has a prime factor `p` with
`p^(e_p+1) ≤ ω(N) * (2 φ(R) + 1)`. -/
theorem exists_pow_succ_le_card_mul {N : ℕ} (hN : N.Perfect) :
    ∃ p ∈ N.primeFactors, p ^ (N.factorization p + 1) ≤
      N.primeFactors.card * (2 * ∏ p ∈ N.primeFactors, (p - 1) + 1) := by
  set φR := ∏ p ∈ N.primeFactors, (p - 1)
  set R := ∏ p ∈ N.primeFactors, p
  set k := N.primeFactors.card
  set x : ℕ → ℚ := fun p => ((p : ℚ) ^ (N.factorization p + 1))⁻¹
  have hne : N.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (one_lt_of_perfect hN)
  have hk : (0 : ℚ) < k := by exact_mod_cast hne.card_pos
  have hlt := two_mul_prod_sub_one_lt_prod hN
  have hRφ : (2 * (φR : ℚ)) + 1 ≤ R := by exact_mod_cast hlt
  have hφ : (0 : ℚ) ≤ φR := by positivity
  have hR : (0 : ℚ) < R := by linarith
  have hW := one_sub_sum_le_prod_one_sub N.primeFactors x
    (fun p hp => (inv_pow_nonneg_le_one (Nat.prime_of_mem_primeFactors hp) _).1)
    (fun p hp => (inv_pow_nonneg_le_one (Nat.prime_of_mem_primeFactors hp) _).2)
  rw [prod_one_sub_eq hN] at hW
  -- `∑ x ≥ 1 - 2 φ(R)/R ≥ 1/(2 φ(R) + 1)`
  have hsum : 1 / (2 * (φR : ℚ) + 1) ≤ ∑ p ∈ N.primeFactors, x p := by
    have h1 : 1 / (2 * (φR : ℚ) + 1) ≤ 1 - 2 * φR / R := by
      rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, one_mul,
        le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hR]
      nlinarith
    linarith
  by_contra hcon
  push Not at hcon
  have hlt' : ∑ p ∈ N.primeFactors, x p <
      ∑ _p ∈ N.primeFactors, 1 / ((k : ℚ) * (2 * φR + 1)) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro p hp
    have := hcon p hp
    have hc : ((k : ℚ) * (2 * φR + 1)) < (p : ℚ) ^ (N.factorization p + 1) := by
      exact_mod_cast this
    simp only [x]
    rw [one_div]
    exact inv_strictAnti₀ (by positivity) hc
  rw [Finset.sum_const, nsmul_eq_mul] at hlt'
  have : (k : ℚ) * (1 / (k * (2 * φR + 1))) = 1 / (2 * φR + 1) := by
    field_simp
  linarith

/-- Every component is large: for a perfect `N` and each prime factor `p`,
`R ≤ p^(e_p+1) * (R - 2 φ(R))`, the cross multiplied form of `p^(e_p+1) ≥ H(N)/(H(N) - 2)`. -/
theorem prod_le_pow_succ_mul {N : ℕ} (hN : N.Perfect) {p : ℕ} (hp : p ∈ N.primeFactors) :
    ∏ p ∈ N.primeFactors, p ≤
      p ^ (N.factorization p + 1) *
        (∏ p ∈ N.primeFactors, p - 2 * ∏ p ∈ N.primeFactors, (p - 1)) := by
  set φR := ∏ p ∈ N.primeFactors, (p - 1)
  set R := ∏ p ∈ N.primeFactors, p
  set x : ℕ → ℚ := fun p => ((p : ℚ) ^ (N.factorization p + 1))⁻¹
  have hlt := two_mul_prod_sub_one_lt_prod hN
  have hR : (0 : ℚ) < R := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hP := prod_one_sub_eq hN
  rw [← Finset.mul_prod_erase _ _ hp] at hP
  have hrest : ∏ q ∈ N.primeFactors.erase p, (1 - x q) ≤ 1 := Finset.prod_le_one
    (fun q hq => by
      linarith [(inv_pow_nonneg_le_one (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq)) (N.factorization q)).2])
    (fun q hq => by
      linarith [(inv_pow_nonneg_le_one (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq)) (N.factorization q)).1])
  have hxp := inv_pow_nonneg_le_one hpp (N.factorization p)
  have hrest0 : 0 ≤ ∏ q ∈ N.primeFactors.erase p, (1 - x q) := Finset.prod_nonneg
    (fun q hq => by
      linarith [(inv_pow_nonneg_le_one (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_erase hq)) (N.factorization q)).2])
  -- `2 φ(R)/R ≤ 1 - x_p`
  have h1 : 2 * (φR : ℚ) / R ≤ 1 - x p := by
    rw [← hP]
    exact mul_le_of_le_one_right (by linarith [hxp.2]) hrest
  have hpow : (0 : ℚ) < (p : ℚ) ^ (N.factorization p + 1) := by
    have := hpp.pos; positivity
  have h2 : (R : ℚ) ≤ (p : ℚ) ^ (N.factorization p + 1) * (R - 2 * φR) := by
    rw [div_le_iff₀ hR] at h1
    simp only [x] at h1
    have e : ((p : ℚ) ^ (N.factorization p + 1))⁻¹ * (p : ℚ) ^ (N.factorization p + 1) = 1 :=
      inv_mul_cancel₀ hpow.ne'
    nlinarith
  have hcast : ((R - 2 * φR : ℕ) : ℚ) = R - 2 * φR := by
    rw [Nat.cast_sub hlt.le, Nat.cast_mul, Nat.cast_two]
  rw [← hcast] at h2
  exact_mod_cast h2

/-- Zelinsky's denominator lemma (arXiv 2402.14234): if `S` is a finite set of odd numbers
greater than one (for instance distinct odd primes) with `∏_{p ∈ S} p/(p-1) ≤ 2`, and `q > 1`
satisfies `∏_{p ∈ S} p/(p-1) * q/(q-1) > 2`, then `q ≤ 2 ∏_{p ∈ S} (p - 1) - 1`. -/
theorem le_two_mul_prod_sub_one_sub_one {S : Finset ℕ} (hS : ∀ p ∈ S, Odd p ∧ 1 < p)
    (hle : ∏ p ∈ S, (p : ℚ) / (p - 1) ≤ 2) {q : ℕ} (hq : 1 < q)
    (hgt : 2 < (∏ p ∈ S, (p : ℚ) / (p - 1)) * ((q : ℚ) / (q - 1))) :
    q ≤ 2 * ∏ p ∈ S, (p - 1) - 1 := by
  set A := ∏ p ∈ S, p
  set B := ∏ p ∈ S, (p - 1)
  have hB : 0 < B := Finset.prod_pos fun p hp => by have := (hS p hp).2; omega
  have hAodd : Odd A := Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
    fun p hp => (hS p hp).1
  have hH : ∏ p ∈ S, (p : ℚ) / (p - 1) = (A : ℚ) / B := by
    rw [Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_prod]
    congr 1
    exact Finset.prod_congr rfl fun p hp => by
      rw [Nat.cast_sub (hS p hp).2.le, Nat.cast_one]
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  rw [hH, div_le_iff₀ hBq] at hle
  have hAB : A ≤ 2 * B := by exact_mod_cast (by linarith : (A : ℚ) ≤ 2 * B)
  have hAB' : A + 1 ≤ 2 * B := by
    rcases Nat.lt_or_ge A (2 * B) with h | h
    · omega
    · exfalso
      have : A = 2 * B := le_antisymm hAB h
      rw [this] at hAodd
      exact (Nat.not_even_iff_odd.mpr hAodd) (even_two_mul B)
  have hAB'' : (A : ℚ) + 1 ≤ 2 * B := by exact_mod_cast hAB'
  have hq' : (1 : ℚ) < q := by exact_mod_cast hq
  rw [hH, div_mul_div_comm, lt_div_iff₀ (by nlinarith)] at hgt
  have : (q : ℚ) < 2 * B := by nlinarith
  have : q < 2 * B := by exact_mod_cast this
  omega

private theorem odd_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : Odd p :=
  (Nat.prime_of_mem_primeFactors hp).odd_of_ne_two fun h2 =>
    h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp)

private theorem three_le_of_mem {N p : ℕ} (h : OddPerfect N) (hp : p ∈ N.primeFactors) : 3 ≤ p := by
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  have := odd_of_mem h hp
  rcases this with ⟨j, rfl⟩; omega

private theorem f_le {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private theorem f_nonneg {x : ℕ} (hx : 1 ≤ x) : (0 : ℚ) ≤ (x : ℚ) / (x - 1) := by
  have : (1 : ℚ) ≤ x := by exact_mod_cast hx
  apply div_nonneg <;> linarith

/-- Second smallest prime factor (Zelinsky, arXiv 2005.12118, sharpened by telescoping): if
`p, q` are prime factors of an odd perfect number `N` and every prime factor other than `q` is
at least `p` (so `p` is the second smallest when `q < p`), then `p ≤ 3 ω(N) - 3`. -/
theorem second_prime_le {N p q : ℕ} (h : OddPerfect N) (hq : q ∈ N.primeFactors)
    (hp : p ∈ N.primeFactors) (hmin : ∀ r ∈ N.primeFactors, r ≠ q → p ≤ r) :
    p ≤ 3 * N.primeFactors.card - 3 := by
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hq3 := three_le_of_mem h hq
  have hT := prod_div_sub_one_le (N.primeFactors.erase q) hp2
    (fun r hr => hmin r (Finset.mem_of_mem_erase hr) (Finset.ne_of_mem_erase hr))
  rw [Finset.card_erase_of_mem hq] at hT
  have h2 := two_lt_prod_primeFactors h
  rw [← Finset.mul_prod_erase _ _ hq] at h2
  have hfq : (q : ℚ) / (q - 1) ≤ 3 / 2 := by
    have := f_le (m := 3) (by norm_num) hq3; norm_num at this ⊢; exact this
  have hk : 1 ≤ N.primeFactors.card := Finset.card_pos.mpr ⟨q, hq⟩
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp2
  have hrest0 : (0 : ℚ) ≤ ∏ r ∈ N.primeFactors.erase q, (r : ℚ) / (r - 1) :=
    Finset.prod_nonneg fun r hr =>
      f_nonneg (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hr)).one_le
  have h3 : 2 < 3 / 2 * (1 + ((N.primeFactors.card - 1 : ℕ) : ℚ) / (p - 1)) := by
    calc (2 : ℚ) < _ := h2
      _ ≤ 3 / 2 * ∏ r ∈ N.primeFactors.erase q, (r : ℚ) / (r - 1) :=
          mul_le_mul_of_nonneg_right hfq hrest0
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by norm_num)
  have h4 : (p : ℚ) - 1 < 3 * ((N.primeFactors.card - 1 : ℕ) : ℚ) := by
    have : (1 : ℚ) / 3 < ((N.primeFactors.card - 1 : ℕ) : ℚ) / (p - 1) := by linarith
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have h5 : p < 3 * (N.primeFactors.card - 1) + 1 := by
    have : (p : ℚ) < 3 * ((N.primeFactors.card - 1 : ℕ) : ℚ) + 1 := by linarith
    exact_mod_cast this
  omega

/-- Third smallest prime factor: if `q₁ < q₂` and `p` are prime factors of an odd perfect number
`N` and every prime factor other than `q₁, q₂` is at least `p` (so `p` is the third smallest when
`q₂ < p`), then `p ≤ 15 ω(N) - 30`. -/
theorem third_prime_le {N p q₁ q₂ : ℕ} (h : OddPerfect N) (hq₁ : q₁ ∈ N.primeFactors)
    (hq₂ : q₂ ∈ N.primeFactors) (hp : p ∈ N.primeFactors) (h12 : q₁ < q₂)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → p ≤ r) :
    p ≤ 15 * N.primeFactors.card - 30 := by
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hq₁3 := three_le_of_mem h hq₁
  have hq₂5 : 5 ≤ q₂ := by
    have := odd_of_mem h hq₂
    rcases this with ⟨j, rfl⟩; omega
  set S := (N.primeFactors.erase q₁).erase q₂
  have hq₂' : q₂ ∈ N.primeFactors.erase q₁ := Finset.mem_erase.mpr ⟨by omega, hq₂⟩
  have hT := prod_div_sub_one_le S hp2 (fun r hr => by
    have h1 := Finset.ne_of_mem_erase hr
    have h2 := Finset.mem_of_mem_erase hr
    exact hmin r (Finset.mem_of_mem_erase h2) (Finset.ne_of_mem_erase h2) h1)
  have hcard : S.card = N.primeFactors.card - 2 := by
    rw [Finset.card_erase_of_mem hq₂', Finset.card_erase_of_mem hq₁]; omega
  rw [hcard] at hT
  have h2 := two_lt_prod_primeFactors h
  rw [← Finset.mul_prod_erase _ _ hq₁, ← Finset.mul_prod_erase _ _ hq₂', ← mul_assoc] at h2
  have hf : (q₁ : ℚ) / (q₁ - 1) * ((q₂ : ℚ) / (q₂ - 1)) ≤ 15 / 8 := by
    have a := f_le (m := 3) (by norm_num) hq₁3
    have b := f_le (m := 5) (by norm_num) hq₂5
    norm_num at a b
    calc _ ≤ (3 / 2 : ℚ) * (5 / 4) :=
          mul_le_mul a b (f_nonneg (by omega)) (by norm_num)
      _ = 15 / 8 := by norm_num
  have hk : 3 ≤ N.primeFactors.card := three_le_card_primeFactors h
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp2
  have hrest0 : (0 : ℚ) ≤ ∏ r ∈ S, (r : ℚ) / (r - 1) :=
    Finset.prod_nonneg fun r hr => f_nonneg (Nat.prime_of_mem_primeFactors
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))).one_le
  have h3 : 2 < 15 / 8 * (1 + ((N.primeFactors.card - 2 : ℕ) : ℚ) / (p - 1)) := by
    calc (2 : ℚ) < _ := h2
      _ ≤ 15 / 8 * ∏ r ∈ S, (r : ℚ) / (r - 1) := mul_le_mul_of_nonneg_right hf hrest0
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by norm_num)
  have h4 : (p : ℚ) - 1 < 15 * ((N.primeFactors.card - 2 : ℕ) : ℚ) := by
    have : (1 : ℚ) / 15 < ((N.primeFactors.card - 2 : ℕ) : ℚ) / (p - 1) := by linarith
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have h5 : p < 15 * (N.primeFactors.card - 2) + 1 := by
    have : (p : ℚ) < 15 * ((N.primeFactors.card - 2 : ℕ) : ℚ) + 1 := by linarith
    exact_mod_cast this
  omega

/-! ## The cap `255/128` on three prime components -/

/-- The abundancy of a prime power is at least one. -/
private theorem one_le_abundancy_pow {p : ℕ} (hp : p.Prime) (e : ℕ) : 1 ≤ abundancy (p ^ e) := by
  have := abundancy_le_of_dvd (pow_ne_zero e hp.ne_zero) (one_dvd (p ^ e))
  simpa [abundancy] using this

/-- For a perfect `N`, a subset `S` of its prime factors and exponents `g p ≤ e_p`,
`∏_{p ∈ S} σ(p^(g p))/p^(g p) ≤ 2`. -/
private theorem prod_abundancy_le_two {N : ℕ} (hN : N.Perfect) {S : Finset ℕ}
    (hS : S ⊆ N.primeFactors) (g : ℕ → ℕ) (hg : ∀ p ∈ S, g p ≤ N.factorization p) :
    ∏ p ∈ S, abundancy (p ^ g p) ≤ 2 := by
  rw [← (perfect_iff_abundancy_eq_two hN.2).mp hN, abundancy_eq_prod_primeFactors hN.2.ne']
  calc ∏ p ∈ S, abundancy (p ^ g p)
      ≤ ∏ p ∈ S, abundancy (p ^ N.factorization p) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact zero_le_one.trans (one_le_abundancy_pow (Nat.prime_of_mem_primeFactors (hS hp)) _)
        · intro p hp
          exact abundancy_prime_pow_mono (Nat.prime_of_mem_primeFactors (hS hp)) (hg p hp)
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le hS
        (fun p hp => zero_le_one.trans
          (one_le_abundancy_pow (Nat.prime_of_mem_primeFactors (hS hp)) _))
        fun p hp _ => one_le_abundancy_pow (Nat.prime_of_mem_primeFactors hp) _

private theorem mem_pf {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N) :
    p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, h.ne_zero⟩

/-- A prime `p ≡ 3 (mod 4)` dividing an odd perfect number has even exponent at least two. -/
private theorem even_two_le_of_mod_four {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N)
    (h3 : p % 4 = 3) : Even (N.factorization p) ∧ 2 ≤ N.factorization p := by
  obtain ⟨q, -, -, hq4, -, hev⟩ := exists_special_prime h
  refine ⟨hev p hp (by rintro rfl; omega), ?_⟩
  exact (hp.pow_dvd_iff_le_factorization h.ne_zero).mp
    (sq_dvd_of_prime_dvd_of_mod_four_eq_three h hp hpN h3)

private theorem one_le_fact {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N) :
    1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN

private theorem sigma_three_sq : σ 1 (3 ^ 2) = 13 := by
  rw [sigma_one_apply_prime_pow (by norm_num)]; norm_num [Finset.sum_range_succ]

private theorem sigma_eleven_sq : σ 1 (11 ^ 2) = 7 * 19 := by
  rw [sigma_one_apply_prime_pow (by norm_num)]; norm_num [Finset.sum_range_succ]

/-- If `3 · 5 · 11` divides an odd perfect number `N`, then `5 ∥ N`. -/
theorem factorization_five_eq_one_of_eleven {N : ℕ} (h : OddPerfect N) (h3 : 3 ∣ N) (h5 : 5 ∣ N)
    (h11 : 11 ∣ N) : N.factorization 5 = 1 := by
  have h7 := not_seven_dvd_of_three_five h h3 h5
  obtain ⟨⟨i, hi⟩, e3⟩ := even_two_le_of_mod_four h (by norm_num) h3 (by norm_num)
  obtain ⟨j, hj⟩ := (even_two_le_of_mod_four h (by norm_num) h11 (by norm_num)).1
  have e11 := (even_two_le_of_mod_four h (by norm_num) h11 (by norm_num)).2
  have e5 := one_le_fact h (by norm_num) h5
  have f11 : 4 ≤ N.factorization 11 := by
    by_contra hlt
    have he : N.factorization 11 = 2 := by omega
    apply h7
    exact OPNStarter.force_prime h.perfect (by norm_num) he (by norm_num) (by norm_num)
      (by rw [sigma_eleven_sq]; exact dvd_mul_right 7 19)
  have f3 : 4 ≤ N.factorization 3 := by
    by_contra hlt
    have he : N.factorization 3 = 2 := by omega
    have h13 : 13 ∣ N := OPNStarter.force_prime h.perfect (by norm_num) he (by norm_num)
      (by norm_num) (by rw [sigma_three_sq])
    have key := prod_abundancy_le_two h.perfect (S := {3, 5, 11, 13})
      (g := fun p => if p = 3 ∨ p = 11 then 2 else 1)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact mem_pf h (by norm_num) h3
        · exact mem_pf h (by norm_num) h5
        · exact mem_pf h (by norm_num) h11
        · exact mem_pf h (by norm_num) h13)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        have := one_le_fact h (by norm_num) h13
        rcases hp with rfl | rfl | rfl | rfl <;> simp <;> omega)
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton] at key
    simp only [abundancy_prime_pow (by norm_num : Nat.Prime 3),
      abundancy_prime_pow (by norm_num : Nat.Prime 5),
      abundancy_prime_pow (by norm_num : Nat.Prime 11),
      abundancy_prime_pow (by norm_num : Nat.Prime 13)] at key
    norm_num [Finset.sum_range_succ] at key
  by_contra hne
  have key := prod_abundancy_le_two h.perfect (S := {3, 5, 11})
    (g := fun p => if p = 5 then 2 else 4)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_pf h (by norm_num) h3
      · exact mem_pf h (by norm_num) h5
      · exact mem_pf h (by norm_num) h11)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp <;> omega)
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] at key
  simp only [abundancy_prime_pow (by norm_num : Nat.Prime 3),
    abundancy_prime_pow (by norm_num : Nat.Prime 5),
    abundancy_prime_pow (by norm_num : Nat.Prime 11)] at key
  norm_num [Finset.sum_range_succ] at key

/-- If `3 · 5 · 13` divides an odd perfect number `N`, then `5 ∥ N` or `3² ∥ N`. -/
theorem factorization_five_eq_one_or_three_eq_two_of_thirteen {N : ℕ} (h : OddPerfect N)
    (h3 : 3 ∣ N) (h5 : 5 ∣ N) (h13 : 13 ∣ N) :
    N.factorization 5 = 1 ∨ N.factorization 3 = 2 := by
  have h7 := not_seven_dvd_of_three_five h h3 h5
  obtain ⟨⟨i, hi⟩, e3⟩ := even_two_le_of_mod_four h (by norm_num) h3 (by norm_num)
  have e5 := one_le_fact h (by norm_num) h5
  have e13' := one_le_fact h (by norm_num) h13
  have ev13 : Even (N.factorization 13) := by
    by_contra hodd
    apply h7
    have hs := succ_dvd_sigma_special (N := N) (by norm_num : Nat.Prime 13)
      (Nat.not_even_iff_odd.mp hodd)
    exact OPNStarter.force_prime h.perfect (by norm_num) rfl (by norm_num) (by norm_num)
      ((by norm_num : 7 ∣ 13 + 1).trans hs)
  obtain ⟨j, hj⟩ := ev13
  by_contra hne
  push Not at hne
  have key := prod_abundancy_le_two h.perfect (S := {3, 5, 13})
    (g := fun p => if p = 3 then 4 else 2)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact mem_pf h (by norm_num) h3
      · exact mem_pf h (by norm_num) h5
      · exact mem_pf h (by norm_num) h13)
    (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> simp <;> omega)
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] at key
  simp only [abundancy_prime_pow (by norm_num : Nat.Prime 3),
    abundancy_prime_pow (by norm_num : Nat.Prime 5),
    abundancy_prime_pow (by norm_num : Nat.Prime 13)] at key
  norm_num [Finset.sum_range_succ] at key

private theorem abundancy_pos {p : ℕ} (hp : p.Prime) (e : ℕ) : 0 < abundancy (p ^ e) :=
  zero_lt_one.trans_le (one_le_abundancy_pow hp e)

/-- Three strict factor bounds `σ(x^i)/x^i < x/(x-1) ≤ m/(m-1)`. -/
private theorem prod3_lt {a b c i j l ma mb mc : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hma : 2 ≤ ma) (hmb : 2 ≤ mb) (hmc : 2 ≤ mc) (ha' : ma ≤ a) (hb' : mb ≤ b) (hc' : mc ≤ c) :
    abundancy (a ^ i) * abundancy (b ^ j) * abundancy (c ^ l) <
      (ma : ℚ) / (ma - 1) * ((mb : ℚ) / (mb - 1)) * ((mc : ℚ) / (mc - 1)) := by
  have x := (abundancy_prime_pow_lt ha i).trans_le (f_le hma ha')
  have y := (abundancy_prime_pow_lt hb j).trans_le (f_le hmb hb')
  have z := (abundancy_prime_pow_lt hc l).trans_le (f_le hmc hc')
  exact mul_lt_mul'' (mul_lt_mul'' x y (abundancy_pos ha i).le (abundancy_pos hb j).le) z
    (mul_pos (abundancy_pos ha i) (abundancy_pos hb j)).le (abundancy_pos hc l).le

/-- Zelinsky (arXiv 2005.12118): for any three distinct prime factors `a < b < c` of an odd
perfect number `N`, `σ(a^e_a b^e_b c^e_c)/(a^e_a b^e_b c^e_c) < 255/128`. In particular this holds
for the three smallest prime factors. -/
theorem abundancy_three_components_lt {N a b c : ℕ} (h : OddPerfect N) (ha : a ∈ N.primeFactors)
    (hb : b ∈ N.primeFactors) (hc : c ∈ N.primeFactors) (hab : a < b) (hbc : b < c) :
    abundancy (a ^ N.factorization a) * abundancy (b ^ N.factorization b) *
      abundancy (c ^ N.factorization c) < 255 / 128 := by
  have hap := Nat.prime_of_mem_primeFactors ha
  have hbp := Nat.prime_of_mem_primeFactors hb
  have hcp := Nat.prime_of_mem_primeFactors hc
  obtain ⟨a', rfl⟩ := odd_of_mem h ha
  obtain ⟨b', rfl⟩ := odd_of_mem h hb
  obtain ⟨c', rfl⟩ := odd_of_mem h hc
  have ha3 := three_le_of_mem h ha
  have hc9 : 2 * c' + 1 ≠ 9 := by rintro h9; rw [h9] at hcp; norm_num at hcp
  have hc15 : 2 * c' + 1 ≠ 15 := by rintro h9; rw [h9] at hcp; norm_num at hcp
  -- generic bound with `m₁, m₂, m₃`
  have gen := fun {ma mb mc : ℕ} (hma : 2 ≤ ma) (hmb : 2 ≤ mb) (hmc : 2 ≤ mc)
      (h1 : ma ≤ 2 * a' + 1) (h2 : mb ≤ 2 * b' + 1) (h3 : mc ≤ 2 * c' + 1) =>
    prod3_lt (i := N.factorization (2 * a' + 1)) (j := N.factorization (2 * b' + 1))
      (l := N.factorization (2 * c' + 1)) hap hbp hcp hma hmb hmc h1 h2 h3
  rcases (by omega : 2 * a' + 1 = 3 ∨ 5 ≤ 2 * a' + 1) with ha3 | ha5
  · rcases (by omega : 2 * b' + 1 = 5 ∨ 7 ≤ 2 * b' + 1) with hb5 | hb7
    · have h3 : 3 ∣ N := ha3 ▸ Nat.dvd_of_mem_primeFactors ha
      have h5 : 5 ∣ N := hb5 ▸ Nat.dvd_of_mem_primeFactors hb
      have hc7 : 2 * c' + 1 ≠ 7 := fun e =>
        not_seven_dvd_of_three_five h h3 h5 (e ▸ Nat.dvd_of_mem_primeFactors hc)
      rcases (by omega : 2 * c' + 1 = 11 ∨ 2 * c' + 1 = 13 ∨ 17 ≤ 2 * c' + 1) with
        hc11 | hc13 | hc17
      · have h11 : 11 ∣ N := hc11 ▸ Nat.dvd_of_mem_primeFactors hc
        have e5 := factorization_five_eq_one_of_eleven h h3 h5 h11
        rw [ha3, hb5, hc11, e5]
        have x := abundancy_prime_pow_lt (by norm_num : Nat.Prime 3) (N.factorization 3)
        have z := abundancy_prime_pow_lt (by norm_num : Nat.Prime 11) (N.factorization 11)
        have x0 := abundancy_pos (by norm_num : Nat.Prime 3) (N.factorization 3)
        have z0 := abundancy_pos (by norm_num : Nat.Prime 11) (N.factorization 11)
        rw [abundancy_prime_pow (by norm_num : Nat.Prime 5)]
        norm_num [Finset.sum_range_succ] at x z ⊢
        nlinarith
      · have h13 : 13 ∣ N := hc13 ▸ Nat.dvd_of_mem_primeFactors hc
        have x := abundancy_prime_pow_lt (by norm_num : Nat.Prime 3) (N.factorization 3)
        have y := abundancy_prime_pow_lt (by norm_num : Nat.Prime 5) (N.factorization 5)
        have z := abundancy_prime_pow_lt (by norm_num : Nat.Prime 13) (N.factorization 13)
        have x0 := abundancy_pos (by norm_num : Nat.Prime 3) (N.factorization 3)
        have y0 := abundancy_pos (by norm_num : Nat.Prime 5) (N.factorization 5)
        have z0 := abundancy_pos (by norm_num : Nat.Prime 13) (N.factorization 13)
        rw [ha3, hb5, hc13]
        rcases factorization_five_eq_one_or_three_eq_two_of_thirteen h h3 h5 h13 with e | e
        · rw [e, abundancy_prime_pow (by norm_num : Nat.Prime 5)]
          norm_num [Finset.sum_range_succ] at x z ⊢
          nlinarith
        · rw [e, abundancy_prime_pow (by norm_num : Nat.Prime 3)]
          norm_num [Finset.sum_range_succ] at y z ⊢
          nlinarith
      · have := gen (ma := 3) (mb := 5) (mc := 17) (by norm_num) (by norm_num) (by norm_num)
          (by omega) (by omega) hc17
        norm_num at this
        exact this
    · have := gen (ma := 3) (mb := 7) (mc := 11) (by norm_num) (by norm_num) (by norm_num)
        (by omega) hb7 (by omega)
      norm_num at this
      exact this.trans (by norm_num)
  · have := gen (ma := 5) (mb := 7) (mc := 11) (by norm_num) (by norm_num) (by norm_num)
      ha5 (by omega) (by omega)
    norm_num at this
    exact this.trans (by norm_num)

/-- Fourth smallest prime factor (from the `255/128` cap and telescoping, as in arXiv 2005.12118):
if `q₁ < q₂ < q₃` and `p` are prime factors of an odd perfect number `N` and every prime factor
other than `q₁, q₂, q₃` is at least `p` (so `p` is the fourth smallest when `q₃ < p`), then `p ≤ 255 ω(N) - 765`. -/
theorem fourth_prime_le {N p q₁ q₂ q₃ : ℕ} (h : OddPerfect N) (hq₁ : q₁ ∈ N.primeFactors)
    (hq₂ : q₂ ∈ N.primeFactors) (hq₃ : q₃ ∈ N.primeFactors) (hp : p ∈ N.primeFactors)
    (h12 : q₁ < q₂) (h23 : q₂ < q₃)
    (hmin : ∀ r ∈ N.primeFactors, r ≠ q₁ → r ≠ q₂ → r ≠ q₃ → p ≤ r) :
    p ≤ 255 * N.primeFactors.card - 765 := by
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  set S := ((N.primeFactors.erase q₁).erase q₂).erase q₃
  have hq₂' : q₂ ∈ N.primeFactors.erase q₁ := Finset.mem_erase.mpr ⟨by omega, hq₂⟩
  have hq₃' : q₃ ∈ (N.primeFactors.erase q₁).erase q₂ :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, hq₃⟩⟩
  have hSpf : ∀ r ∈ S, r ∈ N.primeFactors := fun r hr =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr))
  have hT := prod_div_sub_one_le S hp2 (fun r hr => by
    have h1 := Finset.ne_of_mem_erase hr
    have h2 := Finset.mem_of_mem_erase hr
    have h3 := Finset.mem_of_mem_erase h2
    exact hmin r (Finset.mem_of_mem_erase h3) (Finset.ne_of_mem_erase h3)
      (Finset.ne_of_mem_erase h2) h1)
  have hcard : S.card = N.primeFactors.card - 3 := by
    rw [Finset.card_erase_of_mem hq₃', Finset.card_erase_of_mem hq₂',
      Finset.card_erase_of_mem hq₁]; omega
  rw [hcard] at hT
  have h2 := abundancy_eq_prod_primeFactors h.ne_zero
  rw [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect, ← Finset.mul_prod_erase _ _ hq₁,
    ← Finset.mul_prod_erase _ _ hq₂', ← Finset.mul_prod_erase _ _ hq₃', ← mul_assoc,
    ← mul_assoc] at h2
  have hA := abundancy_three_components_lt h hq₁ hq₂ hq₃ h12 h23
  have hB0 : 0 < ∏ r ∈ S, abundancy (r ^ N.factorization r) :=
    Finset.prod_pos fun r hr => abundancy_pos (Nat.prime_of_mem_primeFactors (hSpf r hr)) _
  have hBT : ∏ r ∈ S, abundancy (r ^ N.factorization r) ≤ ∏ r ∈ S, (r : ℚ) / (r - 1) :=
    Finset.prod_le_prod (fun r hr => (abundancy_pos (Nat.prime_of_mem_primeFactors (hSpf r hr)) _).le)
      fun r hr => (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors (hSpf r hr)) _).le
  have hk : 3 ≤ N.primeFactors.card := three_le_card_primeFactors h
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp2
  have h3 : 2 < 255 / 128 * (1 + ((N.primeFactors.card - 3 : ℕ) : ℚ) / (p - 1)) := by
    calc (2 : ℚ) = _ := h2
      _ < 255 / 128 * ∏ r ∈ S, abundancy (r ^ N.factorization r) :=
          mul_lt_mul_of_pos_right hA hB0
      _ ≤ 255 / 128 * ∏ r ∈ S, (r : ℚ) / (r - 1) := mul_le_mul_of_nonneg_left hBT (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by norm_num)
  have h4 : (p : ℚ) - 1 < 255 * ((N.primeFactors.card - 3 : ℕ) : ℚ) := by
    have : (1 : ℚ) / 255 < ((N.primeFactors.card - 3 : ℕ) : ℚ) / (p - 1) := by linarith
    rw [lt_div_iff₀ (by linarith)] at this
    linarith
  have h5 : p < 255 * (N.primeFactors.card - 3) + 1 := by
    have : (p : ℚ) < 255 * ((N.primeFactors.card - 3 : ℕ) : ℚ) + 1 := by linarith
    exact_mod_cast this
  omega

end OddPerfect

#print axioms OddPerfect.abundancy_prime_pow_eq_mul
#print axioms OddPerfect.abundancy_eq_prod_mul_prod
#print axioms OddPerfect.two_eq_prod_mul_prod
#print axioms OddPerfect.prod_sub_two_eq
#print axioms OddPerfect.prod_div_sub_one_eq_div
#print axioms OddPerfect.totient_prod_primeFactors
#print axioms OddPerfect.two_mul_prod_sub_one_lt_prod
#print axioms OddPerfect.inv_prod_sub_one_le_prod_sub_two
#print axioms OddPerfect.one_sub_sum_le_prod_one_sub
#print axioms OddPerfect.exists_pow_succ_le_card_mul
#print axioms OddPerfect.prod_le_pow_succ_mul
#print axioms OddPerfect.le_two_mul_prod_sub_one_sub_one
#print axioms OddPerfect.second_prime_le
#print axioms OddPerfect.third_prime_le
#print axioms OddPerfect.factorization_five_eq_one_of_eleven
#print axioms OddPerfect.factorization_five_eq_one_or_three_eq_two_of_thirteen
#print axioms OddPerfect.abundancy_three_components_lt
#print axioms OddPerfect.fourth_prime_le
