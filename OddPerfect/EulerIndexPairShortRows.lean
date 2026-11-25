import OddPerfect.EulerIndexPairPrimeLength
import OddPerfect.HalfSigmaSquare
import OddPerfect.SpecialPrime

/-!
# Two prime Euler index: the short sender rows are impossible

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly the two prime factors
`r ≠ s`. `eulerIndex_pair_prime_length` labels them `(t, u)` with `σ(t ^ e) = q u ^ v`,
`σ(u ^ f) = t ^ j` (`e = v_t(N)`, `f = v_u(N)`, `j` odd, `0 < j < e`), `e + 1` prime, and
either `v = 0`, or `v = 1`, `u = e + 1`, `t ≡ 1 (mod u)` and `q + 1 = 2 w ^ 2`, where
`w = ∏ p ^ (v_p(N) / 2)` over the primes `p ∣ N` outside `{q, r, s}`. In general
`q + 1 = 2 u ^ d w ^ 2` with `u ∤ w`.

Arithmetic lemmas (no odd perfect number):

* `sigma_prime_sq_row_eq_thirtyone`: `σ(t ^ 2) = q`, `q + 1 = 2 u ^ d w ^ 2` and
  `σ(u ^ f) = t` force `q = 31`: modulo `u`, `t ≡ 1` and `q + 1 ≡ 4`, so `d = 0`, and then
  `t = 5` (`eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq`).
* `sigma_prime_fourth_row_false`: `σ(t ^ 4) = q`, `q + 1 = 2 u ^ d w ^ 2` with `u ∤ w`, and
  `σ(u ^ f) = t ^ j` with `j ∈ {1, 3}` and even `f ≥ 2` are incompatible. `d = 0` is excluded
  by `sigma_prime_fourth_succ_ne_two_mul_sq`; otherwise, modulo `u`, `t ^ 3 ≡ 1` and
  `t ^ 4 + t ^ 3 + t ^ 2 + t + 2 ≡ 0` give `18 ≡ 0`, so `u = 3`. Then `2 t ^ j + 1 = 3 ^ (f + 1)`;
  for `j = 3` this fails modulo 9, and for `j = 1` it gives `t ≡ 13` or `t ≡ 121 (mod 243)`,
  where `q + 1` is `81` or `108` modulo `243`, never `2 * 3 ^ d * w ^ 2` with `3 ∤ w`.
* `sigma_outsider_row_three_false`: an odd prime `p ≠ 3` with even `g ≥ 2`, `g + 1` prime or
  a prime square, `σ(p ^ g) = t * 3 ^ y`, `p ∣ q + 1` and `σ(t ^ 2) = 3 q` (with `t ≠ 3`
  prime) is impossible. `sigma_row_split` for the row of `p` leaves `y = 0` (then `t ≡ 1` and
  `p ∣ 6`), `y = 1` with `g = 2` (then `3 t ≡ 1` and `p ∣ 40`, but `p ≡ 1 (mod 3)`), and
  `y = 2` with `g = 8` (both factors of `R_3(p) R_3(p ^ 3) = 9 t` are divisible by 3).

Family result `eulerIndex_pair_short_rows`: the conclusion of `eulerIndex_pair_prime_length`
with `6 ≤ e` in the branch `v = 0` (the rows `e = 2` and `e = 4` are impossible) and `5 ≤ u`
in the branch `v = 1` (the case `u = 3`, `e = 2` is impossible: the valuation count at `t`
leaves one outside row `σ(p ^ g) = t * 3 ^ y` with `p ^ g ∣ q + 1`).

These are restricted results (special exponent 1, Euler index supported on exactly two
primes). The case is not excluded. Their novelty has not been verified.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairShortRows

/-- `R_(a b)(r) = R_a(r) * R_b(r ^ a)`. -/
private theorem eipsr_geom_mul (r a b : ℕ) :
    ∑ i ∈ range (a * b), r ^ i = (∑ i ∈ range a, r ^ i) * ∑ i ∈ range b, (r ^ a) ^ i := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h2 : ∑ x ∈ range a, r ^ (a * b + x) = (∑ i ∈ range a, r ^ i) * (r ^ a) ^ b := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by rw [pow_add, pow_mul]; ring
    rw [mul_add_one, sum_range_add, ih, sum_range_succ, mul_add, h2]

/-- A geometric sum with base at least `2` and at least two terms exceeds its length. -/
private theorem eipsr_gt {x n : ℕ} (hx : 2 ≤ x) (hn : 2 ≤ n) : n < ∑ i ∈ range n, x ^ i := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ]
  have h1 : k ≤ ∑ i ∈ range k, x ^ i := by
    have := sum_le_sum (s := range k) (f := fun _ => 1) (g := fun i => x ^ i)
      (fun i _ => Nat.pos_of_ne_zero (pow_ne_zero _ (by omega)))
    simpa using this
  have h2 : 2 ≤ x ^ k := le_trans hx (le_self_pow (by omega) (by omega))
  omega

/-- If `x ≡ 1`, then `R_n(x) ≡ n`. -/
private theorem eipsr_cast_one {R : Type*} [CommRing R] {x : ℕ} (hx : (x : R) = 1) (n : ℕ) :
    ((∑ i ∈ range n, x ^ i : ℕ) : R) = n := by
  push_cast
  simp [hx]

/-- From `t % u = 1`, `t ≡ 1` in `ZMod u`. -/
private theorem eipsr_cast_of_mod {t u : ℕ} (hu : 1 < u) (h : t % u = 1) :
    (t : ZMod u) = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' t 1 u).mpr (by rw [h, Nat.mod_eq_of_lt hu])
  simpa using this

/-- The row `R_(u ^ 2)(t) = q u ^ 2` with `t ≡ 1 (mod u)` is impossible. -/
private theorem eipsr_square_row {t u q : ℕ} (ht : t.Prime) (hu : u.Prime) (hq : q.Prime)
    (htu1 : t % u = 1) (hrow : ∑ i ∈ range (u ^ 2), t ^ i = q * u ^ 2) : False := by
  have ht1 : (t : ZMod u) = 1 := eipsr_cast_of_mod hu.one_lt htu1
  have htu : ((t ^ u : ℕ) : ZMod u) = 1 := by push_cast; rw [ht1, one_pow]
  have hA : u ∣ ∑ i ∈ range u, t ^ i :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by rw [eipsr_cast_one ht1, ZMod.natCast_self])
  have hB : u ∣ ∑ i ∈ range u, (t ^ u) ^ i :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by rw [eipsr_cast_one htu, ZMod.natCast_self])
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  rw [sq, eipsr_geom_mul, ha, hb] at hrow
  have hab : a * b = q := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hu.pos hu.pos)
    calc u * u * (a * b) = u * a * (u * b) := by ring
      _ = q * (u * u) := hrow
      _ = u * u * q := by ring
  have hgA := eipsr_gt ht.two_le hu.two_le
  have hgB := eipsr_gt (x := t ^ u) (le_trans ht.two_le (le_self_pow ht.one_lt.le hu.ne_zero))
    hu.two_le
  rw [ha] at hgA
  rw [hb] at hgB
  rcases Nat.prime_mul_iff.mp (hab ▸ hq) with ⟨-, h1⟩ | ⟨-, h1⟩
  · rw [h1, mul_one] at hgB; exact lt_irrefl _ hgB
  · rw [h1, mul_one] at hgA; exact lt_irrefl _ hgA

/-- `σ(u ^ f) ≡ 1 (mod u)`. -/
private theorem eipsr_row_one {u f : ℕ} (hu : u.Prime) :
    ((σ 1 (u ^ f) : ℕ) : ZMod u) = 1 := by
  rw [sigma_one_apply_prime_pow hu, sum_range_succ']
  push_cast
  simp

/-- `2 R_n(3) + 1 = 3 ^ n`. -/
private theorem eipsr_geom_three (n : ℕ) : 2 * ∑ i ∈ range n, 3 ^ i + 1 = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, pow_succ]; linarith

/-- No `r < 9` has `2 r ^ 3 + 1 ≡ 0 (mod 9)`. -/
private theorem eipsr_mod_nine : ∀ r, r < 9 → (2 * r ^ 3 + 1) % 9 ≠ 0 := by decide +kernel

/-- Residues of `2 * 3 ^ d * w ^ 2` modulo `243` for `3 ∤ w` and `d < 5`. -/
private theorem eipsr_res : ∀ w, w < 243 → w % 3 ≠ 0 → ∀ d, d < 5 →
    (2 * 3 ^ d * w ^ 2) % 243 ≠ 81 ∧ (2 * 3 ^ d * w ^ 2) % 243 ≠ 108 := by
  decide +kernel

/-- If `t ≡ 13` or `t ≡ 121 (mod 243)`, then `t ^ 4 + t ^ 3 + t ^ 2 + t + 2` is not
`2 * 3 ^ d * w ^ 2` with `3 ∤ w`. -/
private theorem eipsr_mod_243 {t d w : ℕ} (ht : t % 243 = 13 ∨ t % 243 = 121) (hw : ¬ 3 ∣ w)
    (h : t ^ 4 + t ^ 3 + t ^ 2 + t + 2 = 2 * 3 ^ d * w ^ 2) : False := by
  have hm := Nat.mod_modEq t 243
  have hc : (t % 243) ^ 4 + (t % 243) ^ 3 + (t % 243) ^ 2 + t % 243 + 2 ≡
      t ^ 4 + t ^ 3 + t ^ 2 + t + 2 [MOD 243] :=
    ((((hm.pow 4).add (hm.pow 3)).add (hm.pow 2)).add hm).add_right 2
  have hL : (t ^ 4 + t ^ 3 + t ^ 2 + t + 2) % 243 = 81 ∨
      (t ^ 4 + t ^ 3 + t ^ 2 + t + 2) % 243 = 108 := by
    rw [Nat.ModEq] at hc
    rw [← hc]
    rcases ht with h1 | h1 <;> rw [h1] <;> norm_num
  have hR : 2 * 3 ^ d * (w % 243) ^ 2 ≡ 2 * 3 ^ d * w ^ 2 [MOD 243] :=
    ((Nat.mod_modEq w 243).pow 2).mul_left _
  rw [Nat.ModEq] at hR
  rw [h, ← hR] at hL
  have hw' : w % 243 % 3 ≠ 0 := by omega
  rcases Nat.lt_or_ge d 5 with hd | hd
  · have := eipsr_res (w % 243) (Nat.mod_lt _ (by norm_num)) hw' d hd
    omega
  · obtain ⟨c, hc⟩ := pow_dvd_pow 3 hd
    have h0 : (2 * 3 ^ d * (w % 243) ^ 2) % 243 = 0 := by
      rw [hc, show (3 : ℕ) ^ 5 = 243 by norm_num]
      exact Nat.mod_eq_zero_of_dvd ⟨2 * c * (w % 243) ^ 2, by ring⟩
    omega

/-- `σ(t ^ 2) = t ^ 2 + t + 1`. -/
private theorem eipsr_sigma_two {t : ℕ} (ht : t.Prime) : σ 1 (t ^ 2) = t ^ 2 + t + 1 := by
  rw [sigma_one_apply_prime_pow ht]
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one]
  ring

/-- `σ(t ^ 4) = t ^ 4 + t ^ 3 + t ^ 2 + t + 1`. -/
private theorem eipsr_sigma_four {t : ℕ} (ht : t.Prime) :
    σ 1 (t ^ 4) = t ^ 4 + t ^ 3 + t ^ 2 + t + 1 := by
  rw [sigma_one_apply_prime_pow ht]
  simp only [sum_range_succ, sum_range_zero, pow_zero, pow_one]
  ring

/-- A swapped labeling would give `q ∣ t ^ j`, so the two labelings agree. -/
private theorem eipsr_label {N q m r s t u t' u' j v' : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (htu : ({t, u} : Finset ℕ) = {r, s}) (htu' : ({t', u'} : Finset ℕ) = {r, s})
    (hne' : t' ≠ u') (hB : σ 1 (u ^ N.factorization u) = t ^ j)
    (hA' : σ 1 (t' ^ N.factorization t') = q * u' ^ v') : t' = t ∧ u' = u := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have ht : t.Prime := Nat.prime_of_mem_primeFactors htJ
  have htm : t ∣ m := ht.dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors htJ).trans (eulerIndex_dvd_sq h hq hN1 hqm))
  have ht' : t' ∈ ({t, u} : Finset ℕ) := by rw [htu, ← htu']; simp
  have hu' : u' ∈ ({t, u} : Finset ℕ) := by rw [htu, ← htu']; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht' hu'
  rcases ht' with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hu' with h2 | h2
    · exact absurd (h1.trans h2.symm) hne'
    · exact h2
  · exfalso
    rw [h1, hB] at hA'
    have hqt : q ∣ t := hq.dvd_of_dvd_pow (Dvd.intro _ hA'.symm)
    rw [(Nat.prime_dvd_prime_iff_eq hq ht).mp hqt] at hqm
    exact hqm htm

/-- An outsider is a prime of `N` other than `q`, `t`, `u`. -/
private theorem eipsr_mem_out {N q r s t u p : ℕ} (htu : ({t, u} : Finset ℕ) = {r, s})
    (hp : p ∈ N.primeFactors \ {q, r, s}) :
    p ∈ N.primeFactors ∧ p ≠ q ∧ p ≠ t ∧ p ≠ u := by
  rw [Finset.mem_sdiff, ← htu] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩

end EulerIndexPairShortRows

open EulerIndexPairShortRows

/-- **Sender row of length 3.** Let `t`, `u` be primes, `t` and `u` odd, with
`σ(t ^ 2) = q`, `q + 1 = 2 u ^ d w ^ 2` and `σ(u ^ f) = t`. Then `q = 31`.
Elementary; nothing new is claimed. -/
theorem sigma_prime_sq_row_eq_thirtyone {t u q d w f : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    (hu : u.Prime) (hu2 : u ≠ 2) (hrow : σ 1 (t ^ 2) = q) (hd : q + 1 = 2 * u ^ d * w ^ 2)
    (hcol : σ 1 (u ^ f) = t) : q = 31 := by
  have ht1 : (t : ZMod u) = 1 := by
    have h1 := eipsr_row_one (f := f) hu
    rwa [hcol] at h1
  have hd0 : d = 0 := by
    by_contra hd0
    have hdvd : u ∣ q + 1 :=
      hd ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self u hd0) 2) _
    have h4 : ((2 ^ 2 : ℕ) : ZMod u) = 0 := by
      have hq0 : ((q + 1 : ℕ) : ZMod u) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [← hrow, eipsr_sigma_two ht] at hq0
      push_cast at hq0
      rw [ht1] at hq0
      push_cast
      linear_combination hq0
    have h4d : u ∣ 2 ^ 2 := (ZMod.natCast_eq_zero_iff _ _).mp h4
    exact hu2 ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp (hu.dvd_of_dvd_pow h4d))
  rw [hd0, pow_zero, mul_one] at hd
  have ht5 := eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq ht ht2 (z := w) (by rw [hrow]; exact hd)
  have hs := eipsr_sigma_two ht
  rw [hrow, ht5] at hs
  norm_num at hs
  exact hs

/-- **Sender row of length 5.** Let `t`, `u` be primes, `t` and `u` odd, with `σ(t ^ 4) = q`,
`q + 1 = 2 u ^ d w ^ 2`, `u ∤ w`, and `σ(u ^ f) = t ^ j` with `j = 1` or `j = 3` and `f ≥ 2`
even. This is impossible. Elementary; nothing new is claimed. -/
theorem sigma_prime_fourth_row_false {t u q d w j f : ℕ} (ht : t.Prime) (ht2 : t ≠ 2)
    (hu : u.Prime) (hu2 : u ≠ 2) (hrow : σ 1 (t ^ 4) = q) (hd : q + 1 = 2 * u ^ d * w ^ 2)
    (huw : ¬ u ∣ w) (hj : j = 1 ∨ j = 3) (hf : 2 ≤ f) (hfe : Even f)
    (hcol : σ 1 (u ^ f) = t ^ j) : False := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one, ← hrow] at hd
    exact sigma_prime_fourth_succ_ne_two_mul_sq ht ht2 hd
  have hdvd : u ∣ q + 1 :=
    hd ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self u hd0) 2) _
  have hu3 : u = 3 := by
    have htj : (t : ZMod u) ^ j = 1 := by
      have h1 := eipsr_row_one (f := f) hu
      rw [hcol] at h1
      exact_mod_cast h1
    have ht3 : (t : ZMod u) ^ 3 = 1 := by
      rcases hj with rfl | rfl
      · rw [pow_one] at htj; rw [htj, one_pow]
      · exact htj
    have hq0 : (t : ZMod u) ^ 4 + (t : ZMod u) ^ 3 + (t : ZMod u) ^ 2 + t + 2 = 0 := by
      have h1 : ((q + 1 : ℕ) : ZMod u) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [← hrow, eipsr_sigma_four ht] at h1
      push_cast at h1
      linear_combination h1
    have h18 : ((2 * 3 ^ 2 : ℕ) : ZMod u) = 0 := by
      push_cast
      linear_combination (1 + ((t : ZMod u) - 3) * ((t : ZMod u) - 2)) * hq0 -
        ((1 + ((t : ZMod u) - 3) * ((t : ZMod u) - 2)) * ((t : ZMod u) + 1) +
          ((t : ZMod u) - 3)) * ht3
    rcases (Nat.Prime.dvd_mul hu).mp ((ZMod.natCast_eq_zero_iff _ _).mp h18) with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp h) hu2
    · exact (Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp (hu.dvd_of_dvd_pow h)
  subst hu3
  have hgeo : 2 * σ 1 (3 ^ f) + 1 = 3 ^ (f + 1) := by
    rw [sigma_one_apply_prime_pow Nat.prime_three]
    exact eipsr_geom_three (f + 1)
  rcases hj with rfl | rfl
  · rw [pow_one] at hcol
    rw [hcol] at hgeo
    have ht243 : t % 243 = 13 ∨ t % 243 = 121 := by
      obtain ⟨k, hk⟩ := hfe
      rcases (show f = 2 ∨ 4 ≤ f by omega) with h2 | h4
      · left
        rw [h2, show (3 : ℕ) ^ (2 + 1) = 27 by norm_num] at hgeo
        omega
      · right
        obtain ⟨c, hc⟩ := pow_dvd_pow 3 (show 5 ≤ f + 1 by omega)
        rw [hc, show (3 : ℕ) ^ 5 = 243 by norm_num] at hgeo
        omega
    have hq : t ^ 4 + t ^ 3 + t ^ 2 + t + 2 = 2 * 3 ^ d * w ^ 2 := by
      have := eipsr_sigma_four ht
      rw [hrow] at this
      omega
    exact eipsr_mod_243 ht243 huw hq
  · rw [hcol] at hgeo
    have h9 : 9 ∣ 2 * t ^ 3 + 1 := by
      rw [hgeo]
      obtain ⟨c, hc⟩ := pow_dvd_pow 3 (show 2 ≤ f + 1 by omega)
      rw [hc]
      exact Dvd.dvd.mul_right (by norm_num) c
    have hm : 2 * (t % 9) ^ 3 + 1 ≡ 2 * t ^ 3 + 1 [MOD 9] :=
      (((Nat.mod_modEq t 9).pow 3).mul_left 2).add_right 1
    rw [Nat.ModEq] at hm
    have := eipsr_mod_nine (t % 9) (Nat.mod_lt _ (by norm_num))
    rw [hm] at this
    exact this (Nat.mod_eq_zero_of_dvd h9)

/-- **An outside row into `t` and `3`.** Let `t ≠ 3` and `p` be primes, `p` odd, `p ≠ 3`,
`g ≥ 2` even with `g + 1` prime or the square of a prime, `σ(p ^ g) = t * 3 ^ y`,
`p ∣ q + 1` and `σ(t ^ 2) = 3 q`. This is impossible. Elementary; nothing new is claimed. -/
theorem sigma_outsider_row_three_false {t p q g y : ℕ} (ht : t.Prime) (ht3 : t ≠ 3)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hge : Even g) (hg : 2 ≤ g)
    (hgP : (g + 1).Prime ∨ ∃ P, P.Prime ∧ g + 1 = P ^ 2) (hrow : σ 1 (p ^ g) = t * 3 ^ y)
    (hpq : p ∣ q + 1) (hq : σ 1 (t ^ 2) = q * 3) : False := by
  have hp3' : (p : ZMod 3) ^ 2 = 1 := by
    have h0 : (p : ZMod 3) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
    have key : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by decide
    exact key _ h0
  have hsplit := sigma_row_split hp hp2 Nat.prime_three (by norm_num) ht hp3 (Ne.symm ht3) hge
    hrow (by norm_num : 0 < 2) (by omega) hp3'
  have hqp : (q : ZMod p) + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr hpq
    push_cast at this
    exact this
  have hts : (t : ZMod p) ^ 2 + t + 1 = q * 3 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hq
    rw [eipsr_sigma_two ht] at this
    push_cast at this
    exact this
  have hrowp := eipsr_row_one (f := g) hp
  rcases hgP with hpr | ⟨P, hP, hPe⟩
  · rcases hsplit.1 hpr with hy | ⟨hy, hg3, hmod⟩
    · rw [hrow, hy, pow_zero, mul_one] at hrowp
      have h6 : ((2 * 3 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination hts - ((t : ZMod p) + 2) * hrowp + 3 * hqp
      rcases (Nat.Prime.dvd_mul hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp h6) with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
    · rw [hrow, hy, pow_one] at hrowp
      push_cast at hrowp
      have h40 : ((2 ^ 3 * 5 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination 9 * hts + 27 * hqp - (3 * (t : ZMod p) + 4) * hrowp
      rcases (Nat.Prime.dvd_mul hp).mp ((ZMod.natCast_eq_zero_iff _ _).mp h40) with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      · have h5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : (5 : ℕ).Prime)).mp h
        rw [h5] at hmod
        norm_num at hmod
  · rcases hsplit.2 P hP hPe with ⟨hy, hP3, hmod⟩ | ⟨-, hP2, -⟩
    · have hg8 : g + 1 = 3 ^ 2 := by rw [hPe, ← hP3]
      rw [sigma_one_apply_prime_pow hp, hg8, hy] at hrow
      exact eipsr_square_row hp Nat.prime_three ht hmod hrow
    · have h2 : P = 2 := (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp hP2
      rw [h2] at hPe
      obtain ⟨k, hk⟩ := hge
      norm_num at hPe
      omega

variable {N q m r s : ℕ}

/-- **Two prime index, the short sender rows.** Let `N = q m ^ 2` be an odd perfect number with
special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has
exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_prime_length`, with `e = v_t(N)`, `σ(t ^ e) = q u ^ v`, `σ(u ^ v_u(N)) = t ^ j`,
`j` odd and `j < e`, the number `e + 1` is prime, and either `v = 0`, `σ(t ^ e) = q` and
`e ≥ 6`, or `v = 1`, `u = e + 1 ≥ 5`, `t ≡ 1 (mod u)`, `q ≡ 1 (mod u)` and `q + 1 = 2 w ^ 2`,
where `w = ∏ p ^ (v_p(N) / 2)` over the primes `p ∣ N` outside `{q, r, s}`. This is a
restricted result (special exponent 1, index supported on exactly two primes); it does not
exclude this case. Its novelty has not been verified. -/
theorem eulerIndex_pair_short_rows (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧ ∃ v j,
      σ 1 (t ^ N.factorization t) = q * u ^ v ∧ 0 < j ∧ Odd j ∧
      σ 1 (u ^ N.factorization u) = t ^ j ∧ j < N.factorization t ∧
      (N.factorization t + 1).Prime ∧
      ((v = 0 ∧ σ 1 (t ^ N.factorization t) = q ∧ 6 ≤ N.factorization t) ∨
        (v = 1 ∧ u = N.factorization t + 1 ∧ 5 ≤ u ∧ t % u = 1 ∧ q % u = 1 ∧
          q + 1 = 2 * (∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2)) ^ 2)) := by
  obtain ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, hcases⟩ :=
    eulerIndex_pair_prime_length h hq hN hqm hr hs hrs hJ
  obtain ⟨t', u', htu', hne', ⟨v', hA'⟩, -, -, -, hf1, -, -, -, -, hrest, d, hd⟩ :=
    eulerIndex_pair_cofactor h hq hN hqm hr hs hrs hJ
  obtain ⟨h1, h2⟩ := eipsr_label h hq hN hqm hJ htu htu' hne' hB hA'
  rw [h1, h2] at hrest
  rw [h2] at hf1 hd
  obtain ⟨t'', u'', htu'', hne'', ⟨v'', hA''⟩, -, -, j'', -, -, hB'', hcount, -⟩ :=
    eulerIndex_pair_t_count h hq hN hqm hr hs hrs hJ
  obtain ⟨h1', h2'⟩ := eipsr_label h hq hN hqm hJ htu htu'' hne'' hB hA''
  rw [h1', h2'] at hB''
  rw [h1'] at hcount
  set w := ∏ p ∈ N.primeFactors \ {q, r, s}, p ^ (N.factorization p / 2) with hwdef
  -- basic facts
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hJm := eulerIndex_dvd_sq h hq hN1 hqm
  have hfacts : ∀ p ∈ ({t, u} : Finset ℕ), p.Prime ∧ p ≠ 2 ∧ p ≠ q := by
    intro p hp
    rw [htu, ← hJ] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpJ := Nat.dvd_of_mem_primeFactors hp
    have hpm : p ∣ m := hpp.dvd_of_dvd_pow (hpJ.trans hJm)
    refine ⟨hpp, ?_, ?_⟩
    · rintro rfl
      exact (Nat.not_even_iff_odd.mpr (odd_eulerIndex h hq hN1 hqm)) (even_iff_two_dvd.mpr hpJ)
    · rintro rfl; exact hqm hpm
  obtain ⟨ht, ht2, htq⟩ := hfacts t (by simp)
  obtain ⟨hu, hu2, huq⟩ := hfacts u (by simp)
  have hvq : N.factorization q = 1 := by
    rw [hN, Nat.factorization_mul hq.ne_zero (pow_ne_zero _ hm), Finsupp.add_apply,
      hq.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun hd => hqm (hq.dvd_of_dvd_pow hd))]
  have hodd : Odd (N.factorization q) := by rw [hvq]; exact odd_one
  have he : Even (N.factorization t) := even_factorization_of_ne h hq hodd ht htq
  have hfe : Even (N.factorization u) := even_factorization_of_ne h hq hodd hu huq
  have hf0 : N.factorization u ≠ 0 := fun h0 => by
    rw [h0] at hf1; exact Nat.not_prime_one hf1
  have huw : ¬ u ∣ w := by
    intro huw'
    obtain ⟨p, hp, hpd⟩ := (hu.prime.dvd_finsetProd_iff _).mp huw'
    obtain ⟨hpN, -, -, hpu⟩ := eipsr_mem_out htu hp
    exact hpu ((Nat.prime_dvd_prime_iff_eq hu (Nat.prime_of_mem_primeFactors hpN)).mp
      (hu.dvd_of_dvd_pow hpd)).symm
  have hjj : j'' = j := by
    rw [hB] at hB''
    exact Nat.pow_right_injective ht.two_le hB''.symm
  rw [hjj] at hcount
  refine ⟨t, u, htu, hne, v, j, hA, hj, hjo, hB, hje, hp, ?_⟩
  rcases hcases with ⟨hv, hq0⟩ | ⟨hv, hue, htu1, hqu, hw⟩
  · left
    refine ⟨hv, hq0, ?_⟩
    obtain ⟨k, hk⟩ := he
    obtain ⟨i, hi⟩ := hjo
    rcases (show N.factorization t = 2 ∨ N.factorization t = 4 ∨ 6 ≤ N.factorization t by
      omega) with he2 | he4 | he6
    · exfalso
      have hj1 : j = 1 := by omega
      rw [hj1, pow_one] at hB
      rw [he2] at hq0
      have h31 := sigma_prime_sq_row_eq_thirtyone ht ht2 hu hu2 hq0 hd hB
      have := (special_mod_four h hq hodd).1
      omega
    · exfalso
      rw [he4] at hq0
      exact sigma_prime_fourth_row_false ht ht2 hu hu2 hq0 hd huw (by omega)
        (by obtain ⟨c, hc⟩ := hfe; omega) hfe hB
    · exact he6
  · right
    refine ⟨hv, hue, ?_, htu1, hqu, hw⟩
    obtain ⟨k, hk⟩ := he
    by_contra hu5
    have hu3 : u = 3 := by
      have := hu.two_le
      omega
    have he2 : N.factorization t = 2 := by omega
    have hj1 : j = 1 := by omega
    rw [he2, hj1] at hcount
    set O := N.primeFactors \ {q, r, s} with hOdef
    have hsum : ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization t = 1 := by omega
    obtain ⟨p, hpO, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; norm_num :
      ∑ p ∈ O, (σ 1 (p ^ N.factorization p)).factorization t ≠ 0)
    have hle : (σ 1 (p ^ N.factorization p)).factorization t ≤ 1 :=
      (Finset.single_le_sum (f := fun p => (σ 1 (p ^ N.factorization p)).factorization t)
        (fun i _ => Nat.zero_le _) hpO).trans hsum.le
    obtain ⟨hpN, hpq, hpt, hpu⟩ := eipsr_mem_out htu hpO
    obtain ⟨⟨x, y, hxy⟩, hpdvd, hgP⟩ := hrest p hpN hpq hpt hpu
    have hx : x = 1 := by
      have hfx : (σ 1 (p ^ N.factorization p)).factorization t = x := by
        rw [hxy, Nat.factorization_mul (pow_ne_zero _ ht.ne_zero) (pow_ne_zero _ hu.ne_zero),
          Finsupp.add_apply, ht.factorization_pow, hu.factorization_pow,
          Finsupp.single_eq_same, Finsupp.single_apply, if_neg hne.symm, add_zero]
      omega
    rw [hx, pow_one, hu3] at hxy
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpN
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hpN)
    have hge : Even (N.factorization p) := even_factorization_of_ne h hq hodd hpp hpq
    have hg0 : N.factorization p ≠ 0 :=
      (hpp.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hpN)).ne'
    have hg2 : 2 ≤ N.factorization p := by obtain ⟨c, hc⟩ := hge; omega
    have hpq1 : p ∣ q + 1 := (dvd_pow_self p hg0).trans hpdvd
    rw [hv, hu3, pow_one, he2] at hA
    have ht3 : t ≠ 3 := by rw [← hu3]; exact hne
    have hp3 : p ≠ 3 := by rw [← hu3]; exact hpu
    exact sigma_outsider_row_three_false ht ht3 hpp hp2 hp3 hge hg2 hgP hxy hpq1 hA

end OddPerfect

#print axioms OddPerfect.sigma_prime_sq_row_eq_thirtyone
#print axioms OddPerfect.sigma_prime_fourth_row_false
#print axioms OddPerfect.sigma_outsider_row_three_false
#print axioms OddPerfect.eulerIndex_pair_short_rows
