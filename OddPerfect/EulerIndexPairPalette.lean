import OddPerfect.EulerIndexPairAll
import OddPerfect.NagellPrime
import OddPerfect.HalfSigmaSquare

/-!
# Two prime Euler index: the exponent of the second row and the exponents 2 and 4

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors.
`eulerIndex_pair_rows_all` labels them `(t, u)` with `σ(t ^ e) = q u ^ v` and
`σ(u ^ f) = t ^ j`, where `e = v_t(N)` and `f = v_u(N)`.

* `eulerIndex_pair_pure_exponent_odd`: `j` is odd. An even `j` makes `σ(u ^ f)` a square, so
  `(u, f) = (3, 4)` and `t = 11` (`isSquare_sigma_prime_pow_iff`), and both are `3` modulo `4`,
  against `eulerIndex_pair_not_both_three_mod_four`.
* `eulerIndex_pair_palette`: if both index primes have exponent `2` or `4` in `N`, then
  `f = 4` and `σ(u ^ 4) = t ^ j` with `j ≥ 3` odd. First `j = 1` is excluded: then
  `t = σ(u ^ f) ≡ 1 (mod u)`, so `u ∣ σ(t ^ e)` only for `u = e + 1`, which leaves finitely
  many explicit cases; otherwise `v = 0`, `q = σ(t ^ e)`, and `((q + 1) / 2) J = m ^ 2` with
  `(q + 1) / 2` coprime to `J` makes `(σ(t ^ e) + 1) / 2` a square, which the module
  `HalfSigmaSquare` rules out. Then `f = 2` would give `u ^ 2 + u + 1 = t ^ j` with `j ≠ 1`,
  against Nagell's theorem (`phi3_eq_prime_pow_exponent`).

These are restricted results (special exponent 1, Euler index supported on exactly two
primes, and for the second theorem both index primes with exponent 2 or 4). The remaining
case `u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = t ^ j` with `j ≥ 3` odd is NOT excluded here. Their
novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairPalette

/-- `σ(p ^ 2) = p ^ 2 + p + 1`. -/
private lemma sig2 {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  ring

/-- `σ(p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1`. -/
private lemma sig4 {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 4) = p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]
  ring

/-- The common facts for an odd perfect number `q * m ^ 2` and the primes of its index. -/
private lemma setup {N q m : ℕ} (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) :
    (q + 1) * eulerIndex q 1 m = 2 * m ^ 2 ∧ eulerIndex q 1 m ≠ 0 ∧ m ≠ 0 ∧ Odd q ∧
      ∀ p ∈ (eulerIndex q 1 m).primeFactors, p.Prime ∧ p ≠ 2 ∧
        N.factorization p = (m ^ 2).factorization p ∧ Even (N.factorization p) ∧
        N.factorization p ≠ 0 := by
  set J := eulerIndex q 1 m with hJdef
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hJ2 : (q + 1) * J = 2 * m ^ 2 := by
    have := sigma_special_mul_eulerIndex h hq hN1 hqm
    rw [sigma_one_apply_prime_pow hq] at this
    simpa [Finset.sum_range_succ, add_comm] using this
  have hJm : J ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN1 hqm
  have hqJ : ¬ q ∣ J := fun hd => hqm (hq.dvd_of_dvd_pow (hd.trans hJm))
  have hJ0 : J ≠ 0 := fun h0 => hqJ (h0 ▸ dvd_zero q)
  have hmN : m ^ 2 ∣ N := by rw [hN]; exact dvd_mul_left _ _
  have hqo : Odd q := Odd.of_dvd_nat h.1 (by rw [hN]; exact dvd_mul_right q _)
  refine ⟨hJ2, hJ0, hm, hqo, fun p hp => ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpJ : p ∣ J := Nat.dvd_of_mem_primeFactors hp
  have hpq : p ≠ q := by rintro rfl; exact hqJ hpJ
  have hbr : N.factorization p = (m ^ 2).factorization p := by
    rw [hN, Nat.factorization_mul hq.ne_zero hn0, Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hpq), zero_add]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.1) (even_iff_two_dvd.mpr ((hpJ.trans hJm).trans hmN))
  refine ⟨hpp, hp2, hbr, ?_, ?_⟩
  · rw [hbr, Nat.factorization_pow]; exact ⟨m.factorization p, by simp [two_mul]⟩
  · rw [hbr]; exact (hpp.factorization_pos_of_dvd hn0 (hpJ.trans hJm)).ne'

/-- `u ∣ u c + d` gives `u ∣ d`. -/
private lemma dvd_of_dvd_mul_add {u c d : ℕ} (h : u ∣ u * c + d) : u ∣ d :=
  (Nat.dvd_add_right (dvd_mul_right u c)).mp h

/-- From `q * b ^ (w + 1) = b * n` to `q * b ^ w = n`. -/
private lemma cancel_pow {q b w n : ℕ} (hb : 0 < b) (h : q * b ^ (w + 1) = n * b) :
    q * b ^ w = n :=
  Nat.eq_of_mul_eq_mul_right hb (by rw [mul_assoc, ← pow_succ]; exact h)

/-- The case `j = 1` is impossible when both exponents are `2` or `4`. -/
private lemma core {q m J t u v e f : ℕ} (hq : q.Prime) (ht : t.Prime) (ht2 : t ≠ 2)
    (hu : u.Prime) (hu2 : u ≠ 2) (hJ2 : (q + 1) * J = 2 * m ^ 2) (hJ : J.primeFactors = {t, u})
    (hJ0 : J ≠ 0) (hm : m ≠ 0) (hqo : Odd q) (he : e = 2 ∨ e = 4) (hf : f = 2 ∨ f = 4)
    (hfm : (m ^ 2).factorization u = f) (hA : σ 1 (t ^ e) = q * u ^ v)
    (hB : σ 1 (u ^ f) = t) (htq : ¬ t ∣ q + 1) : False := by
  have hu3 : 3 ≤ u := by have := hu.two_le; omega
  obtain ⟨a, hta⟩ : ∃ a, t = u * a + 1 := by
    rcases hf with hf' | hf' <;> rw [hf'] at hB
    · exact ⟨u + 1, by rw [← hB, sig2 hu]; ring⟩
    · exact ⟨u ^ 3 + u ^ 2 + u + 1, by rw [← hB, sig4 hu]; ring⟩
  have h13 : 13 ≤ t := by
    rcases hf with hf' | hf' <;> rw [hf'] at hB
    · rw [sig2 hu] at hB; nlinarith
    · rw [sig4 hu] at hB; nlinarith [Nat.zero_le (u ^ 4), Nat.zero_le (u ^ 3)]
  rcases Nat.eq_zero_or_pos v with hv | hv
  · -- `v = 0`: `q = σ(t ^ e)`
    rw [hv, pow_zero, mul_one] at hA
    obtain ⟨d, hd⟩ : ∃ d, q + 1 = 2 * d := by obtain ⟨c, hc⟩ := hqo; exact ⟨c + 1, by omega⟩
    have hsq : ¬ u ∣ q + 1 → ∃ z, q + 1 = 2 * z ^ 2 := by
      intro hun
      have hdJ : d * J = m ^ 2 :=
        Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [← hJ2, hd]; ring)
      have hcop : Nat.Coprime d J := by
        refine Nat.coprime_of_dvd fun p hp hpd hpJ => ?_
        have hmem : p ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpJ, hJ0⟩
        rw [hJ] at hmem
        have hpq : p ∣ q + 1 := by rw [hd]; exact dvd_mul_of_dvd_right hpd 2
        rcases Finset.mem_insert.mp hmem with rfl | hpu
        · exact htq hpq
        · rw [Finset.mem_singleton.mp hpu] at hpq; exact hun hpq
      obtain ⟨z, hz⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hdJ
      exact ⟨z, by rw [hd, hz]⟩
    rcases he with rfl | rfl
    · rw [sig2 ht] at hA
      have hun : ¬ u ∣ q + 1 := by
        intro hd'
        rw [← hA, hta, show (u * a + 1) ^ 2 + (u * a + 1) + 1 + 1 =
          u * (u * a ^ 2 + 3 * a) + 2 * 2 by ring] at hd'
        rcases (Nat.Prime.dvd_mul hu).mp (dvd_of_dvd_mul_add hd') with h | h <;>
          exact hu2 ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp h)
      obtain ⟨z, hz⟩ := hsq hun
      have h5 := eq_five_of_sigma_prime_sq_succ_eq_two_mul_sq ht ht2
        (by rw [sig2 ht, hA]; exact hz)
      omega
    · rw [sig4 ht] at hA
      by_cases hu3' : u = 3
      · subst hu3'
        rcases hf with rfl | rfl
        · rw [sig2 Nat.prime_three] at hB
          have ht' : t = 13 := by linarith
          subst ht'
          have hq' : q = 30941 := by linarith
          subst hq'
          have h81 : 3 ^ 4 ∣ m ^ 2 := by
            have h2 : 3 ^ 4 ∣ 2 * m ^ 2 := by
              rw [← hJ2]; exact dvd_mul_of_dvd_left (by norm_num) _
            exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2
          have := (Nat.prime_three.pow_dvd_iff_le_factorization (pow_ne_zero 2 hm)).mp h81
          omega
        · rw [sig4 Nat.prime_three] at hB
          have ht' : t = 121 := by linarith
          subst ht'
          norm_num at ht
      · have hun : ¬ u ∣ q + 1 := by
          intro hd'
          rw [← hA, hta, show (u * a + 1) ^ 4 + (u * a + 1) ^ 3 + (u * a + 1) ^ 2 + (u * a + 1)
            + 1 + 1 = u * (u ^ 3 * a ^ 4 + 5 * u ^ 2 * a ^ 3 + 10 * u * a ^ 2 + 10 * a) + 2 * 3
            by ring] at hd'
          rcases (Nat.Prime.dvd_mul hu).mp (dvd_of_dvd_mul_add hd') with h | h
          · exact hu2 ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_two).mp h)
          · exact hu3' ((Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp h)
        obtain ⟨z, hz⟩ := hsq hun
        exact sigma_prime_fourth_succ_ne_two_mul_sq ht ht2 (by rw [sig4 ht, hA]; exact hz)
  · -- `v ≥ 1`: `u ∣ σ(t ^ e) ≡ e + 1 (mod u)`
    have hud : u ∣ σ 1 (t ^ e) := by
      rw [hA]; exact dvd_mul_of_dvd_right (dvd_pow_self u hv.ne') q
    obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    rcases he with rfl | rfl
    · rw [sig2 ht, hta, show (u * a + 1) ^ 2 + (u * a + 1) + 1 = u * (u * a ^ 2 + 3 * a) + 3
        by ring] at hud
      have hu3' : u = 3 := (Nat.prime_dvd_prime_iff_eq hu Nat.prime_three).mp
        (dvd_of_dvd_mul_add hud)
      subst hu3'
      rcases hf with rfl | rfl
      · rw [sig2 Nat.prime_three] at hB
        have ht' : t = 13 := by linarith
        subst ht'
        rw [sig2 ht] at hA
        have hq61 : q * 3 ^ w = 61 := cancel_pow (by norm_num) (by linarith)
        rcases Nat.eq_zero_or_pos w with rfl | hw
        · rw [pow_zero, mul_one] at hq61
          subst hq61
          have hmJ : m ^ 2 = 31 * J := by omega
          have hp31 : Nat.Prime 31 := by norm_num
          have h1 : 31 ∣ m := hp31.dvd_of_dvd_pow (⟨J, hmJ⟩ : 31 ∣ m ^ 2)
          have h2 : 31 * 31 ∣ 31 * J := by rw [← hmJ, sq]; exact mul_dvd_mul h1 h1
          have h3 : 31 ∣ J := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
          have hmem : 31 ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hp31, h3, hJ0⟩
          rw [hJ] at hmem
          simp at hmem
        · have h3 : 3 ∣ 61 := by
            rw [← hq61]; exact dvd_mul_of_dvd_right (dvd_pow_self 3 hw.ne') q
          norm_num at h3
      · rw [sig4 Nat.prime_three] at hB
        have ht' : t = 121 := by linarith
        subst ht'
        norm_num at ht
    · rw [sig4 ht, hta, show (u * a + 1) ^ 4 + (u * a + 1) ^ 3 + (u * a + 1) ^ 2 + (u * a + 1)
        + 1 = u * (u ^ 3 * a ^ 4 + 5 * u ^ 2 * a ^ 3 + 10 * u * a ^ 2 + 10 * a) + 5
        by ring] at hud
      have hu5 : u = 5 := (Nat.prime_dvd_prime_iff_eq hu (by norm_num)).mp
        (dvd_of_dvd_mul_add hud)
      subst hu5
      rcases hf with rfl | rfl
      · rw [sig2 (by norm_num : Nat.Prime 5)] at hB
        have ht' : t = 31 := by linarith
        subst ht'
        rw [sig4 ht] at hA
        have hq1 : q * 5 ^ w = 190861 := cancel_pow (by norm_num) (by linarith)
        rcases Nat.eq_zero_or_pos w with rfl | hw
        · rw [pow_zero, mul_one] at hq1
          subst hq1
          norm_num at hq
        · have h5 : 5 ∣ 190861 := by
            rw [← hq1]; exact dvd_mul_of_dvd_right (dvd_pow_self 5 hw.ne') q
          norm_num at h5
      · rw [sig4 (by norm_num : Nat.Prime 5)] at hB
        have ht' : t = 781 := by linarith
        subst ht'
        norm_num at ht

end EulerIndexPairPalette

open EulerIndexPairPalette

variable {N q m r s : ℕ}

/-- **Two prime index, odd exponent in the second row.** Let `N = q m ^ 2` be an odd perfect
number with special prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index
`J = σ(m ^ 2) / q` has exactly the two prime factors `r ≠ s`. For the labeling `(t, u)` of
`eulerIndex_pair_rows_all`, all of its conclusions hold, and moreover the exponent `j` in
`σ(u ^ v_u(N)) = t ^ j` is odd. This is a restricted result (special exponent 1, index
supported on exactly two primes); it does not exclude this case. Its novelty has not been
verified. -/
theorem eulerIndex_pair_pure_exponent_odd (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ Odd j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t ∧
      (N.factorization u + 1).Prime ∧ orderOf (u : ZMod t) = N.factorization u + 1 ∧
      t % (2 * (N.factorization u + 1)) = 1 ∧
      ((N.factorization t + 1).Prime ∨ ∃ p, p.Prime ∧ N.factorization t + 1 = p ^ 2) ∧
      (orderOf (q : ZMod t) = 1 ∨ orderOf (q : ZMod t) = N.factorization u + 1) ∧
      ∀ p ∈ N.primeFactors, p ≠ q → p ≠ t → p ≠ u →
        (∃ x y, σ 1 (p ^ N.factorization p) = t ^ x * u ^ y) ∧
        p ^ N.factorization p ∣ q + 1 ∧
        ((N.factorization p + 1).Prime ∨ ∃ P, P.Prime ∧ N.factorization p + 1 = P ^ 2) := by
  obtain ⟨t, u, htu, hne, hA, ⟨j, hj, hB⟩, h3, h4, hf1, hord, hmod, hE, hordq, hrest⟩ :=
    eulerIndex_pair_rows_all h hq hN hqm hr hs hrs hJ
  refine ⟨t, u, htu, hne, hA, ⟨j, hj, ?_, hB⟩, h3, h4, hf1, hord, hmod, hE, hordq, hrest⟩
  obtain ⟨-, -, -, -, hP⟩ := setup h hq hN hqm
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  obtain ⟨hu, hu2, -, hfe, hf0⟩ := hP u huJ
  obtain ⟨ht, -, -, -, -⟩ := hP t htJ
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | hodd
  · exfalso
    have hsq : IsSquare (σ 1 (u ^ N.factorization u)) := ⟨t ^ i, by rw [hB, hi, pow_add]⟩
    obtain ⟨rfl, hf4⟩ := (isSquare_sigma_prime_pow_iff hu hu2 hfe hf0).mp hsq
    have h121 : σ 1 (3 ^ 4) = 121 := (sig4 Nat.prime_three).trans (by norm_num)
    rw [hf4, h121] at hB
    have h11 : t = 11 := by
      have hd : t ∣ 11 ^ 2 := by
        rw [show (11 : ℕ) ^ 2 = 121 by norm_num, hB]; exact dvd_pow_self t hj.ne'
      exact (Nat.prime_dvd_prime_iff_eq ht (by norm_num)).mp (ht.dvd_of_dvd_pow hd)
    subst h11
    apply eulerIndex_pair_not_both_three_mod_four h hq hN hqm hr hs hrs hJ
    have hr' : r ∈ ({11, 3} : Finset ℕ) := by rw [htu]; simp
    have hs' : s ∈ ({11, 3} : Finset ℕ) := by rw [htu]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr' hs'
    rcases hr' with rfl | rfl <;> rcases hs' with rfl | rfl <;> norm_num
  · exact hodd

/-- **Two prime index, exponents 2 and 4.** In the setting of
`eulerIndex_pair_pure_exponent_odd`, suppose moreover that both prime factors `r` and `s` of
the Euler index have exponent `2` or `4` in `N`. Then for the labeling `(t, u)` (with
`σ(t ^ v_t(N)) = q u ^ v` and `t ∤ q + 1`) we have `v_u(N) = 4` and
`σ(u ^ 4) = u ^ 4 + u ^ 3 + u ^ 2 + u + 1 = t ^ j` with `j ≥ 3` odd. This is a restricted
result (special exponent 1, index supported on exactly two primes, both with exponent 2 or 4);
the remaining case `σ(u ^ 4) = t ^ j` with `j ≥ 3` odd is NOT excluded here. Its novelty has
not been verified. -/
theorem eulerIndex_pair_palette (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s})
    (hexp : ∀ p ∈ ({r, s} : Finset ℕ), N.factorization p = 2 ∨ N.factorization p = 4) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧ ¬ t ∣ q + 1 ∧
      N.factorization u = 4 ∧ ∃ j, 3 ≤ j ∧ Odd j ∧ σ 1 (u ^ 4) = t ^ j := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hjo, hB⟩, h3, -⟩ :=
    eulerIndex_pair_pure_exponent_odd h hq hN hqm hr hs hrs hJ
  obtain ⟨hJ2, hJ0, hm, hqo, hP⟩ := setup h hq hN hqm
  have huJ : u ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  have htJ : t ∈ (eulerIndex q 1 m).primeFactors := by rw [hJ, ← htu]; simp
  obtain ⟨hu, hu2, hbu, -, -⟩ := hP u huJ
  obtain ⟨ht, ht2, -, -, -⟩ := hP t htJ
  have he := hexp t (by rw [← htu]; simp)
  have hf := hexp u (by rw [← htu]; simp)
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [pow_one] at hB
    exact core hq ht ht2 hu hu2 hJ2 (by rw [hJ, ← htu]) hJ0 hm hqo he hf hbu.symm hA hB h3
  have hf4 : N.factorization u = 4 := by
    rcases hf with hf | hf
    · exfalso
      apply hj1
      rw [hf, sigma_prime_sq hu] at hB
      exact phi3_eq_prime_pow_exponent ht hu hj hB
    · exact hf
  refine ⟨t, u, htu, hne, ⟨v, hA⟩, h3, hf4, j, ?_, hjo, by rw [← hf4]; exact hB⟩
  obtain ⟨i, rfl⟩ := hjo
  omega

end OddPerfect

#print axioms OddPerfect.eulerIndex_pair_pure_exponent_odd
#print axioms OddPerfect.eulerIndex_pair_palette
