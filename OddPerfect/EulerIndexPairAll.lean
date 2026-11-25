import OddPerfect.EulerIndexPairRows

/-!
# All rows when the Euler index is supported on two primes

Let `N = q * m ^ 2` be an odd perfect number with special prime `q` of exponent 1 and
`q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly two prime factors.
`eulerIndex_pair_rows` (in `OddPerfect/EulerIndexPairRows.lean`) labels them `(t, u)` with
`σ(t ^ e) = q u ^ v` and `σ(u ^ f) = t ^ j`, where `e = v_t(N)` and `f = v_u(N)`, and gives the
shape of these two rows. This module adds two facts for the same labeling.

* The order of `q` modulo `t` is `1` or `f + 1`: modulo `t` we have `q u ^ v ≡ 1` and
  `u ^ (f + 1) ≡ 1`, so `q ^ (f + 1) ≡ 1`, and `f + 1` is prime.
* Every other row: for a prime `p ∣ N` other than `q`, `t`, `u`, with `g = v_p(N)`, the row
  `σ(p ^ g)` is a product `t ^ x u ^ y`, `p ^ g ∣ q + 1`, and `g + 1` is prime or the square of a
  prime (`succ_prime_or_prime_sq_of_sigma_eq_prime_pow_mul_prime_pow`).

These are restricted results (special exponent 1, index supported on exactly two primes).
They do not exclude this case. Their novelty has not been verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace EulerIndexPairAll

/-- `σ(n) = σ(p ^ v_p(n)) σ(n / p ^ v_p(n))`. -/
private lemma sigma_split {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    σ 1 n = σ 1 (p ^ n.factorization p) * σ 1 (ordCompl[p] n) := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  exact isMultiplicative_sigma.map_mul_of_coprime ((Nat.coprime_ordCompl hp hn).pow_left _)

/-- The row of one prime divides `σ(n)`. -/
private lemma row_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    σ 1 (p ^ n.factorization p) ∣ σ 1 n :=
  ⟨_, sigma_split hp hn⟩

/-- The rows of two distinct primes divide `σ(n)` together. -/
private lemma pair_dvd {n p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hpp : p ≠ p')
    (hn : n ≠ 0) :
    σ 1 (p ^ n.factorization p) * σ 1 (p' ^ n.factorization p') ∣ σ 1 n := by
  rw [sigma_split hp hn]
  have h0 : ordCompl[p] n ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hf : (ordCompl[p] n).factorization p' = n.factorization p' := by
    rw [Nat.factorization_ordCompl, Finsupp.erase_ne hpp.symm]
  exact mul_dvd_mul_left _ (hf ▸ row_dvd hp' h0)

end EulerIndexPairAll

open EulerIndexPairAll

/-- **Row supported on two primes.** Let `p ≥ 3` be a prime, `g ≥ 2` even, `t` and `u` primes,
and `σ(p ^ g) = t ^ x u ^ y`. Then `g + 1` is prime or the square of a prime. Each divisor
`d ≥ 3` of `g + 1` yields a prime of `{t, u}` in which `p` has order `d`
(`exists_prime_dvd_sigma_orderOf_eq`), so `g + 1` has at most two divisors above 1. -/
theorem succ_prime_or_prime_sq_of_sigma_eq_prime_pow_mul_prime_pow {p g t u x y : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hg : Even g) (hg2 : 2 ≤ g) (ht : t.Prime) (hu : u.Prime)
    (hrow : σ 1 (p ^ g) = t ^ x * u ^ y) :
    (g + 1).Prime ∨ ∃ P, P.Prime ∧ g + 1 = P ^ 2 := by
  have hmem : ∀ d, 3 ≤ d → d ∣ g + 1 →
      ∃ w, (w = t ∨ w = u) ∧ orderOf (p : ZMod w) = d := by
    intro d hd3 hd
    obtain ⟨w, hw, hwd, ho, -⟩ := exists_prime_dvd_sigma_orderOf_eq hp hp3 hd3 hd
    rw [hrow] at hwd
    refine ⟨w, ?_, ho⟩
    rcases (Nat.Prime.dvd_mul hw).mp hwd with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hw ht).mp (hw.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hw hu).mp (hw.dvd_of_dvd_pow h))
  have hodd : ¬ 2 ∣ g + 1 := by obtain ⟨k, hk⟩ := hg; omega
  have hn3 : 3 ≤ g + 1 := by omega
  have hP : (g + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hPd : (g + 1).minFac ∣ g + 1 := Nat.minFac_dvd _
  set P := (g + 1).minFac
  have hP3 : 3 ≤ P := by
    have := hP.two_le
    rcases (show P = 2 ∨ 3 ≤ P by omega) with h | h
    · exact absurd (h ▸ hPd) hodd
    · exact h
  by_cases hPn : P = g + 1
  · left; rw [← hPn]; exact hP
  right
  refine ⟨P, hP, ?_⟩
  obtain ⟨c, hc⟩ := hPd
  have hcd : c ∣ g + 1 := ⟨P, by rw [hc, mul_comm]⟩
  have hc3 : 3 ≤ c := by
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c by omega) with h | h | h | h
    · rw [h, mul_zero] at hc; omega
    · rw [h, mul_one] at hc; exact absurd hc.symm hPn
    · rw [h] at hc; exact absurd ⟨P, by rw [hc, mul_comm]⟩ hodd
    · exact h
  obtain ⟨w1, hw1, ho1⟩ := hmem P hP3 ⟨c, hc⟩
  obtain ⟨w2, hw2, ho2⟩ := hmem (g + 1) hn3 (dvd_refl _)
  obtain ⟨w3, hw3, ho3⟩ := hmem c hc3 hcd
  have h12 : w1 ≠ w2 := by
    rintro rfl; exact hPn (ho1.symm.trans ho2)
  rcases (show w3 = w1 ∨ w3 = w2 by omega) with rfl | rfl
  · rw [ho1] at ho3
    rw [hc, ← ho3, sq]
  · rw [ho2] at ho3
    have h1 : P * c = 1 * c := by rw [← hc, one_mul, ho3]
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < c) h1
    omega

variable {N q m r s : ℕ}

/-- **Two prime index, all rows.** Let `N = q m ^ 2` be an odd perfect number with special
prime `q` of exponent 1, `q ∤ m`, and suppose the Euler index `J = σ(m ^ 2) / q` has exactly
the two prime factors `r ≠ s`. For one labeling `(t, u)` of `{r, s}`, with `e = v_t(N)` and
`f = v_u(N)`, all conclusions of `eulerIndex_pair_rows` hold; moreover the order of `q` modulo
`t` is `1` or `f + 1`, and for every prime `p ∣ N` other than `q`, `t`, `u`, with
`g = v_p(N)`, the row `σ(p ^ g)` has the form `t ^ x u ^ y`, `p ^ g ∣ q + 1`, and `g + 1` is
prime or the square of a prime. This is a restricted result (special exponent 1, index
supported on exactly two primes); it does not exclude this case. Its novelty has not been
verified. -/
theorem eulerIndex_pair_rows_all (h : OddPerfect N) (hq : q.Prime) (hN : N = q * m ^ 2)
    (hqm : ¬ q ∣ m) (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s)
    (hJ : (eulerIndex q 1 m).primeFactors = {r, s}) :
    ∃ t u, ({t, u} : Finset ℕ) = {r, s} ∧ t ≠ u ∧
      (∃ v, σ 1 (t ^ N.factorization t) = q * u ^ v) ∧
      (∃ j, 0 < j ∧ σ 1 (u ^ N.factorization u) = t ^ j) ∧ ¬ t ∣ q + 1 ∧
      (eulerIndex q 1 m).factorization t = N.factorization t ∧
      (N.factorization u + 1).Prime ∧ orderOf (u : ZMod t) = N.factorization u + 1 ∧
      t % (2 * (N.factorization u + 1)) = 1 ∧
      ((N.factorization t + 1).Prime ∨ ∃ p, p.Prime ∧ N.factorization t + 1 = p ^ 2) ∧
      (orderOf (q : ZMod t) = 1 ∨ orderOf (q : ZMod t) = N.factorization u + 1) ∧
      ∀ p ∈ N.primeFactors, p ≠ q → p ≠ t → p ≠ u →
        (∃ x y, σ 1 (p ^ N.factorization p) = t ^ x * u ^ y) ∧
        p ^ N.factorization p ∣ q + 1 ∧
        ((N.factorization p + 1).Prime ∨ ∃ P, P.Prime ∧ N.factorization p + 1 = P ^ 2) := by
  obtain ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hB⟩, h3, h4, hf1, hord, hmod, hE⟩ :=
    eulerIndex_pair_rows h hq hN hqm hr hs hrs hJ
  set J := eulerIndex q 1 m with hJdef
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero _ hm
  have hσ : σ 1 (m ^ 2) = q * J := by
    have := sigma_sq_eq_mul_eulerIndex h hq hN1 hqm
    rwa [pow_one] at this
  have hJ2 : (q + 1) * J = 2 * m ^ 2 := by
    have := sigma_special_mul_eulerIndex h hq hN1 hqm
    rw [sigma_one_apply_prime_pow hq] at this
    simpa [Finset.sum_range_succ, add_comm] using this
  have hJm : J ∣ m ^ 2 := eulerIndex_dvd_sq h hq hN1 hqm
  have hqJ : ¬ q ∣ J := fun hd => hqm (hq.dvd_of_dvd_pow (hd.trans hJm))
  have hJ0 : J ≠ 0 := fun h0 => hqJ (h0 ▸ dvd_zero q)
  have hbr : ∀ p, p ≠ q → N.factorization p = (m ^ 2).factorization p := by
    intro p hp
    rw [hN, Nat.factorization_mul hq.ne_zero hn0, Finsupp.add_apply,
      hq.factorization, Finsupp.single_apply, if_neg (Ne.symm hp), zero_add]
  have htJ : t ∈ J.primeFactors := by rw [hJ, ← htu]; simp
  have ht : t.Prime := Nat.prime_of_mem_primeFactors htJ
  have htq : t ≠ q := by
    rintro rfl; exact hqJ (Nat.dvd_of_mem_primeFactors htJ)
  -- the order of `q` modulo `t`
  have hordq : orderOf (q : ZMod t) = 1 ∨ orderOf (q : ZMod t) = N.factorization u + 1 := by
    have hA1 : ((σ 1 (t ^ N.factorization t) : ℕ) : ZMod t) = 1 := by
      rw [sigma_one_apply_prime_pow ht, Finset.sum_range_succ']
      push_cast
      simp
    have hAq : (q : ZMod t) * (u : ZMod t) ^ v = 1 := by
      rw [← hA1, hA]; push_cast; ring
    have hu1 : (u : ZMod t) ^ (N.factorization u + 1) = 1 := by
      rw [← hord]; exact pow_orderOf_eq_one _
    have hpow : (q : ZMod t) ^ (N.factorization u + 1) = 1 := by
      calc (q : ZMod t) ^ (N.factorization u + 1)
          = ((q : ZMod t) * (u : ZMod t) ^ v) ^ (N.factorization u + 1) := by
            rw [mul_pow, ← pow_mul, mul_comm v, pow_mul, hu1, one_pow, mul_one]
        _ = 1 := by rw [hAq, one_pow]
    exact hf1.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hpow)
  refine ⟨t, u, htu, hne, ⟨v, hA⟩, ⟨j, hj, hB⟩, h3, h4, hf1, hord, hmod, hE, hordq, ?_⟩
  -- every other row
  intro p hpN hpq hpt hpu
  have huJ : u ∈ J.primeFactors := by rw [hJ, ← htu]; simp
  have hu : u.Prime := Nat.prime_of_mem_primeFactors huJ
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hpm : p ∣ m := by
    rcases (Nat.Prime.dvd_mul hpp).mp (hN ▸ Nat.dvd_of_mem_primeFactors hpN) with hd | hd
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hq).mp hd) hpq
    · exact hpp.dvd_of_dvd_pow hd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.1) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hpN))
  rw [hbr p hpq]
  have hg : (m ^ 2).factorization p = 2 * m.factorization p := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hpos := hpp.factorization_pos_of_dvd hm hpm
  -- the row of `p` carries no `q`
  have hA' : σ 1 (t ^ (m ^ 2).factorization t) = q * u ^ v := by rw [← hbr t htq]; exact hA
  have hqP : ¬ q ∣ σ 1 (p ^ (m ^ 2).factorization p) := by
    intro hd
    have h2 := (mul_dvd_mul (⟨u ^ v, hA'⟩ : q ∣ σ 1 (t ^ (m ^ 2).factorization t)) hd).trans
      (pair_dvd ht hpp (Ne.symm hpt) hn0)
    rw [hσ] at h2
    exact hqJ (Nat.dvd_of_mul_dvd_mul_left hq.pos h2)
  have hPJ : σ 1 (p ^ (m ^ 2).factorization p) ∣ J :=
    ((hq.coprime_iff_not_dvd.mpr hqP).symm).dvd_of_dvd_mul_left (hσ ▸ row_dvd hpp hn0)
  set A := σ 1 (p ^ (m ^ 2).factorization p) with hAdef
  have hA0 : A ≠ 0 := (sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)).ne'
  have hsub : A.factorization.support ⊆ {t, u} := by
    rw [Nat.support_factorization, htu, ← hJ]
    exact Nat.primeFactors_mono hPJ hJ0
  have hshape : A = t ^ A.factorization t * u ^ A.factorization u := by
    have hprod := Nat.prod_factorization_pow_eq_self hA0
    rw [Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _),
      Finset.prod_pair hne] at hprod
    exact hprod.symm
  refine ⟨⟨_, _, hshape⟩, ?_, ?_⟩
  · -- `p ^ g ∣ q + 1`
    have hpJ : ¬ p ∣ J := by
      intro hd
      have hmem : p ∈ J.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hd, hJ0⟩
      rw [hJ, ← htu] at hmem
      rcases Finset.mem_insert.mp hmem with h' | h'
      · exact hpt h'
      · exact hpu (Finset.mem_singleton.mp h')
    have hcop : Nat.Coprime (p ^ (m ^ 2).factorization p) J :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpJ)
    have hd : p ^ (m ^ 2).factorization p ∣ (q + 1) * J :=
      hJ2 ▸ (Nat.ordProj_dvd (m ^ 2) p).trans (dvd_mul_left _ 2)
    exact hcop.dvd_of_dvd_mul_right hd
  · exact succ_prime_or_prime_sq_of_sigma_eq_prime_pow_mul_prime_pow hpp
      (by have := hpp.two_le; omega) ⟨m.factorization p, by omega⟩ (by omega) ht hu hshape

end OddPerfect

#print axioms OddPerfect.succ_prime_or_prime_sq_of_sigma_eq_prime_pow_mul_prime_pow
#print axioms OddPerfect.eulerIndex_pair_rows_all
