import OddPerfect.RankTwoPaletteAux

/-!
# The special exponent in the palette of exponents 2 and 4: four values remain

Restricted family result; the family is not excluded, and whether the result is in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, and let exactly one prime factor `P` exceed
`q` (every prime factor other than `P` is at most `q`). Then `a ∈ {1, 5, 9, 13}`
(`special_exponent_eq_one_five_nine_or_thirteen`), refining `special_exponent_le_41`; and
`a ∈ {1, 9, 13}` under the explicit hypothesis `3 ∤ N`. The values `1, 5, 9, 13` remain
possible here.

Proof outline, with `e = v_P(N) ∈ {2, 4}`, `w = v_q(σ(P ^ e))` and `b ≤ 8` the total `q`
valuation of the rows of the primes below `q`, so that `a = b + w`, `a ≡ 1 (mod 4)`,
`a ≤ 41`, and `P > 200000`. Suppose `a ≥ 17`, so `w ≥ 9`.

* No row of a prime below `q` is divisible by `P`: then `P ^ e ∣ σ(q ^ a)`, so
  `P ^ e < (q + 1) ^ φ(a + 1)` (one cyclotomic factor), and
  `q ^ w ≤ σ(P ^ e) < 2 P ^ e < 2 (q + 1) ^ φ(a + 1) < q ^ (φ(a + 1) + 3)`, against
  `w ≥ a - 8 ≥ φ(a + 1) + 3`.
* Some row `σ(u ^ g)`, `u < q`, is divisible by `P`: then `P < q ^ 4`, so `w < 4 e`, which
  forces `e = 4` and `a ∈ {17, 21}`; then `P > q ^ 2`, at most one such `u` exists, it carries
  one unit of `P`, so `P ^ 3 ∣ σ(q ^ a)`. For `a = 17` the sizes contradict
  `P ^ 3 < (q + 1) ^ 6`. For `a = 21` the sizes give `w = 13`, hence `b = 8`, hence
  `q ≡ 1 (mod 60)`, and `rankTwo_twentyone_thirteen_false` applies.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem sigmaWeight_eq_geom' {N p q : ℕ} (hp : p.Prime) :
    sigmaWeight N p q =
      (∑ i ∈ Finset.range (N.factorization p + 1), p ^ i).factorization q := by
  unfold sigmaWeight
  rw [sigma_one_apply_prime_pow hp]

/-- Residue form of the palette capacity at the special prime. Let `N` be an odd perfect number
with special prime `q` such that every other prime factor has exponent `2` or `4`. Then the rows
of the prime factors below `q` carry at most
`(if q % 3 = 1 then 2 else 0) + (if q % 5 = 1 then 6 else 0)` at `q`. Restricted family result. -/
theorem sum_sigmaWeight_below_special_le_mod {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤
      (if q % 3 = 1 then 2 else 0) + (if q % 5 = 1 then 6 else 0) := by
  classical
  set U := N.primeFactors.filter (· < q) with hU
  have hUp : ∀ s : Finset ℕ, s ⊆ U → ∀ u ∈ s, u.Prime ∧ u < q := fun s hs u hu =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hs hu)).1,
      (Finset.mem_filter.mp (hs hu)).2⟩
  have hq2 := hq.two_le
  by_cases hsmall : q = 3 ∨ q = 5
  · have hz : ∀ p ∈ U, sigmaWeight N p q = 0 := by
      intro p hp
      obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hp2 : p ≠ 2 := fun h2 => h.not_two_dvd (h2 ▸ Nat.dvd_of_mem_primeFactors hp')
      have hp3 : p = 3 ∧ q = 5 := by
        have := hpp.two_le
        rcases hsmall with rfl | rfl
        · omega
        · interval_cases p
          · exact absurd rfl hp2
          · exact ⟨rfl, rfl⟩
          · exact absurd hpp (by norm_num)
      obtain ⟨rfl, rfl⟩ := hp3
      rw [sigmaWeight_eq_geom' hpp]
      rcases hexp 3 hp' (by norm_num) with hf | hf <;> rw [hf] <;>
        exact Nat.factorization_eq_zero_of_not_dvd (by decide)
    rw [Finset.sum_eq_zero hz]
    exact Nat.zero_le _
  push Not at hsmall
  have hpt : ∀ p ∈ U, sigmaWeight N p q ≤
      (if N.factorization p = 2 then (∑ i ∈ Finset.range 3, p ^ i).factorization q else 0) +
      (if N.factorization p = 4 then (∑ i ∈ Finset.range 5, p ^ i).factorization q
        else 0) := by
    intro p hp
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp'
    rw [sigmaWeight_eq_geom' hpp]
    rcases hexp p hp' (by omega) with hf | hf
    · rw [if_pos hf, if_neg (by omega), add_zero, hf]
    · rw [if_neg (by omega), if_pos hf, zero_add, hf]
  have hle := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hle
  have h2 : ∑ p ∈ U.filter (fun p => N.factorization p = 2),
      (∑ i ∈ Finset.range 3, p ^ i).factorization q ≤ if q % 3 = 1 then 2 else 0 := by
    split_ifs with h3
    · exact sum_factorization_geom_sum_three_le_two_of_primes hq hsmall.1 _
        (hUp _ (Finset.filter_subset _ _))
    · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
      exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_three hsmall.1 (by omega) u
  have h4 : ∑ p ∈ U.filter (fun p => N.factorization p = 4),
      (∑ i ∈ Finset.range 5, p ^ i).factorization q ≤ if q % 5 = 1 then 6 else 0 := by
    split_ifs with h5
    · exact sum_factorization_geom_sum_five_le_six_of_primes hq hsmall.2 _
        (hUp _ (Finset.filter_subset _ _))
    · refine (Finset.sum_eq_zero fun u _ => Nat.factorization_eq_zero_of_not_dvd ?_).le
      exact not_dvd_geom_sum_of_not_dvd_sub_one hq Nat.prime_five hsmall.2 (by omega) u
  omega

/-- Palette with one prime above the special prime. Let `N` be an odd perfect number with
special prime `q`, let every other prime factor have exponent `2` or `4`, and let `q` be the
second largest prime factor (some prime factor `P > q`, every prime factor other than `P` at
most `q`). Then `v_q(N) ∈ {1, 5, 9, 13}`. Restricted family result: the four values remain
possible and the family is not excluded; novelty not verified. -/
theorem special_exponent_eq_one_five_nine_or_thirteen {N q P : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q = 1 ∨ N.factorization q = 5 ∨ N.factorization q = 9 ∨
      N.factorization q = 13 := by
  classical
  have hPp := Nat.prime_of_mem_primeFactors hP
  have hPq : P ≠ q := by omega
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hqmem : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hqo := hoddN q hqmem
  have hPo := hoddN P hP
  have hq2 : q ≠ 2 := by omega
  have hP2 : P ≠ 2 := by omega
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  have ha41 := special_exponent_le_41 h hq hodd hP hqP hsecond hexp
  have hb8 := sum_sigmaWeight_below_special_le_eight h hq hexp
  have hbmod := sum_sigmaWeight_below_special_le_mod h hq hexp
  have hP200 : 200000 < P := by
    obtain ⟨p, hp, hlt⟩ := exists_primeFactor_gt_200000 h
    by_cases hpP : p = P
    · exact hpP ▸ hlt
    · have := hsecond p hp hpP
      omega
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hqP2 : q + 1 < P := by omega
  -- the ledgers at `q` and at `P`
  have hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, P} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, hpq⟩
      by_cases hpP : p = P
      · exact Or.inr hpP
      · have := hsecond p hp hpP
        exact Or.inl (by omega)
    · rintro (rfl | rfl)
      · exact ⟨hqmem, lt_irrefl _⟩
      · exact ⟨hP, by omega⟩
  have hledq := sigmaWeight_sum_eq h.2 hq hq2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_pair hPq.symm, sigmaWeight_self hq] at hledq
  have hledP := sigmaWeight_sum_eq h.2 hPp hP2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_pair hPq.symm, sigmaWeight_self hPp] at hledP
  have he24 := hexp P hP hPq
  set a := N.factorization q with ha
  set e := N.factorization P with he
  have hqw : q ^ sigmaWeight N P q ∣ σ 1 (P ^ e) := Nat.ordProj_dvd _ _
  have hPv : P ^ sigmaWeight N q P ∣ σ 1 (q ^ a) := Nat.ordProj_dvd _ _
  have hσP0 : 0 < σ 1 (P ^ e) := sigma_pos 1 _ (pow_ne_zero _ hPp.ne_zero)
  have hqwle : q ^ sigmaWeight N P q ≤ σ 1 (P ^ e) := Nat.le_of_dvd hσP0 hqw
  by_contra hgoal
  have ha17 : 17 ≤ a := by omega
  have hw9 : 9 ≤ sigmaWeight N P q := by omega
  by_cases hc0 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p P = 0
  · -- no row of a prime below `q` is divisible by `P`
    have hve : sigmaWeight N q P = e := by omega
    have hPe : P ^ e ∣ σ 1 (q ^ a) := hve ▸ hPv
    have hFA := pow_lt_succ_pow_totient_of_pow_dvd_sigma hq hPp hqP2 (by omega) (by omega) hPe
    have htot : (a + 1).totient + 11 ≤ a ∧ (a + 1).totient ≤ 18 := by
      have : a = 17 ∨ a = 21 ∨ a = 25 ∨ a = 29 ∨ a = 33 ∨ a = 37 ∨ a = 41 := by omega
      rcases this with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] <;> decide
    have hσ2 := rankTwo_sigma_lt_two_mul (k := e) hPp
    have hlt := two_mul_succ_pow_lt_pow hq5 htot.2
    have hpow : q ^ ((a + 1).totient + 3) ≤ q ^ sigmaWeight N P q :=
      Nat.pow_le_pow_right hq.pos (by omega)
    have : 2 * P ^ e < 2 * (q + 1) ^ (a + 1).totient := by linarith
    linarith
  · -- some row of a prime below `q` is divisible by `P`
    obtain ⟨u, hu, hu0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc0
    obtain ⟨hu', huq⟩ := Finset.mem_filter.mp hu
    have hup := Nat.prime_of_mem_primeFactors hu'
    have hPu : P ∣ σ 1 (u ^ N.factorization u) := Nat.dvd_of_factorization_pos hu0
    have hg := hexp u hu' (by omega)
    have hPq4 : P < q ^ 4 := by
      have h1 : P ≤ σ 1 (u ^ N.factorization u) :=
        Nat.le_of_dvd (sigma_pos 1 _ (pow_ne_zero _ hup.ne_zero)) hPu
      have h2 := sigma_prime_pow_lt_succ_pow hup (k := N.factorization u) (by omega)
      have h3 : (u + 1) ^ N.factorization u ≤ q ^ N.factorization u :=
        Nat.pow_le_pow_left (by omega) _
      have h4 : q ^ N.factorization u ≤ q ^ 4 := Nat.pow_le_pow_right hq.pos (by omega)
      omega
    have hw4e : sigmaWeight N P q < 4 * e := by
      have h1 := sigma_prime_pow_lt_succ_pow hPp (k := e) (by omega)
      have h2 : (P + 1) ^ e ≤ q ^ (4 * e) := by
        rw [pow_mul]
        exact Nat.pow_le_pow_left (by omega) e
      exact (Nat.pow_lt_pow_iff_right hq.one_lt).mp (by omega)
    have he4 : e = 4 := by omega
    have ha1721 : a = 17 ∨ a = 21 := by omega
    rw [he4] at hqw hqwle hσP0
    have hσ4 := rankTwo_sigma_lt_two_mul (k := 4) hPp
    have hPq2 : q ^ 2 < P := by
      by_contra hle
      push Not at hle
      have h1 : P ^ 4 ≤ (q ^ 2) ^ 4 := Nat.pow_le_pow_left hle 4
      have h2 : q ^ 9 ≤ q ^ sigmaWeight N P q := Nat.pow_le_pow_right hq.pos hw9
      have h3 : q ^ 9 = q * (q ^ 2) ^ 4 := by ring
      have h4 : 0 < (q ^ 2) ^ 4 := by positivity
      nlinarith
    -- each row below `q` carries at most one unit of `P`, and at most one row carries any
    have hterm : ∀ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p P ≤ 1 ∧
        (sigmaWeight N p P ≠ 0 → P ∣ ∑ i ∈ Finset.range 5, p ^ i) := by
      intro p hp
      obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      rcases hexp p hp' (by omega) with hf | hf
      · have hw' : sigmaWeight N p P = (σ 1 (p ^ 2)).factorization P := by
          unfold sigmaWeight
          rw [hf]
        rw [hw']
        have hσ0 : 0 < σ 1 (p ^ 2) := sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)
        have hlt2 := sigma_prime_pow_lt_succ_pow hpp (k := 2) (by norm_num)
        have h1 : (p + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have hz : (σ 1 (p ^ 2)).factorization P = 0 := by
          refine Nat.factorization_eq_zero_of_not_dvd fun hd => ?_
          have := Nat.le_of_dvd hσ0 hd
          omega
        exact ⟨by omega, fun h0 => absurd hz h0⟩
      · have hw' : sigmaWeight N p P = (σ 1 (p ^ 4)).factorization P := by
          unfold sigmaWeight
          rw [hf]
        rw [hw']
        have hσ0 : 0 < σ 1 (p ^ 4) := sigma_pos 1 _ (pow_ne_zero _ hpp.ne_zero)
        have hlt4 := sigma_prime_pow_lt_succ_pow hpp (k := 4) (by norm_num)
        have h1 : (p + 1) ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
        have h2 : q ^ 4 < P ^ 2 := by
          have := Nat.pow_lt_pow_left hPq2 (show (2 : ℕ) ≠ 0 by norm_num)
          rw [← pow_mul] at this
          exact this
        refine ⟨?_, fun h0 => ?_⟩
        · by_contra h2'
          push Not at h2'
          have hd : P ^ 2 ∣ σ 1 (p ^ 4) :=
            (hPp.pow_dvd_iff_le_factorization hσ0.ne').mpr (by omega)
          have := Nat.le_of_dvd hσ0 hd
          omega
        · have hd : P ∣ σ 1 (p ^ 4) := Nat.dvd_of_factorization_pos h0
          rw [sigma_one_apply_prime_pow hpp] at hd
          exact hd
    have hcard : ((N.primeFactors.filter (· < q)).filter
        (fun p => sigmaWeight N p P ≠ 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
      have hxq := (Finset.mem_filter.mp hx1).2
      have hyq := (Finset.mem_filter.mp hy1).2
      have hxx : x * x < P := by nlinarith
      have hyy : y * y < P := by nlinarith
      exact eq_of_dvd_geom_five_of_mul_lt hPp (by omega)
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx1).1)
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hy1).1) hxx hyy
        ((hterm x hx1).2 hx2) ((hterm y hy1).2 hy2)
    have hc1 : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p P ≤ 1 := by
      rw [← Finset.sum_filter_ne_zero]
      have := Finset.sum_le_card_nsmul
        ((N.primeFactors.filter (· < q)).filter (fun p => sigmaWeight N p P ≠ 0))
        (fun p => sigmaWeight N p P) 1
        (fun p hp => (hterm p (Finset.mem_filter.mp hp).1).1)
      simp only [smul_eq_mul, mul_one] at this
      omega
    have hv3 : 3 ≤ sigmaWeight N q P := by omega
    have hP3 : P ^ 3 ∣ σ 1 (q ^ a) := (pow_dvd_pow P hv3).trans hPv
    have hSR := rankTwo_sigma_mul_sub_one (k := 4) hPp
    rcases ha1721 with h17 | h21
    · have hFA := pow_lt_succ_pow_totient_of_pow_dvd_sigma hq hPp hqP2 (by omega) (by omega) hP3
      rw [h17, show Nat.totient (17 + 1) = 6 by decide] at hFA
      have hS : q ^ 9 ≤ σ 1 (P ^ 4) :=
        le_trans (Nat.pow_le_pow_right hq.pos hw9) hqwle
      refine rankTwo_seventeen_false (q := q) (P := P) (S := (σ 1 (P ^ 4) : ℕ))
        (by exact_mod_cast hq5) (by exact_mod_cast hP200) (by exact_mod_cast hFA)
        (by exact_mod_cast hS) ?_
      rw [hSR]
      norm_num
    · rw [h21] at hP3
      have hw13 : sigmaWeight N P q ≤ 13 := by
        by_contra h14
        push Not at h14
        exact rankTwo_twentyone_le_thirteen hq hPp hq5 hqP2 hP3
          ((pow_dvd_pow q h14).trans hqw)
      have hw13' : sigmaWeight N P q = 13 := by omega
      have hb : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q = 8 := by omega
      rw [hb] at hbmod
      have hmod : q % 3 = 1 ∧ q % 5 = 1 := by
        constructor <;> by_contra hne <;> split_ifs at hbmod <;> omega
      exact rankTwo_twentyone_thirteen_false hq hPp (by omega) hmod.1 hP200 hqP2 hP3
        (hw13' ▸ hqw)

/-- Palette with one prime above the special prime, without the prime `3`: in the setting of
`special_exponent_eq_one_five_nine_or_thirteen`, under the explicit hypothesis `3 ∤ N`,
`v_q(N) ∈ {1, 9, 13}`. Restricted family result; novelty not verified. -/
theorem special_exponent_eq_one_nine_or_thirteen_of_not_three_dvd {N q P : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hP : P ∈ N.primeFactors) (hqP : q < P)
    (hsecond : ∀ p ∈ N.primeFactors, p ≠ P → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    N.factorization q = 1 ∨ N.factorization q = 9 ∨ N.factorization q = 13 := by
  have h1 := special_exponent_eq_one_five_nine_or_thirteen h hq hodd hP hqP hsecond hexp
  have h4 := not_three_dvd_succ_special_exponent h hq hodd h3
  rcases h1 with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1] at h4
    exact absurd (by norm_num) h4
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

end OddPerfect

#print axioms OddPerfect.sum_sigmaWeight_below_special_le_mod
#print axioms OddPerfect.special_exponent_eq_one_five_nine_or_thirteen
#print axioms OddPerfect.special_exponent_eq_one_nine_or_thirteen_of_not_three_dvd
