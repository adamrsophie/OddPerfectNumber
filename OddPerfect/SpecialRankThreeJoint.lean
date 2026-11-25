import OddPerfect.SpecialRankThree

/-!
# The special exponent at most 85 when exactly two prime factors exceed the special prime

Restricted family result; the family is not excluded, and whether the result is in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, and let exactly two prime factors `L < R`
exceed `q`. Then `a ≤ 85` (`special_exponent_le_85_of_two_above`). This sharpens
`special_exponent_le_121_of_two_above` in the same family.

Notation as in `OddPerfect.SpecialRankThree`: `A = σ(L ^ g)`, `B = σ(R ^ e)`, `c = v_q(A)`,
`w = v_q(B)`, `d = v_R(A)`, `b ≤ 8` the `q` valuation of the rows of the primes below `q`,
`a = b + c + w`, `m = φ(a + 1)`, `2 m ≤ a + 1`. Suppose `a ≥ 89`; then `A < q ^ 36`.

The one new observation: `q` and `R` are distinct primes, so `q ^ c R ^ d` divides `A` and
`q ^ c R ^ d < q ^ 36`.

* A prime below `q` feeds `R`: `w ≤ 15` and `a ≤ 58`.
* `d = 0`: `w ≤ m`, so `a ≤ 87`.
* `e ≤ 2 d`: `q ^ (w + 2 c) ≤ B (q ^ c) ^ 2 < 2 (q ^ c R ^ d) ^ 2 < q ^ 73`, so `a ≤ 80`.
* `e = 4`, `d = 1`: `R < q ^ (36 - c)` gives `w < 4 (36 - c)`, and `3 w ≤ 4 m + 1` as landed;
  these exclude `a ≥ 89`.

Remark: the integer constraints used here are all satisfied by `a = 85`, `b = 8`, `c = 21`,
`w = 56`, `m = 42`, so this argument cannot lower the bound further without a new idea.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem srj_rest {N q L R : ℕ} (hqm : q ∈ N.primeFactors) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q) :
    N.primeFactors.filter (fun p => ¬ p < q) = {q, L, R} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hpq⟩
    by_cases hpL : p = L
    · exact Or.inr (Or.inl hpL)
    · by_cases hpR : p = R
      · exact Or.inr (Or.inr hpR)
      · have := hthird p hp hpL hpR
        exact Or.inl (by omega)
  · rintro (rfl | rfl | rfl)
    · exact ⟨hqm, lt_irrefl _⟩
    · exact ⟨hL, by omega⟩
    · exact ⟨hR, by omega⟩

private theorem srj_ledger {N q L R r : ℕ} (h : OddPerfect N) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, L, R}) (hqL : q ≠ L) (hqR : q ≠ R)
    (hLR : L ≠ R) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p r +
      (sigmaWeight N q r + (sigmaWeight N L r + sigmaWeight N R r)) = N.factorization r := by
  have hs := sigmaWeight_sum_eq h.2 hr hr2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_insert (by simp [hqL, hqR]), Finset.sum_pair hLR] at hs
  exact hs

private theorem srj_sigma_ne_zero {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem srj_sigma_int {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) * ((p ^ k : ℕ) : ℤ) - 1 := by
  rw [rankTwo_sigma_mul_sub_one hp]
  push_cast
  ring

/-- Two primes above the special prime. Let `N` be an odd perfect number with special prime `q`
(`v_q(N)` odd), let every other prime factor have exponent `2` or `4`, and let exactly two
prime factors `L < R` exceed `q` (every prime factor other than `L` and `R` is at most `q`).
Then `v_q(N) ≤ 85`. Restricted family result: the family is not excluded and the exponent
classes below the bound remain; novelty not verified. -/
theorem special_exponent_le_85_of_two_above {N q L R : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 85 := by
  classical
  have hstep := special_exponent_le_eight_or_succ_le_pow_nine h hq hodd hL hR hqL hLR hthird
    hexp
  have hLp := Nat.prime_of_mem_primeFactors hL
  have hRp := Nat.prime_of_mem_primeFactors hR
  have hoddN : ∀ p ∈ N.primeFactors, p % 2 = 1 := fun p hp =>
    Nat.odd_iff.mp (h.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp))
  have hqm : q ∈ N.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by obtain ⟨j, hj⟩ := hodd; omega)
  have hqo := hoddN q hqm
  have hLo := hoddN L hL
  have hq2 : q ≠ 2 := by omega
  have hR2 : R ≠ 2 := by have := hoddN R hR; omega
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hrest := srj_rest hqm hL hR hqL hLR hthird
  have hledq := srj_ledger h hq hq2 hrest (by omega) (by omega) (by omega)
  have hledR := srj_ledger h hRp hR2 hrest (by omega) (by omega) (by omega)
  rw [sigmaWeight_self hq] at hledq
  rw [sigmaWeight_self hRp] at hledR
  have hb8 := sum_sigmaWeight_below_special_le_eight h hq hexp
  set a := N.factorization q with ha
  set g := N.factorization L with hg
  set e := N.factorization R with he
  have hg24 : g = 2 ∨ g = 4 := hexp L hL (by omega)
  have he24 : e = 2 ∨ e = 4 := hexp R hR (by omega)
  by_contra hgoal
  have ha89 : 89 ≤ a := by omega
  have hL9 : L + 1 ≤ q ^ 9 := hstep.resolve_left (by omega)
  set A := σ 1 (L ^ g) with hA
  set B := σ 1 (R ^ e) with hB
  set T := σ 1 (q ^ a) with hT
  have hA0 : A ≠ 0 := srj_sigma_ne_zero hLp
  have hB0 : B ≠ 0 := srj_sigma_ne_zero hRp
  -- `σ(L ^ g) < q ^ 36` and `c ≤ 35`
  have hA36 : A < q ^ 36 := by
    have h1 := sigma_prime_pow_lt_succ_pow hLp (k := g) (by omega)
    have h2 : (L + 1) ^ g ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (L + 1) ^ 4 ≤ q ^ 36 := by
      have := Nat.pow_le_pow_left hL9 4
      rwa [← pow_mul] at this
    omega
  have hc35 : sigmaWeight N L q ≤ 35 := by
    have h1 : q ^ sigmaWeight N L q ≤ A := Nat.le_of_dvd (Nat.pos_of_ne_zero hA0)
      (Nat.ordProj_dvd A q)
    have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt h1 hA36)
    omega
  have hqwB : q ^ sigmaWeight N R q ≤ B :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hB0) (Nat.ordProj_dvd B q)
  have hwlt : ∀ k, B < q ^ k → sigmaWeight N R q < k := fun k hk =>
    (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt hqwB hk)
  have hBsucc : B < (R + 1) ^ 4 := by
    have h1 := sigma_prime_pow_lt_succ_pow hRp (k := e) (by omega)
    have h2 : (R + 1) ^ e ≤ (R + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  -- no prime below `q` feeds `R`
  by_cases hfeed : ∃ p ∈ N.primeFactors, p < q ∧ R ∣ σ 1 (p ^ N.factorization p)
  · obtain ⟨p, hp, hpq, hd⟩ := hfeed
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hk := hexp p hp (by omega)
    have hσ0 := srj_sigma_ne_zero (k := N.factorization p) hpp
    have hRs := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
    have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
    have h2 : (p + 1) ^ N.factorization p ≤ q ^ N.factorization p :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : q ^ N.factorization p ≤ q ^ 4 := Nat.pow_le_pow_right hq.pos (by omega)
    have h4 : (R + 1) ^ 4 ≤ q ^ 16 := by
      have := Nat.pow_le_pow_left (show R + 1 ≤ q ^ 4 by omega) 4
      rwa [← pow_mul] at this
    have := hwlt 16 (by omega)
    omega
  push Not at hfeed
  have hzR : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p R = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    exact Nat.factorization_eq_zero_of_not_dvd (hfeed p hp' hpq)
  have hmax : ∀ p ∈ N.primeFactors, p ≤ R := by
    intro p hp
    by_cases hpL : p = L
    · omega
    · by_cases hpR : p = R
      · omega
      · have := hthird p hp hpL hpR
        omega
  have hRa : ¬ R ∣ a + 1 := largest_not_dvd_succ_factorization h hR hmax hqm
  have hqR : q + 1 < R := by omega
  have htot : 2 * (a + 1).totient ≤ a + 1 := by
    obtain ⟨m, hm⟩ : ∃ m, a + 1 = 2 * m := ⟨(a + 1) / 2, by omega⟩
    rw [hm]
    exact two_mul_totient_two_mul_le m
  have hvR : sigmaWeight N q R + sigmaWeight N L R = e := by omega
  have hTR : R ^ sigmaWeight N q R ∣ T := Nat.ordProj_dvd T R
  have hSR := srj_sigma_int (k := e) hRp
  have hσ2 := rankTwo_sigma_lt_two_mul (k := e) hRp
  rcases Nat.eq_zero_or_pos (sigmaWeight N L R) with hc0 | hc1
  · -- all of `R ^ e` divides `σ(q ^ a)`
    have hRe : R ^ e ∣ T := by rw [← hvR, hc0, add_zero]; exact hTR
    have hF := sub_two_mul_pow_le_of_pow_dvd_sigma hq hRp (by omega) hqR hRa (by omega) hRe
    zify [show 2 ≤ q by omega, show 1 ≤ q by omega] at hF
    have hw := srt_case_one (Q := q) (S := B) (X := ((R ^ e : ℕ) : ℤ)) (F := ((R ^ e : ℕ) : ℤ))
      (w := sigmaWeight N R q) (m := (a + 1).totient) (by exact_mod_cast hq5)
      (by exact_mod_cast hqwB) (by exact_mod_cast hσ2) le_rfl (by push_cast at hF ⊢; exact hF)
    omega
  · -- the joint divisibility `q ^ c * R ^ d ∣ σ(L ^ g)`
    have hJ : q ^ sigmaWeight N L q * R ^ sigmaWeight N L R < q ^ 36 :=
      lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd
          (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hRp).mpr (by omega)))
          (Nat.ordProj_dvd A q) (Nat.ordProj_dvd A R))) hA36
    by_cases hsq : e ≤ 2 * sigmaWeight N L R
    · -- `e = 2`, or `e = 4` and `d ≥ 2`
      have h1 : R ^ e ≤ (R ^ sigmaWeight N L R) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right hRp.pos (by omega)
      have h2 : (q ^ sigmaWeight N L q * R ^ sigmaWeight N L R) ^ 2 < (q ^ 36) ^ 2 :=
        Nat.pow_lt_pow_left hJ (by norm_num)
      have hqc : 0 < (q ^ sigmaWeight N L q) ^ 2 := pow_pos (pow_pos hq.pos _) _
      have h3 : q ^ (sigmaWeight N R q + 2 * sigmaWeight N L q) < q ^ 73 :=
        calc q ^ (sigmaWeight N R q + 2 * sigmaWeight N L q)
            = q ^ sigmaWeight N R q * (q ^ sigmaWeight N L q) ^ 2 := by ring
          _ ≤ B * (q ^ sigmaWeight N L q) ^ 2 := Nat.mul_le_mul_right _ hqwB
          _ < 2 * R ^ e * (q ^ sigmaWeight N L q) ^ 2 := mul_lt_mul_of_pos_right hσ2 hqc
          _ ≤ 2 * (R ^ sigmaWeight N L R) ^ 2 * (q ^ sigmaWeight N L q) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
          _ = 2 * (q ^ sigmaWeight N L q * R ^ sigmaWeight N L R) ^ 2 := by ring
          _ < 2 * (q ^ 36) ^ 2 := mul_lt_mul_of_pos_left h2 (by norm_num)
          _ ≤ q * (q ^ 36) ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = q ^ 73 := by ring
      have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp h3
      omega
    · -- `e = 4` and `d = 1`
      have hd1 : sigmaWeight N L R = 1 := by omega
      have he4 : e = 4 := by omega
      rw [hd1, pow_one] at hJ
      have hsplit : q ^ 36 = q ^ sigmaWeight N L q * q ^ (36 - sigmaWeight N L q) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at hJ
      have hRlt := Nat.lt_of_mul_lt_mul_left hJ
      have h4 : (R + 1) ^ 4 ≤ q ^ ((36 - sigmaWeight N L q) * 4) := by
        have := Nat.pow_le_pow_left (show R + 1 ≤ q ^ (36 - sigmaWeight N L q) by omega) 4
        rwa [← pow_mul] at this
      have hw4 := hwlt _ (lt_of_lt_of_le hBsucc h4)
      have hR3 : R ^ 3 ∣ T := by
        have : sigmaWeight N q R = 3 := by omega
        rw [← this]; exact hTR
      have hF := sub_two_mul_pow_le_of_pow_dvd_sigma hq hRp (by omega) hqR hRa (by omega) hR3
      zify [show 2 ≤ q by omega, show 1 ≤ q by omega] at hF
      have hSR4 : (B : ℤ) * ((R : ℤ) - 1) < (R : ℤ) ^ 5 := by
        rw [hB, hSR, he4]
        push_cast
        nlinarith
      have hw := srt_case_four (Q := q) (R := R) (S := B) (F := ((R ^ 3 : ℕ) : ℤ))
        (w := sigmaWeight N R q) (m := (a + 1).totient) (by exact_mod_cast hq5)
        (by exact_mod_cast (show 5 ≤ R by omega)) hSR4 (by exact_mod_cast hqwB)
        (by push_cast; exact le_rfl) (by push_cast at hF ⊢; exact hF)
      omega

end OddPerfect

#print axioms OddPerfect.special_exponent_le_85_of_two_above
