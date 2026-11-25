import OddPerfect.SpecialRankThreeAux
import OddPerfect.PrimeCapFree
import OddPerfect.SpecialRankSharp

/-!
# The special exponent when exactly two prime factors exceed the special prime

Restricted family result; the family is not excluded, and whether the result is in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, and let exactly two prime factors `L < R`
exceed `q`. Then `a ≤ 113` or `a ∈ {117, 121}`
(`special_exponent_le_113_or_eq_of_two_above`), so `a ≤ 121`
(`special_exponent_le_121_of_two_above`). The exponent classes below the bound remain open in
this family, and the number of prime factors above the special prime is not bounded in general.

Proof outline, with `b ≤ 8` the total `q` valuation of the rows of the primes below `q`,
`c = v_q(σ(L ^ g))`, `w = v_q(σ(R ^ e))`, `g, e ∈ {2, 4}`, so `a = b + c + w`.

* `special_exponent_le_eight_or_succ_le_pow_nine`: `a ≤ 8` or `L + 1 ≤ q ^ 9`. If a prime below
  `q` feeds `L` or `R`, then `L < q ^ 4`. Otherwise `M = L ^ g R ^ e` and `q ^ (a - b)` both
  divide `σ(q ^ a) σ(M)`, and the sharp rational gap `lt_pow_mul_sigma_sub_sharp` gives
  `(q - 2) (L - 1) < 3 q ^ (b + 1)`. Hence `c ≤ 35` and `w ≥ a - 43`.
* Suppose `a ≥ 125`. No prime below `q` feeds `R` (else `w ≤ 15`). The prime `R` is the
  largest prime factor, so `R ∤ a + 1`, and every power of `R` dividing `σ(q ^ a)` divides one
  cyclotomic value `Φ_t(q)`, `t ∣ a + 1`, with `(q - 2) Φ_t(q) ≤ (q - 1) q ^ φ(t)`. Let
  `c' = v_R(σ(L ^ g))`. If `c' = 0` then `w ≤ φ(a + 1) ≤ (a + 1) / 2`. If `c' ≥ 1` and
  `e = 2`, or `c' ≥ 2`, then `R < q ^ 36`, resp. `R < q ^ 18`, and `w ≤ 71`. If `c' = 1` and
  `e = 4` then `R ^ 3 ∣ Φ_t(q)` and `3 w ≤ 4 φ(a + 1) + 1`, which fails for `a ∈ {125, 129}` and
  for `a ≥ 133`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem srt_rest {N q L R : ℕ} (hqm : q ∈ N.primeFactors) (hL : L ∈ N.primeFactors)
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

private theorem srt_ledger {N q L R r : ℕ} (h : OddPerfect N) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, L, R}) (hqL : q ≠ L) (hqR : q ≠ R)
    (hLR : L ≠ R) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p r +
      (sigmaWeight N q r + (sigmaWeight N L r + sigmaWeight N R r)) = N.factorization r := by
  have hs := sigmaWeight_sum_eq h.2 hr hr2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_insert (by simp [hqL, hqR]), Finset.sum_pair hLR] at hs
  exact hs

private theorem srt_succ_pow_le {q P m : ℕ} (hq : q.Prime) (hP : P.Prime) (hqP : q < P)
    (hle : P ≤ q ^ m) : P + 1 ≤ q ^ m := by
  rcases Nat.lt_or_ge P (q ^ m) with h | h
  · omega
  · exfalso
    have heq : P = q ^ m := le_antisymm hle h
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [pow_zero] at heq
      exact hP.one_lt.ne' heq
    · have hd : q ∣ P := heq ▸ dvd_pow_self q hm.ne'
      have := (Nat.prime_dvd_prime_iff_eq hq hP).mp hd
      omega

private theorem srt_sigma_ne_zero {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem srt_sigma_int {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) * ((p ^ k : ℕ) : ℤ) - 1 := by
  rw [rankTwo_sigma_mul_sub_one hp]
  push_cast
  ring

private theorem srt_le_sigma {p k : ℕ} (hp : p.Prime) : p ^ k ≤ σ 1 (p ^ k) := by
  have h := srt_sigma_int (k := k) hp
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : (0 : ℤ) ≤ ((p ^ k : ℕ) : ℤ) := by positivity
  have : ((p ^ k : ℕ) : ℤ) ≤ ((σ 1 (p ^ k) : ℕ) : ℤ) := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this

/-- Step one: in the setting of `special_exponent_le_113_or_eq_of_two_above`, either
`v_q(N) ≤ 8` or `L + 1 ≤ q ^ 9`. Restricted family result; novelty not verified. -/
theorem special_exponent_le_eight_or_succ_le_pow_nine {N q L R : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 8 ∨ L + 1 ≤ q ^ 9 := by
  classical
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
  have hL2 : L ≠ 2 := by omega
  have hR2 : R ≠ 2 := by have := hoddN R hR; omega
  have hq5 : 5 ≤ q := by
    have h4 := (special_mod_four h hq hodd).1
    have := hq.two_le
    omega
  have hL7 : 7 ≤ L := by omega
  have hrest := srt_rest hqm hL hR hqL hLR hthird
  have hledq := srt_ledger h hq hq2 hrest (by omega) (by omega) (by omega)
  have hledL := srt_ledger h hLp hL2 hrest (by omega) (by omega) (by omega)
  have hledR := srt_ledger h hRp hR2 hrest (by omega) (by omega) (by omega)
  rw [sigmaWeight_self hq] at hledq
  rw [sigmaWeight_self hLp] at hledL
  rw [sigmaWeight_self hRp] at hledR
  have hb8 := sum_sigmaWeight_below_special_le_eight h hq hexp
  set a := N.factorization q with ha
  set g := N.factorization L with hg
  set e := N.factorization R with he
  set b := ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q with hb
  have hg24 := hexp L hL (by omega)
  have he24 := hexp R hR (by omega)
  by_cases ha8 : a ≤ 8
  · exact Or.inl ha8
  right
  by_cases hfeed : ∃ p ∈ N.primeFactors, p < q ∧
      (L ∣ σ 1 (p ^ N.factorization p) ∨ R ∣ σ 1 (p ^ N.factorization p))
  · obtain ⟨p, hp, hpq, hd⟩ := hfeed
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hk := hexp p hp (by omega)
    have hσ0 := srt_sigma_ne_zero (k := N.factorization p) hpp
    have hLs : L ≤ σ 1 (p ^ N.factorization p) := by
      rcases hd with hd | hd
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
        omega
    have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
    have h2 : (p + 1) ^ N.factorization p ≤ q ^ N.factorization p :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : q ^ N.factorization p ≤ q ^ 9 := Nat.pow_le_pow_right hq.pos (by omega)
    omega
  push Not at hfeed
  have hzL : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p L = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    exact Nat.factorization_eq_zero_of_not_dvd (hfeed p hp' hpq).1
  have hzR : ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p R = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    obtain ⟨hp', hpq⟩ := Finset.mem_filter.mp hp
    exact Nat.factorization_eq_zero_of_not_dvd (hfeed p hp' hpq).2
  set T := σ 1 (q ^ a) with hT
  set A := σ 1 (L ^ g) with hA
  set B := σ 1 (R ^ e) with hB
  set X := L ^ g with hX
  set Y := R ^ e with hY
  have hT0 : T ≠ 0 := srt_sigma_ne_zero hq
  have hA0 : A ≠ 0 := srt_sigma_ne_zero hLp
  have hB0 : B ≠ 0 := srt_sigma_ne_zero hRp
  have hXY : X.Coprime Y :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hLp hRp).mpr (by omega))
  have hσM : σ 1 (X * Y) = A * B := isMultiplicative_sigma.map_mul_of_coprime hXY
  have hTAB0 : T * (A * B) ≠ 0 := mul_ne_zero hT0 (mul_ne_zero hA0 hB0)
  have hfac : ∀ r, (T * (A * B)).factorization r =
      T.factorization r + (A.factorization r + B.factorization r) := by
    intro r
    rw [Nat.factorization_mul hT0 (mul_ne_zero hA0 hB0), Nat.factorization_mul hA0 hB0]
    rfl
  have hdL : X ∣ T * (A * B) := by
    refine (hLp.pow_dvd_iff_le_factorization hTAB0).mpr ?_
    rw [hfac]
    have e1 : A.factorization L = 0 := sigmaWeight_self hLp
    have e2 : T.factorization L = sigmaWeight N q L := rfl
    have e3 : B.factorization L = sigmaWeight N R L := rfl
    omega
  have hdR : Y ∣ T * (A * B) := by
    refine (hRp.pow_dvd_iff_le_factorization hTAB0).mpr ?_
    rw [hfac]
    have e1 : B.factorization R = 0 := sigmaWeight_self hRp
    have e2 : T.factorization R = sigmaWeight N q R := rfl
    have e3 : A.factorization R = sigmaWeight N L R := rfl
    omega
  have hdq : q ^ (a - b) ∣ A * B := by
    have h1 : q ^ (sigmaWeight N L q) ∣ A := Nat.ordProj_dvd A q
    have h2 : q ^ (sigmaWeight N R q) ∣ B := Nat.ordProj_dvd B q
    rw [show a - b = sigmaWeight N L q + sigmaWeight N R q by omega, pow_add]
    exact mul_dvd_mul h1 h2
  have hqXY : (q ^ (a - b)).Coprime (X * Y) := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hLp).mpr (by omega))
    · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hRp).mpr (by omega))
  have hfull : q ^ (a - b) * (X * Y) ∣ T * σ 1 (X * Y) := by
    rw [hσM]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hqXY (Dvd.dvd.mul_left hdq T)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd hXY hdL hdR)
  have hAi := srt_sigma_int (k := g) hLp
  have hBi := srt_sigma_int (k := e) hRp
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hLp.ne_zero)
  have hY1 : 1 ≤ Y := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hRp.ne_zero)
  have hM2 : σ 1 (X * Y) < 2 * (X * Y) := by
    rw [hσM]
    have := srt_sigma_lt_two_mul (L := L) (R := R) (A := A) (B := B) (X := X) (Y := Y)
      (by exact_mod_cast hL7) (by exact_mod_cast (show 8 ≤ R by omega))
      (by exact_mod_cast hX1) (by exact_mod_cast hY1) hAi hBi
    exact_mod_cast this
  have hgap := lt_pow_mul_sigma_sub_sharp hq hq2 hM2 (by omega) hfull
  have hAX : X ≤ A := srt_le_sigma hLp
  have hBY : Y ≤ B := srt_le_sigma hRp
  have hABXY : X * Y ≤ A * B := Nat.mul_le_mul hAX hBY
  rw [hσM] at hgap
  zify [hABXY, show 2 ≤ q by omega] at hgap
  have hgap2 := srt_gap (L := L) (R := R) (A := A) (B := B) (X := X) (Y := Y)
    (by exact_mod_cast (show 1 < L by omega)) (by exact_mod_cast hLR.le)
    (by exact_mod_cast hX1) (by exact_mod_cast hY1) (by positivity) hAi hBi hgap
  have hLQ : L ≤ q ^ (b + 1) := by
    have h3 : (3 : ℤ) ≤ (q : ℤ) - 2 := by
      have : (5 : ℤ) ≤ q := by exact_mod_cast hq5
      linarith
    have hL1 : (0 : ℤ) ≤ (L : ℤ) - 1 := by
      have : (1 : ℤ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hL1
    have : (L : ℤ) ≤ (q : ℤ) ^ (b + 1) := by linarith
    exact_mod_cast this
  have h5 := srt_succ_pow_le hq hLp hqL hLQ
  have h6 : q ^ (b + 1) ≤ q ^ 9 := Nat.pow_le_pow_right hq.pos (by omega)
  omega

/-- Two primes above the special prime. Let `N` be an odd perfect number with special prime `q`
(`v_q(N)` odd), let every other prime factor have exponent `2` or `4`, and let exactly two
prime factors `L < R` exceed `q` (every prime factor other than `L` and `R` is at most `q`).
Then `v_q(N) ≤ 113` or `v_q(N) ∈ {117, 121}`. Restricted family result: the family is not
excluded and the exponent classes below the bound remain; novelty not verified. -/
theorem special_exponent_le_113_or_eq_of_two_above {N q L R : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 113 ∨ N.factorization q = 117 ∨ N.factorization q = 121 := by
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
  have hrest := srt_rest hqm hL hR hqL hLR hthird
  have hledq := srt_ledger h hq hq2 hrest (by omega) (by omega) (by omega)
  have hledR := srt_ledger h hRp hR2 hrest (by omega) (by omega) (by omega)
  rw [sigmaWeight_self hq] at hledq
  rw [sigmaWeight_self hRp] at hledR
  have hb8 := sum_sigmaWeight_below_special_le_eight h hq hexp
  set a := N.factorization q with ha
  set g := N.factorization L with hg
  set e := N.factorization R with he
  have hg24 : g = 2 ∨ g = 4 := hexp L hL (by omega)
  have he24 : e = 2 ∨ e = 4 := hexp R hR (by omega)
  by_contra hgoal
  have ha125 : 125 ≤ a := by omega
  have hL9 : L + 1 ≤ q ^ 9 := hstep.resolve_left (by omega)
  set A := σ 1 (L ^ g) with hA
  set B := σ 1 (R ^ e) with hB
  set T := σ 1 (q ^ a) with hT
  have hA0 : A ≠ 0 := srt_sigma_ne_zero hLp
  have hB0 : B ≠ 0 := srt_sigma_ne_zero hRp
  have hT0 : T ≠ 0 := srt_sigma_ne_zero hq
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
  -- `w ≤ 71` from `σ(R ^ e) < q ^ 72`
  have hw71 : B < q ^ 72 → False := by
    intro hB72
    have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt hqwB hB72)
    omega
  have hBsucc : B < (R + 1) ^ 4 := by
    have h1 := sigma_prime_pow_lt_succ_pow hRp (k := e) (by omega)
    have h2 : (R + 1) ^ e ≤ (R + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  -- no prime below `q` feeds `R`
  by_cases hfeed : ∃ p ∈ N.primeFactors, p < q ∧ R ∣ σ 1 (p ^ N.factorization p)
  · obtain ⟨p, hp, hpq, hd⟩ := hfeed
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hk := hexp p hp (by omega)
    have hσ0 := srt_sigma_ne_zero (k := N.factorization p) hpp
    have hRs := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
    have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
    have h2 : (p + 1) ^ N.factorization p ≤ q ^ N.factorization p :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : q ^ N.factorization p ≤ q ^ 4 := Nat.pow_le_pow_right hq.pos (by omega)
    have h4 : (R + 1) ^ 4 ≤ q ^ 16 := by
      have := Nat.pow_le_pow_left (show R + 1 ≤ q ^ 4 by omega) 4
      rwa [← pow_mul] at this
    have h5 : q ^ 16 ≤ q ^ 72 := Nat.pow_le_pow_right hq.pos (by omega)
    exact hw71 (by omega)
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
  have hSR := srt_sigma_int (k := e) hRp
  rcases Nat.eq_zero_or_pos (sigmaWeight N L R) with hc0 | hc1
  · -- all of `R ^ e` divides `σ(q ^ a)`
    have hRe : R ^ e ∣ T := by rw [← hvR, hc0, add_zero]; exact hTR
    have hF := sub_two_mul_pow_le_of_pow_dvd_sigma hq hRp (by omega) hqR hRa (by omega) hRe
    have hσ2 := rankTwo_sigma_lt_two_mul (k := e) hRp
    zify [show 2 ≤ q by omega, show 1 ≤ q by omega] at hF
    have hw := srt_case_one (Q := q) (S := B) (X := ((R ^ e : ℕ) : ℤ)) (F := ((R ^ e : ℕ) : ℤ))
      (w := sigmaWeight N R q) (m := (a + 1).totient) (by exact_mod_cast hq5)
      (by exact_mod_cast hqwB) (by exact_mod_cast hσ2) le_rfl (by push_cast at hF ⊢; exact hF)
    omega
  · have hAR : A.factorization R ≠ 0 := by
      have : A.factorization R = sigmaWeight N L R := rfl
      omega
    have hRA : R ≤ A := Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) (Nat.dvd_of_factorization_pos hAR)
    rcases he24 with he2 | he4
    · -- `e = 2`
      have h1 := sigma_prime_pow_lt_succ_pow hRp (k := e) (by omega)
      have h2 : (R + 1) ^ e ≤ q ^ 72 := by
        rw [he2]
        have := Nat.pow_le_pow_left (show R + 1 ≤ q ^ 36 by omega) 2
        rwa [← pow_mul] at this
      exact hw71 (by omega)
    · rcases (show sigmaWeight N L R = 1 ∨ 2 ≤ sigmaWeight N L R by omega) with hc' | hc'
      · -- `e = 4` and one unit of `R` from the row of `L`
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
        have ha132 : a ≤ 132 := by omega
        have hcases : a = 125 ∨ a = 129 := by omega
        rcases hcases with h' | h' <;> rw [h'] at hw
        · rw [show Nat.totient (125 + 1) = 36 by decide] at hw
          omega
        · rw [show Nat.totient (129 + 1) = 48 by decide] at hw
          omega
      · -- at least two units of `R` from the row of `L`
        have hR2A : R ^ 2 ≤ A := Nat.le_of_dvd (Nat.pos_of_ne_zero hA0)
          ((pow_dvd_pow R hc').trans (Nat.ordProj_dvd A R))
        have hR18 : R ≤ q ^ 18 := by
          by_contra hlt
          push Not at hlt
          have h0 : q ^ 36 ≤ R ^ 2 := by
            have := Nat.pow_le_pow_left hlt.le 2
            rwa [← pow_mul] at this
          omega
        have h1 := srt_succ_pow_le hq hRp (by omega) hR18
        have h2 : (R + 1) ^ 4 ≤ q ^ 72 := by
          have := Nat.pow_le_pow_left h1 4
          rwa [← pow_mul] at this
        exact hw71 (by omega)

/-- Two primes above the special prime: in the setting of
`special_exponent_le_113_or_eq_of_two_above`, `v_q(N) ≤ 121`. Restricted family result: the
family is not excluded; novelty not verified. -/
theorem special_exponent_le_121_of_two_above {N q L R : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) :
    N.factorization q ≤ 121 := by
  rcases special_exponent_le_113_or_eq_of_two_above h hq hodd hL hR hqL hLR hthird hexp with
    h1 | h1 | h1 <;> omega

end OddPerfect

#print axioms OddPerfect.special_exponent_le_eight_or_succ_le_pow_nine
#print axioms OddPerfect.special_exponent_le_113_or_eq_of_two_above
#print axioms OddPerfect.special_exponent_le_121_of_two_above
