import OddPerfect.SpecialRankThree
import OddPerfect.MixedPaletteEdges

/-!
# The special exponent at most 73 when two primes exceed the special prime and `3 ∤ N`

Restricted family result; the family is not excluded, and whether the result is in the
literature was not verified.

Let `N` be an odd perfect number with special prime `q` and special exponent `a = v_q(N)`, let
every other prime factor have exponent `2` or `4`, let exactly two prime factors `L < R`
exceed `q`, and let `3 ∤ N`. Then `a ≤ 73`
(`special_exponent_le_73_of_two_above_of_not_three_dvd`). This sharpens
`special_exponent_le_85_of_two_above` under the extra hypothesis `3 ∤ N`. By the Main Theorem
of Fletcher, Nielsen and Ochem (Math. Comp. 81 (2012)) the least prime factor exceeds `10 ^ 8`
when every prime factor other than the special prime has exponent `2` or `4`, so `3 ∤ N` holds
in this family; that theorem is not formalized here, and `3 ∤ N` is an explicit hypothesis.

The proof is the landed proof of `special_exponent_le_85_of_two_above` with the lower weight
`b ≤ 8` replaced by `b ≤ 7` (`mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd`).
Notation: `c = v_q(σ(L ^ g))`, `w = v_q(σ(R ^ e))`, `d = v_R(σ(L ^ g))`, `m = φ(a + 1)`,
`a = b + c + w`, `2 m ≤ a + 1`.

* Step one with `b ≤ 7` gives `L + 1 ≤ q ^ 8`, so `σ(L ^ g) < q ^ 32` and `c ≤ 31`.
* Suppose `a ≥ 77`. A prime below `q` feeds `R`: `w ≤ 15` and `a ≤ 53`.
* `d = 0`: `w ≤ m`, so `a ≤ 38 + m ≤ 77`, and `a = 77` fails since `φ(78) = 24`.
* `e ≤ 2 d`: `q ^ (w + 2 c) < q ^ 65`, so `a ≤ 71`.
* `e = 4`, `d = 1`: `w < 4 (32 - c)` and `3 w ≤ 4 m + 1` give `a ≤ 79`, and `a = 77` fails.

The bound is `73`, not lower: `a = 73`, `b = 7`, `c = 31`, `w = 35`, `m = φ(74) = 36` satisfies
every constraint of the branch `d = 0`, so this argument does not exclude it.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

private theorem srf_rest {N q L R : ℕ} (hqm : q ∈ N.primeFactors) (hL : L ∈ N.primeFactors)
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

private theorem srf_ledger {N q L R r : ℕ} (h : OddPerfect N) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrest : N.primeFactors.filter (fun p => ¬ p < q) = {q, L, R}) (hqL : q ≠ L) (hqR : q ≠ R)
    (hLR : L ≠ R) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p r +
      (sigmaWeight N q r + (sigmaWeight N L r + sigmaWeight N R r)) = N.factorization r := by
  have hs := sigmaWeight_sum_eq h.2 hr hr2
  rw [← Finset.sum_filter_add_sum_filter_not N.primeFactors (· < q), hrest,
    Finset.sum_insert (by simp [hqL, hqR]), Finset.sum_pair hLR] at hs
  exact hs

private theorem srf_succ_pow_le {q P m : ℕ} (hq : q.Prime) (hP : P.Prime) (hqP : q < P)
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

private theorem srf_sigma_ne_zero {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) ≠ 0 :=
  (sigma_pos 1 _ (pow_ne_zero _ hp.ne_zero)).ne'

private theorem srf_sigma_int {p k : ℕ} (hp : p.Prime) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) * ((p ^ k : ℕ) : ℤ) - 1 := by
  rw [rankTwo_sigma_mul_sub_one hp]
  push_cast
  ring

private theorem srf_le_sigma {p k : ℕ} (hp : p.Prime) : p ^ k ≤ σ 1 (p ^ k) := by
  have h := srf_sigma_int (k := k) hp
  have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : (0 : ℤ) ≤ ((p ^ k : ℕ) : ℤ) := by positivity
  have : ((p ^ k : ℕ) : ℤ) ≤ ((σ 1 (p ^ k) : ℕ) : ℤ) := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this

/-- The lower weight without the prime `3`: at most `7`. -/
private theorem srf_lower_le_seven {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q ≤ 7 := by
  have := mixed_sum_sigmaWeight_below_special_le_mod_of_not_three_dvd h hq hexp h3
  split_ifs at this <;> omega

/-- Step one without the prime `3`: if `v_q(N) ≥ 8` then `L + 1 ≤ q ^ 8`. The landed step one
with the lower weight `7` in place of `8`. -/
private theorem srf_succ_le_pow_eight {N q L R : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hL : L ∈ N.primeFactors)
    (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N)
    (ha8 : 8 ≤ N.factorization q) :
    L + 1 ≤ q ^ 8 := by
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
  have hrest := srf_rest hqm hL hR hqL hLR hthird
  have hledq := srf_ledger h hq hq2 hrest (by omega) (by omega) (by omega)
  have hledL := srf_ledger h hLp hL2 hrest (by omega) (by omega) (by omega)
  have hledR := srf_ledger h hRp hR2 hrest (by omega) (by omega) (by omega)
  rw [sigmaWeight_self hq] at hledq
  rw [sigmaWeight_self hLp] at hledL
  rw [sigmaWeight_self hRp] at hledR
  have hb7 := srf_lower_le_seven h hq hexp h3
  set a := N.factorization q with ha
  set g := N.factorization L with hg
  set e := N.factorization R with he
  set b := ∑ p ∈ N.primeFactors.filter (· < q), sigmaWeight N p q with hb
  have hg24 := hexp L hL (by omega)
  have he24 := hexp R hR (by omega)
  by_cases hfeed : ∃ p ∈ N.primeFactors, p < q ∧
      (L ∣ σ 1 (p ^ N.factorization p) ∨ R ∣ σ 1 (p ^ N.factorization p))
  · obtain ⟨p, hp, hpq, hd⟩ := hfeed
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hk := hexp p hp (by omega)
    have hσ0 := srf_sigma_ne_zero (k := N.factorization p) hpp
    have hLs : L ≤ σ 1 (p ^ N.factorization p) := by
      rcases hd with hd | hd
      · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
      · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hσ0) hd
        omega
    have h1 := sigma_prime_pow_lt_succ_pow hpp (k := N.factorization p) (by omega)
    have h2 : (p + 1) ^ N.factorization p ≤ q ^ N.factorization p :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : q ^ N.factorization p ≤ q ^ 8 := Nat.pow_le_pow_right hq.pos (by omega)
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
  have hT0 : T ≠ 0 := srf_sigma_ne_zero hq
  have hA0 : A ≠ 0 := srf_sigma_ne_zero hLp
  have hB0 : B ≠ 0 := srf_sigma_ne_zero hRp
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
  have hAi := srf_sigma_int (k := g) hLp
  have hBi := srf_sigma_int (k := e) hRp
  have hX1 : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hLp.ne_zero)
  have hY1 : 1 ≤ Y := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hRp.ne_zero)
  have hM2 : σ 1 (X * Y) < 2 * (X * Y) := by
    rw [hσM]
    have := srt_sigma_lt_two_mul (L := L) (R := R) (A := A) (B := B) (X := X) (Y := Y)
      (by exact_mod_cast hL7) (by exact_mod_cast (show 8 ≤ R by omega))
      (by exact_mod_cast hX1) (by exact_mod_cast hY1) hAi hBi
    exact_mod_cast this
  have hgap := lt_pow_mul_sigma_sub_sharp hq hq2 hM2 (by omega) hfull
  have hAX : X ≤ A := srf_le_sigma hLp
  have hBY : Y ≤ B := srf_le_sigma hRp
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
  have h5 := srf_succ_pow_le hq hLp hqL hLQ
  have h6 : q ^ (b + 1) ≤ q ^ 8 := Nat.pow_le_pow_right hq.pos (by omega)
  omega

/-- Two primes above the special prime, without the prime `3`. Let `N` be an odd perfect
number with special prime `q` (`v_q(N)` odd), let every other prime factor have exponent `2`
or `4`, let exactly two prime factors `L < R` exceed `q` (every prime factor other than `L` and
`R` is at most `q`), and let `3 ∤ N`. Then `v_q(N) ≤ 73`. Restricted family result: the family
is not excluded and the exponent classes below the bound remain. The Main Theorem of Fletcher,
Nielsen and Ochem (Math. Comp. 81 (2012)) gives `3 ∤ N` in this family; that theorem is not
formalized here and `3 ∤ N` is an explicit hypothesis. Novelty not verified. -/
theorem special_exponent_le_73_of_two_above_of_not_three_dvd {N q L R : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (hL : L ∈ N.primeFactors) (hR : R ∈ N.primeFactors) (hqL : q < L) (hLR : L < R)
    (hthird : ∀ p ∈ N.primeFactors, p ≠ L → p ≠ R → p ≤ q)
    (hexp : ∀ p ∈ N.primeFactors, p ≠ q →
      N.factorization p = 2 ∨ N.factorization p = 4) (h3 : ¬ 3 ∣ N) :
    N.factorization q ≤ 73 := by
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
  have hR2 : R ≠ 2 := by have := hoddN R hR; omega
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  have hrest := srf_rest hqm hL hR hqL hLR hthird
  have hledq := srf_ledger h hq hq2 hrest (by omega) (by omega) (by omega)
  have hledR := srf_ledger h hRp hR2 hrest (by omega) (by omega) (by omega)
  rw [sigmaWeight_self hq] at hledq
  rw [sigmaWeight_self hRp] at hledR
  have hb7 := srf_lower_le_seven h hq hexp h3
  set a := N.factorization q with ha
  set g := N.factorization L with hg
  set e := N.factorization R with he
  have hg24 : g = 2 ∨ g = 4 := hexp L hL (by omega)
  have he24 : e = 2 ∨ e = 4 := hexp R hR (by omega)
  by_contra hgoal
  have ha77 : 77 ≤ a := by omega
  have hL8 := srf_succ_le_pow_eight h hq hodd hL hR hqL hLR hthird hexp h3
    (le_trans (by norm_num) ha77)
  set A := σ 1 (L ^ g) with hA
  set B := σ 1 (R ^ e) with hB
  set T := σ 1 (q ^ a) with hT
  have hA0 : A ≠ 0 := srf_sigma_ne_zero hLp
  have hB0 : B ≠ 0 := srf_sigma_ne_zero hRp
  -- `σ(L ^ g) < q ^ 32` and `c ≤ 31`
  have hA32 : A < q ^ 32 := by
    have h1 := sigma_prime_pow_lt_succ_pow hLp (k := g) (by omega)
    have h2 : (L + 1) ^ g ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (L + 1) ^ 4 ≤ q ^ 32 := by
      have := Nat.pow_le_pow_left hL8 4
      rwa [← pow_mul] at this
    omega
  have hc31 : sigmaWeight N L q ≤ 31 := by
    have h1 : q ^ sigmaWeight N L q ≤ A := Nat.le_of_dvd (Nat.pos_of_ne_zero hA0)
      (Nat.ordProj_dvd A q)
    have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp (lt_of_le_of_lt h1 hA32)
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
    have hσ0 := srf_sigma_ne_zero (k := N.factorization p) hpp
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
  have hSR := srf_sigma_int (k := e) hRp
  have hσ2 := rankTwo_sigma_lt_two_mul (k := e) hRp
  rcases Nat.eq_zero_or_pos (sigmaWeight N L R) with hc0 | hc1
  · -- all of `R ^ e` divides `σ(q ^ a)`
    have hRe : R ^ e ∣ T := by rw [← hvR, hc0, add_zero]; exact hTR
    have hF := sub_two_mul_pow_le_of_pow_dvd_sigma hq hRp (by omega) hqR hRa (by omega) hRe
    zify [show 2 ≤ q by omega, show 1 ≤ q by omega] at hF
    have hw := srt_case_one (Q := q) (S := B) (X := ((R ^ e : ℕ) : ℤ)) (F := ((R ^ e : ℕ) : ℤ))
      (w := sigmaWeight N R q) (m := (a + 1).totient) (by exact_mod_cast hq5)
      (by exact_mod_cast hqwB) (by exact_mod_cast hσ2) le_rfl (by push_cast at hF ⊢; exact hF)
    have hm : (a + 1).totient = 24 := by
      rw [show a + 1 = 78 by omega]
      decide
    omega
  · -- the joint divisibility `q ^ c * R ^ d ∣ σ(L ^ g)`
    have hJ : q ^ sigmaWeight N L q * R ^ sigmaWeight N L R < q ^ 32 :=
      lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0)
        (Nat.Coprime.mul_dvd_of_dvd_of_dvd
          (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq hRp).mpr (by omega)))
          (Nat.ordProj_dvd A q) (Nat.ordProj_dvd A R))) hA32
    by_cases hsq : e ≤ 2 * sigmaWeight N L R
    · -- `e = 2`, or `e = 4` and `d ≥ 2`
      have h1 : R ^ e ≤ (R ^ sigmaWeight N L R) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right hRp.pos (by omega)
      have h2 : (q ^ sigmaWeight N L q * R ^ sigmaWeight N L R) ^ 2 < (q ^ 32) ^ 2 :=
        Nat.pow_lt_pow_left hJ (by norm_num)
      have hqc : 0 < (q ^ sigmaWeight N L q) ^ 2 := pow_pos (pow_pos hq.pos _) _
      have h3 : q ^ (sigmaWeight N R q + 2 * sigmaWeight N L q) < q ^ 65 :=
        calc q ^ (sigmaWeight N R q + 2 * sigmaWeight N L q)
            = q ^ sigmaWeight N R q * (q ^ sigmaWeight N L q) ^ 2 := by ring
          _ ≤ B * (q ^ sigmaWeight N L q) ^ 2 := Nat.mul_le_mul_right _ hqwB
          _ < 2 * R ^ e * (q ^ sigmaWeight N L q) ^ 2 := mul_lt_mul_of_pos_right hσ2 hqc
          _ ≤ 2 * (R ^ sigmaWeight N L R) ^ 2 * (q ^ sigmaWeight N L q) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
          _ = 2 * (q ^ sigmaWeight N L q * R ^ sigmaWeight N L R) ^ 2 := by ring
          _ < 2 * (q ^ 32) ^ 2 := mul_lt_mul_of_pos_left h2 (by norm_num)
          _ ≤ q * (q ^ 32) ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = q ^ 65 := by ring
      have := (Nat.pow_lt_pow_iff_right hq.one_lt).mp h3
      omega
    · -- `e = 4` and `d = 1`
      have hd1 : sigmaWeight N L R = 1 := by omega
      have he4 : e = 4 := by omega
      rw [hd1, pow_one] at hJ
      have hsplit : q ^ 32 = q ^ sigmaWeight N L q * q ^ (32 - sigmaWeight N L q) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit] at hJ
      have hRlt := Nat.lt_of_mul_lt_mul_left hJ
      have h4 : (R + 1) ^ 4 ≤ q ^ ((32 - sigmaWeight N L q) * 4) := by
        have := Nat.pow_le_pow_left (show R + 1 ≤ q ^ (32 - sigmaWeight N L q) by omega) 4
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
      have hm : (a + 1).totient = 24 := by
        rw [show a + 1 = 78 by omega]
        decide
      omega

end OddPerfect

#print axioms OddPerfect.special_exponent_le_73_of_two_above_of_not_three_dvd
