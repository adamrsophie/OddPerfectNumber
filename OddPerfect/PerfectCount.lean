import OddPerfect.PerfectRigidity
import OddPerfect.UpperBound
import OddPerfect.SmallestPrime
import OddPerfect.UnconditionalSupport

/-!
# Reconstruction of a perfect number from its least prime and a sequence of exponents

Let `N` be a perfect number, even or odd. Start with the full power of its least prime factor.
This is a unitary divisor `B` of `N`; as long as `B < N`, the divisor sum of `B` forces a prime
into the cofactor `N / B` (`OddPerfect.PerfectRigidity`). The least such prime depends on `B`
alone, so multiplying by its full power in `N` gives the next unitary divisor. The chain gains
one prime factor at each step and stops at `N`. Hence `N` is determined by its least prime
factor and the exponents used along the chain.

For odd perfect numbers with at most `k` distinct prime factors, the least prime is below
`(2 k + 6) / 3` and every exponent is below `3 * 4 ^ (k - 1)` (from `N < 2 ^ 4 ^ k`). This
gives the count of Pollack (Amer. Math. Monthly 118, 2011): at most `4 ^ (k ^ 2)` odd perfect
numbers have at most `k` distinct prime factors. With `ω(N) ≤ 5 T + 7` it bounds the number
with total excess at most `T`.
-/

namespace OddPerfect

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The least prime that divides `σ(B)` to a higher power than `2 B`, or `0` if there is none.
Such a prime divides `σ(B)`, so the search below `σ(B) + 1` is complete. -/
noncomputable def forcedPrime (B : ℕ) : ℕ :=
  if h : ∃ r, r < σ 1 B + 1 ∧ r.Prime ∧ (2 * B).factorization r < (σ 1 B).factorization r then
    Nat.find h
  else 0

/-- The reconstruction chain of `N`: start with the full power of the least prime factor; at
each step multiply by the full power of the forced prime of the current value; stop at `N`. -/
noncomputable def chain (N : ℕ) : ℕ → ℕ
  | 0 => N.minFac ^ N.factorization N.minFac
  | i + 1 =>
    if chain N i = N then N
    else chain N i * forcedPrime (chain N i) ^ N.factorization (forcedPrime (chain N i))

/-- The exponent used at step `i` (`0` once the chain has reached `N`). -/
noncomputable def chainExp (N : ℕ) : ℕ → ℕ
  | 0 => N.factorization N.minFac
  | i + 1 => if chain N i = N then 0 else N.factorization (forcedPrime (chain N i))

/-- For a unitary divisor `B` of a perfect number `N` with `1 < B < N`, `forcedPrime B` is a
prime that divides the cofactor `N / B`. -/
theorem forcedPrime_spec {N B : ℕ} (hN : σ 1 N = 2 * N) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (h1 : 1 < B) (hlt : B < N) :
    (forcedPrime B).Prime ∧ forcedPrime B ∣ N / B := by
  obtain ⟨r, hr, hf⟩ := exists_forced_prime hN hB hcop h1 hlt
  have hB0 : B ≠ 0 := by omega
  have hs0 : σ 1 B ≠ 0 := (sigma_pos 1 B hB0).ne'
  have hrle : r < σ 1 B + 1 := by
    have hrd : r ∣ σ 1 B := (hr.dvd_iff_one_le_factorization hs0).mpr (by omega)
    exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hrd)
  have hex : ∃ r, r < σ 1 B + 1 ∧ r.Prime ∧
      (2 * B).factorization r < (σ 1 B).factorization r := ⟨r, hrle, hr, hf⟩
  have hspec := Nat.find_spec hex
  have hdef : forcedPrime B = Nat.find hex := by
    unfold forcedPrime
    rw [dif_pos hex]
  rw [hdef]
  exact ⟨hspec.2.1, forced_prime_dvd_cofactor hN hB hcop h1 hspec.2.1 hspec.2.2⟩

/-- Multiplying a unitary divisor `B` of `N` by the full power of a prime `p` of the cofactor
gives a unitary divisor; moreover `p` does not divide `B`. -/
theorem unitary_mul_ordProj {N B p : ℕ} (hN0 : N ≠ 0) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (hp : p.Prime) (hpC : p ∣ N / B) :
    B * p ^ N.factorization p ∣ N ∧
      Nat.Coprime (B * p ^ N.factorization p) (N / (B * p ^ N.factorization p)) ∧
      ¬ p ∣ B := by
  have hB0 : B ≠ 0 := by
    rintro rfl
    exact hN0 (zero_dvd_iff.mp hB)
  have hBC : B * (N / B) = N := Nat.mul_div_cancel' hB
  have hC0 : N / B ≠ 0 := by
    intro h
    rw [h, Nat.mul_zero] at hBC
    exact hN0 hBC.symm
  have hpB : ¬ p ∣ B := fun h => Nat.not_coprime_of_dvd_of_dvd hp.one_lt h hpC hcop
  have hfac : N.factorization p = (N / B).factorization p := by
    conv_lhs => rw [← hBC]
    rw [Nat.factorization_mul hB0 hC0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpB, Nat.zero_add]
  rw [hfac]
  have hCD : p ^ (N / B).factorization p * ((N / B) / p ^ (N / B).factorization p) = N / B :=
    Nat.ordProj_mul_ordCompl_eq_self (N / B) p
  have hND : B * p ^ (N / B).factorization p * ((N / B) / p ^ (N / B).factorization p) = N := by
    rw [Nat.mul_assoc, hCD, hBC]
  have hpos : 0 < B * p ^ (N / B).factorization p :=
    Nat.pos_of_ne_zero (Nat.mul_ne_zero hB0 (pow_ne_zero _ hp.ne_zero))
  have hdiv : N / (B * p ^ (N / B).factorization p) =
      (N / B) / p ^ (N / B).factorization p :=
    Nat.div_eq_of_eq_mul_left hpos (by rw [Nat.mul_comm]; exact hND.symm)
  refine ⟨⟨_, hND.symm⟩, ?_, hpB⟩
  rw [hdiv]
  apply Nat.Coprime.mul_left
  · exact Nat.Coprime.coprime_dvd_right (Nat.ordCompl_dvd (N / B) p) hcop
  · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hC0)

/-- A unitary divisor of `N` that contains every prime factor of `N` is `N`. -/
private theorem eq_of_unitary_of_primeFactors_subset {N B : ℕ} (hN0 : N ≠ 0) (hB : B ∣ N)
    (hcop : Nat.Coprime B (N / B)) (hsub : N.primeFactors ⊆ B.primeFactors) : B = N := by
  by_contra hne
  have hBC : B * (N / B) = N := Nat.mul_div_cancel' hB
  have hC1 : N / B ≠ 1 := by
    intro h
    rw [h, Nat.mul_one] at hBC
    exact hne hBC
  obtain ⟨q, hq, hqC⟩ := Nat.exists_prime_and_dvd hC1
  have hqN : q ∣ N := hqC.trans (Nat.div_dvd_of_dvd hB)
  have hqB : q ∣ B :=
    Nat.dvd_of_mem_primeFactors (hsub (Nat.mem_primeFactors.mpr ⟨hq, hqN, hN0⟩))
  exact Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqB hqC hcop

/-- Step `0` of the chain. -/
theorem chain_zero (N : ℕ) : chain N 0 = N.minFac ^ N.factorization N.minFac := rfl

/-- The exponent of step `0`. -/
theorem chainExp_zero (N : ℕ) : chainExp N 0 = N.factorization N.minFac := rfl

/-- Once the chain reaches `N` it stays there. -/
theorem chain_succ_of_eq {N i : ℕ} (h : chain N i = N) : chain N (i + 1) = N := by
  simp only [chain, h, ↓reduceIte]

/-- A real step of the chain. -/
theorem chain_succ_of_ne {N i : ℕ} (h : chain N i ≠ N) :
    chain N (i + 1) = chain N i * forcedPrime (chain N i) ^ chainExp N (i + 1) := by
  simp only [chain, chainExp, h, ↓reduceIte]

/-- A step after the chain has stopped has exponent `0`. -/
theorem chainExp_succ_of_eq {N i : ℕ} (h : chain N i = N) : chainExp N (i + 1) = 0 := by
  simp only [chainExp, h, ↓reduceIte]

/-- The exponent of a real step. -/
theorem chainExp_succ_of_ne {N i : ℕ} (h : chain N i ≠ N) :
    chainExp N (i + 1) = N.factorization (forcedPrime (chain N i)) := by
  simp only [chainExp, h, ↓reduceIte]

/-- Chain invariant. Every `chain N i` is a unitary divisor of `N` greater than `1`; if it is
not yet `N`, it has exactly `i + 1` distinct prime factors. -/
theorem chain_unitary {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) (i : ℕ) :
    chain N i ∣ N ∧ Nat.Coprime (chain N i) (N / chain N i) ∧ 1 < chain N i ∧
      (chain N i = N ∨ (chain N i).primeFactors.card = i + 1) := by
  have hN0 : N ≠ 0 := by omega
  induction i with
  | zero =>
    have hm := Nat.minFac_prime (show N ≠ 1 by omega)
    have he : N.factorization N.minFac ≠ 0 :=
      (hm.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)).ne'
    rw [chain_zero]
    refine ⟨Nat.ordProj_dvd N N.minFac, ?_, Nat.one_lt_pow he hm.one_lt, ?_⟩
    · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hm hN0)
    · right
      rw [Nat.primeFactors_prime_pow he hm, Finset.card_singleton]
  | succ i ih =>
    obtain ⟨hB, hcop, h1B, hcase⟩ := ih
    by_cases hstop : chain N i = N
    · rw [chain_succ_of_eq hstop, Nat.div_self (by omega)]
      exact ⟨dvd_rfl, Nat.coprime_one_right N, h1, Or.inl rfl⟩
    · have hcard : (chain N i).primeFactors.card = i + 1 := hcase.resolve_left hstop
      have hlt : chain N i < N := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hB) hstop
      obtain ⟨hp, hpC⟩ := forcedPrime_spec hN hB hcop h1B hlt
      obtain ⟨hdvd, hcop', hpB⟩ := unitary_mul_ordProj hN0 hB hcop hp hpC
      have he : N.factorization (forcedPrime (chain N i)) ≠ 0 :=
        (hp.factorization_pos_of_dvd hN0 (hpC.trans (Nat.div_dvd_of_dvd hB))).ne'
      rw [chain_succ_of_ne hstop, chainExp_succ_of_ne hstop]
      refine ⟨hdvd, hcop', ?_, ?_⟩
      · exact lt_of_lt_of_le h1B (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
          (pow_ne_zero _ hp.ne_zero)))
      · by_cases hfin : chain N i * forcedPrime (chain N i) ^
            N.factorization (forcedPrime (chain N i)) = N
        · exact Or.inl hfin
        · right
          have hco : Nat.Coprime (chain N i)
              (forcedPrime (chain N i) ^ N.factorization (forcedPrime (chain N i))) :=
            Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
              hpB))
          rw [Nat.Coprime.primeFactors_mul hco, Nat.primeFactors_prime_pow he hp,
            Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr
              (fun hmem => hpB (Nat.dvd_of_mem_primeFactors hmem))),
            Finset.card_singleton, hcard]

/-- The chain has reached `N` at every step `i` with `ω(N) ≤ i + 1`. -/
theorem chain_eq_self {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) {i : ℕ}
    (hi : N.primeFactors.card ≤ i + 1) : chain N i = N := by
  have hN0 : N ≠ 0 := by omega
  obtain ⟨hB, hcop, -, hcase⟩ := chain_unitary hN h1 i
  rcases hcase with h | h
  · exact h
  · apply eq_of_unitary_of_primeFactors_subset hN0 hB hcop
    have heq := Finset.eq_of_subset_of_card_le (Nat.primeFactors_mono hB hN0) (by omega)
    rw [heq]

/-- A real step of the chain has a positive exponent. -/
theorem chainExp_succ_pos {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) {i : ℕ}
    (h : chain N i ≠ N) : 0 < chainExp N (i + 1) := by
  have hN0 : N ≠ 0 := by omega
  obtain ⟨hB, hcop, h1B, -⟩ := chain_unitary hN h1 i
  have hlt : chain N i < N := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hB) h
  obtain ⟨hp, hpC⟩ := forcedPrime_spec hN hB hcop h1B hlt
  rw [chainExp_succ_of_ne h]
  exact hp.factorization_pos_of_dvd hN0 (hpC.trans (Nat.div_dvd_of_dvd hB))

/-- The exponent at step `i` is positive exactly when step `i` is a real step. -/
theorem chainExp_pos_iff {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) (i : ℕ) :
    0 < chainExp N i ↔ i = 0 ∨ chain N (i - 1) ≠ N := by
  have hN0 : N ≠ 0 := by omega
  rcases i with _ | i
  · simp only [true_or, iff_true, chainExp_zero]
    exact (Nat.minFac_prime (show N ≠ 1 by omega)).factorization_pos_of_dvd hN0
      (Nat.minFac_dvd N)
  · simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, false_or]
    by_cases h : chain N i = N
    · simp only [chainExp_succ_of_eq h, lt_irrefl, h, ne_eq, not_true_eq_false]
    · simp only [chainExp_succ_pos hN h1 h, h, ne_eq, not_false_eq_true]

/-- Each exponent of the chain is `0` or the full exponent in `N` of a prime `p ∣ N` with
`N.minFac ≤ p`; in particular `p ^ chainExp N i ∣ N`. -/
theorem chainExp_cases {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) (i : ℕ) :
    chainExp N i = 0 ∨ ∃ p, p.Prime ∧ p ∣ N ∧ N.minFac ≤ p ∧ chainExp N i = N.factorization p := by
  rcases i with _ | i
  · right
    have hm := Nat.minFac_prime (show N ≠ 1 by omega)
    exact ⟨N.minFac, hm, Nat.minFac_dvd N, le_rfl, chainExp_zero N⟩
  · by_cases h : chain N i = N
    · exact Or.inl (chainExp_succ_of_eq h)
    · right
      obtain ⟨hB, hcop, h1B, -⟩ := chain_unitary hN h1 i
      have hlt : chain N i < N := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hB) h
      obtain ⟨hp, hpC⟩ := forcedPrime_spec hN hB hcop h1B hlt
      have hpN := hpC.trans (Nat.div_dvd_of_dvd hB)
      exact ⟨_, hp, hpN, Nat.minFac_le_of_dvd hp.two_le hpN, chainExp_succ_of_ne h⟩

/-- Every exponent of the chain from step `ω(N)` on is `0`. -/
theorem chainExp_eq_zero {N : ℕ} (hN : σ 1 N = 2 * N) (h1 : 1 < N) {i : ℕ}
    (hi : N.primeFactors.card ≤ i) : chainExp N i = 0 := by
  have hpos : 0 < N.primeFactors.card :=
    Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h1)
  rcases i with _ | i
  · omega
  · exact chainExp_succ_of_eq (chain_eq_self hN h1 hi)

/-- Two perfect numbers greater than 1 with the same least prime factor and the same sequence of
chain exponents are equal. -/
theorem eq_of_minFac_eq_of_chainExp_eq {N N' : ℕ} (hN : σ 1 N = 2 * N) (hN' : σ 1 N' = 2 * N')
    (h1 : 1 < N) (h1' : 1 < N') (hm : N.minFac = N'.minFac)
    (he : ∀ i, chainExp N i = chainExp N' i) : N = N' := by
  have hc : ∀ i, chain N i = chain N' i := by
    intro i
    induction i with
    | zero =>
      have h0 : N.factorization N.minFac = N'.factorization N'.minFac := he 0
      rw [chain_zero, chain_zero, h0, hm]
    | succ i ih =>
      by_cases hs : chain N i = N <;> by_cases hs' : chain N' i = N'
      · rw [chain_succ_of_eq hs, chain_succ_of_eq hs']
        exact hs.symm.trans (ih.trans hs')
      · have h0 := he (i + 1)
        rw [chainExp_succ_of_eq hs] at h0
        have := chainExp_succ_pos hN' h1' hs'
        omega
      · have h0 := he (i + 1)
        rw [chainExp_succ_of_eq hs'] at h0
        have := chainExp_succ_pos hN h1 hs
        omega
      · rw [chain_succ_of_ne hs, chain_succ_of_ne hs', ih, he (i + 1)]
  rw [← chain_eq_self hN h1 (i := N.primeFactors.card + N'.primeFactors.card) (by omega),
    hc, chain_eq_self hN' h1' (by omega)]

/-- `(2 k - 1) 3 ^ k ≤ 3 * 4 ^ k`. -/
private theorem two_mul_sub_one_mul_three_pow_le (k : ℕ) : (2 * k - 1) * 3 ^ k ≤ 3 * 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> norm_num
    · obtain ⟨a, ha⟩ : ∃ a, a = 2 * k - 1 := ⟨_, rfl⟩
      have h2 : 2 * (k + 1) - 1 = a + 2 := by omega
      have h3 : (a + 2) * 3 ≤ 4 * a := by omega
      rw [← ha] at ih
      rw [h2, pow_succ, pow_succ]
      calc (a + 2) * (3 ^ k * 3) = ((a + 2) * 3) * 3 ^ k := by ring
        _ ≤ (4 * a) * 3 ^ k := Nat.mul_le_mul_right _ h3
        _ = 4 * (a * 3 ^ k) := by ring
        _ ≤ 4 * (3 * 4 ^ k) := Nat.mul_le_mul_left _ ih
        _ = 3 * (4 ^ k * 4) := by ring

/-- If `3 ^ e < 2 ^ 4 ^ k` with `1 ≤ k`, then `e < 3 * 4 ^ (k - 1)`. -/
private theorem lt_of_three_pow_lt {e k : ℕ} (hk : 1 ≤ k) (h : 3 ^ e < 2 ^ 4 ^ k) :
    e < 3 * 4 ^ (k - 1) := by
  by_contra hge
  have hge : 3 * 4 ^ (k - 1) ≤ e := by omega
  have h4 : 4 ^ k = 4 * 4 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hgt : 2 ^ 4 ^ k < 3 ^ e :=
    calc 2 ^ 4 ^ k = 16 ^ 4 ^ (k - 1) := by rw [h4, pow_mul]; norm_num
      _ < 27 ^ 4 ^ (k - 1) := Nat.pow_lt_pow_left (by norm_num) (by positivity)
      _ = 3 ^ (3 * 4 ^ (k - 1)) := by rw [pow_mul]; norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) hge
  omega

/-- `((2 k - 1) / 3) (3 * 4 ^ (k - 1)) ^ k ≤ 4 ^ (k ^ 2)`. -/
private theorem count_arith (k : ℕ) :
    (2 * k - 1) / 3 * (3 * 4 ^ (k - 1)) ^ k ≤ 4 ^ (k ^ 2) := by
  have hP : (2 * k - 1) / 3 * 3 ^ k ≤ 4 ^ k := by
    have h1 : 3 * ((2 * k - 1) / 3) ≤ 2 * k - 1 := by omega
    have h3 : 3 * ((2 * k - 1) / 3) * 3 ^ k ≤ (2 * k - 1) * 3 ^ k := Nat.mul_le_mul_right _ h1
    have h4 : 3 * ((2 * k - 1) / 3 * 3 ^ k) ≤ 3 * 4 ^ k := by
      rw [← Nat.mul_assoc]
      exact h3.trans (two_mul_sub_one_mul_three_pow_le k)
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  calc (2 * k - 1) / 3 * (3 * 4 ^ (k - 1)) ^ k
        = ((2 * k - 1) / 3 * 3 ^ k) * 4 ^ ((k - 1) * k) := by
          rw [mul_pow, ← pow_mul, Nat.mul_assoc]
    _ ≤ 4 ^ k * 4 ^ ((k - 1) * k) := Nat.mul_le_mul_right _ hP
    _ = 4 ^ (k ^ 2) := by
      rw [← pow_add]
      congr 1
      rcases k with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]
        ring

/-- Dickson (1913): only finitely many odd perfect numbers have at most `k` distinct prime
factors. -/
theorem finite_oddPerfect_card_primeFactors_le (k : ℕ) :
    {N : ℕ | OddPerfect N ∧ N.primeFactors.card ≤ k}.Finite :=
  (Set.finite_Iio (2 ^ 4 ^ k)).subset fun N hN =>
    (lt_two_pow_four_pow hN.1).trans_le
      (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) hN.2))

/-- Pollack (2011): at most `4 ^ (k ^ 2)` odd perfect numbers have at most `k` distinct prime
factors.
The set is finite (`finite_oddPerfect_card_primeFactors_le`), so `ncard` is its true size. -/
theorem ncard_oddPerfect_card_primeFactors_le (k : ℕ) :
    {N : ℕ | OddPerfect N ∧ N.primeFactors.card ≤ k}.ncard ≤ 4 ^ (k ^ 2) := by
  let f : ℕ → ℕ × (Fin k → ℕ) := fun N => (N.minFac - 3, fun i => chainExp N i)
  let t : Finset (ℕ × (Fin k → ℕ)) :=
    Finset.range ((2 * k - 1) / 3) ×ˢ Fintype.piFinset fun _ => Finset.range (3 * 4 ^ (k - 1))
  have hone : ∀ {N : ℕ}, OddPerfect N → 1 < N := by
    intro N h
    have := three_le_minFac h
    have h0 := h.ne_zero
    rcases Nat.lt_or_ge 1 N with h' | h'
    · exact h'
    · interval_cases N
      · exact absurd rfl h0
      · simp at this
  have hmaps : ∀ N ∈ {N : ℕ | OddPerfect N ∧ N.primeFactors.card ≤ k}, f N ∈ (t : Set _) := by
    rintro N ⟨h, hk⟩
    have h3 := three_le_card_primeFactors h
    have hm3 := three_le_minFac h
    have hml := three_mul_minFac_lt h
    have h1 := hone h
    have hlt : N < 2 ^ 4 ^ k := (lt_two_pow_four_pow h).trans_le
      (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) hk))
    rw [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset]
    refine ⟨Finset.mem_range.mpr (show N.minFac - 3 < (2 * k - 1) / 3 by omega),
      fun i => Finset.mem_range.mpr ?_⟩
    rcases chainExp_cases h.sigma_eq h1 i with h0 | ⟨p, -, hpN, hpm, he⟩
    · show chainExp N i < 3 * 4 ^ (k - 1)
      rw [h0]
      positivity
    · show chainExp N i < 3 * 4 ^ (k - 1)
      apply lt_of_three_pow_lt (by omega)
      rw [he]
      calc 3 ^ N.factorization p ≤ p ^ N.factorization p :=
            Nat.pow_le_pow_left (hm3.trans hpm) _
        _ ≤ N := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd N p)
        _ < 2 ^ 4 ^ k := hlt
  have hinj : Set.InjOn f {N : ℕ | OddPerfect N ∧ N.primeFactors.card ≤ k} := by
    rintro N ⟨h, hk⟩ N' ⟨h', hk'⟩ hf
    simp only [f, Prod.mk.injEq] at hf
    obtain ⟨hm, he⟩ := hf
    have hm3 := three_le_minFac h
    have hm3' := three_le_minFac h'
    apply eq_of_minFac_eq_of_chainExp_eq h.sigma_eq h'.sigma_eq (hone h) (hone h') (by omega)
    intro i
    by_cases hi : i < k
    · exact congrFun he ⟨i, hi⟩
    · rw [chainExp_eq_zero h.sigma_eq (hone h) (by omega),
        chainExp_eq_zero h'.sigma_eq (hone h') (by omega)]
  calc {N : ℕ | OddPerfect N ∧ N.primeFactors.card ≤ k}.ncard
        ≤ (t : Set (ℕ × (Fin k → ℕ))).ncard :=
          Set.ncard_le_ncard_of_injOn f hmaps hinj (Finset.finite_toSet t)
    _ = (2 * k - 1) / 3 * (3 * 4 ^ (k - 1)) ^ k := by
          rw [Set.ncard_coe_finset]
          simp [t, Finset.card_product]
    _ ≤ 4 ^ (k ^ 2) := count_arith k

/-- At most `4 ^ ((5 * T + 7) ^ 2)` odd perfect numbers have total excess at most `T`.
The set is finite (`finite_of_excess_le`), so `ncard` is its true size. -/
theorem ncard_oddPerfect_excess_le (T : ℕ) :
    {N : ℕ | ∃ q, OddPerfect N ∧ q.Prime ∧ Odd (N.factorization q) ∧
      ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) ≤ T}.ncard ≤
      4 ^ ((5 * T + 7) ^ 2) := by
  refine le_trans (Set.ncard_le_ncard ?_ ?_) (ncard_oddPerfect_card_primeFactors_le (5 * T + 7))
  · rintro N ⟨q, h, hq, hodd, hT⟩
    exact ⟨h, (card_primeFactors_le_five_excess_add_seven h hq hodd).trans (by omega)⟩
  · exact (Set.finite_Iio (2 ^ 4 ^ (5 * T + 7))).subset fun N hN =>
      (lt_two_pow_four_pow hN.1).trans_le
        (Nat.pow_le_pow_right two_pos (Nat.pow_le_pow_right (by norm_num) hN.2))

end OddPerfect

#print axioms OddPerfect.forcedPrime_spec
#print axioms OddPerfect.unitary_mul_ordProj
#print axioms OddPerfect.chain_zero
#print axioms OddPerfect.chainExp_zero
#print axioms OddPerfect.chain_succ_of_eq
#print axioms OddPerfect.chain_succ_of_ne
#print axioms OddPerfect.chainExp_succ_of_eq
#print axioms OddPerfect.chainExp_succ_of_ne
#print axioms OddPerfect.chain_unitary
#print axioms OddPerfect.chain_eq_self
#print axioms OddPerfect.chainExp_succ_pos
#print axioms OddPerfect.chainExp_pos_iff
#print axioms OddPerfect.chainExp_cases
#print axioms OddPerfect.chainExp_eq_zero
#print axioms OddPerfect.eq_of_minFac_eq_of_chainExp_eq
#print axioms OddPerfect.finite_oddPerfect_card_primeFactors_le
#print axioms OddPerfect.ncard_oddPerfect_card_primeFactors_le
#print axioms OddPerfect.ncard_oddPerfect_excess_le
