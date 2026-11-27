import OddPerfect.ImpureRowCount
import OddPerfect.Abundancy
import OddPerfect.Valuation

/-!
# The number of impure rows grows with the common index prime (reduction to a gap statement)

Let `N` be an odd perfect number with special prime `q` and let `l` be an odd prime dividing
every ordinary index `e_p + 1` (`p ≠ q` a prime factor of `N`). The row of `p` is
`σ(p ^ e_p)`; it is impure when it is not a prime power.

`exists_index_bound_of_impure_rows_of` shows: if the gap statement `AbundancyGapStatement K`
holds for every `K`, then for every `K` there is a bound `L` such that for every such `N` with
`l ≥ L`, at least `K` ordinary rows are impure. The bound is not explicit: the proof gives no
value for it, since the gap statement provides none.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. The common index family is not excluded, and the odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The gap statement for sets of at most `K` odd prime powers. -/
def AbundancyGapStatement (K : ℕ) : Prop :=
    ∃ B : ℕ, ∃ ε : ℚ, 0 < ε ∧
      ∀ (C : Finset ℕ) (e : ℕ → ℕ) (q : ℕ), C.card ≤ K → (∀ c ∈ C, c.Prime ∧ c ≠ 2) →
        (∀ c ∈ C, c ≠ q → B ≤ e c) → (q ∈ C → q % 4 = 1 ∧ e q % 4 = 1) →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) ≤ 2 →
        ∏ c ∈ C, ((σ 1 (c ^ e c) : ℚ) / ((c : ℚ) ^ e c)) < 2 - ε

/-- The product factor of `impureRowT` is at most `((L + 1)/L) ^ K`. -/
private theorem gapB_prod_le {L K : ℕ} (hL : 0 < L) :
    ∏ j ∈ Finset.range K, (((2 * (j + 1) * L + 1 : ℕ) : ℚ) / ((2 * (j + 1) * L : ℕ) : ℚ)) ≤
      (((L + 1 : ℕ) : ℚ) / ((L : ℕ) : ℚ)) ^ K := by
  calc _ ≤ ∏ _j ∈ Finset.range K, (((L + 1 : ℕ) : ℚ) / ((L : ℕ) : ℚ)) :=
        Finset.prod_le_prod₀ (fun j _ => by positivity)
          (fun j _ => impureRow_succ_div_le hL (by nlinarith))
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

/-- `((L + 1)/L) ^ K ≤ L/(L - K)` for `K < L`. -/
private theorem gapB_pow_le {L K : ℕ} (hKL : K < L) :
    (((L + 1 : ℕ) : ℚ) / ((L : ℕ) : ℚ)) ^ K ≤ (L : ℚ) / ((L : ℚ) - K) := by
  have hL : (0 : ℚ) < L := by exact_mod_cast (show 0 < L by omega)
  have hKL' : (K : ℚ) < L := by exact_mod_cast hKL
  have hK0 : (0 : ℚ) ≤ K := Nat.cast_nonneg K
  have hL1 : (L : ℚ) + 1 ≠ 0 := by positivity
  have hinv0 : 0 ≤ 1 / ((L : ℚ) + 1) := by positivity
  have hinv1 : 1 / ((L : ℚ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hb := one_add_mul_le_pow (a := -(1 / ((L : ℚ) + 1))) (by linarith) K
  have e1 : (1 : ℚ) + -(1 / ((L : ℚ) + 1)) = (L : ℚ) / ((L : ℚ) + 1) := by
    field_simp
    ring
  have e3 : (1 : ℚ) + (K : ℚ) * -(1 / ((L : ℚ) + 1)) = ((L : ℚ) + 1 - K) / ((L : ℚ) + 1) := by
    field_simp
    ring
  rw [e1, e3] at hb
  have hpos : (0 : ℚ) < ((L : ℚ) + 1 - K) / ((L : ℚ) + 1) := div_pos (by linarith) (by positivity)
  have e2 : (((L + 1 : ℕ) : ℚ) / ((L : ℕ) : ℚ)) ^ K = 1 / ((L : ℚ) / ((L : ℚ) + 1)) ^ K := by
    rw [one_div, ← inv_pow, inv_div, Nat.cast_add, Nat.cast_one]
  rw [e2]
  calc 1 / ((L : ℚ) / ((L : ℚ) + 1)) ^ K ≤ 1 / (((L : ℚ) + 1 - K) / ((L : ℚ) + 1)) :=
        one_div_le_one_div_of_le hpos hb
    _ = ((L : ℚ) + 1) / ((L : ℚ) + 1 - K) := one_div_div _ _
    _ ≤ (L : ℚ) / ((L : ℚ) - K) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith

/-- **Explicit bound on `impureRowT`.** For `K < L` and `L + 1 ≤ l`,
`impureRowT l K ≤ (L/(L - K)) ^ 2`. -/
private theorem gapB_T_le {l L K : ℕ} (hKL : K < L) (hLl : L + 1 ≤ l) :
    impureRowT l K ≤ ((L : ℚ) / ((L : ℚ) - K)) ^ 2 := by
  have hL0 : 0 < L := by omega
  have hKL' : (K : ℚ) < L := by exact_mod_cast hKL
  have hK0 : (0 : ℚ) ≤ K := Nat.cast_nonneg K
  have h3 : (L : ℚ) ≤ 3 ^ L - 1 := by
    have h := impureRow_succ_le_three_pow L
    have h' : ((L + 1 : ℕ) : ℚ) ≤ ((3 ^ L : ℕ) : ℚ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hT := impureRowT_le (l := l) (L := L) (m := L) (K := K) hL0 (by omega) (by omega)
    (by linarith : (K : ℚ) < 3 ^ L - 1)
  have hA := (gapB_prod_le (K := K) hL0).trans (gapB_pow_le hKL)
  have hB : ((3 : ℚ) ^ L - 1) / ((3 : ℚ) ^ L - 1 - (K : ℚ)) ≤ (L : ℚ) / ((L : ℚ) - K) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h3 hK0]
  have hB0 : 0 ≤ ((3 : ℚ) ^ L - 1) / ((3 : ℚ) ^ L - 1 - (K : ℚ)) :=
    div_nonneg (by linarith) (by linarith)
  have hu0 : 0 ≤ (L : ℚ) / ((L : ℚ) - K) := div_nonneg (by linarith) (by linarith)
  rw [sq]
  exact hT.trans (mul_le_mul hA hB hB0 hu0)

/-- **Many impure rows for a large common index prime, assuming the gap statement.** Let `N`
be an odd perfect number with special prime `q` and `l` a prime dividing `e_p + 1` for every
prime factor `p ≠ q` of `N`. If the gap statement holds for every `K`, then for every `K` there
is a bound `L` such that, for `l ≥ L`, every set `M` outside of which all ordinary rows
`σ(p ^ e_p)` are prime powers has at least `K` elements; so at least `K` ordinary rows are
impure.

Restricted result (one odd prime divides every ordinary index). The bound `L` is not explicit:
the proof gives no value for it. No published source was checked; novelty not verified. The
common index family is not excluded, and the odd perfect number conjecture remains open. -/
theorem exists_index_bound_of_impure_rows_of (hgap : ∀ K, AbundancyGapStatement K) (K : ℕ) :
    ∃ L : ℕ, ∀ {N q l : ℕ}, OddPerfect N → q.Prime → Odd (N.factorization q) → l.Prime →
      L ≤ l → (∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) →
      ∀ M : Finset ℕ, (∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
        ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) → K ≤ M.card := by
  obtain ⟨B, ε₀, hε₀, hgapK⟩ := hgap K
  obtain ⟨ε, hε, hε1, hεε⟩ : ∃ ε : ℚ, 0 < ε ∧ ε ≤ 1 ∧ ε ≤ ε₀ :=
    ⟨min ε₀ 1, lt_min hε₀ one_pos, min_le_right _ _, min_le_left _ _⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (6 * (K : ℚ) / ε)
  refine ⟨K + n + B + 4, ?_⟩
  intro N q l h hq hodd hl hLl hidx M hM
  by_contra hlt
  push Not at hlt
  have hl2 : l ≠ 2 := by omega
  have hKl : K + 1 < 3 ^ (l - 1) := by
    have := impureRow_succ_le_three_pow (l - 1)
    omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)⟩
  have hqX : q ∈ insert q M := Finset.mem_insert_self q M
  have hne : ∀ p, p ∉ insert q M → p ≠ q := fun p hpX e => hpX (e ▸ hqX)
  have hXK : (insert q M).card ≤ K := (Finset.card_insert_le q M).trans (by omega)
  obtain ⟨C, hCS, hCK, -, hT⟩ := packingStatement_holds hl hl2 hS hXK hKl
    (impureRow_cover h hq hodd hl hl2 hqX (fun p hp hpX => hidx p hp (hne p hpX))
      (fun p hp hpX => hM p hp (hne p hpX) fun hpM => hpX (Finset.mem_insert_of_mem hpM)))
  change _ ≤ impureRowT l K at hT
  -- The abundancy factors.
  set f : ℕ → ℚ := fun p => (σ 1 (p ^ N.factorization p) : ℚ) / ((p : ℚ) ^ N.factorization p)
    with hf
  have hfab : ∀ p, f p = abundancy (p ^ N.factorization p) := fun p => by
    simp only [hf, abundancy, Nat.cast_pow]
  have hprod : ∏ p ∈ N.primeFactors, f p = 2 := by
    rw [Finset.prod_congr rfl fun p _ => hfab p, ← abundancy_eq_prod_primeFactors h.ne_zero]
    exact (perfect_iff_abundancy_eq_two h.pos).mp h.perfect
  have hf1 : ∀ p ∈ N.primeFactors, 1 ≤ f p := fun p hp => by
    have := abundancy_prime_pow_mono (hS p hp).1 (Nat.zero_le (N.factorization p))
    have h1 : abundancy 1 = 1 := by simp [abundancy]
    rw [pow_zero, h1] at this
    rw [hfab]
    exact this
  have hfH : ∀ p ∈ N.primeFactors, f p ≤ (p : ℚ) / ((p : ℚ) - 1) := fun p hp => by
    rw [hfab]
    exact (abundancy_prime_pow_lt (hS p hp).1 _).le
  have hsplit := Finset.prod_sdiff (f := f) hCS
  rw [hprod] at hsplit
  have hR1 : 1 ≤ ∏ p ∈ N.primeFactors \ C, f p :=
    Finset.one_le_prod₀ fun p hp => hf1 p (Finset.mem_sdiff.mp hp).1
  have hRH : ∏ p ∈ N.primeFactors \ C, f p ≤
      ∏ p ∈ N.primeFactors \ C, ((p : ℚ) / ((p : ℚ) - 1)) :=
    Finset.prod_le_prod₀ (fun p hp => zero_le_one.trans (hf1 p (Finset.mem_sdiff.mp hp).1))
      fun p hp => hfH p (Finset.mem_sdiff.mp hp).1
  have hV0 : 0 ≤ ∏ p ∈ C, f p :=
    Finset.prod_nonneg fun p hp => zero_le_one.trans (hf1 p (hCS hp))
  have hV2 : ∏ p ∈ C, f p ≤ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hR1) hV0]
  -- The gap statement.
  have hgapV : ∏ p ∈ C, f p < 2 - ε₀ := by
    refine hgapK C (fun p => N.factorization p) q hCK (fun c hc => hS c (hCS hc))
      (fun c hc hcq => ?_) (fun _ => mod_four_special h hq hodd) hV2
    show B ≤ N.factorization c
    have hd := Nat.le_of_dvd (Nat.succ_pos _) (hidx c (hCS hc) hcq)
    omega
  -- The explicit bound on `impureRowT`.
  have hTu := gapB_T_le (l := l) (L := K + n + B + 3) (K := K) (by omega) (by omega)
  have hD : ((K + n + B + 3 : ℕ) : ℚ) - K = (n : ℚ) + B + 3 := by push_cast; ring
  rw [hD] at hTu
  have hn' : 6 * (K : ℚ) < ε * ((n : ℚ) + B + 3) := by
    rw [div_lt_iff₀ hε] at hn
    have : (0 : ℚ) ≤ B := Nat.cast_nonneg B
    nlinarith [mul_nonneg hε.le (by positivity : (0 : ℚ) ≤ (B : ℚ) + 3)]
  have hc : (((K + n + B + 3 : ℕ) : ℚ) / ((n : ℚ) + B + 3)) ^ 2 ≤ 1 + ε / 2 := by
    have hD0 : (0 : ℚ) < (n : ℚ) + B + 3 := by positivity
    have hK0 : (0 : ℚ) ≤ K := Nat.cast_nonneg K
    have hKD : (K : ℚ) ≤ (n : ℚ) + B + 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hε1) hD0.le]
    rw [div_pow, div_le_iff₀ (by positivity)]
    have e : ((K + n + B + 3 : ℕ) : ℚ) = (n : ℚ) + B + 3 + K := by push_cast; ring
    rw [e]
    nlinarith [mul_pos (sub_pos.mpr hn') hD0, mul_nonneg hK0 (sub_nonneg.mpr hKD)]
  have hTc := hT.trans (hTu.trans hc)
  -- The contradiction.
  have h2 : (2 : ℚ) ≤ (1 + ε / 2) * ∏ p ∈ C, f p := by
    exact hsplit.symm.le.trans (mul_le_mul_of_nonneg_right (hRH.trans hTc) hV0)
  nlinarith [mul_pos (by positivity : (0 : ℚ) < 1 + ε / 2) (sub_pos.mpr hgapV), mul_pos hε hε₀]

end OddPerfect

#print axioms OddPerfect.exists_index_bound_of_impure_rows_of
