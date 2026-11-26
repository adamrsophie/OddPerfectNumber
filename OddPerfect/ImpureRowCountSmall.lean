import OddPerfect.ImpureRowTreeD01
import OddPerfect.ImpureRowTreeD02
import OddPerfect.ImpureRowTreeD03
import OddPerfect.ImpureRowTreeD04
import OddPerfect.ImpureRowTreeD05
import OddPerfect.ImpureRowTreeD06
import OddPerfect.ImpureRowTreeD07
import OddPerfect.ImpureRowTreeD08
import OddPerfect.ImpureRowTreeD09
import OddPerfect.ImpureRowTreeD10
import OddPerfect.ImpureRowCount

/-!
# Four impure rows for every prime length from 5 to 521

Let `N` be an odd perfect number with special prime `q` and let `l` be a prime with
`5 ≤ l ≤ 521` dividing every ordinary index `e_p + 1` (`p ≠ q` a prime factor of `N`). Then
any finite set `M` containing every ordinary prime whose row `σ(p ^ e_p)` is not a prime power
has at least four elements (`four_le_card_of_pure_outside_small`). For `l ≥ 523` the same
count is `four_le_card_of_pure_outside`.

Argument. Suppose `M.card ≤ 3`.
* Seed (`impureRowTree_seed`): `3 ∣ N`, or `5 ∣ N` with `5 ≠ q`. Otherwise the packing bound
  `impureRow_core_of` with `X = insert q M` and `K = 4` gives at most four centers, all primes
  at least `7`, and `2 < H(7) H(11) H(13) H(17) T(5, 4) < 2`, where `H(x) = x / (x - 1)`.
* For each length a certificate tree, checked by kernel reduction in the data modules
  `ImpureRowTreeD01` to `ImpureRowTreeD10` with the checker of `ImpureRowTreeCheck`, exhibits
  four distinct ordinary primes with an impure row starting from the seed.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. Nothing is said when no odd prime divides every ordinary index.
The odd perfect number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open ImpTree

/-- One step of a bound for a product of `p / (p - 1)` over distinct primes: the least element
is at least `a`, the others are primes above it, hence at least `b`. -/
theorem impureRowTree_prod_H_step {C : Finset ℕ} {a b k : ℕ} {B : ℚ} (ha : 2 ≤ a)
    (hB : 1 ≤ B) (hC : ∀ x ∈ C, x.Prime ∧ a ≤ x) (hcard : C.card ≤ k + 1)
    (hab : ∀ x, x.Prime → a < x → b ≤ x)
    (hrest : ∀ D : Finset ℕ, D.card ≤ k → (∀ x ∈ D, x.Prime ∧ b ≤ x) →
      ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤ B) :
    ∏ x ∈ C, ((x : ℚ) / ((x : ℚ) - 1)) ≤ (a : ℚ) / ((a : ℚ) - 1) * B := by
  have hHa := impureRow_one_le_H ha
  rcases C.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.prod_empty]
    nlinarith
  · have hm : C.min' hne ∈ C := C.min'_mem hne
    rw [← Finset.mul_prod_erase C _ hm]
    have h1 := impureRow_H_anti ha (hC _ hm).2
    have h2 : ∏ x ∈ C.erase (C.min' hne), ((x : ℚ) / ((x : ℚ) - 1)) ≤ B := by
      refine hrest _ (by rw [Finset.card_erase_of_mem hm]; omega) fun x hx => ?_
      obtain ⟨hxm, hxC⟩ := Finset.mem_erase.mp hx
      have hle : C.min' hne ≤ x := C.min'_le x hxC
      have := (hC _ hm).2
      exact ⟨(hC x hxC).1, hab x (hC x hxC).1 (by omega)⟩
    exact mul_le_mul h1 h2 (impureRow_prod_H_nonneg fun x hx =>
      (hC x (Finset.mem_of_mem_erase hx)).1.two_le) (by linarith)

/-- The product of `p / (p - 1)` over at most four distinct primes, each at least `7`, is at
most `H(7) H(11) H(13) H(17)`. -/
theorem impureRowTree_prod_H_seven {C : Finset ℕ} (hC : ∀ x ∈ C, x.Prime ∧ 7 ≤ x)
    (hcard : C.card ≤ 4) :
    ∏ x ∈ C, ((x : ℚ) / ((x : ℚ) - 1)) ≤
      ((7 : ℕ) : ℚ) / (((7 : ℕ) : ℚ) - 1) * (((11 : ℕ) : ℚ) / (((11 : ℕ) : ℚ) - 1) *
        (((13 : ℕ) : ℚ) / (((13 : ℕ) : ℚ) - 1) *
          (((17 : ℕ) : ℚ) / (((17 : ℕ) : ℚ) - 1) * 1))) := by
  have g1 : ∀ x, x.Prime → 7 < x → 11 ≤ x := by
    intro x hx h
    by_contra hc
    rcases (by omega : x = 8 ∨ x = 9 ∨ x = 10) with rfl | rfl | rfl <;> norm_num at hx
  have g2 : ∀ x, x.Prime → 11 < x → 13 ≤ x := by
    intro x hx h
    by_contra hc
    rcases (by omega : x = 12) with rfl
    norm_num at hx
  have g3 : ∀ x, x.Prime → 13 < x → 17 ≤ x := by
    intro x hx h
    by_contra hc
    rcases (by omega : x = 14 ∨ x = 15 ∨ x = 16) with rfl | rfl | rfl <;> norm_num at hx
  have g4 : ∀ x, x.Prime → 17 < x → 19 ≤ x := by
    intro x hx h
    by_contra hc
    rcases (by omega : x = 18) with rfl
    norm_num at hx
  have L0 : ∀ D : Finset ℕ, D.card ≤ 0 → (∀ x ∈ D, x.Prime ∧ 19 ≤ x) →
      ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤ 1 := fun D hD _ => by
    rw [Finset.card_eq_zero.mp (show D.card = 0 by omega)]
    simp
  have L1 : ∀ D : Finset ℕ, D.card ≤ 1 → (∀ x ∈ D, x.Prime ∧ 17 ≤ x) →
      ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤ ((17 : ℕ) : ℚ) / (((17 : ℕ) : ℚ) - 1) * 1 :=
    fun D hD hDp => impureRowTree_prod_H_step (k := 0) (by norm_num) le_rfl hDp hD g4 L0
  have L2 : ∀ D : Finset ℕ, D.card ≤ 2 → (∀ x ∈ D, x.Prime ∧ 13 ≤ x) →
      ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤ ((13 : ℕ) : ℚ) / (((13 : ℕ) : ℚ) - 1) *
        (((17 : ℕ) : ℚ) / (((17 : ℕ) : ℚ) - 1) * 1) :=
    fun D hD hDp => impureRowTree_prod_H_step (k := 1) (by norm_num) (by norm_num) hDp hD g3 L1
  have L3 : ∀ D : Finset ℕ, D.card ≤ 3 → (∀ x ∈ D, x.Prime ∧ 11 ≤ x) →
      ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤ ((11 : ℕ) : ℚ) / (((11 : ℕ) : ℚ) - 1) *
        (((13 : ℕ) : ℚ) / (((13 : ℕ) : ℚ) - 1) *
          (((17 : ℕ) : ℚ) / (((17 : ℕ) : ℚ) - 1) * 1)) :=
    fun D hD hDp => impureRowTree_prod_H_step (k := 2) (by norm_num) (by norm_num) hDp hD g2 L2
  exact impureRowTree_prod_H_step (k := 3) (by norm_num) (by norm_num) hC hcard g1 L3

/-- **Seed.** Under the hypotheses of `four_le_card_of_pure_outside_small` and `M.card ≤ 3`:
`3 ∣ N`, or `5 ∣ N` and `5` is not the special prime. -/
theorem impureRowTree_seed {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl5 : 5 ≤ l)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) (hM3 : M.card ≤ 3) :
    3 ∣ N ∨ (5 ∣ N ∧ 5 ≠ q) := by
  by_cases h3 : 3 ∣ N
  · exact Or.inl h3
  right
  have h5q : 5 ≠ q := by
    rintro rfl
    exact h3 (dvd_of_dvd_special_succ h hq hodd Nat.prime_three (by norm_num) (by norm_num))
  refine ⟨?_, h5q⟩
  by_contra h5
  have hl2 : l ≠ 2 := by omega
  have hX : (insert q M).card ≤ 4 := (Finset.card_insert_le _ _).trans (by omega)
  have hK : 4 + 1 < 3 ^ (l - 1) :=
    calc 4 + 1 < 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (l - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨C, hCS, hCK, -, hprod⟩ := impureRow_core_of packingStatement_holds h hq hodd hl hl2
    (X := insert q M) (Finset.mem_insert_self q M)
    (fun p hp hpX => hidx p hp fun e => hpX (Finset.mem_insert.mpr (Or.inl e)))
    (fun p hp hpX => hM p hp (fun e => hpX (Finset.mem_insert.mpr (Or.inl e)))
      fun hpM => hpX (Finset.mem_insert_of_mem hpM))
    hX hK
  have h2 := two_lt_prod_primeFactors_div h
  have hCp : ∀ x ∈ C, x.Prime ∧ 7 ≤ x := by
    intro x hx
    have hxN := hCS hx
    have hxp := Nat.prime_of_mem_primeFactors hxN
    have hxd := Nat.dvd_of_mem_primeFactors hxN
    refine ⟨hxp, ?_⟩
    have hx2 : x ≠ 2 := fun e => h.not_two_dvd (by subst e; exact hxd)
    have hx3 : x ≠ 3 := fun e => h3 (by subst e; exact hxd)
    have hx5 : x ≠ 5 := fun e => h5 (by subst e; exact hxd)
    have hx4 : x ≠ 4 := by rintro rfl; norm_num at hxp
    have hx6 : x ≠ 6 := by rintro rfl; norm_num at hxp
    have := hxp.two_le
    omega
  have hC := impureRowTree_prod_H_seven hCp hCK
  have hT := impureRowT_le (l := l) (L := 5) (m := 4) (K := 4) (by norm_num) hl5 (by omega)
    (by norm_num)
  have hT0 := impureRowT_nonneg hK
  have key := mul_le_mul hC hT hT0 (by norm_num)
  have hnum : ((7 : ℕ) : ℚ) / (((7 : ℕ) : ℚ) - 1) * (((11 : ℕ) : ℚ) / (((11 : ℕ) : ℚ) - 1) *
        (((13 : ℕ) : ℚ) / (((13 : ℕ) : ℚ) - 1) *
          (((17 : ℕ) : ℚ) / (((17 : ℕ) : ℚ) - 1) * 1))) *
      ((∏ j ∈ Finset.range 4,
          (((2 * (j + 1) * 5 + 1 : ℕ) : ℚ) / ((2 * (j + 1) * 5 : ℕ) : ℚ))) *
        (((3 : ℚ) ^ 4 - 1) / ((3 : ℚ) ^ 4 - 1 - ((4 : ℕ) : ℚ)))) < 2 := by
    norm_num [Finset.prod_range_succ]
  linarith

/-- Every prime from `5` to `521` is a length of one of the ten tables. -/
theorem impureRowTree_lengths :
    (List.range 522).all (fun n => !(decide (5 ≤ n) && Pratt.trialPrime n) ||
      (ImpureRowTreeD01.ls.contains n ||
        ImpureRowTreeD02.ls.contains n ||
        ImpureRowTreeD03.ls.contains n ||
        ImpureRowTreeD04.ls.contains n ||
        ImpureRowTreeD05.ls.contains n ||
        ImpureRowTreeD06.ls.contains n ||
        ImpureRowTreeD07.ls.contains n ||
        ImpureRowTreeD08.ls.contains n ||
        ImpureRowTreeD09.ls.contains n ||
        ImpureRowTreeD10.ls.contains n)) = true := by
  decide +kernel

theorem impureRowTree_mem_lengths {l : ℕ} (hl : l.Prime) (hl5 : 5 ≤ l) (hl521 : l ≤ 521) :
    l ∈ ImpureRowTreeD01.ls ∨
      l ∈ ImpureRowTreeD02.ls ∨
      l ∈ ImpureRowTreeD03.ls ∨
      l ∈ ImpureRowTreeD04.ls ∨
      l ∈ ImpureRowTreeD05.ls ∨
      l ∈ ImpureRowTreeD06.ls ∨
      l ∈ ImpureRowTreeD07.ls ∨
      l ∈ ImpureRowTreeD08.ls ∨
      l ∈ ImpureRowTreeD09.ls ∨
      l ∈ ImpureRowTreeD10.ls := by
  have h1 := List.all_eq_true.mp impureRowTree_lengths l (List.mem_range.mpr (by omega))
  rw [trialPrime_of_prime hl] at h1
  simpa [hl5, List.contains_iff_mem, or_assoc] using h1

/-- **Four impure rows for the lengths 5 to 521.** Let `N` be an odd perfect number with special
prime `q` and `l` a prime with `5 ≤ l ≤ 521` dividing `e_p + 1` for every prime factor `p ≠ q`.
If `M` is a finite set such that every prime factor `p ≠ q` outside `M` has a row
`σ(p ^ e_p)` that is a prime power, then `M` has at least four elements; so at least four
ordinary rows are not prime powers.

Restricted result (one odd prime divides every ordinary index); no published source was
checked; novelty not verified. Nothing is said when no odd prime divides every ordinary index.
The odd perfect number conjecture remains open. -/
theorem four_le_card_of_pure_outside_small {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl5 : 5 ≤ l) (hl521 : l ≤ 521)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 4 ≤ M.card := by
  by_cases hM3 : M.card ≤ 3
  · have hseed := impureRowTree_seed h hq hodd hl hl5 hidx M hM hM3
    have hl2 : l ≠ 2 := by omega
    have key : ∀ {pc : List (ℕ × ℕ × List ℕ)} {tab : List (ℕ × Tree × Tree)} {ls : List ℕ},
        tableOK pc tab = true → tab.map Prod.fst = ls → l ∈ ls → 4 ≤ M.card :=
      fun htab hls hm => tableOK_sound htab (hls ▸ hm) h hq hodd hl hl2 hidx M hM hseed
    rcases impureRowTree_mem_lengths hl hl5 hl521 with
      hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
    exacts [key ImpureRowTreeD01.tab_ok ImpureRowTreeD01.tab_ls hm,
      key ImpureRowTreeD02.tab_ok ImpureRowTreeD02.tab_ls hm,
      key ImpureRowTreeD03.tab_ok ImpureRowTreeD03.tab_ls hm,
      key ImpureRowTreeD04.tab_ok ImpureRowTreeD04.tab_ls hm,
      key ImpureRowTreeD05.tab_ok ImpureRowTreeD05.tab_ls hm,
      key ImpureRowTreeD06.tab_ok ImpureRowTreeD06.tab_ls hm,
      key ImpureRowTreeD07.tab_ok ImpureRowTreeD07.tab_ls hm,
      key ImpureRowTreeD08.tab_ok ImpureRowTreeD08.tab_ls hm,
      key ImpureRowTreeD09.tab_ok ImpureRowTreeD09.tab_ls hm,
      key ImpureRowTreeD10.tab_ok ImpureRowTreeD10.tab_ls hm]
  · omega

end OddPerfect

#print axioms OddPerfect.impureRowTree_prod_H_step
#print axioms OddPerfect.impureRowTree_prod_H_seven
#print axioms OddPerfect.impureRowTree_seed
#print axioms OddPerfect.impureRowTree_lengths
#print axioms OddPerfect.impureRowTree_mem_lengths
#print axioms OddPerfect.four_le_card_of_pure_outside_small
