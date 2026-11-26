import OddPerfect.Spoof
import OddPerfect.Abundancy
import OddPerfect.Valuation

/-!
# Integer spoof factorizations

Following the BYU spoof paper (arXiv 2006.10697), a factorization is a list of pairs
`(b, e)` with `b : ℤ`; its value is `∏ b ^ e` and its formal divisor sum is
`∏ (1 + b + ... + b ^ e)`. It is spoof perfect when the formal divisor sum is twice the value.
The structural side conditions of a genuine odd perfect number (odd bases, `|b| > 1`,
pairwise coprime bases, positive exponents, Euler's parity pattern) are separate predicates,
so each example is tested against each.

Main contents.

* Voight's spoof `3^4 7^2 11^2 19^2 (-127)^1`, with one theorem per structural condition it
  passes or fails.
* Euler's pattern counts list positions: with odd bases, `2 ^ c` divides the formal divisor
  sum, `c` the number of positions of odd exponent (`two_pow_countP_dvd_formalSigma`), so a
  spoof with odd bases has at most one such position (`countP_odd_exponent_le_one`).
* The arithmetic identity (`sigma_eq_two_mul_add_div_iff_isSpoofPerfect`): for prime
  factorizations `m` and `k > 0`, `k ∣ m ∧ σ(m) = 2m + m/k` holds iff `m * (-(2k+1))^1` is a
  spoof. Near perfect numbers (Pollack and Shevelev: `σ(m) = 2m + d` with `d` a proper divisor,
  `IsNearPerfectWith`, `IsNearPerfect`) correspond to the case `1 < k`
  (`isNearPerfectWith_iff_isSpoofPerfect`, `isNearPerfect_iff_exists_isSpoofPerfect`). At
  `k = 1` the identity holds for `m = 120`, but `120` is not near perfect
  (`not_isNearPerfect_120`). Johnson's odd near perfect number `173369889 = 3^4 7^2 11^2 19^2`
  with `k = 63` (`isNearPerfectWith_johnson`) gives Voight's spoof.
* Formal conservation (`valuation_balance`): every spoof satisfies the analog of
  `OPNStarter.valuation_balance` at every `q`, for the absolute values of the component sums.
* Positivity: genuine components have abundancy in `(1, p/(p-1))`; the formal factor of
  `(-127)^1` is `126/127 < 1`. Consequently the positive part `173369889` of Voight's value is
  an abundant divisor (abundancy `127/63 > 2`), which a genuine odd perfect number cannot have.

## Which library theorems can separate genuine numbers from signed spoofs

Arguments that only use `σ(N) = 2N`, multiplicativity, and congruences or valuations of the
component sums transfer to integer spoofs (the formal versions hold, `valuation_balance`), so
they cannot rule out signed spoofs. Arguments that use positivity or size can. Classification
of the main results of the library, with the Voight verdicts proved below:

* Transfer (no positivity): Euler's form (`exists_euler_form`, `special_mod_four`, the
  `2`-adic ledger): BYU Prop 4.1 (not formalized here) is a pure `2`-adic computation valid for
  signed bases; Voight passes with the signed base `-127 ≡ 1 (mod 4)`
  (`eulerPattern_voight`) and fails with `127 ≡ 3 (mod 4)` (`not_eulerPatternAbs_voight`).
  `mod_four`, `touchard`, `mod_refined`: pass for the signed value, fail for its absolute value. Valuation conservation and the
  forcing step (`OPNStarter.force_prime`): pass (`valuation_balance_voight`). Strong
  connectivity of the formal graph (`Network`): passes (`hamiltonian_cycle_voight`).
  `SteuerwaldThree` (case `3 ∣ N`, pure `3`-adic counting): its hypothesis fails for Voight
  (exponent of `3` is `4`). The closed form `3`-adic ledger
  `factorization_three_eq_sum_threeWeight` needs the residue of the actual signed base mod 3:
  with `127 ≡ 1` it predicts `v_3 = 2` but the truth is `4` (`not_threeWeight_ledger_abs_voight`);
  with `-127 ≡ 2` the formula gives `4` (`threeWeight_ledger_signed_voight`).
* Use positivity or size: everything built on `abundancy` and `σ(p^e) > p^e`:
  `not_perfect_of_dvd_of_two_lt_abundancy` and its users `not_105_dvd`,
  `not_three_five_eleven_thirteen`, the certificate exclusions, `abundancy_special_lt`,
  `abundancy_sq_bounds`; the `ω` bounds `three_le_card_primeFactors`,
  `four_le_card_primeFactors`, `five_le_card_primeFactors` and `SmallestPrime` (products of
  `p/(p-1)`); `McDaniel` (abundant divisor leaves); `ClosedLoop` and hence `steuerwald`
  (`3 ∣ N` free case via a size comparison); Nielsen's bound `lt_two_pow_four_pow` (Cook's
  lemma on `∏ (1 - 1/x_i)` with `x_i ≥ 2`). Voight passes the conclusions of `not_105_dvd`,
  `ω ≥ 5` and Nielsen's bound anyway (they are not violated by this example), but violates
  the abundancy statements: the abundant divisor test (`abundant_divisor_voight`) and the lower
  bound `1 < σ(p^e)/p^e` at the base `-127` (`formalFactor_voight_lt_one`). A negative base at
  even exponent also violates the upper bound `p/(p-1)` (`formalFactor_neg_three_sq`).
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect.SpoofInt

/-! ## Definitions -/

/-- `geom b e = 1 + b + ... + b ^ e` over `ℤ`, by recursion so that the kernel evaluates it. -/
def geom (b : ℤ) : ℕ → ℤ
  | 0 => 1
  | e + 1 => geom b e + b ^ (e + 1)

/-- Formal value `∏ b ^ e` of an integer factorization. -/
def value (l : List (ℤ × ℕ)) : ℤ := (l.map fun x => x.1 ^ x.2).prod

/-- Formal divisor sum `∏ (1 + b + ... + b ^ e)` of an integer factorization. -/
def formalSigma (l : List (ℤ × ℕ)) : ℤ := (l.map fun x => geom x.1 x.2).prod

/-- Spoof perfect: the formal divisor sum is twice the value. No side conditions. -/
def IsSpoofPerfect (l : List (ℤ × ℕ)) : Prop := formalSigma l = 2 * value l

/-- Every base is odd. -/
def BasesOdd (l : List (ℤ × ℕ)) : Prop := ∀ x ∈ l, x.1 % 2 = 1

/-- Every base has absolute value greater than one. -/
def BasesNontrivial (l : List (ℤ × ℕ)) : Prop := ∀ x ∈ l, 1 < x.1.natAbs

/-- Every exponent is positive. -/
def ExponentsPos (l : List (ℤ × ℕ)) : Prop := ∀ x ∈ l, 0 < x.2

/-- The bases are pairwise coprime. -/
def PairwiseCoprime (l : List (ℤ × ℕ)) : Prop := l.Pairwise fun x y => Int.gcd x.1 y.1 = 1

/-- Every base is positive. -/
def BasesPos (l : List (ℤ × ℕ)) : Prop := ∀ x ∈ l, 0 < x.1

/-- Euler's pattern for signed bases: exactly one position of the list carries an odd
exponent (the sublist of odd exponent entries is `[x]`, so a repeated entry counts twice),
and that entry has base `≡ 1 (mod 4)` (as an integer, `%` being the nonnegative remainder)
and exponent `≡ 1 (mod 4)`. -/
def EulerPattern (l : List (ℤ × ℕ)) : Prop :=
  ∃ x ∈ l, x.1 % 4 = 1 ∧ x.2 % 4 = 1 ∧ l.filter (fun y => y.2 % 2 = 1) = [x]

/-- Euler's pattern read on absolute values of the bases: exactly one position of the list
carries an odd exponent, and that entry has `|b| ≡ 1 (mod 4)` and exponent `≡ 1 (mod 4)`. -/
def EulerPatternAbs (l : List (ℤ × ℕ)) : Prop :=
  ∃ x ∈ l, x.1.natAbs % 4 = 1 ∧ x.2 % 4 = 1 ∧ l.filter (fun y => y.2 % 2 = 1) = [x]

instance (l : List (ℤ × ℕ)) : Decidable (IsSpoofPerfect l) := by
  unfold IsSpoofPerfect; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (BasesOdd l) := by unfold BasesOdd; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (BasesNontrivial l) := by
  unfold BasesNontrivial; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (ExponentsPos l) := by
  unfold ExponentsPos; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (PairwiseCoprime l) := by
  unfold PairwiseCoprime; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (BasesPos l) := by unfold BasesPos; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (EulerPattern l) := by
  unfold EulerPattern; infer_instance
instance (l : List (ℤ × ℕ)) : Decidable (EulerPatternAbs l) := by
  unfold EulerPatternAbs; infer_instance

/-- Lift a natural factorization to an integer one. -/
def ofNat (l : List (ℕ × ℕ)) : List (ℤ × ℕ) := l.map fun x => ((x.1 : ℤ), x.2)

/-- `geom` commutes with the cast from `ℕ`. -/
theorem geom_natCast (b e : ℕ) : geom (b : ℤ) e = (Spoof.geom b e : ℤ) := by
  induction e with
  | zero => simp [geom, Spoof.geom]
  | succ e ih => simp [geom, Spoof.geom, ih]

/-- `geom b 1 = 1 + b`. -/
theorem geom_one (b : ℤ) : geom b 1 = 1 + b := by simp [geom]

/-- The formal divisor sum of a lifted factorization is the cast of the natural one. -/
theorem formalSigma_ofNat (l : List (ℕ × ℕ)) :
    formalSigma (ofNat l) = (Spoof.formalSigma l : ℤ) := by
  simp only [formalSigma, ofNat, Spoof.formalSigma, Nat.cast_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [geom_natCast]

/-- The value of a lifted factorization is the cast of the natural one. -/
theorem value_ofNat (l : List (ℕ × ℕ)) : value (ofNat l) = (Spoof.value l : ℤ) := by
  simp only [value, ofNat, Spoof.value, Nat.cast_list_prod, List.map_map]
  congr 1

/-- Appending a factor multiplies the formal divisor sum. -/
theorem formalSigma_append (l : List (ℤ × ℕ)) (y : ℤ × ℕ) :
    formalSigma (l ++ [y]) = formalSigma l * geom y.1 y.2 := by
  simp [formalSigma]

/-- Appending a factor multiplies the value. -/
theorem value_append (l : List (ℤ × ℕ)) (y : ℤ × ℕ) :
    value (l ++ [y]) = value l * y.1 ^ y.2 := by
  simp [value]

/-! ## Voight's spoof -/

/-- Voight's spoof `3^4 7^2 11^2 19^2 (-127)^1`. -/
def voight : List (ℤ × ℕ) := [(3, 4), (7, 2), (11, 2), (19, 2), (-127, 1)]

/-- Voight's spoof is spoof perfect: `121 * 57 * 133 * 381 * (-126) = 2 * (-22017975903)`. -/
theorem isSpoofPerfect_voight : IsSpoofPerfect voight := by decide

/-- The value of Voight's spoof. -/
theorem value_voight : value voight = -22017975903 := by decide

/-- Voight's spoof has odd bases. -/
theorem basesOdd_voight : BasesOdd voight := by decide

/-- Voight's spoof has bases of absolute value greater than one. -/
theorem basesNontrivial_voight : BasesNontrivial voight := by decide

/-- Voight's spoof has positive exponents. -/
theorem exponentsPos_voight : ExponentsPos voight := by decide

/-- Voight's spoof has pairwise coprime bases. -/
theorem pairwiseCoprime_voight : PairwiseCoprime voight := by decide

/-- The absolute values of the bases of Voight's spoof are prime. -/
theorem prime_natAbs_voight : ∀ x ∈ voight, x.1.natAbs.Prime := by
  simp only [voight, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- Voight's spoof is not positive: the base `-127` is negative. Of the predicates
`BasesOdd`, `BasesNontrivial`, `ExponentsPos`, `PairwiseCoprime`, `BasesPos`, `EulerPattern`
it fails only `BasesPos`; it also fails `EulerPatternAbs` (`not_eulerPatternAbs_voight`). -/
theorem not_basesPos_voight : ¬ BasesPos voight := by decide

/-- Euler's pattern holds for the signed base: the unique odd exponent is `1`, at the base
`-127 ≡ 1 (mod 4)`. -/
theorem eulerPattern_voight : EulerPattern voight := by decide

/-- Euler's pattern fails on absolute values: `127 ≡ 3 (mod 4)`. -/
theorem not_eulerPatternAbs_voight : ¬ EulerPatternAbs voight := by decide

/-! Regression checks: the Euler patterns count list positions, not distinct entries. -/

example : ¬ EulerPattern [(5, 1), (5, 1)] := by decide
example : ¬ EulerPatternAbs [(5, 1), (5, 1)] := by decide
example : EulerPattern [(5, 1)] := by decide
example : EulerPatternAbs [(5, 1)] := by decide
example : ¬ EulerPattern [(5, 1), (13, 1)] := by decide
example : ¬ EulerPatternAbs [(5, 1), (13, 1)] := by decide

/-- For an odd base, `1 + b + ... + b ^ e` is even exactly when `e` is odd. -/
theorem even_geom_iff {b : ℤ} (hb : Odd b) (e : ℕ) : Even (geom b e) ↔ Odd e := by
  induction e with
  | zero => simp [geom]
  | succ e ih =>
    rw [geom, Int.even_add, ih, Nat.odd_add_one]
    have : ¬ Even (b ^ (e + 1)) := Int.not_even_iff_odd.mpr hb.pow
    tauto

/-- For odd bases, `2 ^ c` divides the formal divisor sum, where `c` is the number of list
positions carrying an odd exponent. -/
theorem two_pow_countP_dvd_formalSigma {l : List (ℤ × ℕ)} (hl : BasesOdd l) :
    2 ^ l.countP (fun y => y.2 % 2 = 1) ∣ formalSigma l := by
  induction l with
  | nil => simp [formalSigma]
  | cons x l ih =>
    have hx : Odd x.1 := Int.odd_iff.mpr (hl x (List.mem_cons_self ..))
    have ih := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hf : formalSigma (x :: l) = geom x.1 x.2 * formalSigma l := by simp [formalSigma]
    rw [hf, List.countP_cons]
    by_cases he : x.2 % 2 = 1
    · have h2 : (2 : ℤ) ∣ geom x.1 x.2 :=
        even_iff_two_dvd.mp ((even_geom_iff hx _).mpr (Nat.odd_iff.mpr he))
      simpa [he, pow_succ, mul_comm] using mul_dvd_mul h2 ih
    · simpa [he] using dvd_mul_of_dvd_right ih _


/-- For odd bases, the value is odd. -/
theorem odd_value {l : List (ℤ × ℕ)} (hl : BasesOdd l) : Odd (value l) := by
  induction l with
  | nil => simp [value]
  | cons x l ih =>
    have hx : Odd x.1 := Int.odd_iff.mpr (hl x (List.mem_cons_self ..))
    have : value (x :: l) = x.1 ^ x.2 * value l := by simp [value]
    rw [this]
    exact (hx.pow).mul (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-- With odd bases and at least two list positions of odd exponent (equal entries counted
separately), the formal divisor sum is divisible by `4`. -/
theorem four_dvd_formalSigma {l : List (ℤ × ℕ)} (hl : BasesOdd l)
    (h2 : 2 ≤ l.countP (fun y => y.2 % 2 = 1)) : (4 : ℤ) ∣ formalSigma l :=
  (pow_dvd_pow 2 h2).trans (two_pow_countP_dvd_formalSigma hl)

/-- A spoof with odd bases has at most one list position of odd exponent: otherwise
`4 ∣ formalSigma l = 2 * value l` with `value l` odd. -/
theorem countP_odd_exponent_le_one {l : List (ℤ × ℕ)} (hl : BasesOdd l)
    (h : IsSpoofPerfect l) : l.countP (fun y => y.2 % 2 = 1) ≤ 1 := by
  by_contra hc
  have h4 := four_dvd_formalSigma hl (by omega)
  rw [h] at h4
  obtain ⟨j, hj⟩ := odd_value hl
  rw [hj] at h4
  omega

/-- `mod_four` passes for the signed value: `value ≡ 1 (mod 4)`. -/
theorem value_voight_mod_four : value voight % 4 = 1 := by decide

/-- `mod_four` fails for the absolute value: `|value| ≡ 3 (mod 4)`. -/
theorem natAbs_value_voight_mod_four : (value voight).natAbs % 4 = 3 := by decide

/-- Touchard passes for the signed value: `value ≡ 9 (mod 36)`. -/
theorem touchard_voight : value voight % 12 = 1 ∨ value voight % 36 = 9 := by decide

/-- Touchard fails for the absolute value: `|value| ≡ 3 (mod 12)` and `≡ 27 (mod 36)`. -/
theorem not_touchard_natAbs_voight :
    ¬ ((value voight).natAbs % 12 = 1 ∨ (value voight).natAbs % 36 = 9) := by decide

/-- The refined congruence `mod_refined` passes for the signed value (`≡ 81 (mod 324)`). -/
theorem mod_refined_voight :
    value voight % 12 = 1 ∨ value voight % 468 = 117 ∨ value voight % 324 = 81 := by decide

/-- The refined congruence fails for the absolute value. -/
theorem not_mod_refined_natAbs_voight :
    ¬ ((value voight).natAbs % 12 = 1 ∨ (value voight).natAbs % 468 = 117 ∨
      (value voight).natAbs % 324 = 81) := by decide

/-- The conclusion of `not_105_dvd` holds (trivially: `5` is not a base). -/
theorem not_105_dvd_voight : ¬ (105 : ℤ) ∣ value voight := by decide

/-- The conclusion of `not_three_five_eleven_thirteen` holds. -/
theorem not_three_five_eleven_thirteen_voight :
    ¬ ((3 : ℤ) ∣ value voight ∧ (5 : ℤ) ∣ value voight ∧ (11 : ℤ) ∣ value voight ∧
      (13 : ℤ) ∣ value voight) := by decide

/-- `ω ≥ 5` holds: the absolute value has at least five prime factors. -/
theorem five_le_card_primeFactors_voight : 5 ≤ (value voight).natAbs.primeFactors.card := by
  have hv : (value voight).natAbs = 22017975903 := by decide
  have hs : ({3, 7, 11, 19, 127} : Finset ℕ) ⊆ (value voight).natAbs.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rw [hv, Nat.mem_primeFactors]
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact (Finset.card_le_card hs).trans_eq' (by decide)

/-- Nielsen's bound `|value| < 2^(4^ω)` holds with `ω = 5`. -/
theorem nielsen_voight : (value voight).natAbs < 2 ^ (4 ^ 5) := by
  rw [show (value voight).natAbs = 22017975903 by decide]
  calc 22017975903 < 2 ^ 35 := by norm_num
    _ ≤ 2 ^ (4 ^ 5) := Nat.pow_le_pow_right (by norm_num) (by norm_num)

/-- Steuerwald does not apply: not every even exponent equals `2` (base `3` has exponent
`4`). Equivalently the analog of `exists_even_exponent_ge_four` holds. -/
theorem steuerwald_hyp_fails_voight : ¬ ∀ x ∈ voight, x.2 % 2 = 0 → x.2 = 2 := by decide

/-- The analog of `exists_even_exponent_ge_four` holds. -/
theorem exists_even_exponent_ge_four_voight : ∃ x ∈ voight, x.2 % 2 = 0 ∧ 4 ≤ x.2 := by
  decide

/-- McDaniel does not apply: `4 % 3 = 1`, so not every even exponent is `≡ 2 (mod 3)`. -/
theorem mcdaniel_hyp_fails_voight : ¬ ∀ x ∈ voight, x.2 % 2 = 0 → x.2 % 3 = 2 := by decide

/-- The formal components: `σ~(3^4) = 11^2`, `σ~(7^2) = 3 * 19`, `σ~(11^2) = 7 * 19`,
`σ~(19^2) = 3 * 127`, `σ~((-127)^1) = -2 * 3^2 * 7`. -/
theorem components_voight :
    geom 3 4 = 11 ^ 2 ∧ geom 7 2 = 3 * 19 ∧ geom 11 2 = 7 * 19 ∧ geom 19 2 = 3 * 127 ∧
      geom (-127) 1 = -2 * 3 ^ 2 * 7 := by decide

/-- The `2`-adic part of Euler's argument: every component sum is odd except the one at the
odd exponent, which is `≡ 2 (mod 4)`. -/
theorem two_adic_voight :
    (∀ x ∈ voight, x.2 % 2 = 0 → geom x.1 x.2 % 2 = 1) ∧ geom (-127) 1 % 4 = 2 := by decide

/-- Strong connectivity of the formal graph (edge `p → r` when `r` divides the component sum
at `p`): the Hamiltonian cycle `3 → 11 → 7 → 19 → -127 → 3` passes through every base. -/
theorem hamiltonian_cycle_voight :
    (11 : ℤ) ∣ geom 3 4 ∧ (7 : ℤ) ∣ geom 11 2 ∧ (19 : ℤ) ∣ geom 7 2 ∧ (-127 : ℤ) ∣ geom 19 2 ∧
      (3 : ℤ) ∣ geom (-127) 1 := by decide

/-- The `3`-adic exponent of the value is exactly `4`, and the component sums carry exactly
`3^0, 3^1, 3^0, 3^1, 3^2`, so the ledger balances: `4 = 0 + 1 + 0 + 1 + 2`. -/
theorem three_adic_ledger_voight :
    (3 ^ 4 : ℤ) ∣ value voight ∧ ¬ (3 ^ 5 : ℤ) ∣ value voight ∧
      ¬ (3 : ℤ) ∣ geom 3 4 ∧ (3 : ℤ) ∣ geom 7 2 ∧ ¬ (3 ^ 2 : ℤ) ∣ geom 7 2 ∧
      ¬ (3 : ℤ) ∣ geom 11 2 ∧ (3 : ℤ) ∣ geom 19 2 ∧ ¬ (3 ^ 2 : ℤ) ∣ geom 19 2 ∧
      (3 ^ 2 : ℤ) ∣ geom (-127) 1 ∧ ¬ (3 ^ 3 : ℤ) ∣ geom (-127) 1 := by decide

/-- The closed form `3`-adic ledger read on absolute values fails: `threeWeight` applied to
`|b|` sums to `2` (since `127 ≡ 1 (mod 3)` with exponent `1` contributes `v_3(2) = 0`), but
`v_3(|value|) = 4`. -/
theorem not_threeWeight_ledger_abs_voight :
    (voight.map fun x => threeWeight x.1.natAbs x.2).sum = 2 ∧
      ¬ (3 ^ 2 ∣ (value voight).natAbs ∧ ¬ 3 ^ 3 ∣ (value voight).natAbs) := by
  refine ⟨?_, by decide⟩
  simp [voight, threeWeight, Nat.padicValNat_def, Nat.multiplicity_self (by norm_num : 1 < 3),
    multiplicity_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]

/-- The closed form `3`-adic ledger with signed residues balances: `-127 ≡ 2 (mod 3)` at odd
exponent `1` contributes `v_3(|-127 + 1|) + v_3(2) = 2`, and the other bases contribute
`0 + 1 + 0 + 1`, total `4 = v_3(|value|)`. -/
theorem threeWeight_ledger_signed_voight :
    ((-127 : ℤ) % 3 = 2 ∧ padicValNat 3 ((-127 + 1 : ℤ).natAbs) + padicValNat 3 2 = 2) ∧
      threeWeight 3 4 + threeWeight 7 2 + threeWeight 11 2 + threeWeight 19 2 + 2 = 4 := by
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · have h126 : ((-127 + 1 : ℤ).natAbs) = 3 ^ 2 * 14 := by decide
    rw [h126, Nat.padicValNat_def, Nat.padicValNat_def,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 14),
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  · simp [threeWeight, Nat.padicValNat_def, Nat.multiplicity_self (by norm_num : 1 < 3)]

/-! ## Formal conservation -/

/-- `natAbs` of a list product is the product of the `natAbs`. -/
theorem natAbs_list_prod (L : List ℤ) : L.prod.natAbs = (L.map Int.natAbs).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Int.natAbs_mul, ih]

/-- Formal valuation conservation for integer spoofs: for every `q`, the analog of
`OPNStarter.valuation_balance` holds with the absolute values of the component sums. It holds
at every `q`, in particular at every base that is a signed prime, so this bookkeeping (and
every identity derived from `formalSigma = 2 * value` and multiplicativity over the bases)
cannot distinguish a genuine odd perfect number from a signed spoof. The only hypothesis
besides the spoof equation is that no base is zero. -/
theorem valuation_balance {l : List (ℤ × ℕ)} (h : IsSpoofPerfect l) (hb : ∀ x ∈ l, x.1 ≠ 0)
    (q : ℕ) :
    Nat.factorization 2 q + (value l).natAbs.factorization q =
      (l.map fun x => (geom x.1 x.2).natAbs.factorization q).sum := by
  have hv : value l ≠ 0 := List.prod_ne_zero fun h0 => by
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    exact pow_ne_zero _ (hb x hx) hx0
  have habs : (formalSigma l).natAbs = 2 * (value l).natAbs := by
    rw [h, Int.natAbs_mul]; rfl
  have hS : formalSigma l ≠ 0 := by rw [h]; exact mul_ne_zero two_ne_zero hv
  have hg : ∀ n ∈ (l.map fun x => geom x.1 x.2).map Int.natAbs, n ≠ 0 := by
    simp only [List.mem_map]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ h0
    exact hS (List.prod_eq_zero (List.mem_map.mpr ⟨x, hx, Int.natAbs_eq_zero.mp h0⟩))
  rw [← Finsupp.add_apply, ← Nat.factorization_mul two_ne_zero (Int.natAbs_ne_zero.mpr hv),
    ← habs, formalSigma, natAbs_list_prod, Spoof.factorization_list_prod _ hg, List.map_map,
    List.map_map]
  rfl

/-- Voight's spoof satisfies formal valuation conservation at every `q`. -/
theorem valuation_balance_voight (q : ℕ) :
    Nat.factorization 2 q + (value voight).natAbs.factorization q =
      (voight.map fun x => (geom x.1 x.2).natAbs.factorization q).sum :=
  valuation_balance isSpoofPerfect_voight (by decide) q

/-! ## The near perfect link -/

/-- Appending the base `-(2c+1)` at exponent `1`: the result is spoof perfect iff
`c * formalSigma l = (2c+1) * value l`. No hypothesis on `l` or `c`. -/
theorem isSpoofPerfect_append_iff (l : List (ℤ × ℕ)) (c : ℤ) :
    IsSpoofPerfect (l ++ [(-(2 * c + 1), 1)]) ↔ c * formalSigma l = (2 * c + 1) * value l := by
  rw [IsSpoofPerfect, formalSigma_append, value_append, geom_one, pow_one]
  constructor <;> intro h <;> linarith

/-- Arithmetic identity behind the near perfect link. For a factorization `l` with distinct
prime bases and value `m`, and `k > 0`: `k ∣ m` and `σ(m) = 2m + m/k` iff `m * (-(2k+1))^1`
is a spoof. This is not a classification of near perfect numbers: at `k = 1` the amount
`m / k = m` is not a proper divisor (see `isNearPerfectWith_iff_isSpoofPerfect` for `1 < k`).
Neither coprimality of `2k+1` with `m` nor oddness of `m` is needed (coprimality is only a
side condition for the extended spoof); `k ∣ m` is automatic on the spoof side since
`gcd(k, 2k+1) = 1`. -/
theorem sigma_eq_two_mul_add_div_iff_isSpoofPerfect {l : List (ℕ × ℕ)}
    (hp : ∀ x ∈ l, x.1.Prime) (hd : (l.map Prod.fst).Nodup) {k : ℕ} (hk : 0 < k) :
    (k ∣ Spoof.value l ∧ σ 1 (Spoof.value l) = 2 * Spoof.value l + Spoof.value l / k) ↔
      IsSpoofPerfect (ofNat l ++ [(-(2 * (k : ℤ) + 1), 1)]) := by
  rw [isSpoofPerfect_append_iff, formalSigma_ofNat, value_ofNat,
    Spoof.formalSigma_eq_sigma l hp hd]
  generalize Spoof.value l = m
  generalize σ 1 m = s
  have key : (k : ℤ) * s = (2 * k + 1) * m ↔ k * s = (2 * k + 1) * m := by
    constructor <;> intro h <;> exact_mod_cast h
  rw [key]
  constructor
  · rintro ⟨⟨j, rfl⟩, hs⟩
    rw [Nat.mul_div_cancel_left _ hk] at hs
    rw [hs]; ring
  · intro h
    have hcop : Nat.Coprime k (2 * k + 1) :=
      (Nat.coprime_mul_right_add_right k 1 2).mpr (Nat.coprime_one_right k)
    obtain ⟨j, rfl⟩ : k ∣ m := hcop.dvd_of_dvd_mul_left ⟨s, h.symm⟩
    refine ⟨dvd_mul_right _ _, ?_⟩
    rw [Nat.mul_div_cancel_left _ hk]
    have : k * s = k * ((2 * k + 1) * j) := by rw [h]; ring
    rw [Nat.eq_of_mul_eq_mul_left hk this]; ring

/-- Near perfect with omitted divisor `d` (Pollack and Shevelev): `d` is a proper divisor of
`m` (`d ∣ m`, `d < m`) and `σ(m) = 2m + d`, that is, `m` is the sum of its proper divisors
other than `d`. -/
def IsNearPerfectWith (m d : ℕ) : Prop := d ∣ m ∧ d < m ∧ σ 1 m = 2 * m + d

/-- `m` is near perfect: `IsNearPerfectWith m d` for some `d`. -/
def IsNearPerfect (m : ℕ) : Prop := ∃ d, IsNearPerfectWith m d

/-- For `0 < m` and `0 < k`, the amount `m / k` is less than `m` exactly when `1 < k`. -/
theorem div_lt_self_iff_one_lt {m k : ℕ} (hm : 0 < m) (hk : 0 < k) : m / k < m ↔ 1 < k := by
  refine ⟨fun h => ?_, Nat.div_lt_self hm⟩
  by_contra hk1
  rw [show k = 1 by omega, Nat.div_one] at h
  exact lt_irrefl _ h

/-- The near perfect link. For a factorization `l` with distinct prime bases and value `m`,
and `1 < k`: `k ∣ m` and `m` is near perfect with omitted proper divisor `m / k` iff
`m * (-(2k+1))^1` is a spoof. -/
theorem isNearPerfectWith_iff_isSpoofPerfect {l : List (ℕ × ℕ)} (hp : ∀ x ∈ l, x.1.Prime)
    (hd : (l.map Prod.fst).Nodup) {k : ℕ} (hk : 1 < k) :
    (k ∣ Spoof.value l ∧ IsNearPerfectWith (Spoof.value l) (Spoof.value l / k)) ↔
      IsSpoofPerfect (ofNat l ++ [(-(2 * (k : ℤ) + 1), 1)]) := by
  rw [← sigma_eq_two_mul_add_div_iff_isSpoofPerfect hp hd (by omega)]
  have hm : 0 < Spoof.value l := List.prod_pos fun a ha => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact pow_pos (hp x hx).pos _
  constructor
  · rintro ⟨h1, -, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Nat.div_dvd_of_dvd h1, (div_lt_self_iff_one_lt hm (by omega)).mpr hk, h2⟩

/-- The natural factorization `3^4 7^2 11^2 19^2` of Johnson's near perfect number. -/
def johnson : List (ℕ × ℕ) := [(3, 4), (7, 2), (11, 2), (19, 2)]

/-- `johnson` has prime bases. -/
theorem prime_johnson : ∀ x ∈ johnson, x.1.Prime := by
  simp only [johnson, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl) <;> norm_num

/-- Johnson's identity: `σ(173369889) = 2 * 173369889 + 173369889 / 63`, with
`63 ∣ 173369889`. -/
theorem nearPerfect_johnson :
    Spoof.value johnson = 173369889 ∧ 63 ∣ Spoof.value johnson ∧
      σ 1 (Spoof.value johnson) = 2 * Spoof.value johnson + Spoof.value johnson / 63 := by
  rw [← Spoof.formalSigma_eq_sigma johnson prime_johnson (by decide)]
  decide

/-- Johnson's number is near perfect in the strict sense, with `k = 63`: the omitted divisor
`173369889 / 63 = 2751903` is a proper divisor. -/
theorem isNearPerfectWith_johnson :
    63 ∣ Spoof.value johnson ∧ IsNearPerfectWith (Spoof.value johnson) (Spoof.value johnson / 63) ∧
      Spoof.value johnson / 63 = 2751903 := by
  obtain ⟨hv, h63, hs⟩ := nearPerfect_johnson
  refine ⟨h63, ⟨Nat.div_dvd_of_dvd h63, ?_, hs⟩, by rw [hv]⟩
  rw [hv]; decide

/-- Voight's spoof is Johnson's near perfect number with the extra base `-(2 * 63 + 1)`. -/
theorem voight_eq_johnson : voight = ofNat johnson ++ [(-(2 * (63 : ℕ) + 1 : ℤ), 1)] := by
  decide

/-- Voight's spoof recovered through the near perfect link. -/
theorem isSpoofPerfect_voight_of_johnson : IsSpoofPerfect voight := by
  rw [voight_eq_johnson]
  exact (sigma_eq_two_mul_add_div_iff_isSpoofPerfect prime_johnson (by decide)
    (by norm_num)).mp nearPerfect_johnson.2

/-- The arithmetic identity `sigma_eq_two_mul_add_div_iff_isSpoofPerfect` stated for a natural
number `m ≠ 0` through its prime factorization list, for `0 < k`. At `k = 1` the amount
`m / k = m` is not a proper divisor. -/
theorem sigma_eq_two_mul_add_div_iff_isSpoofPerfect_nat {m k : ℕ} (hm : m ≠ 0) (hk : 0 < k) :
    (k ∣ m ∧ σ 1 m = 2 * m + m / k) ↔
      IsSpoofPerfect (ofNat (m.primeFactors.toList.map fun p => (p, m.factorization p)) ++
        [(-(2 * (k : ℤ) + 1), 1)]) := by
  set l := m.primeFactors.toList.map fun p => (p, m.factorization p) with hl
  have hp : ∀ x ∈ l, x.1.Prime := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)
  have hd : (l.map Prod.fst).Nodup := by
    rw [hl, List.map_map]
    simpa [Function.comp_def] using m.primeFactors.nodup_toList
  have hv : Spoof.value l = m := by
    rw [Spoof.value, hl, List.map_map, Finset.prod_map_toList]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rfl
  rw [← sigma_eq_two_mul_add_div_iff_isSpoofPerfect hp hd hk, hv]

/-- The near perfect link for a natural number `m ≠ 0` and `1 < k`: `k ∣ m` and `m` is near
perfect with omitted proper divisor `m / k` iff `m * (-(2k+1))^1` is a spoof, with `m`
written through its prime factorization list. -/
theorem isNearPerfectWith_iff_isSpoofPerfect_nat {m k : ℕ} (hm : m ≠ 0) (hk : 1 < k) :
    (k ∣ m ∧ IsNearPerfectWith m (m / k)) ↔
      IsSpoofPerfect (ofNat (m.primeFactors.toList.map fun p => (p, m.factorization p)) ++
        [(-(2 * (k : ℤ) + 1), 1)]) := by
  rw [← sigma_eq_two_mul_add_div_iff_isSpoofPerfect_nat hm (by omega)]
  constructor
  · rintro ⟨h1, -, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Nat.div_dvd_of_dvd h1,
      (div_lt_self_iff_one_lt (Nat.pos_of_ne_zero hm) (by omega)).mpr hk, h2⟩

/-- Every near perfect number `m ≠ 0` arises from the link: with omitted divisor `d`, the
cofactor `k = m / d` satisfies `1 < k`, and the extension by `-(2k+1)` is a spoof. -/
theorem isNearPerfect_iff_exists_isSpoofPerfect {m : ℕ} (hm : m ≠ 0) :
    IsNearPerfect m ↔ ∃ k : ℕ, 1 < k ∧
      IsSpoofPerfect (ofNat (m.primeFactors.toList.map fun p => (p, m.factorization p)) ++
        [(-(2 * (k : ℤ) + 1), 1)]) := by
  constructor
  · rintro ⟨d, hdm, hlt, hs⟩
    obtain ⟨k, rfl⟩ := hdm
    have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by simp [h] at hm
    have hk : 1 < k := by
      by_contra h
      interval_cases k <;> simp_all
    refine ⟨k, hk, (isNearPerfectWith_iff_isSpoofPerfect_nat hm hk).mp ⟨dvd_mul_left _ _, ?_⟩⟩
    rw [Nat.mul_div_cancel _ (by omega)]
    exact ⟨dvd_mul_right _ _, hlt, hs⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨_, ((isNearPerfectWith_iff_isSpoofPerfect_nat hm hk).mpr h).2⟩

/-- `σ(120) = 360`. -/
theorem sigma_120 : σ 1 120 = 360 := by
  have h := Spoof.formalSigma_eq_sigma [(2, 3), (3, 1), (5, 1)] (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> norm_num) (by decide)
  rw [show Spoof.value [(2, 3), (3, 1), (5, 1)] = 120 by decide] at h
  rw [← h]; decide

/-- The arithmetic identity holds at `m = 120`, `k = 1`: `σ(120) = 2 * 120 + 120 / 1`. -/
theorem sigma_eq_two_mul_add_div_120 : 1 ∣ 120 ∧ σ 1 120 = 2 * 120 + 120 / 1 := by
  rw [sigma_120]; decide

/-- The omitted amount `120` at `k = 1` is not a proper divisor of `120`. -/
theorem not_isNearPerfectWith_120_120 : ¬ IsNearPerfectWith 120 120 := fun h =>
  lt_irrefl _ h.2.1

/-- `120` is not near perfect: `σ(120) = 2 * 120 + d` forces `d = 120`, which is not proper. -/
theorem not_isNearPerfect_120 : ¬ IsNearPerfect 120 := by
  rintro ⟨d, -, hlt, hs⟩
  rw [sigma_120] at hs
  omega

/-! ## Positivity -/

/-- Genuine side: for a prime `p` and `e > 0`, `1 < σ(p^e)/p^e < p/(p-1)`. -/
theorem abundancy_prime_pow_bounds {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    1 < abundancy (p ^ e) ∧ abundancy (p ^ e) < (p : ℚ) / (p - 1) := by
  refine ⟨lt_of_lt_of_le ?_ (one_add_inv_le_abundancy_prime_pow hp he),
    abundancy_prime_pow_lt hp e⟩
  have : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have := inv_pos.mpr this
  linarith

/-- Spoof side, general: for a base `b ≤ -2` at exponent `1`, the formal factor
`(1 + b)/b` lies strictly between `0` and `1`. -/
theorem formalFactor_neg_lt_one {b : ℤ} (hb : b ≤ -2) :
    0 < (geom b 1 : ℚ) / b ∧ (geom b 1 : ℚ) / b < 1 := by
  rw [geom_one]
  have hb' : (b : ℚ) ≤ -2 := by exact_mod_cast hb
  push_cast
  constructor
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · rw [div_lt_one_of_neg (by linarith)]; linarith

/-- Voight's formal factor at `-127` is `126/127 < 1`: the lower bound `1 < σ(p^e)/p^e` of
genuine components fails for a negative base. -/
theorem formalFactor_voight_lt_one :
    (geom (-127) 1 : ℚ) / (-127) = 126 / 127 ∧ (geom (-127) 1 : ℚ) / (-127) < 1 := by
  rw [geom_one]; norm_num

/-- A negative base at even exponent breaks the upper bound: the formal factor of `(-3)^2`
is `7/9 > 3/4 = (-3)/((-3) - 1)`. -/
theorem formalFactor_neg_three_sq :
    (geom (-3) 2 : ℚ) / (-3) ^ 2 = 7 / 9 ∧
      (-3 : ℚ) / (-3 - 1) < (geom (-3) 2 : ℚ) / (-3) ^ 2 := by
  have : geom (-3) 2 = 7 := by decide
  rw [this]; norm_num

/-- For positive bases and positive exponents the component sum exceeds the power, so the
formal abundancy of a positive factorization strictly increases when a factor is appended.
This monotonicity is the input of every abundant divisor argument. -/
theorem pow_lt_geom {b : ℤ} (hb : 0 < b) {e : ℕ} (he : 0 < e) : b ^ e < geom b e := by
  have hpos : ∀ n, 0 < geom b n := by
    intro n
    induction n with
    | zero => simp [geom]
    | succ n ih => rw [geom]; have := pow_pos hb (n + 1); linarith
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt he
  rw [zero_add, geom]
  linarith [hpos e]

/-- The positive part of Voight's value, `173369889`, has abundancy `127/63 > 2`, and it
divides the value. A genuine odd perfect number has no divisor of abundancy above `2`
(`not_perfect_of_dvd_of_two_lt_abundancy`), so this is a positivity based separation of
Voight's spoof from a genuine number: the negative factor `126/127` brings the formal
abundancy back to `2`. -/
theorem abundant_divisor_voight :
    abundancy 173369889 = 127 / 63 ∧ 2 < abundancy 173369889 ∧
      (173369889 : ℤ) ∣ value voight := by
  have hs : σ 1 173369889 = 349491681 := by
    have h := Spoof.formalSigma_eq_sigma johnson prime_johnson (by decide)
    rw [show Spoof.value johnson = 173369889 by decide] at h
    rw [← h]; decide
  have ha : abundancy 173369889 = 127 / 63 := by
    rw [abundancy, hs]; norm_num
  exact ⟨ha, by rw [ha]; norm_num, by decide⟩

/-! ## Further examples from the search -/

/-- BYU example (4): `3^2 7^2 7^2 13^1 (-19)^2`. -/
def byuFour : List (ℤ × ℕ) := [(3, 2), (7, 2), (7, 2), (13, 1), (-19, 2)]

/-- BYU example (4) is spoof perfect. -/
theorem isSpoofPerfect_byuFour : IsSpoofPerfect byuFour := by decide

/-- BYU example (4) has odd bases of absolute value above one and positive exponents. -/
theorem basesOdd_byuFour :
    BasesOdd byuFour ∧ BasesNontrivial byuFour ∧ ExponentsPos byuFour := by
  decide

/-- BYU example (4) satisfies Euler's pattern (`13 ≡ 1 (mod 4)` at exponent `1`). -/
theorem eulerPattern_byuFour : EulerPattern byuFour := by decide

/-- BYU example (4) fails pairwise coprimality (the base `7` is repeated). -/
theorem not_pairwiseCoprime_byuFour : ¬ PairwiseCoprime byuFour := by decide

/-- BYU example (2): `1^2 (-3)^2 (-5)^2 49^1`. -/
def byuTwo : List (ℤ × ℕ) := [(1, 2), (-3, 2), (-5, 2), (49, 1)]

/-- BYU example (2) is spoof perfect. -/
theorem isSpoofPerfect_byuTwo : IsSpoofPerfect byuTwo := by decide

/-- BYU example (2) fails `|b| > 1` (the base `1`). -/
theorem not_basesNontrivial_byuTwo : ¬ BasesNontrivial byuTwo := by decide

/-- The Descartes spoof lifted to `ℤ` is spoof perfect, with positive bases. -/
theorem isSpoofPerfect_descartes :
    IsSpoofPerfect (ofNat Spoof.descartes) ∧ BasesPos (ofNat Spoof.descartes) := by decide

end OddPerfect.SpoofInt

#print axioms OddPerfect.SpoofInt.geom_natCast
#print axioms OddPerfect.SpoofInt.geom_one
#print axioms OddPerfect.SpoofInt.formalSigma_ofNat
#print axioms OddPerfect.SpoofInt.value_ofNat
#print axioms OddPerfect.SpoofInt.formalSigma_append
#print axioms OddPerfect.SpoofInt.value_append
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_voight
#print axioms OddPerfect.SpoofInt.value_voight
#print axioms OddPerfect.SpoofInt.basesOdd_voight
#print axioms OddPerfect.SpoofInt.basesNontrivial_voight
#print axioms OddPerfect.SpoofInt.exponentsPos_voight
#print axioms OddPerfect.SpoofInt.pairwiseCoprime_voight
#print axioms OddPerfect.SpoofInt.prime_natAbs_voight
#print axioms OddPerfect.SpoofInt.not_basesPos_voight
#print axioms OddPerfect.SpoofInt.eulerPattern_voight
#print axioms OddPerfect.SpoofInt.not_eulerPatternAbs_voight
#print axioms OddPerfect.SpoofInt.even_geom_iff
#print axioms OddPerfect.SpoofInt.two_pow_countP_dvd_formalSigma
#print axioms OddPerfect.SpoofInt.odd_value
#print axioms OddPerfect.SpoofInt.four_dvd_formalSigma
#print axioms OddPerfect.SpoofInt.countP_odd_exponent_le_one
#print axioms OddPerfect.SpoofInt.value_voight_mod_four
#print axioms OddPerfect.SpoofInt.natAbs_value_voight_mod_four
#print axioms OddPerfect.SpoofInt.touchard_voight
#print axioms OddPerfect.SpoofInt.not_touchard_natAbs_voight
#print axioms OddPerfect.SpoofInt.mod_refined_voight
#print axioms OddPerfect.SpoofInt.not_mod_refined_natAbs_voight
#print axioms OddPerfect.SpoofInt.not_105_dvd_voight
#print axioms OddPerfect.SpoofInt.not_three_five_eleven_thirteen_voight
#print axioms OddPerfect.SpoofInt.five_le_card_primeFactors_voight
#print axioms OddPerfect.SpoofInt.nielsen_voight
#print axioms OddPerfect.SpoofInt.steuerwald_hyp_fails_voight
#print axioms OddPerfect.SpoofInt.exists_even_exponent_ge_four_voight
#print axioms OddPerfect.SpoofInt.mcdaniel_hyp_fails_voight
#print axioms OddPerfect.SpoofInt.components_voight
#print axioms OddPerfect.SpoofInt.two_adic_voight
#print axioms OddPerfect.SpoofInt.hamiltonian_cycle_voight
#print axioms OddPerfect.SpoofInt.three_adic_ledger_voight
#print axioms OddPerfect.SpoofInt.not_threeWeight_ledger_abs_voight
#print axioms OddPerfect.SpoofInt.threeWeight_ledger_signed_voight
#print axioms OddPerfect.SpoofInt.natAbs_list_prod
#print axioms OddPerfect.SpoofInt.valuation_balance
#print axioms OddPerfect.SpoofInt.valuation_balance_voight
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_append_iff
#print axioms OddPerfect.SpoofInt.sigma_eq_two_mul_add_div_iff_isSpoofPerfect
#print axioms OddPerfect.SpoofInt.div_lt_self_iff_one_lt
#print axioms OddPerfect.SpoofInt.isNearPerfectWith_iff_isSpoofPerfect
#print axioms OddPerfect.SpoofInt.prime_johnson
#print axioms OddPerfect.SpoofInt.nearPerfect_johnson
#print axioms OddPerfect.SpoofInt.isNearPerfectWith_johnson
#print axioms OddPerfect.SpoofInt.voight_eq_johnson
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_voight_of_johnson
#print axioms OddPerfect.SpoofInt.sigma_eq_two_mul_add_div_iff_isSpoofPerfect_nat
#print axioms OddPerfect.SpoofInt.isNearPerfectWith_iff_isSpoofPerfect_nat
#print axioms OddPerfect.SpoofInt.isNearPerfect_iff_exists_isSpoofPerfect
#print axioms OddPerfect.SpoofInt.sigma_120
#print axioms OddPerfect.SpoofInt.sigma_eq_two_mul_add_div_120
#print axioms OddPerfect.SpoofInt.not_isNearPerfectWith_120_120
#print axioms OddPerfect.SpoofInt.not_isNearPerfect_120
#print axioms OddPerfect.SpoofInt.abundancy_prime_pow_bounds
#print axioms OddPerfect.SpoofInt.formalFactor_neg_lt_one
#print axioms OddPerfect.SpoofInt.formalFactor_voight_lt_one
#print axioms OddPerfect.SpoofInt.formalFactor_neg_three_sq
#print axioms OddPerfect.SpoofInt.pow_lt_geom
#print axioms OddPerfect.SpoofInt.abundant_divisor_voight
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_byuFour
#print axioms OddPerfect.SpoofInt.basesOdd_byuFour
#print axioms OddPerfect.SpoofInt.eulerPattern_byuFour
#print axioms OddPerfect.SpoofInt.not_pairwiseCoprime_byuFour
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_byuTwo
#print axioms OddPerfect.SpoofInt.not_basesNontrivial_byuTwo
#print axioms OddPerfect.SpoofInt.isSpoofPerfect_descartes
