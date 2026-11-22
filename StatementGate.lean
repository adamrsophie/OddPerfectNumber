import OddPerfect

/-!
# Statement gate

Restates each headline theorem of the library, as listed on the theorems page of the project
site, in terms of the definitions of mathlib and core and the two project definitions
`OddPerfect` and `OddPerfectConjecture`, and proves each restatement by a direct reference to
the library theorem. Run after `lake build` with

    lake env lean StatementGate.lean

The command fails (nonzero exit status) if a restatement no longer matches its library
theorem up to definitional equality, or if the check at the end of the file finds a
restatement that mentions a project definition outside `allowedDefinitions`.

The file opens no namespace and uses no notation of the library. Every name is written in
full; `_root_` is put in front of `OddPerfect` and `Nat.Prime`, so that a declaration of the
library in another namespace cannot take their place. The `example`s fix the meaning of the
project definitions that the statements mention: `OddPerfect`, `OddPerfectConjecture`, and the
facts and states of the certificate checker. Nothing in the library imports this file.

The check at the end looks at every theorem `StatementGate.*` of the environment: each
constant in its statement must come from a module outside the library (`OddPerfect` and
`OddPerfect.*`) and outside this file, or be one of `allowedDefinitions`.
-/

/-! ## The project definitions -/

example (N : ℕ) : _root_.OddPerfect N ↔ Odd N ∧ Nat.Perfect N := Iff.rfl

example : _root_.OddPerfectConjecture ↔ ∀ N : ℕ, ¬ _root_.OddPerfect N := Iff.rfl

example (n : ℕ) :
    Nat.Perfect n ↔ Finset.sum (Nat.properDivisors n) (fun i => i) = n ∧ 0 < n := Iff.rfl

example (p e N : ℕ) :
    OddPerfect.Cert.Fact.Holds (OddPerfect.Cert.Fact.exact p e) N ↔ Nat.factorization N p = e :=
  Iff.rfl

example (p e N : ℕ) :
    OddPerfect.Cert.Fact.Holds (OddPerfect.Cert.Fact.powDvd p e) N ↔ p ^ e ∣ N := Iff.rfl

example (p N : ℕ) : OddPerfect.Cert.Fact.Holds (OddPerfect.Cert.Fact.notDvd p) N ↔ ¬ p ∣ N :=
  Iff.rfl

example (s : List OddPerfect.Cert.Fact) (N : ℕ) :
    OddPerfect.Cert.State.Holds s N ↔ ∀ f ∈ s, OddPerfect.Cert.Fact.Holds f N := Iff.rfl

/-! ## Size and number of prime factors -/

theorem StatementGate.lower_bound :
    ∀ {N : ℕ}, _root_.OddPerfect N → 10 ^ 79 < N :=
  @OddPerfect.LowerBound.lower_bound

theorem StatementGate.lt_two_pow_four_pow :
    ∀ {N : ℕ}, _root_.OddPerfect N → N < 2 ^ 4 ^ (Nat.primeFactors N).card :=
  @OddPerfect.lt_two_pow_four_pow

theorem StatementGate.five_le_card_primeFactors :
    ∀ {N : ℕ}, _root_.OddPerfect N → 5 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.five_le_card_primeFactors

theorem StatementGate.six_le_card_primeFactors :
    ∀ {N : ℕ}, _root_.OddPerfect N → 6 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.six_le_card_primeFactors

theorem StatementGate.seven_le_card_primeFactors :
    ∀ {N : ℕ}, _root_.OddPerfect N → 7 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.seven_le_card_primeFactors

theorem StatementGate.exists_prime_dvd_of_card_eq_six :
    ∀ {N : ℕ}, _root_.OddPerfect N → (Nat.primeFactors N).card = 6 →
      3 ∣ N ∧ 5 ∣ N ∧ ∃ p : ℕ, _root_.Nat.Prime p ∧ 11 ≤ p ∧ p ≤ 31 ∧ p ∣ N :=
  @OddPerfect.exists_prime_dvd_of_card_eq_six

theorem StatementGate.ten_le_card_primeFactors_of_not_three_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → 10 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.ten_le_card_primeFactors_of_not_three_dvd

theorem StatementGate.fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → ¬ 5 ∣ N → 15 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd

theorem StatementGate.sixteen_le_card_primeFactors_of_not_three_not_five :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → ¬ 5 ∣ N → 16 ≤ (Nat.primeFactors N).card :=
  @OddPerfect.sixteen_le_card_primeFactors_of_not_three_not_five

theorem StatementGate.three_mul_minFac_lt :
    ∀ {N : ℕ}, _root_.OddPerfect N → 3 * Nat.minFac N < 2 * (Nat.primeFactors N).card + 6 :=
  @OddPerfect.three_mul_minFac_lt

theorem StatementGate.card_primeFactors_le_of_equal_exponents :
    ∀ {N q β : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 2 * β) →
        (Nat.primeFactors N).card ≤ 4 * β ^ 2 + 2 * β + 3 :=
  @OddPerfect.card_primeFactors_le_of_equal_exponents

theorem StatementGate.lt_two_pow_four_pow_of_equal_exponents :
    ∀ {N q β : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 2 * β) →
        N < 2 ^ 4 ^ (4 * β ^ 2 + 2 * β + 3) :=
  @OddPerfect.lt_two_pow_four_pow_of_equal_exponents

theorem StatementGate.finite_setOf_equal_exponents :
    ∀ β : ℕ, Set.Finite {N : ℕ | _root_.OddPerfect N ∧ ∃ q : ℕ, _root_.Nat.Prime q ∧
      Odd (Nat.factorization N q) ∧
      ∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 2 * β} :=
  @OddPerfect.finite_setOf_equal_exponents

theorem StatementGate.twentyone_mul_omega_le :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      21 * ArithmeticFunction.cardDistinctFactors N ≤ 8 * ArithmeticFunction.cardFactors N + 39 :=
  @OddPerfect.twentyone_mul_omega_le

theorem StatementGate.eight_mul_omega_le_of_not_three_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N →
      8 * ArithmeticFunction.cardDistinctFactors N ≤ 3 * ArithmeticFunction.cardFactors N + 7 :=
  @OddPerfect.eight_mul_omega_le_of_not_three_dvd

theorem StatementGate.ninetynine_mul_omega_le :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      99 * ArithmeticFunction.cardDistinctFactors N ≤
        37 * ArithmeticFunction.cardFactors N + 187 :=
  @OddPerfect.ninetynine_mul_omega_le

theorem StatementGate.fiftyone_mul_omega_le_of_not_three_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N →
      51 * ArithmeticFunction.cardDistinctFactors N ≤
        19 * ArithmeticFunction.cardFactors N + 46 :=
  @OddPerfect.fiftyone_mul_omega_le_of_not_three_dvd

/-! ## Form of an odd perfect number and congruences -/

theorem StatementGate.exists_euler_form :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∃ q k m : ℕ,
      _root_.Nat.Prime q ∧ N = q ^ k * m ^ 2 ∧ ¬ q ∣ m ∧ q % 4 = 1 ∧ k % 4 = 1 :=
  @OddPerfect.exists_euler_form

theorem StatementGate.special_pow_lt_sq :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      Odd k → 3 * q ^ k < 2 * m ^ 2 :=
  @OddPerfect.special_pow_lt_sq

theorem StatementGate.special_lt_or_shape :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      q < m ∨ (k = 1 ∧ ∃ p : ℕ, _root_.Nat.Prime p ∧ p ∣ m ∧
        2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) ∧
        ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) = q ∧
        ArithmeticFunction.sigma 1 ((q + 1) / 2) = p ^ Nat.factorization N p) :=
  @OddPerfect.special_lt_or_shape

theorem StatementGate.mod_refined :
    ∀ {N : ℕ}, _root_.OddPerfect N → N % 12 = 1 ∨ N % 468 = 117 ∨ N % 324 = 81 :=
  @OddPerfect.mod_refined

theorem StatementGate.not_105_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 105 ∣ N :=
  @OddPerfect.not_105_dvd

theorem StatementGate.exists_mutual_quadratic_residues :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      ∃ p ∈ Nat.primeFactors N, ∃ r ∈ Nat.primeFactors N,
        p ≠ r ∧ jacobiSym (p : ℤ) r = 1 ∧ jacobiSym (r : ℤ) p = 1 :=
  @OddPerfect.exists_mutual_quadratic_residues

/-! ## Large prime factors -/

theorem StatementGate.exists_primeFactor_gt_200000 :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∃ p ∈ Nat.primeFactors N, 200000 < p :=
  @OddPerfect.exists_primeFactor_gt_200000

theorem StatementGate.exists_two_primeFactors_gt_72 :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      ∃ p ∈ Nat.primeFactors N, ∃ r ∈ Nat.primeFactors N, p ≠ r ∧ 72 < p ∧ 72 < r :=
  @OddPerfect.exists_two_primeFactors_gt_72

theorem StatementGate.largest_primeFactor_ne_40961 :
    ∀ {N : ℕ}, _root_.OddPerfect N → 40961 ∈ Nat.primeFactors N →
      ∃ r ∈ Nat.primeFactors N, 40961 < r :=
  @OddPerfect.largest_primeFactor_ne_40961

theorem StatementGate.largest_prime_sub_one_ne_two_pow :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {P : ℕ}, P ∈ Nat.primeFactors N →
      (∀ r ∈ Nat.primeFactors N, r ≤ P) → ∀ j : ℕ, P - 1 ≠ 2 ^ j :=
  @OddPerfect.largest_prime_sub_one_ne_two_pow

theorem StatementGate.largest_prime_ne_three_mul_four_pow :
    ∀ {N P t : ℕ}, _root_.OddPerfect N → P ∈ Nat.primeFactors N →
      (∀ r ∈ Nat.primeFactors N, r ≤ P) → 2 ≤ t → P ≠ 3 * 4 ^ t + 1 :=
  @OddPerfect.largest_prime_ne_three_mul_four_pow

theorem StatementGate.factorization_largest_le_sum_totient :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {P a m : ℕ}, P ∈ Nat.primeFactors N →
      (∀ r ∈ Nat.primeFactors N, r ≤ P) → P - 1 = 2 ^ a * m → Odd m →
        Nat.factorization N P ≤
          Finset.sum ((Nat.divisors m).erase 1) (fun d => Nat.totient d * (Nat.totient d - 1)) :=
  @OddPerfect.factorization_largest_le_sum_totient

theorem StatementGate.two_mul_factorization_add_three_le :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {p R : ℕ}, p ∈ Nat.primeFactors N →
      (∀ r ∈ Nat.primeFactors N, r ≤ R) → 2 * Nat.factorization N p + 3 ≤ R :=
  @OddPerfect.two_mul_factorization_add_three_le

/-! ## Reciprocal sums -/

theorem StatementGate.sum_inv_lt_log_two :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) < Real.log 2 :=
  @OddPerfect.sum_inv_lt_log_two

theorem StatementGate.sum_inv_gt_5960631_div_10000000 :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      (5960631 / 10000000 : ℝ) < Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) :=
  @OddPerfect.sum_inv_gt_5960631_div_10000000

theorem StatementGate.sum_inv_lt_677637_of_three_or_five :
    ∀ {N : ℕ}, _root_.OddPerfect N → 3 ∣ N ∨ 5 ∣ N →
      Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) < (677637 / 1000000 : ℝ) :=
  @OddPerfect.sum_inv_lt_677637_of_three_or_five

theorem StatementGate.sum_inv_lt_log_two_sub_of_seven_le :
    ∀ {N p₁ : ℕ}, _root_.OddPerfect N → p₁ ∈ Nat.primeFactors N →
      (∀ p ∈ Nat.primeFactors N, p₁ ≤ p) → 7 ≤ p₁ →
        Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) <
          Real.log 2 - 11 / (50 * (p₁ : ℝ) ^ 2) :=
  @OddPerfect.sum_inv_lt_log_two_sub_of_seven_le

/-! ## Exponent patterns: the special prime `q` with odd exponent and the others -/

theorem StatementGate.steuerwald :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 2) → False :=
  @OddPerfect.steuerwald

theorem StatementGate.not_all_exponents_four :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 4) → False :=
  @OddPerfect.not_all_exponents_four

theorem StatementGate.not_all_exponents_six :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 6) → False :=
  @OddPerfect.not_all_exponents_six

theorem StatementGate.not_all_exponents_ten :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 10) → False :=
  @OddPerfect.not_all_exponents_ten

theorem StatementGate.not_all_exponents_twelve :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 12) → False :=
  @OddPerfect.not_all_exponents_twelve

theorem StatementGate.mcdaniel :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p % 3 = 2) → False :=
  @OddPerfect.mcdaniel

theorem StatementGate.pow_four_dvd_of_dvd_succ :
    ∀ {N q t : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → t ∣ Nat.factorization N p + 1) → t ^ 4 ∣ N :=
  @OddPerfect.pow_four_dvd_of_dvd_succ

theorem StatementGate.pow_five_dvd_of_forall_dvd_succ :
    ∀ {N q t : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → t ∣ Nat.factorization N p + 1) → t ^ 5 ∣ N :=
  @OddPerfect.pow_five_dvd_of_forall_dvd_succ

theorem StatementGate.three_dvd_of_one_exception :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
        (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) → 3 ∣ N :=
  @OddPerfect.three_dvd_of_one_exception

theorem StatementGate.three_dvd_of_two_exceptions :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        3 ∣ N :=
  @OddPerfect.three_dvd_of_two_exceptions

theorem StatementGate.three_dvd_of_three_exceptions :
    ∀ {N q r₁ r₂ r₃ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q →
      Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ →
        Nat.factorization N p = 2) → 3 ∣ N :=
  @OddPerfect.three_dvd_of_three_exceptions

theorem StatementGate.three_dvd_of_three_mod_exceptions :
    ∀ {N q r₁ r₂ r₃ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q →
      Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ →
        3 ∣ Nat.factorization N p + 1) → 3 ∣ N :=
  @OddPerfect.three_dvd_of_three_mod_exceptions

theorem StatementGate.four_le_card_mod_exceptions :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      ¬ 3 ∣ N →
        4 ≤ (Finset.filter (fun p => ¬ 3 ∣ Nat.factorization N p + 1)
          ((Nat.primeFactors N).erase q)).card :=
  @OddPerfect.four_le_card_mod_exceptions

theorem StatementGate.five_le_card_mod_exceptions_of_thirteen :
    ∀ {N : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 13) → ¬ 3 ∣ N → 19 ∣ N →
      31 ∣ N →
        5 ≤ (Finset.filter (fun p => ¬ 3 ∣ Nat.factorization N p + 1)
          ((Nat.primeFactors N).erase 13)).card :=
  @OddPerfect.five_le_card_mod_exceptions_of_thirteen

theorem StatementGate.two_exceptions_five_three_cases :
    ∀ {N r₁ r₂ : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        Nat.factorization N 3 = 2 ∨ 6 ≤ Nat.factorization N 3 :=
  @OddPerfect.two_exceptions_five_three_cases

theorem StatementGate.two_exceptions_five_six_le_three :
    ∀ {N r₁ r₂ : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        6 ≤ Nat.factorization N 3 :=
  @OddPerfect.two_exceptions_five_six_le_three

theorem StatementGate.two_exceptions_three_ne_two_of_nine_dvd :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 3 = 2 → 9 ∣ ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        Nat.factorization N 3 ≠ 2 :=
  @OddPerfect.two_exceptions_three_ne_two_of_nine_dvd

theorem StatementGate.two_exceptions_three_pow_four :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q ≠ 5 → Nat.factorization N 3 = 4 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        (r₁ = 3 ∧ r₂ = 11 ∨ r₁ = 11 ∧ r₂ = 3) ∧ Even (Nat.factorization N 11) ∧
          6 ≤ Nat.factorization N 11 ∧ ¬ 3 ∣ Nat.factorization N 11 + 1 ∧
          ¬ 5 ∣ Nat.factorization N 11 + 1 :=
  @OddPerfect.two_exceptions_three_pow_four

theorem StatementGate.not_mixed_index_three_five_seven :
    ∀ {N : ℕ}, _root_.OddPerfect N → Nat.factorization N 3 = 2 → Nat.factorization N 5 = 1 →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 →
        3 ∣ Nat.factorization N p + 1 ∨ 5 ∣ Nat.factorization N p + 1 ∨
          7 ∣ Nat.factorization N p + 1) → False :=
  @OddPerfect.not_mixed_index_three_five_seven

theorem StatementGate.not_mixed_index_special_five :
    ∀ {N : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 →
        3 ∣ Nat.factorization N p + 1 ∨ 5 ∣ Nat.factorization N p + 1 ∨
          7 ∣ Nat.factorization N p + 1) → False :=
  @OddPerfect.MixedIndexThree.not_mixed_index_special_five

theorem StatementGate.exists_index_coprime_105 :
    ∀ {N : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      ∃ p ∈ Nat.primeFactors N, p ≠ 5 ∧ Nat.Coprime (Nat.factorization N p + 1) 105 :=
  @OddPerfect.MixedIndexThree.exists_index_coprime_105

theorem StatementGate.three_mul_card_le :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {q : ℕ}, _root_.Nat.Prime q →
      Odd (Nat.factorization N q) →
        3 * (Nat.primeFactors N).card ≤
          2 * (Finset.filter
            (fun x : ℕ × ℕ => x.2 ∣ ArithmeticFunction.sigma 1 (x.1 ^ Nat.factorization N x.1))
            (Nat.primeFactors N ×ˢ Nat.primeFactors N)).card + 3 :=
  @OddPerfect.three_mul_card_le

/-! ## Divisor sums of prime powers -/

theorem StatementGate.isSquare_sigma_prime_pow_iff :
    ∀ {p e : ℕ}, _root_.Nat.Prime p → p ≠ 2 → Even e → e ≠ 0 →
      (IsSquare (ArithmeticFunction.sigma 1 (p ^ e)) ↔ p = 3 ∧ e = 4) :=
  @OddPerfect.isSquare_sigma_prime_pow_iff

theorem StatementGate.three_dvd_of_thirtyone_exceptional_mod_three :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Finset.filter (fun p => ¬ 3 ∣ Nat.factorization N p + 1)
        ((Nat.primeFactors N).erase q)).card ≤ 31 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → ¬ 3 ∣ Nat.factorization N p + 1 → p % 3 = 2) →
        3 ∣ N :=
  @OddPerfect.three_dvd_of_thirtyone_exceptional_mod_three

theorem StatementGate.card_nine_dvd_le :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ q : ℕ,
      (Finset.filter (fun x => 9 ∣ Nat.factorization N x + 1)
        ((Nat.primeFactors N).erase q)).card ≤
      Finset.sum (Finset.filter (fun t => t % 3 = 1) ((Nat.primeFactors N).erase q))
        (fun t => Nat.factorization N t) :=
  @OddPerfect.card_nine_dvd_le

theorem StatementGate.five_le_card_exponents_of_sigma_prime :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        _root_.Nat.Prime (ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p))) →
      5 ≤ (Finset.image (fun p => Nat.factorization N p) ((Nat.primeFactors N).erase q)).card :=
  @OddPerfect.five_le_card_exponents_of_sigma_prime

theorem StatementGate.restrained_not_dvd_of_lt :
    ∀ {N q r p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      _root_.Nat.Prime p → 5 ≤ p → p < 132257 → ¬ p ∣ N :=
  @OddPerfect.restrained_not_dvd_of_lt

/-! ## The certificate checker -/

theorem StatementGate.cert_check_sound :
    ∀ {s : List OddPerfect.Cert.Fact} {c : OddPerfect.Cert.Cert},
      OddPerfect.Cert.check s c = true →
      ∀ N : ℕ, _root_.OddPerfect N → OddPerfect.Cert.State.Holds s N → False :=
  @OddPerfect.Cert.check_sound

/-! ## The check of the statements -/

namespace StatementGate

open Lean Elab Command

/-- The project definitions that the statements above may mention. -/
def allowedDefinitions : List Name :=
  [``OddPerfect, ``OddPerfectConjecture, ``OddPerfect.Cert.Fact,
    ``OddPerfect.Cert.Cert, ``OddPerfect.Cert.check, ``OddPerfect.Cert.State.Holds]

/-- Checks every theorem `StatementGate.*` of the environment (see the module docstring).
Throws an error listing every offending constant, or logs one summary line. -/
def check : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let fromLibraryOrHere (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some i => (`OddPerfect).isPrefixOf names[i.toNat]!
    | none => true
  let mut count := 0
  let mut errors : Array MessageData := #[]
  for (n, ci) in env.constants.toList do
    unless (`StatementGate).isPrefixOf n && ci matches .thmInfo _ do continue
    count := count + 1
    for c in ci.type.getUsedConstants do
      if fromLibraryOrHere c && !allowedDefinitions.contains c then
        errors := errors.push m!"{n}: mentions {c}, a project definition outside the allowed list"
  unless errors.isEmpty do
    throwError m!"statement gate FAILED ({errors.size} problems):\n" ++
      MessageData.joinSep errors.toList "\n"
  logInfo m!"statement gate OK: {count} restated theorems, project definitions mentioned \
    only from {", ".intercalate (allowedDefinitions.map toString)}"

end StatementGate

run_cmd StatementGate.check
