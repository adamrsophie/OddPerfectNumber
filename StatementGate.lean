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
restatement that mentions a project definition outside `allowedDefinitions`, or finds that the
restatements differ from the inventory `expected`.

The restatements of the two exception checker engine (`OddPerfect.TwoExcEngine`) mention its
parameters, family predicates, state meaning and checker; those definitions are in
`allowedDefinitions`, and the `example`s below pin the family predicates `Fam` and `FamV`, the
state meaning `Holds`, the deficient leaf statement `DefSound`, the guard `paramsOK` and the root
state `rootKeysV`, so that a later change of one of these definitions breaks this file.

The file opens no namespace and uses no notation of the library. Every name is written in
full; `_root_` is put in front of `OddPerfect` and `Nat.Prime`, so that a declaration of the
library in another namespace cannot take their place. The `example`s fix the meaning of the
project definitions that the statements mention: `OddPerfect`, `OddPerfectConjecture`, and the
facts and states of the certificate checker. Nothing in the library imports this file.

The check at the end looks at every theorem `StatementGate.*` of the environment: each
constant in its statement must come from a module outside the library (`OddPerfect` and
`OddPerfect.*`) and outside this file, or be one of `allowedDefinitions`. The theorems
`StatementGate.*` must be exactly the names of the inventory `expected`, and each must be
proved by the library theorem paired with it there, as the bare constant; no name occurs twice
in the inventory. Deleting a restatement or adding one without its inventory entry therefore
fails the check.
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

example (E N q : ℕ) :
    OddPerfect.TwoExcEngine.Fam E N q ↔
      _root_.OddPerfect N ∧ _root_.Nat.Prime q ∧ Odd (Nat.factorization N q) ∧
        Nat.factorization N 3 = 2 ∧
        (Finset.filter (fun p => p ≠ q ∧ Nat.factorization N p ≠ 2) (Nat.primeFactors N)).card ≤
          E := Iff.rfl

example (P : OddPerfect.TwoExcEngine.Params) (N q : ℕ) :
    OddPerfect.TwoExcEngine.FamV P N q ↔
      _root_.OddPerfect N ∧ _root_.Nat.Prime q ∧ Odd (Nat.factorization N q) ∧
        Nat.factorization N 3 = P.V3 ∧
        (Finset.filter (fun p => p ≠ q ∧ Nat.factorization N p ≠ 2) (Nat.primeFactors N)).card ≤
          P.E ∧ (3 : ℕ) ≠ q ∧
        (P.e4 = true → ∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ 3 → Nat.factorization N p ≠ 2 →
          Nat.factorization N p = 4) := Iff.rfl

example (P : OddPerfect.TwoExcEngine.Params) (N q : ℕ) (ks : List OddPerfect.TwoExcEngine.Key)
    (x : ℕ) :
    OddPerfect.TwoExcEngine.Holds P N q ks x ↔
      OddPerfect.TwoExcEngine.FamV P N q ∧
        (∀ k ∈ ks, OddPerfect.TwoExcEngine.KeyHolds N q ks k) ∧
        (List.map OddPerfect.TwoExcEngine.Key.p ks).Nodup ∧
        ∀ p, _root_.Nat.Prime p → p < x → p ∣ N → p ∈ List.map OddPerfect.TwoExcEngine.Key.p ks :=
  Iff.rfl

example (P : OddPerfect.TwoExcEngine.Params) :
    OddPerfect.TwoExcEngine.DefSound P ↔
      ∀ (ks : List OddPerfect.TwoExcEngine.Key) (x : ℕ) (dd : OddPerfect.TwoExcEngine.DefData)
        (N q : ℕ), OddPerfect.TwoExcEngine.deficientB P ks x dd = true →
          OddPerfect.TwoExcEngine.Holds P N q ks x → False := Iff.rfl

example (P : OddPerfect.TwoExcEngine.Params) :
    OddPerfect.TwoExcEngine.paramsOK P = true ↔ P.V3 = 2 ∨ (P.V3 % 2 = 0 ∧ 4 ≤ P.V3) := by
  simp [OddPerfect.TwoExcEngine.paramsOK, Nat.ble_eq]

example (P : OddPerfect.TwoExcEngine.Params) :
    OddPerfect.TwoExcEngine.rootKeysV P =
      [⟨3, cond (P.V3 == 2) .sq (.fr false (P.V3 + 1) false P.V3 true), []⟩] := rfl

/-! ## Size and number of prime factors -/

theorem StatementGate.lower_bound :
    ∀ {N : ℕ}, _root_.OddPerfect N → 10 ^ 150 < N :=
  @OddPerfect.LowerBoundTwo.lower_bound

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

theorem StatementGate.card_primeFactors_le_of_prime_pow_index :
    ∀ {N q l E : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime l → l ≠ 2 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → ∃ γ : ℕ, 1 ≤ γ ∧ Nat.factorization N p + 1 = l ^ γ) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p ≤ E) →
        (Nat.primeFactors N).card ≤ E ^ 2 + 2 * E + 3 :=
  @OddPerfect.card_primeFactors_le_of_prime_pow_index

theorem StatementGate.lt_two_pow_four_pow_of_prime_pow_index :
    ∀ {N q l E : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime l → l ≠ 2 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → ∃ γ : ℕ, 1 ≤ γ ∧ Nat.factorization N p + 1 = l ^ γ) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p ≤ E) →
        N < 2 ^ 4 ^ (E ^ 2 + 2 * E + 3) :=
  @OddPerfect.lt_two_pow_four_pow_of_prime_pow_index

theorem StatementGate.card_primeFactors_le_of_prime_pow_index_receivers :
    ∀ {N q l B : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime l → l ≠ 2 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → ∃ γ : ℕ, 1 ≤ γ ∧ Nat.factorization N p + 1 = l ^ γ) →
      Nat.factorization N l ≤ B →
      (∀ s ∈ Nat.primeFactors N, s ≠ q → s % l = 1 → Nat.factorization N s ≤ B) →
        (Nat.primeFactors N).card ≤ B ^ 2 + 2 * B + 2 :=
  @OddPerfect.card_primeFactors_le_of_prime_pow_index_receivers

theorem StatementGate.card_primeFactors_le_of_common_index :
    ∀ {N q l E : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime l → l ≠ 2 → q % l ≠ 1 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → l ∣ Nat.factorization N p + 1) →
      Nat.factorization N l ≤ E →
      (∀ r ∈ Nat.primeFactors N, r % l = 1 → Nat.factorization N r ≤ E) →
        (Nat.primeFactors N).card ≤ E ^ 2 + 1 :=
  @OddPerfect.card_primeFactors_le_of_common_index

theorem StatementGate.restrained_omega_ge :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        38049 ≤ ArithmeticFunction.cardDistinctFactors N :=
  @OddPerfect.restrained_omega_ge

theorem StatementGate.rad_pow_fourteen_lt :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      (Finset.prod (Nat.primeFactors N) (fun p => p)) ^ 14 < 2 ^ 14 * N ^ 9 :=
  @OddPerfect.rad_pow_fourteen_lt

theorem StatementGate.rad_pow_twentysix_lt :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      (Finset.prod (Nat.primeFactors N) (fun p => p)) ^ 26 < 2 ^ 26 * N ^ 17 :=
  @OddPerfect.rad_pow_twentysix_lt

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

theorem StatementGate.even_card_primeFactors_of_special_ge :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      m ≤ q → Even (Nat.primeFactors N).card :=
  @OddPerfect.even_card_primeFactors_of_special_ge

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

theorem StatementGate.sum_inv_gt_60470764_of_three_not_five :
    ∀ {N : ℕ}, _root_.OddPerfect N → 3 ∣ N → ¬ 5 ∣ N →
      (60470764 / 100000000 : ℝ) < Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) :=
  @OddPerfect.sum_inv_gt_60470764_of_three_not_five

theorem StatementGate.sum_inv_gt_64764966_of_five_not_three :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → 5 ∣ N →
      (64764966 / 100000000 : ℝ) < Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) :=
  @OddPerfect.sum_inv_gt_64764966_of_five_not_three

theorem StatementGate.sum_inv_gt_66747288_of_not_three_not_five :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → ¬ 5 ∣ N →
      (66747288 / 100000000 : ℝ) < Finset.sum (Nat.primeFactors N) (fun p => (1 : ℝ) / (p : ℝ)) :=
  @OddPerfect.sum_inv_gt_66747288_of_not_three_not_five

theorem StatementGate.prod_div_sub_one_le_two_add_of_seven_le :
    ∀ {N p₁ : ℕ}, _root_.OddPerfect N → p₁ ∈ Nat.primeFactors N →
      (∀ p ∈ Nat.primeFactors N, p₁ ≤ p) → 7 ≤ p₁ →
        Finset.prod (Nat.primeFactors N) (fun p => (p : ℝ) / ((p : ℝ) - 1)) ≤
          2 + 9 / (4 * (p₁ : ℝ) ^ 2) :=
  @OddPerfect.prod_div_sub_one_le_two_add_of_seven_le

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

theorem StatementGate.two_exceptions_five_normal_form :
    ∀ {N r₁ r₂ : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        ∃ s : ℕ, _root_.Nat.Prime s ∧ s ∈ Nat.primeFactors N ∧ s % 5 = 1 ∧
          5 ∣ Nat.factorization N s + 1 ∧
          (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ 3 → p ≠ s → Nat.factorization N p = 2) ∧
          Nat.Coprime (Nat.factorization N 3 + 1) 105 :=
  @OddPerfect.two_exceptions_five_normal_form

theorem StatementGate.two_exceptions_five_thirtysix_le_three :
    ∀ {N r₁ r₂ : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        36 ≤ Nat.factorization N 3 :=
  @OddPerfect.two_exceptions_five_thirtysix_le_three

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

theorem StatementGate.two_exceptions_three_pow_four_special_mod_twelve :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Nat.factorization N 3 = 4 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        q % 12 = 1 :=
  @OddPerfect.two_exceptions_three_pow_four_special_mod_twelve

theorem StatementGate.two_exceptions_three_ne_four :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        Nat.factorization N 3 ≠ 4 :=
  @OddPerfect.two_exceptions_three_ne_four

theorem StatementGate.exists_pow_four_dvd_of_three_sq :
    ∀ {N : ℕ}, _root_.OddPerfect N → Nat.factorization N 3 = 2 →
      ∃ p ∈ ({7, 13, 19, 31, 61, 97, 127, 331} : Finset ℕ), p ^ 4 ∣ N :=
  @OddPerfect.exists_pow_four_dvd_of_three_sq

theorem StatementGate.two_exceptions_three_ne_two :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        Nat.factorization N 3 ≠ 2 :=
  @OddPerfect.two_exceptions_three_ne_two

theorem StatementGate.two_exceptions_six_le_three :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        6 ≤ Nat.factorization N 3 :=
  @OddPerfect.two_exceptions_six_le_three

theorem StatementGate.two_exceptions_three_exceptional :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
        r₁ = 3 ∨ r₂ = 3 :=
  @OddPerfect.two_exceptions_three_exceptional

theorem StatementGate.exists_pow_four_dvd_of_three_pow_four :
    ∀ {N : ℕ}, _root_.OddPerfect N → Nat.factorization N 3 = 4 →
      ∃ p ∈ ({7, 11, 19, 31, 127, 5419} : Finset ℕ),
        p ^ 4 ∣ N ∧ ¬ 3 ∣ Nat.factorization N p + 1 :=
  @OddPerfect.exists_pow_four_dvd_of_three_pow_four

theorem StatementGate.exists_seven_mod_twelve_exception :
    ∀ {N q p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Nat.factorization N 3 ≤ 2 → p ∈ Nat.primeFactors N → (p % 12 = 5 ∨ p % 12 = 7) →
        3 ∣ Nat.factorization N p + 1 →
          ∃ r ∈ Nat.primeFactors N,
            r % 12 = 7 ∧ 4 ≤ Nat.factorization N r ∧ ¬ 3 ∣ Nat.factorization N r + 1 :=
  @OddPerfect.exists_seven_mod_twelve_exception

theorem StatementGate.special_index_witnesses :
    ∀ {N q l : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime l → l ≠ 2 →
        2 * padicValNat l (Nat.factorization N q + 1) +
            padicValNat l (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
          Nat.factorization N l +
            (Finset.filter (fun p => p ≠ q ∧ p % l = 1 ∧ ¬ l ∣ Nat.factorization N p + 1)
              (Nat.primeFactors N)).card :=
  @OddPerfect.special_index_witnesses

theorem StatementGate.four_exceptions_of_three_sq_of_nine_dvd :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Nat.factorization N 3 = 2 → 9 ∣ Nat.factorization N q + 1 →
        4 ≤ (Finset.filter (fun p => p ≠ q ∧ p % 3 = 1 ∧ 4 ≤ Nat.factorization N p)
          (Nat.primeFactors N)).card :=
  @OddPerfect.four_exceptions_of_three_sq_of_nine_dvd

theorem StatementGate.four_le_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      4 ≤ Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.four_le_excess

theorem StatementGate.four_le_cardFactors_sub :
    ∀ {N q a m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      ArithmeticFunction.cardDistinctFactors m + 4 ≤ ArithmeticFunction.cardFactors m :=
  @OddPerfect.four_le_cardFactors_sub

theorem StatementGate.two_mul_omega_add_special_le_Omega :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      2 * ArithmeticFunction.cardDistinctFactors N + Nat.factorization N q + 6 ≤
        ArithmeticFunction.cardFactors N :=
  @OddPerfect.two_mul_omega_add_special_le_Omega

theorem StatementGate.two_mul_omega_add_seven_le_Omega :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      2 * ArithmeticFunction.cardDistinctFactors N + 7 ≤ ArithmeticFunction.cardFactors N :=
  @OddPerfect.two_mul_omega_add_seven_le_Omega

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 3 = 2 →
      (Nat.primeFactors N).card + 2 *
        padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 5 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five

theorem StatementGate.card_primeFactors_le_five_excess_add_three :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 3 = 2 →
      (Nat.primeFactors N).card ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 3 :=
  @OddPerfect.card_primeFactors_le_five_excess_add_three

theorem StatementGate.cardDistinctFactors_le_five_mul_sub_add_three :
    ∀ {N q a m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      q % 3 = 2 →
      ArithmeticFunction.cardDistinctFactors N ≤
        5 * (ArithmeticFunction.cardFactors m - ArithmeticFunction.cardDistinctFactors m) + 3 :=
  @OddPerfect.cardDistinctFactors_le_five_mul_sub_add_three

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_escape :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card + 2 *
        padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) + 5 +
          (Finset.filter (fun p : ℕ => ∀ r ∈ (p ^ 2 + p + 1).primeFactors, r = 3 ∨ r = q)
            (Finset.filter (fun p => p ≠ q ∧ Nat.factorization N p = 2)
              (Nat.primeFactors N))).card :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_escape

theorem StatementGate.conditional_card_primeFactors_le_five_excess_add_six :
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = r ^ a → a = 1) →
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = 3 * r ^ a →
      a ≤ 2) →
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 6 :=
  @OddPerfect.conditional_card_primeFactors_le_five_excess_add_six

theorem StatementGate.conditional_finite_of_excess_le :
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = r ^ a → a = 1) →
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = 3 * r ^ a →
      a ≤ 2) →
    ∀ T : ℕ, {N : ℕ | ∃ q, _root_.OddPerfect N ∧ _root_.Nat.Prime q ∧
      Odd (Nat.factorization N q) ∧
      Finset.sum ((Nat.primeFactors N).erase q)
        (fun p => Nat.factorization N p / 2 - 1) ≤ T}.Finite :=
  @OddPerfect.conditional_finite_of_excess_le

theorem StatementGate.not_all_pure_common_index :
    ∀ {N q l : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime l → l ≠ 2 →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → l ∣ Nat.factorization N p + 1) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        ∃ r w, _root_.Nat.Prime r ∧
          ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) = r ^ w) → False :=
  @OddPerfect.not_all_pure_common_index

theorem StatementGate.three_cycle_excess_or_outside :
    ∀ {N r s t : ℕ}, _root_.OddPerfect N → r ∈ Nat.primeFactors N → s ∈ Nat.primeFactors N →
      t ∈ Nat.primeFactors N → r ≠ s → s ≠ t → t ≠ r → r % 12 = 7 → s % 12 = 7 → t % 12 = 7 →
      s ∣ r ^ 2 + r + 1 → t ∣ s ^ 2 + s + 1 → r ∣ t ^ 2 + t + 1 →
      (4 ≤ Nat.factorization N r ∨ 4 ≤ Nat.factorization N s ∨ 4 ≤ Nat.factorization N t) ∨
        ∃ u, _root_.Nat.Prime u ∧ u ≠ 3 ∧ u ≠ r ∧ u ≠ s ∧ u ≠ t ∧
          (u ∣ r ^ 2 + r + 1 ∨ u ∣ s ^ 2 + s + 1 ∨ u ∣ t ^ 2 + t + 1) :=
  @OddPerfect.three_cycle_excess_or_outside

theorem StatementGate.card_divisors_filter_three_add_le :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Finset.filter (fun d => 3 ∣ d) (Nat.divisors (Nat.factorization N q + 1))).card +
          padicValNat 3 (Nat.factorization N q + 1) ≤
        2 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 2 :=
  @OddPerfect.card_divisors_filter_three_add_le

theorem StatementGate.card_divisors_special_index_le_four_mul_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      3 ∣ Nat.factorization N q + 1 →
      (Nat.divisors (Nat.factorization N q + 1)).card ≤
        4 * Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.card_divisors_special_index_le_four_mul_excess

theorem StatementGate.orderOf_eq_of_geom_sum_eq_mul_prime_pow :
    ∀ {w m p k s : ℕ}, _root_.Nat.Prime p → p ≠ 2 → 2 ≤ w → m ≠ 0 → 1 ≤ s → k < p →
      Finset.sum (Finset.range m) (fun i => w ^ i) = k * p ^ s →
      orderOf (w : ZMod p) = m :=
  @OddPerfect.orderOf_eq_of_geom_sum_eq_mul_prime_pow

theorem StatementGate.gcd_phi3_prime_pair :
    ∀ {p q : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime q → 3 < p → 3 < q →
      p ∣ q ^ 2 + q + 1 → q ∣ p ^ 2 + p + 1 →
      ∃ m, Nat.gcd (p ^ 2 + p + 1) (q ^ 2 + q + 1) = 3 * 7 ^ m :=
  @OddPerfect.gcd_phi3_prime_pair

theorem StatementGate.not_dvd_sigma_of_dvd_special_succ :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r % 4 = 3 → r ∣ q + 1 →
      ¬ q ∣ ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) :=
  @OddPerfect.not_dvd_sigma_of_dvd_special_succ

theorem StatementGate.phi3_eq_mul_prime_pow_unique :
    ∀ {q : ℕ}, _root_.Nat.Prime q → q % 4 = 1 → ∀ {c : ℕ}, c = 1 ∨ c = 3 →
      ∀ {p p' j j' : ℕ}, Odd p → Odd p' → 1 ≤ j → 1 ≤ j' →
      p ^ 2 + p + 1 = c * q ^ j → p' ^ 2 + p' + 1 = c * q ^ j' → p = p' :=
  @OddPerfect.phi3_eq_mul_prime_pow_unique

theorem StatementGate.card_escapeRows_le_two :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Finset.filter (fun p : ℕ => ∀ r ∈ (p ^ 2 + p + 1).primeFactors, r = 3 ∨ r = q)
        (Finset.filter (fun p => p ≠ q ∧ Nat.factorization N p = 2)
          (Nat.primeFactors N))).card ≤ 2 :=
  @OddPerfect.card_escapeRows_le_two

theorem StatementGate.card_primeFactors_le_five_excess_add_seven :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 7 :=
  @OddPerfect.card_primeFactors_le_five_excess_add_seven

theorem StatementGate.lt_two_pow_four_pow_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      N < 2 ^ 4 ^ (5 * Finset.sum ((Nat.primeFactors N).erase q)
        (fun p => Nat.factorization N p / 2 - 1) + 7) :=
  @OddPerfect.lt_two_pow_four_pow_excess

theorem StatementGate.finite_of_excess_le :
    ∀ T : ℕ, {N : ℕ | ∃ q, _root_.OddPerfect N ∧ _root_.Nat.Prime q ∧
      Odd (Nat.factorization N q) ∧
      Finset.sum ((Nat.primeFactors N).erase q)
        (fun p => Nat.factorization N p / 2 - 1) ≤ T}.Finite :=
  @OddPerfect.finite_of_excess_le

theorem StatementGate.fermat_special_mul_le_excess :
    ∀ {N q k : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q = 2 ^ k + 1 → 5 ≤ q →
      (q - 3) / 2 * Nat.factorization N q ≤
        Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.fermat_special_mul_le_excess

theorem StatementGate.fermat_factor_excess_le :
    ∀ {N q F k : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime F → F = 2 ^ k + 1 → 5 ≤ F → F ≠ q → q % F ≠ 1 → q % F ≠ F - 1 → F ∣ N →
      (F - 2) * (Nat.factorization N F / 2 - 1) + (F - 3) ≤
        Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.fermat_factor_excess_le

theorem StatementGate.least_odd_factor_le_excess :
    ∀ {N q L : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ d, _root_.Nat.Prime d → d ≠ 2 → d ∣ q - 1 → L ≤ d) → L ≤ q →
      (L - 3) / 2 ≤
        Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.least_odd_factor_le_excess

theorem StatementGate.seven_mul_minFac_lt :
    ∀ {N : ℕ}, _root_.OddPerfect N → 7 * Nat.minFac N < 3 * (Nat.primeFactors N).card + 21 :=
  @OddPerfect.seven_mul_minFac_lt

theorem StatementGate.special_exponent_add_two_sq_dvd :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime (Nat.factorization N q + 2) → ¬ (Nat.factorization N q + 2) ∣ q - 1 →
      (Nat.factorization N q + 2) ^ 2 ∣ N :=
  @OddPerfect.special_exponent_add_two_sq_dvd

theorem StatementGate.perfect_eq_of_factorization_eq_on_common :
    ∀ {N N' : ℕ}, ArithmeticFunction.sigma 1 N = 2 * N →
      ArithmeticFunction.sigma 1 N' = 2 * N' → N ≠ 0 → N' ≠ 0 →
      (∃ p, _root_.Nat.Prime p ∧ p ∣ N ∧ p ∣ N') →
      (∀ p, _root_.Nat.Prime p → p ∣ N → p ∣ N' →
        Nat.factorization N p = Nat.factorization N' p) → N = N' :=
  @OddPerfect.perfect_eq_of_factorization_eq_on_common

theorem StatementGate.even_card_one_mod_four_iff :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Even (((Nat.primeFactors N).erase q).filter
        (fun p => p % 4 = 1 ∧ Nat.factorization N p % 4 = 2)).card ↔
        q % 8 = Nat.factorization N q % 8) :=
  @OddPerfect.even_card_one_mod_four_iff

theorem StatementGate.finite_oddPerfect_card_primeFactors_le :
    ∀ k : ℕ, {N : ℕ | _root_.OddPerfect N ∧ (Nat.primeFactors N).card ≤ k}.Finite :=
  @OddPerfect.finite_oddPerfect_card_primeFactors_le

theorem StatementGate.ncard_oddPerfect_card_primeFactors_le :
    ∀ k : ℕ, {N : ℕ | _root_.OddPerfect N ∧ (Nat.primeFactors N).card ≤ k}.ncard ≤
      4 ^ (k ^ 2) :=
  @OddPerfect.ncard_oddPerfect_card_primeFactors_le

theorem StatementGate.ncard_oddPerfect_excess_le :
    ∀ T : ℕ, {N : ℕ | ∃ q, _root_.OddPerfect N ∧ _root_.Nat.Prime q ∧
      Odd (Nat.factorization N q) ∧
      Finset.sum ((Nat.primeFactors N).erase q)
        (fun p => Nat.factorization N p / 2 - 1) ≤ T}.ncard ≤ 4 ^ ((5 * T + 7) ^ 2) :=
  @OddPerfect.ncard_oddPerfect_excess_le

theorem StatementGate.excessS1 :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Nat.factorization N 3 = 6 → (r ∈ Nat.primeFactors N → Nat.factorization N r = 4) →
        (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ 3 → p ≠ r → Nat.factorization N p = 2) → False :=
  @OddPerfect.excessS1

theorem StatementGate.excessS2a :
    ∀ {N q r₁ r₂ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Nat.factorization N 3 = 4 → (r₁ ∈ Nat.primeFactors N → Nat.factorization N r₁ = 4) →
        (r₂ ∈ Nat.primeFactors N → Nat.factorization N r₂ = 4) →
          (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ 3 → p ≠ r₁ → p ≠ r₂ →
            Nat.factorization N p = 2) → False :=
  @OddPerfect.excessS2a

theorem StatementGate.excessS2b :
    ∀ {N q r₁ r₂ r₃ : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q →
      Odd (Nat.factorization N q) → Nat.factorization N 3 = 2 →
        (r₁ ∈ Nat.primeFactors N → Nat.factorization N r₁ = 4) →
          (r₂ ∈ Nat.primeFactors N → Nat.factorization N r₂ = 4) →
            (r₃ ∈ Nat.primeFactors N → Nat.factorization N r₃ = 4) →
              (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ →
                Nat.factorization N p = 2) → False :=
  @OddPerfect.excessS2b

theorem StatementGate.two_exceptions_five_three_sq_thirteen_ne_two :
    ∀ {N r₁ r₂ : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 → p ≠ r₁ → p ≠ r₂ → Nat.factorization N p = 2) →
      Nat.factorization N 3 = 2 → Nat.factorization N 13 ≠ 2 :=
  @OddPerfect.two_exceptions_five_three_sq_thirteen_ne_two

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

theorem StatementGate.not_mixed_index_special_five_of_three :
    ∀ {N : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      (∀ p ∈ Nat.primeFactors N, p ≠ 5 →
        3 ∣ Nat.factorization N p + 1 ∨ 5 ∣ Nat.factorization N p + 1 ∨
          7 ∣ Nat.factorization N p + 1) →
      (3 ∣ Nat.factorization N 3 + 1 ∨ 5 ∣ Nat.factorization N 3 + 1) → False :=
  @OddPerfect.MixedIndexTwo.not_mixed_index_special_five_of_three

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

theorem StatementGate.eleven_le_card_exponents_of_sigma_prime :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        _root_.Nat.Prime (ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p))) →
      11 ≤ (Finset.image (fun p => Nat.factorization N p) ((Nat.primeFactors N).erase q)).card :=
  @OddPerfect.eleven_le_card_exponents_of_sigma_prime

theorem StatementGate.exists_prime_sigma_collision :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        _root_.Nat.Prime (ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p))) →
      ∃ s p r : ℕ, s ∈ Nat.primeFactors N ∧ s ≠ q ∧
        ArithmeticFunction.sigma 1 (s ^ Nat.factorization N s) = q ∧
        ¬ s ∣ ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q) ∧
        Even (Nat.factorization N s) ∧ 2 ≤ Nat.factorization N s ∧
        p ∈ Nat.primeFactors N ∧ p ≠ q ∧ r ∈ Nat.primeFactors N ∧ r ≠ q ∧ p ≠ r ∧
        ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) = s ∧
        ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = s ∧
        Nat.factorization N p ≠ Nat.factorization N r :=
  @OddPerfect.exists_prime_sigma_collision

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

theorem StatementGate.famV_of_fam :
    ∀ {P : OddPerfect.TwoExcEngine.Params} {N q : ℕ}, P.V3 = 2 ∧ P.e4 = false →
      OddPerfect.TwoExcEngine.Fam P.E N q → OddPerfect.TwoExcEngine.FamV P N q :=
  @OddPerfect.TwoExcEngine.famV_of_fam

theorem StatementGate.holds_rootV :
    ∀ {P : OddPerfect.TwoExcEngine.Params} {N q : ℕ}, OddPerfect.TwoExcEngine.paramsOK P = true →
      OddPerfect.TwoExcEngine.FamV P N q →
        OddPerfect.TwoExcEngine.Holds P N q (OddPerfect.TwoExcEngine.rootKeysV P) 5 :=
  @OddPerfect.TwoExcEngine.holds_rootV

theorem StatementGate.checkV_sound :
    ∀ {P : OddPerfect.TwoExcEngine.Params} {pr : ℕ → Bool}
      {done : List OddPerfect.TwoExcEngine.Key → ℕ → Bool},
      OddPerfect.TwoExcEngine.DefSound P → (∀ n : ℕ, pr n = true → _root_.Nat.Prime n) →
      (∀ (ks : List OddPerfect.TwoExcEngine.Key) (x N q : ℕ), done ks x = true →
        OddPerfect.TwoExcEngine.Holds P N q ks x → False) →
      (P.landed = true → P.E ≤ 2) → ∀ {c : OddPerfect.TwoExcEngine.Cert},
      OddPerfect.TwoExcEngine.checkV P pr done c = true → ∀ {N q : ℕ},
      OddPerfect.TwoExcEngine.FamV P N q → False :=
  @OddPerfect.TwoExcEngine.checkV_sound

theorem StatementGate.famV_of_named :
    ∀ {P : OddPerfect.TwoExcEngine.Params} {N q : ℕ} (rs : List ℕ),
      rs.length + (if P.V3 = 2 then 0 else 1) ≤ P.E → P.V3 % 2 = 0 → _root_.OddPerfect N →
      _root_.Nat.Prime q → Odd (Nat.factorization N q) → Nat.factorization N 3 = P.V3 →
      (∀ r ∈ rs, r ∈ Nat.primeFactors N → Nat.factorization N r = 4) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ 3 → p ∉ rs → Nat.factorization N p = 2) →
        OddPerfect.TwoExcEngine.FamV P N q :=
  @OddPerfect.TwoExcEngine.famV_of_named

/-! ## The check of the statements -/

namespace StatementGate

open Lean Elab Command

/-- The project definitions that the statements above may mention. -/
def allowedDefinitions : List Name :=
  [``OddPerfect, ``OddPerfectConjecture, ``OddPerfect.Cert.Fact,
    ``OddPerfect.Cert.Cert, ``OddPerfect.Cert.check, ``OddPerfect.Cert.State.Holds,
    ``OddPerfect.TwoExcEngine.Params, ``OddPerfect.TwoExcEngine.Params.E,
    ``OddPerfect.TwoExcEngine.Params.V3, ``OddPerfect.TwoExcEngine.Params.e4,
    ``OddPerfect.TwoExcEngine.Params.landed, ``OddPerfect.TwoExcEngine.Key,
    ``OddPerfect.TwoExcEngine.Cert, ``OddPerfect.TwoExcEngine.Fam,
    ``OddPerfect.TwoExcEngine.FamV, ``OddPerfect.TwoExcEngine.Holds,
    ``OddPerfect.TwoExcEngine.DefSound, ``OddPerfect.TwoExcEngine.paramsOK,
    ``OddPerfect.TwoExcEngine.rootKeysV, ``OddPerfect.TwoExcEngine.checkV]

/-- The inventory: every restatement of this file, paired with the library theorem that proves
it. The check requires the theorems `StatementGate.*` to be exactly the first components, each
proved by the second component alone; a restatement removed from the file, or added without
an entry here, fails the check. -/
def expected : List (Name × Name) :=
  [(`StatementGate.lower_bound, ``OddPerfect.LowerBoundTwo.lower_bound),
    (`StatementGate.lt_two_pow_four_pow, ``OddPerfect.lt_two_pow_four_pow),
    (`StatementGate.five_le_card_primeFactors, ``OddPerfect.five_le_card_primeFactors),
    (`StatementGate.six_le_card_primeFactors, ``OddPerfect.six_le_card_primeFactors),
    (`StatementGate.seven_le_card_primeFactors, ``OddPerfect.seven_le_card_primeFactors),
    (`StatementGate.exists_prime_dvd_of_card_eq_six, ``OddPerfect.exists_prime_dvd_of_card_eq_six),
    (`StatementGate.ten_le_card_primeFactors_of_not_three_dvd,
      ``OddPerfect.ten_le_card_primeFactors_of_not_three_dvd),
    (`StatementGate.fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd,
      ``OddPerfect.fifteen_le_card_primeFactors_of_not_three_dvd_of_not_five_dvd),
    (`StatementGate.sixteen_le_card_primeFactors_of_not_three_not_five,
      ``OddPerfect.sixteen_le_card_primeFactors_of_not_three_not_five),
    (`StatementGate.three_mul_minFac_lt, ``OddPerfect.three_mul_minFac_lt),
    (`StatementGate.card_primeFactors_le_of_equal_exponents,
      ``OddPerfect.card_primeFactors_le_of_equal_exponents),
    (`StatementGate.lt_two_pow_four_pow_of_equal_exponents,
      ``OddPerfect.lt_two_pow_four_pow_of_equal_exponents),
    (`StatementGate.finite_setOf_equal_exponents, ``OddPerfect.finite_setOf_equal_exponents),
    (`StatementGate.card_primeFactors_le_of_prime_pow_index,
      ``OddPerfect.card_primeFactors_le_of_prime_pow_index),
    (`StatementGate.lt_two_pow_four_pow_of_prime_pow_index,
      ``OddPerfect.lt_two_pow_four_pow_of_prime_pow_index),
    (`StatementGate.card_primeFactors_le_of_prime_pow_index_receivers,
      ``OddPerfect.card_primeFactors_le_of_prime_pow_index_receivers),
    (`StatementGate.card_primeFactors_le_of_common_index,
      ``OddPerfect.card_primeFactors_le_of_common_index),
    (`StatementGate.restrained_omega_ge, ``OddPerfect.restrained_omega_ge),
    (`StatementGate.rad_pow_fourteen_lt, ``OddPerfect.rad_pow_fourteen_lt),
    (`StatementGate.rad_pow_twentysix_lt, ``OddPerfect.rad_pow_twentysix_lt),
    (`StatementGate.twentyone_mul_omega_le, ``OddPerfect.twentyone_mul_omega_le),
    (`StatementGate.eight_mul_omega_le_of_not_three_dvd,
      ``OddPerfect.eight_mul_omega_le_of_not_three_dvd),
    (`StatementGate.ninetynine_mul_omega_le, ``OddPerfect.ninetynine_mul_omega_le),
    (`StatementGate.fiftyone_mul_omega_le_of_not_three_dvd,
      ``OddPerfect.fiftyone_mul_omega_le_of_not_three_dvd),
    (`StatementGate.exists_euler_form, ``OddPerfect.exists_euler_form),
    (`StatementGate.special_pow_lt_sq, ``OddPerfect.special_pow_lt_sq),
    (`StatementGate.special_lt_or_shape, ``OddPerfect.special_lt_or_shape),
    (`StatementGate.even_card_primeFactors_of_special_ge,
      ``OddPerfect.even_card_primeFactors_of_special_ge),
    (`StatementGate.mod_refined, ``OddPerfect.mod_refined),
    (`StatementGate.not_105_dvd, ``OddPerfect.not_105_dvd),
    (`StatementGate.exists_mutual_quadratic_residues,
      ``OddPerfect.exists_mutual_quadratic_residues),
    (`StatementGate.exists_primeFactor_gt_200000, ``OddPerfect.exists_primeFactor_gt_200000),
    (`StatementGate.exists_two_primeFactors_gt_72, ``OddPerfect.exists_two_primeFactors_gt_72),
    (`StatementGate.largest_primeFactor_ne_40961, ``OddPerfect.largest_primeFactor_ne_40961),
    (`StatementGate.largest_prime_sub_one_ne_two_pow,
      ``OddPerfect.largest_prime_sub_one_ne_two_pow),
    (`StatementGate.largest_prime_ne_three_mul_four_pow,
      ``OddPerfect.largest_prime_ne_three_mul_four_pow),
    (`StatementGate.factorization_largest_le_sum_totient,
      ``OddPerfect.factorization_largest_le_sum_totient),
    (`StatementGate.two_mul_factorization_add_three_le,
      ``OddPerfect.two_mul_factorization_add_three_le),
    (`StatementGate.sum_inv_lt_log_two, ``OddPerfect.sum_inv_lt_log_two),
    (`StatementGate.sum_inv_gt_5960631_div_10000000, ``OddPerfect.sum_inv_gt_5960631_div_10000000),
    (`StatementGate.sum_inv_lt_677637_of_three_or_five,
      ``OddPerfect.sum_inv_lt_677637_of_three_or_five),
    (`StatementGate.sum_inv_lt_log_two_sub_of_seven_le,
      ``OddPerfect.sum_inv_lt_log_two_sub_of_seven_le),
    (`StatementGate.sum_inv_gt_60470764_of_three_not_five,
      ``OddPerfect.sum_inv_gt_60470764_of_three_not_five),
    (`StatementGate.sum_inv_gt_64764966_of_five_not_three,
      ``OddPerfect.sum_inv_gt_64764966_of_five_not_three),
    (`StatementGate.sum_inv_gt_66747288_of_not_three_not_five,
      ``OddPerfect.sum_inv_gt_66747288_of_not_three_not_five),
    (`StatementGate.prod_div_sub_one_le_two_add_of_seven_le,
      ``OddPerfect.prod_div_sub_one_le_two_add_of_seven_le),
    (`StatementGate.steuerwald, ``OddPerfect.steuerwald),
    (`StatementGate.not_all_exponents_four, ``OddPerfect.not_all_exponents_four),
    (`StatementGate.not_all_exponents_six, ``OddPerfect.not_all_exponents_six),
    (`StatementGate.not_all_exponents_ten, ``OddPerfect.not_all_exponents_ten),
    (`StatementGate.not_all_exponents_twelve, ``OddPerfect.not_all_exponents_twelve),
    (`StatementGate.mcdaniel, ``OddPerfect.mcdaniel),
    (`StatementGate.pow_four_dvd_of_dvd_succ, ``OddPerfect.pow_four_dvd_of_dvd_succ),
    (`StatementGate.pow_five_dvd_of_forall_dvd_succ, ``OddPerfect.pow_five_dvd_of_forall_dvd_succ),
    (`StatementGate.three_dvd_of_one_exception, ``OddPerfect.three_dvd_of_one_exception),
    (`StatementGate.three_dvd_of_two_exceptions, ``OddPerfect.three_dvd_of_two_exceptions),
    (`StatementGate.three_dvd_of_three_exceptions, ``OddPerfect.three_dvd_of_three_exceptions),
    (`StatementGate.three_dvd_of_three_mod_exceptions,
      ``OddPerfect.three_dvd_of_three_mod_exceptions),
    (`StatementGate.four_le_card_mod_exceptions, ``OddPerfect.four_le_card_mod_exceptions),
    (`StatementGate.five_le_card_mod_exceptions_of_thirteen,
      ``OddPerfect.five_le_card_mod_exceptions_of_thirteen),
    (`StatementGate.two_exceptions_five_three_cases, ``OddPerfect.two_exceptions_five_three_cases),
    (`StatementGate.two_exceptions_five_six_le_three,
      ``OddPerfect.two_exceptions_five_six_le_three),
    (`StatementGate.two_exceptions_five_normal_form, ``OddPerfect.two_exceptions_five_normal_form),
    (`StatementGate.two_exceptions_five_thirtysix_le_three,
      ``OddPerfect.two_exceptions_five_thirtysix_le_three),
    (`StatementGate.two_exceptions_three_ne_two_of_nine_dvd,
      ``OddPerfect.two_exceptions_three_ne_two_of_nine_dvd),
    (`StatementGate.two_exceptions_three_pow_four, ``OddPerfect.two_exceptions_three_pow_four),
    (`StatementGate.two_exceptions_three_pow_four_special_mod_twelve,
      ``OddPerfect.two_exceptions_three_pow_four_special_mod_twelve),
    (`StatementGate.two_exceptions_three_ne_four, ``OddPerfect.two_exceptions_three_ne_four),
    (`StatementGate.exists_pow_four_dvd_of_three_sq,
      ``OddPerfect.exists_pow_four_dvd_of_three_sq),
    (`StatementGate.two_exceptions_three_ne_two, ``OddPerfect.two_exceptions_three_ne_two),
    (`StatementGate.two_exceptions_six_le_three, ``OddPerfect.two_exceptions_six_le_three),
    (`StatementGate.two_exceptions_three_exceptional,
      ``OddPerfect.two_exceptions_three_exceptional),
    (`StatementGate.exists_pow_four_dvd_of_three_pow_four,
      ``OddPerfect.exists_pow_four_dvd_of_three_pow_four),
    (`StatementGate.exists_seven_mod_twelve_exception,
      ``OddPerfect.exists_seven_mod_twelve_exception),
    (`StatementGate.special_index_witnesses, ``OddPerfect.special_index_witnesses),
    (`StatementGate.four_exceptions_of_three_sq_of_nine_dvd,
      ``OddPerfect.four_exceptions_of_three_sq_of_nine_dvd),
    (`StatementGate.four_le_excess, ``OddPerfect.four_le_excess),
    (`StatementGate.four_le_cardFactors_sub, ``OddPerfect.four_le_cardFactors_sub),
    (`StatementGate.two_mul_omega_add_special_le_Omega,
      ``OddPerfect.two_mul_omega_add_special_le_Omega),
    (`StatementGate.two_mul_omega_add_seven_le_Omega,
      ``OddPerfect.two_mul_omega_add_seven_le_Omega),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five),
    (`StatementGate.card_primeFactors_le_five_excess_add_three,
      ``OddPerfect.card_primeFactors_le_five_excess_add_three),
    (`StatementGate.cardDistinctFactors_le_five_mul_sub_add_three,
      ``OddPerfect.cardDistinctFactors_le_five_mul_sub_add_three),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_escape,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_escape),
    (`StatementGate.conditional_card_primeFactors_le_five_excess_add_six,
      ``OddPerfect.conditional_card_primeFactors_le_five_excess_add_six),
    (`StatementGate.conditional_finite_of_excess_le,
      ``OddPerfect.conditional_finite_of_excess_le),
    (`StatementGate.not_all_pure_common_index,
      ``OddPerfect.not_all_pure_common_index),
    (`StatementGate.three_cycle_excess_or_outside,
      ``OddPerfect.three_cycle_excess_or_outside),
    (`StatementGate.card_divisors_filter_three_add_le,
      ``OddPerfect.card_divisors_filter_three_add_le),
    (`StatementGate.card_divisors_special_index_le_four_mul_excess,
      ``OddPerfect.card_divisors_special_index_le_four_mul_excess),
    (`StatementGate.orderOf_eq_of_geom_sum_eq_mul_prime_pow,
      ``OddPerfect.orderOf_eq_of_geom_sum_eq_mul_prime_pow),
    (`StatementGate.gcd_phi3_prime_pair,
      ``OddPerfect.gcd_phi3_prime_pair),
    (`StatementGate.not_dvd_sigma_of_dvd_special_succ,
      ``OddPerfect.not_dvd_sigma_of_dvd_special_succ),
    (`StatementGate.phi3_eq_mul_prime_pow_unique,
      ``OddPerfect.phi3_eq_mul_prime_pow_unique),
    (`StatementGate.card_escapeRows_le_two,
      ``OddPerfect.card_escapeRows_le_two),
    (`StatementGate.card_primeFactors_le_five_excess_add_seven,
      ``OddPerfect.card_primeFactors_le_five_excess_add_seven),
    (`StatementGate.lt_two_pow_four_pow_excess,
      ``OddPerfect.lt_two_pow_four_pow_excess),
    (`StatementGate.finite_of_excess_le,
      ``OddPerfect.finite_of_excess_le),
    (`StatementGate.fermat_special_mul_le_excess,
      ``OddPerfect.fermat_special_mul_le_excess),
    (`StatementGate.fermat_factor_excess_le,
      ``OddPerfect.fermat_factor_excess_le),
    (`StatementGate.least_odd_factor_le_excess,
      ``OddPerfect.least_odd_factor_le_excess),
    (`StatementGate.seven_mul_minFac_lt,
      ``OddPerfect.seven_mul_minFac_lt),
    (`StatementGate.special_exponent_add_two_sq_dvd,
      ``OddPerfect.special_exponent_add_two_sq_dvd),
    (`StatementGate.perfect_eq_of_factorization_eq_on_common,
      ``OddPerfect.perfect_eq_of_factorization_eq_on_common),
    (`StatementGate.even_card_one_mod_four_iff,
      ``OddPerfect.even_card_one_mod_four_iff),
    (`StatementGate.finite_oddPerfect_card_primeFactors_le,
      ``OddPerfect.finite_oddPerfect_card_primeFactors_le),
    (`StatementGate.ncard_oddPerfect_card_primeFactors_le,
      ``OddPerfect.ncard_oddPerfect_card_primeFactors_le),
    (`StatementGate.ncard_oddPerfect_excess_le,
      ``OddPerfect.ncard_oddPerfect_excess_le),
    (`StatementGate.excessS1, ``OddPerfect.excessS1),
    (`StatementGate.excessS2a, ``OddPerfect.excessS2a),
    (`StatementGate.excessS2b, ``OddPerfect.excessS2b),
    (`StatementGate.two_exceptions_five_three_sq_thirteen_ne_two,
      ``OddPerfect.two_exceptions_five_three_sq_thirteen_ne_two),
    (`StatementGate.not_mixed_index_three_five_seven,
      ``OddPerfect.not_mixed_index_three_five_seven),
    (`StatementGate.not_mixed_index_special_five,
      ``OddPerfect.MixedIndexThree.not_mixed_index_special_five),
    (`StatementGate.not_mixed_index_special_five_of_three,
      ``OddPerfect.MixedIndexTwo.not_mixed_index_special_five_of_three),
    (`StatementGate.exists_index_coprime_105,
      ``OddPerfect.MixedIndexThree.exists_index_coprime_105),
    (`StatementGate.three_mul_card_le, ``OddPerfect.three_mul_card_le),
    (`StatementGate.isSquare_sigma_prime_pow_iff, ``OddPerfect.isSquare_sigma_prime_pow_iff),
    (`StatementGate.three_dvd_of_thirtyone_exceptional_mod_three,
      ``OddPerfect.three_dvd_of_thirtyone_exceptional_mod_three),
    (`StatementGate.card_nine_dvd_le, ``OddPerfect.card_nine_dvd_le),
    (`StatementGate.five_le_card_exponents_of_sigma_prime,
      ``OddPerfect.five_le_card_exponents_of_sigma_prime),
    (`StatementGate.eleven_le_card_exponents_of_sigma_prime,
      ``OddPerfect.eleven_le_card_exponents_of_sigma_prime),
    (`StatementGate.exists_prime_sigma_collision, ``OddPerfect.exists_prime_sigma_collision),
    (`StatementGate.restrained_not_dvd_of_lt, ``OddPerfect.restrained_not_dvd_of_lt),
    (`StatementGate.cert_check_sound, ``OddPerfect.Cert.check_sound),
    (`StatementGate.famV_of_fam, ``OddPerfect.TwoExcEngine.famV_of_fam),
    (`StatementGate.holds_rootV, ``OddPerfect.TwoExcEngine.holds_rootV),
    (`StatementGate.checkV_sound, ``OddPerfect.TwoExcEngine.checkV_sound),
    (`StatementGate.famV_of_named, ``OddPerfect.TwoExcEngine.famV_of_named)]

/-- Checks every theorem `StatementGate.*` of the environment against the inventory `exp` and
the allowed list (see the module docstring). Throws an error listing every problem, or logs one
summary line. The controls in `GateControls/` call it with a changed inventory. -/
def checkWith (exp : List (Name × Name)) : CommandElabM Unit := do
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
    unless exp.any (·.1 == n) do
      errors := errors.push m!"{n}: restated but not in the expected list"
  for n in (exp.map (·.1)).eraseDups do
    if (exp.map (·.1)).count n > 1 then
      errors := errors.push m!"{n}: occurs more than once in the expected list"
  for n in (exp.map (·.2)).eraseDups do
    if (exp.map (·.2)).count n > 1 then
      errors := errors.push m!"{n}: paired with more than one restatement in the expected list"
  for (g, l) in exp.eraseDups do
    match env.find? g with
    | some (.thmInfo v) =>
      match v.value with
      | .const c _ =>
        unless c == l do
          errors := errors.push m!"{g}: proved by {c}, expected {l}"
      | _ => errors := errors.push m!"{g}: not proved by the library theorem {l} alone"
    | _ => errors := errors.push m!"{g}: expected restatement of {l} is missing"
  unless errors.isEmpty do
    throwError m!"statement gate FAILED ({errors.size} problems):\n" ++
      MessageData.joinSep errors.toList "\n"
  logInfo m!"statement gate OK: {count} restated theorems, exactly those of the expected list, \
    each proved by its library theorem; project definitions mentioned only from \
    {", ".intercalate (allowedDefinitions.map toString)}"

/-- The check with the inventory of this file. -/
def check : CommandElabM Unit := checkWith expected

end StatementGate

run_cmd StatementGate.check
