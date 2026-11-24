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

The restatements about the distance from a prime factor mention `OddPerfect.ball`, the set of
prime factors reached from a prime `r` in a given number of steps, where a step goes from `p`
to the prime factors of `N` that divide the divisor sum of the power of `p` in `N`. It is in
`allowedDefinitions`, and two `example`s below pin its two defining equations.

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

example (N r : ℕ) : OddPerfect.ball N r 0 = {r} := rfl

example (N r i : ℕ) :
    OddPerfect.ball N r (i + 1) = OddPerfect.ball N r i ∪
      Finset.filter (fun t => ∃ p ∈ OddPerfect.ball N r i,
        t ∣ ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p)) (Nat.primeFactors N) := rfl

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

theorem StatementGate.finite_oddPerfect_le :
    ∀ x : ℕ, {N : ℕ | _root_.OddPerfect N ∧ N ≤ x}.Finite :=
  @OddPerfect.finite_oddPerfect_le

theorem StatementGate.ncard_oddPerfect_le_sqrt :
    ∀ x : ℕ, {N : ℕ | _root_.OddPerfect N ∧ N ≤ x}.ncard ≤ Nat.sqrt (x / 5) :=
  @OddPerfect.ncard_oddPerfect_le_sqrt

theorem StatementGate.factorization_mod_three_ne_two_of_not_three_dvd :
    ∀ {N p : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → _root_.Nat.Prime p → p ∣ N → p % 3 = 1 →
      Nat.factorization N p % 3 ≠ 2 :=
  @OddPerfect.factorization_mod_three_ne_two_of_not_three_dvd

theorem StatementGate.even_factorization_of_mod_three_eq_two_of_not_three_dvd :
    ∀ {N p : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N → _root_.Nat.Prime p → p ∣ N → p % 3 = 2 →
      Even (Nat.factorization N p) :=
  @OddPerfect.even_factorization_of_mod_three_eq_two_of_not_three_dvd

theorem StatementGate.odd_card_one_mod_three_of_not_three_dvd :
    ∀ {N : ℕ}, _root_.OddPerfect N → ¬ 3 ∣ N →
      Odd ((Nat.primeFactors N).filter
        (fun p => p % 3 = 1 ∧ Nat.factorization N p % 3 = 1)).card :=
  @OddPerfect.odd_card_one_mod_three_of_not_three_dvd

theorem StatementGate.exists_high_pure_row_of_le_special :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      m ≤ q →
      ∃ r p w : ℕ, _root_.Nat.Prime r ∧ r ≠ 2 ∧ _root_.Nat.Prime p ∧ r ∣ N ∧ p ∣ N ∧ r ≠ p ∧
        r ≠ q ∧ p ≠ q ∧ Odd w ∧ 3 ≤ w ∧
        ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = p ^ w ∧
        ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) = q :=
  @OddPerfect.exists_high_pure_row_of_le_special

theorem StatementGate.special_lt_of_noHighPureRow :
    (∀ r p g w : ℕ, _root_.Nat.Prime r → r ≠ 2 → _root_.Nat.Prime p → Even g → g ≠ 0 →
      ArithmeticFunction.sigma 1 (r ^ g) = p ^ w → w ≤ 2) →
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      q < m :=
  @OddPerfect.special_lt_of_noHighPureRow

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_six :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 6 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_six

theorem StatementGate.card_primeFactors_le_five_excess_add_two_of_not_three_dvd :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      ¬ 3 ∣ N →
      (Nat.primeFactors N).card ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 2 :=
  @OddPerfect.card_primeFactors_le_five_excess_add_two_of_not_three_dvd

theorem StatementGate.lt_two_pow_four_pow_excess_add_six :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      N < 2 ^ 4 ^ (5 * Finset.sum ((Nat.primeFactors N).erase q)
        (fun p => Nat.factorization N p / 2 - 1) + 6) :=
  @OddPerfect.lt_two_pow_four_pow_excess_add_six

theorem StatementGate.phi3_both_shapes_mod_eight :
    ∀ {q : ℕ}, _root_.Nat.Prime q → q % 4 = 1 → ∀ {p p' n m : ℕ}, Odd p → Odd p' → 1 ≤ n →
      1 ≤ m → p ^ 2 + p + 1 = q ^ n → p' ^ 2 + p' + 1 = 3 * q ^ m → q % 8 = 5 :=
  @OddPerfect.phi3_both_shapes_mod_eight

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 24 ≠ 13 →
      (Nat.primeFactors N).card +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 5 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne

theorem StatementGate.card_escapeRows_le_one :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 24 ≠ 13 →
      (Finset.filter (fun p : ℕ => ∀ r ∈ (p ^ 2 + p + 1).primeFactors, r = 3 ∨ r = q)
        (Finset.filter (fun p => p ≠ q ∧ Nat.factorization N p = 2)
          (Nat.primeFactors N))).card ≤ 1 :=
  @OddPerfect.card_escapeRows_le_one

theorem StatementGate.two_sq_ne_one_add_sigma_of_lt_sixteen :
    ∀ {p e t : ℕ}, _root_.Nat.Prime p → p ≠ 2 → Odd t → Even e → 0 < e →
      _root_.Nat.Prime (e + 1) → e < 16 → 2 * t ^ 2 ≠ 1 + ArithmeticFunction.sigma 1 (p ^ e) :=
  @OddPerfect.two_sq_ne_one_add_sigma_of_lt_sixteen

theorem StatementGate.sixteen_le_exponent_of_le_special :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      m ≤ q → ∃ p : ℕ, _root_.Nat.Prime p ∧ p ∣ m ∧
        ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) = q ∧
        16 ≤ Nat.factorization N p :=
  @OddPerfect.sixteen_le_exponent_of_le_special

theorem StatementGate.nagellPrimePower_of_highPrimeExponent :
    (∀ p y ℓ : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime ℓ → 5 ≤ ℓ → p ^ 2 + p + 1 ≠ y ^ ℓ) →
      ∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = r ^ a →
        a = 1 :=
  @OddPerfect.nagellPrimePower_of_highPrimeExponent

theorem StatementGate.phi3_prime_pow_exponent :
    ∀ {p r a : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime r → p ^ 2 + p + 1 = r ^ a →
      a = 1 ∨ (5 ≤ a ∧ ∀ ℓ, _root_.Nat.Prime ℓ → ℓ ∣ a → 5 ≤ ℓ) :=
  @OddPerfect.phi3_prime_pow_exponent

theorem StatementGate.orderOf_dvd_weight_of_shape :
    ∀ {N q m p r w : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
      _root_.Nat.Prime r → r ∣ (q + 1) / 2 →
      ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = p ^ w →
        orderOf (p : ZMod r) ∣ w ∧ Odd (orderOf (p : ZMod r)) :=
  @OddPerfect.orderOf_dvd_weight_of_shape

theorem StatementGate.three_le_orderOf_of_shape :
    ∀ {N q m p r w : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
      _root_.Nat.Prime r → r ∣ (q + 1) / 2 →
      ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = p ^ w → p % r ≠ 1 →
        3 ≤ orderOf (p : ZMod r) ∧ ¬ orderOf (p : ZMod r) ∣ Nat.factorization N p ∧ 3 ≤ w :=
  @OddPerfect.three_le_orderOf_of_shape

theorem StatementGate.not_dvd_weight_of_shape :
    ∀ {N q m p r w : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
      _root_.Nat.Prime r → r ∣ (q + 1) / 2 →
      ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = p ^ w → ¬ r ∣ w :=
  @OddPerfect.not_dvd_weight_of_shape

theorem StatementGate.mod_eq_one_of_shape_of_fermat :
    ∀ {N q m p r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
      _root_.Nat.Prime r → r ∣ (q + 1) / 2 → (∃ k, r = 2 ^ k + 1) →
        p % r = 1 ∧ r ∣ Nat.factorization N p + 2 :=
  @OddPerfect.mod_eq_one_of_shape_of_fermat

theorem StatementGate.prod_dvd_index_add_two_of_shape :
    ∀ {N q m p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
        Finset.prod (Finset.filter (fun r => p % r = 1) (Nat.primeFactors ((q + 1) / 2)))
          (fun r => r) ∣ Nat.factorization N p + 2 :=
  @OddPerfect.prod_dvd_index_add_two_of_shape

theorem StatementGate.prod_primeFactors_mod_of_shape :
    ∀ {N q m p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
        Finset.prod (Nat.primeFactors ((q + 1) / 2)) (fun r => r) % p = 1 :=
  @OddPerfect.prod_primeFactors_mod_of_shape

theorem StatementGate.two_mul_add_one_le_prod_primeFactors_of_shape :
    ∀ {N q m p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
        2 * p + 1 ≤ Finset.prod (Nat.primeFactors ((q + 1) / 2)) (fun r => r) :=
  @OddPerfect.two_mul_add_one_le_prod_primeFactors_of_shape

theorem StatementGate.exists_row_not_mod_one_of_shape :
    ∀ {N q m p : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q * m ^ 2 → ¬ q ∣ m →
      _root_.Nat.Prime p → p ∣ m → 2 * m ^ 2 = p ^ Nat.factorization N p * (q + 1) →
        ∃ r w : ℕ, _root_.Nat.Prime r ∧ r ∣ (q + 1) / 2 ∧
          ArithmeticFunction.sigma 1 (r ^ Nat.factorization N r) = p ^ w ∧ p % r ≠ 1 ∧
          3 ≤ orderOf (p : ZMod r) ∧ ¬ orderOf (p : ZMod r) ∣ Nat.factorization N p ∧ 3 ≤ w ∧
          7 ≤ r :=
  @OddPerfect.exists_row_not_mod_one_of_shape

theorem StatementGate.conditional_card_primeFactors_add_two_mul_le_five_excess_add_five :
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = r ^ a → a = 1) →
    (∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = 3 * r ^ a →
      a ≤ 2) →
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 5 :=
  @OddPerfect.conditional_card_primeFactors_add_two_mul_le_five_excess_add_five

theorem StatementGate.special_lt_of_noOrderPureRow :
    (∀ r p g s u : ℕ, _root_.Nat.Prime r → _root_.Nat.Prime p → _root_.Nat.Prime s → s ≠ 2 →
      s ∣ r - 1 → Even g → g ≠ 0 → 1 ≤ u → ArithmeticFunction.sigma 1 (r ^ g) ≠ p ^ (s * u)) →
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      q < m :=
  @OddPerfect.special_lt_of_noOrderPureRow

theorem StatementGate.phi3_eq_special_pow_exponent :
    ∀ {q x j : ℕ}, _root_.Nat.Prime q → q % 4 = 1 → _root_.Nat.Prime x → Odd x → 1 ≤ j →
      x ^ 2 + x + 1 = q ^ j → j = 1 :=
  @OddPerfect.phi3_eq_special_pow_exponent

theorem StatementGate.not_phi3_eq_special_and_three_mul_pow :
    ∀ {q : ℕ}, _root_.Nat.Prime q → q % 4 = 1 → ∀ {x x' m : ℕ}, Odd x → Odd x' → 1 ≤ m →
      x ^ 2 + x + 1 = q → x' ^ 2 + x' + 1 = 3 * q ^ m → False :=
  @OddPerfect.not_phi3_eq_special_and_three_mul_pow

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five_all :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      Finset.card (Nat.primeFactors N) +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * (Finset.sum (Finset.erase (Nat.primeFactors N) q)
          (fun p => Nat.factorization N p / 2 - 1)) + 5 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_all

theorem StatementGate.special_lt_root :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      q < m :=
  @OddPerfect.special_lt_root

theorem StatementGate.noSquareCycle :
    ∀ p e t : ℕ, _root_.Nat.Prime p → 1 ≤ e → Odd t →
      ArithmeticFunction.sigma 1 (t ^ 2) = p ^ e →
      2 * t ^ 2 = 1 + ArithmeticFunction.sigma 1 (p ^ e) → False :=
  @OddPerfect.noSquareCycle

theorem StatementGate.repunit_rows_size :
    ∀ (p : ℕ) (I : Finset ℕ) (ℓ : ℕ → ℕ), I.Nonempty →
      (∀ r ∈ I, _root_.Nat.Prime r ∧ r ≠ 2 ∧ _root_.Nat.Prime (ℓ r) ∧ ℓ r ≠ 2 ∧
        ∑ i ∈ Finset.range (ℓ r), r ^ i = p) →
      2 * (∏ r ∈ I, ℓ r) * (∑ r ∈ I, (r - 1)) < p :=
  @OddPerfect.repunit_rows_size

theorem StatementGate.prime_index_of_sigma_prime_pow :
    ∀ {r p g w : ℕ}, _root_.Nat.Prime r → _root_.Nat.Prime p → p ≠ 2 → 1 ≤ g → 1 ≤ w →
      ArithmeticFunction.sigma 1 (r ^ g) = p ^ w →
      _root_.Nat.Prime (g + 1) ∧ g + 1 ∣ p - 1 ∧ r ^ (g + 1) = 1 + (r - 1) * p ^ w :=
  @OddPerfect.prime_index_of_sigma_prime_pow

theorem StatementGate.nagellPrimePower :
    ∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a → p ^ 2 + p + 1 = r ^ a →
      a = 1 :=
  @OddPerfect.nagellPrimePower

theorem StatementGate.ljunggrenThreePrimePower :
    ∀ p r a : ℕ, _root_.Nat.Prime p → _root_.Nat.Prime r → 1 ≤ a →
      p ^ 2 + p + 1 = 3 * r ^ a → a ≤ 2 :=
  @OddPerfect.ljunggrenThreePrimePower

theorem StatementGate.three_mul_prime_pow_exponent_le_two :
    ∀ {p r a : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime r → p ^ 2 + p + 1 = 3 * r ^ a →
      a ≤ 2 :=
  @OddPerfect.three_mul_prime_pow_exponent_le_two

theorem StatementGate.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      2 * (Nat.primeFactors N).card +
          3 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        7 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 10 + Nat.factorization N q :=
  @OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent

theorem StatementGate.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      q % 3 = 2 →
      2 * (Nat.primeFactors N).card +
          3 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        7 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 9 :=
  @OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine

theorem StatementGate.not_isSquare_eulerIndex :
    ∀ {N q k m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → N = q ^ k * m ^ 2 → ¬ q ∣ m →
      k ≠ 1 → ¬ IsSquare (ArithmeticFunction.sigma 1 (m ^ 2) / q ^ k) :=
  @OddPerfect.not_isSquare_eulerIndex

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_two :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (Nat.primeFactors N).card +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 2 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_two

theorem StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      3 ∣ N →
      (Nat.primeFactors N).card +
          2 * padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) ≤
        5 * Finset.sum ((Nat.primeFactors N).erase q)
          (fun p => Nat.factorization N p / 2 - 1) + 1 :=
  @OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd

theorem StatementGate.five_le_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      5 ≤ Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.five_le_excess

theorem StatementGate.five_le_cardFactors_sub :
    ∀ {N q a m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      ArithmeticFunction.cardDistinctFactors m + 5 ≤ ArithmeticFunction.cardFactors m :=
  @OddPerfect.five_le_cardFactors_sub

theorem StatementGate.two_mul_omega_add_special_add_eight_le_Omega :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      2 * ArithmeticFunction.cardDistinctFactors N + Nat.factorization N q + 8 ≤
        ArithmeticFunction.cardFactors N :=
  @OddPerfect.two_mul_omega_add_special_add_eight_le_Omega

theorem StatementGate.six_le_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      6 ≤ Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.six_le_excess

theorem StatementGate.six_le_cardFactors_sub :
    ∀ {N q a m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      ArithmeticFunction.cardDistinctFactors m + 6 ≤ ArithmeticFunction.cardFactors m :=
  @OddPerfect.six_le_cardFactors_sub

theorem StatementGate.two_mul_omega_add_special_add_ten_le_Omega :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      2 * ArithmeticFunction.cardDistinctFactors N + Nat.factorization N q + 10 ≤
        ArithmeticFunction.cardFactors N :=
  @OddPerfect.two_mul_omega_add_special_add_ten_le_Omega

theorem StatementGate.seven_le_excess :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      7 ≤ Finset.sum ((Nat.primeFactors N).erase q) (fun p => Nat.factorization N p / 2 - 1) :=
  @OddPerfect.seven_le_excess

theorem StatementGate.seven_le_cardFactors_sub :
    ∀ {N q a m : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → ¬ q ∣ m → N = q ^ a * m ^ 2 →
      ArithmeticFunction.cardDistinctFactors m + 7 ≤ ArithmeticFunction.cardFactors m :=
  @OddPerfect.seven_le_cardFactors_sub

theorem StatementGate.two_mul_omega_add_special_add_twelve_le_Omega :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      2 * ArithmeticFunction.cardDistinctFactors N + Nat.factorization N q + 12 ≤
        ArithmeticFunction.cardFactors N :=
  @OddPerfect.two_mul_omega_add_special_add_twelve_le_Omega

theorem StatementGate.le_succ_of_safe_prime_row :
    ∀ {p s t a : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime s → _root_.Nat.Prime t →
      t = 2 * s + 1 → Even a → t ∣ ArithmeticFunction.sigma 1 (p ^ a) → s ≤ a + 1 :=
  @OddPerfect.le_succ_of_safe_prime_row

theorem StatementGate.fermat_row :
    ∀ {p r e k : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime r → r = 2 ^ k + 1 → Even e →
      r ∣ ArithmeticFunction.sigma 1 (p ^ e) → p % r = 1 ∧ r ∣ e + 1 :=
  @OddPerfect.fermat_row

theorem StatementGate.exists_pow_dvd_of_safe_prime :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {s t : ℕ}, _root_.Nat.Prime s → _root_.Nat.Prime t →
      t = 2 * s + 1 → t ∣ N →
      ∃ p ∈ Nat.primeFactors N, p ≠ t ∧
        ((s ≤ Nat.factorization N p + 1 ∧ p ^ (s - 1) ∣ N) ∨
          (Odd (Nat.factorization N p) ∧ t ∣ p + 1)) :=
  @OddPerfect.exists_pow_dvd_of_safe_prime

theorem StatementGate.size_of_forall_gt_thousand :
    ∀ {N : ℕ}, _root_.OddPerfect N → (∀ p ∈ Nat.primeFactors N, 1000 < p) →
      1499 ≤ (Nat.primeFactors N).card ∧ 1001 ^ 2999 ≤ N :=
  @OddPerfect.size_of_forall_gt_thousand

theorem StatementGate.restrained_one_ninety_eight_le_three :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        198 ≤ Nat.factorization N 3 :=
  @OddPerfect.restrained_one_ninety_eight_le_three

theorem StatementGate.exists_component_gt_of_factorization_five_eq_one :
    ∀ {N : ℕ}, _root_.OddPerfect N → Nat.factorization N 5 = 1 →
      ∃ p ∈ Nat.primeFactors N, 10 ^ 24 < p ^ Nat.factorization N p :=
  @OddPerfect.exists_component_gt_of_factorization_five_eq_one

theorem StatementGate.restrained_omega_le :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        ArithmeticFunction.cardDistinctFactors N ≤ 2 * Nat.factorization N 3 + 3 :=
  @OddPerfect.restrained_omega_le

theorem StatementGate.restrained_nineteen_thousand_le_three :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        19024 ≤ Nat.factorization N 3 :=
  @OddPerfect.restrained_nineteen_thousand_le_three

theorem StatementGate.restrained_omega_ge_sieve :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        275251 ≤ ArithmeticFunction.cardDistinctFactors N :=
  @OddPerfect.restrained_omega_ge_sieve

theorem StatementGate.restrained_sieve_le_three :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        137624 ≤ Nat.factorization N 3 :=
  @OddPerfect.restrained_sieve_le_three

theorem StatementGate.restrained_Omega_ge_sieve :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        688123 ≤ ArithmeticFunction.cardFactors N :=
  @OddPerfect.restrained_Omega_ge_sieve

theorem StatementGate.restrained_two_mod_three_cases :
    ∀ {N q r t : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      t ∈ Nat.primeFactors N → t % 3 = 2 →
        t ∣ ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q) ∨
          t ∣ Nat.factorization N 3 + 1 ∨ Nat.ModEq (t ^ 2) (3 ^ (t - 1)) 1 :=
  @OddPerfect.restrained_two_mod_three_cases

theorem StatementGate.restrained_clock :
    ∀ {N q r t : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      _root_.Nat.Prime t → t ≠ 2 → t ≠ 3 → t ≠ q →
      orderOf (3 : ZMod t) ∣ Nat.factorization N 3 + 1 →
        padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) +
          padicValNat t (Nat.factorization N 3 + 1) ≤ 2 :=
  @OddPerfect.restrained_clock

theorem StatementGate.restrained_big_succ_lt :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      (∀ p ∈ Nat.primeFactors N, 2 * p + 1 ≤ 3 * q) → Nat.factorization N 3 + 1 < q :=
  @OddPerfect.restrained_big_succ_lt

theorem StatementGate.restrained_big_pow_modEq_of_one_lt :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      (∀ p ∈ Nat.primeFactors N, 2 * p + 1 ≤ 3 * q) → 1 < Nat.factorization N q →
        Nat.ModEq (q ^ 3) (3 ^ (q - 1)) 1 :=
  @OddPerfect.restrained_big_pow_modEq_of_one_lt

theorem StatementGate.lt_two_pow_sq :
    ∀ {N : ℕ}, _root_.OddPerfect N → N < 2 ^ (2 ^ (Nat.primeFactors N).card - 1) ^ 2 :=
  @OddPerfect.lt_two_pow_sq

theorem StatementGate.exists_component_gt_ten_pow_thirty_three_of_factorization_five_eq_one :
    ∀ {N : ℕ}, _root_.OddPerfect N → Nat.factorization N 5 = 1 →
      ∃ p ∈ Nat.primeFactors N, 10 ^ 33 < p ^ Nat.factorization N p :=
  @OddPerfect.exists_component_gt_ten_pow_thirty_three_of_factorization_five_eq_one

theorem StatementGate.no_mutual_rows_five :
    ∀ {p q α β : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime q → 1 ≤ α → 1 ≤ β →
      Finset.sum (Finset.range 5) (fun i => p ^ i) = 5 * q ^ α →
      Finset.sum (Finset.range 5) (fun i => q ^ i) = 5 * p ^ β → False :=
  @OddPerfect.no_mutual_rows_five

theorem StatementGate.factorization_largest_le_eight :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) →
        Nat.factorization N P ≤ 8 :=
  @OddPerfect.factorization_largest_le_eight

theorem StatementGate.padicValNat_three_sigma_special_of_equal_exponents :
    ∀ {N q β : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → Nat.factorization N p = 2 * β) → 3 ∣ N →
        padicValNat 3 (ArithmeticFunction.sigma 1 (q ^ Nat.factorization N q)) = 2 * β :=
  @OddPerfect.padicValNat_three_sigma_special_of_equal_exponents

theorem StatementGate.prime_dvd_sigma_special_of_succ_succ :
    ∀ {N q k : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = k →
      Odd k → _root_.Nat.Prime (k + 2) → q % (k + 2) ≠ 1 →
        k + 2 ∣ ArithmeticFunction.sigma 1 (q ^ k) ∧ k + 2 ∈ Nat.primeFactors N ∧
          (k + 2) ^ 2 ∣ N :=
  @OddPerfect.prime_dvd_sigma_special_of_succ_succ

theorem StatementGate.five_special_exponent_mod_twelve :
    ∀ {N : ℕ}, _root_.OddPerfect N → Odd (Nat.factorization N 5) →
      Nat.factorization N 5 % 12 = 1 ∨ Nat.factorization N 5 % 12 = 9 :=
  @OddPerfect.five_special_exponent_mod_twelve

theorem StatementGate.restrained_omega_eq :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        ArithmeticFunction.cardDistinctFactors N + padicValNat 3 (Nat.factorization N q + 1) =
          Nat.factorization N 3 + 2 +
            (Finset.filter (fun p => p ≠ 3 ∧ p ≠ q ∧ p % 3 = 2) (Nat.primeFactors N)).card :=
  @OddPerfect.restrained_omega_eq

theorem StatementGate.padicValNat_sigma_prime_pow_row :
    ∀ {p r e : ℕ}, _root_.Nat.Prime p → _root_.Nat.Prime r → r ≠ 2 → p ≠ r →
      (¬ orderOf (p : ZMod r) ∣ e + 1 →
          padicValNat r (ArithmeticFunction.sigma 1 (p ^ e)) = 0) ∧
        (orderOf (p : ZMod r) = 1 →
          padicValNat r (ArithmeticFunction.sigma 1 (p ^ e)) = padicValNat r (e + 1)) ∧
        (1 < orderOf (p : ZMod r) → orderOf (p : ZMod r) ∣ e + 1 →
          padicValNat r (ArithmeticFunction.sigma 1 (p ^ e)) =
            padicValNat r (p ^ orderOf (p : ZMod r) - 1) + padicValNat r (e + 1)) :=
  @OddPerfect.padicValNat_sigma_prime_pow_row

theorem StatementGate.restrained_omega_ge_tail :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        360549 ≤ ArithmeticFunction.cardDistinctFactors N :=
  @OddPerfect.restrained_omega_ge_tail

theorem StatementGate.restrained_tail_le_three :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        180274 ≤ Nat.factorization N 3 :=
  @OddPerfect.restrained_tail_le_three

theorem StatementGate.restrained_Omega_ge_tail :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        901369 ≤ ArithmeticFunction.cardFactors N :=
  @OddPerfect.restrained_Omega_ge_tail

theorem StatementGate.restrained_omega_ge_wheel :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        576967 ≤ ArithmeticFunction.cardDistinctFactors N :=
  @OddPerfect.restrained_omega_ge_wheel

theorem StatementGate.restrained_three_ge_wheel :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        288482 ≤ Nat.factorization N 3 :=
  @OddPerfect.restrained_three_ge_wheel

theorem StatementGate.restrained_Omega_ge_wheel :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        1442413 ≤ ArithmeticFunction.cardFactors N :=
  @OddPerfect.restrained_Omega_ge_wheel

theorem StatementGate.restrained_big_special_fermat :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      (∀ p ∈ Nat.primeFactors N, 2 * p + 1 ≤ 3 * q) →
        Nat.factorization N q ≤ 2 + padicValNat q (3 ^ (q - 1) - 1) :=
  @OddPerfect.restrained_big_special_fermat

theorem StatementGate.saturated_receiver :
    ∀ {N t : ℕ}, _root_.OddPerfect N → 3 ∣ N → _root_.Nat.Prime t → t ≠ 2 → t ≠ 3 →
      orderOf (3 : ZMod t) ∣ Nat.factorization N 3 + 1 →
      padicValNat t (3 ^ orderOf (3 : ZMod t) - 1) + padicValNat t (Nat.factorization N 3 + 1) =
        Nat.factorization N t →
        ∀ p ∈ Nat.primeFactors N, p ≠ 3 →
          ¬ t ∣ ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) :=
  @OddPerfect.saturated_receiver

theorem StatementGate.sum_factorization_geom_sum_le_primeIndexCap :
    ∀ {P l : ℕ}, _root_.Nat.Prime P → _root_.Nat.Prime l → l ≠ 2 → l ≠ P → ∀ (U : Finset ℕ),
      (∀ u ∈ U, 1 < u ∧ u < P) →
        ∑ u ∈ U, Nat.factorization (∑ i ∈ Finset.range l, u ^ i) P ≤
          ∑ j ∈ Finset.Icc 1 (l - 2), (l - 1) / j :=
  @OddPerfect.sum_factorization_geom_sum_le_primeIndexCap

theorem StatementGate.factorization_largest_le_sum_primeIndexCap :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) → ∀ (E : Finset ℕ),
      (∀ e ∈ E, _root_.Nat.Prime (e + 1) ∧ e + 1 ≠ 2 ∧ e + 1 ≠ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P → Nat.factorization N p ∈ E) →
        Nat.factorization N P ≤ ∑ e ∈ E, ∑ j ∈ Finset.Icc 1 (e + 1 - 2), (e + 1 - 1) / j :=
  @OddPerfect.factorization_largest_le_sum_primeIndexCap

theorem StatementGate.factorization_largest_le_twentytwo :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4 ∨ Nat.factorization N p = 6) →
        Nat.factorization N P ≤ 22 :=
  @OddPerfect.factorization_largest_le_twentytwo

theorem StatementGate.factorization_largest_le_fourteen :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 6) →
        Nat.factorization N P ≤ 14 :=
  @OddPerfect.factorization_largest_le_fourteen

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

theorem StatementGate.exceptSmall_three :
    ∀ {N : ℕ}, _root_.OddPerfect N → 3 ∣ N →
      ∃ p ∈ Nat.primeFactors N, Even (Nat.factorization N p) ∧ 4 ≤ Nat.factorization N p ∧
        p ≤ 331 :=
  @OddPerfect.exceptSmall_three

theorem StatementGate.exceptSmall_bound :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      ∃ p ∈ Nat.primeFactors N, Even (Nat.factorization N p) ∧ 4 ≤ Nat.factorization N p ∧
        p ≤ max 331 (9 * (Finset.filter (fun p => Even (Nat.factorization N p) ∧
          4 ≤ Nat.factorization N p) (Nat.primeFactors N)).card ^ 2) :=
  @OddPerfect.exceptSmall_bound

theorem StatementGate.exceptSmall_bound_of_card_le_six :
    ∀ {N : ℕ}, _root_.OddPerfect N →
      (Finset.filter (fun p => Even (Nat.factorization N p) ∧
        4 ≤ Nat.factorization N p) (Nat.primeFactors N)).card ≤ 6 →
      ∃ p ∈ Nat.primeFactors N, Even (Nat.factorization N p) ∧ 4 ≤ Nat.factorization N p ∧
        p ≤ 331 :=
  @OddPerfect.exceptSmall_bound_of_card_le_six

theorem StatementGate.sum_factorization_geom_sum_five_le_six_of_primes :
    ∀ {P : ℕ}, _root_.Nat.Prime P → P ≠ 5 → ∀ (U : Finset ℕ),
      (∀ u ∈ U, _root_.Nat.Prime u ∧ u < P) →
        ∑ u ∈ U, Nat.factorization (∑ i ∈ Finset.range 5, u ^ i) P ≤ 6 :=
  @OddPerfect.sum_factorization_geom_sum_five_le_six_of_primes

theorem StatementGate.sum_factorization_geom_sum_seven_le_eleven_of_primes :
    ∀ {P : ℕ}, _root_.Nat.Prime P → P ≠ 7 → ∀ (U : Finset ℕ),
      (∀ u ∈ U, _root_.Nat.Prime u ∧ u < P) →
        ∑ u ∈ U, Nat.factorization (∑ i ∈ Finset.range 7, u ^ i) P ≤ 11 :=
  @OddPerfect.sum_factorization_geom_sum_seven_le_eleven_of_primes

theorem StatementGate.sum_factorization_geom_sum_eleven_le_nineteen_of_primes :
    ∀ {P : ℕ}, _root_.Nat.Prime P → P ≠ 11 → ∀ (U : Finset ℕ),
      (∀ u ∈ U, _root_.Nat.Prime u ∧ u < P) →
        ∑ u ∈ U, Nat.factorization (∑ i ∈ Finset.range 11, u ^ i) P ≤ 19 :=
  @OddPerfect.sum_factorization_geom_sum_eleven_le_nineteen_of_primes

theorem StatementGate.factorization_largest_le_eighteen :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4 ∨ Nat.factorization N p = 6) →
        Nat.factorization N P ≤ 18 :=
  @OddPerfect.factorization_largest_le_eighteen

theorem StatementGate.factorization_largest_le_twelve :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      P ∈ Nat.primeFactors N → P ≠ q → (∀ p ∈ Nat.primeFactors N, p ≤ P) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ P →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 6) →
        Nat.factorization N P ≤ 12 :=
  @OddPerfect.factorization_largest_le_twelve

theorem StatementGate.special_exponent_eq_one_or_five :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) →
        Nat.factorization N q = 1 ∨ Nat.factorization N q = 5 :=
  @OddPerfect.special_exponent_eq_one_or_five

theorem StatementGate.special_exponent_eq_one_of_not_three_dvd :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) → ¬ 3 ∣ N →
        Nat.factorization N q = 1 :=
  @OddPerfect.special_exponent_eq_one_of_not_three_dvd

theorem StatementGate.special_mod_five_of_eq_five :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) →
        Nat.factorization N q = 5 → q % 5 = 1 :=
  @OddPerfect.special_mod_five_of_eq_five

theorem StatementGate.special_mod_three_or_mod_five :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      (∀ p ∈ Nat.primeFactors N, p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) →
        q % 3 = 1 ∨ q % 5 = 1 :=
  @OddPerfect.special_mod_three_or_mod_five

theorem StatementGate.lt_pow_mul_sigma_sub :
    ∀ {q M a b : ℕ}, _root_.Nat.Prime q → q ≠ 2 → ArithmeticFunction.sigma 1 M < 2 * M →
      b < a → q ^ (a - b) * M ∣ ArithmeticFunction.sigma 1 (q ^ a) * ArithmeticFunction.sigma 1 M →
        M < q ^ (b + 1) * (ArithmeticFunction.sigma 1 M - M) :=
  @OddPerfect.lt_pow_mul_sigma_sub

theorem StatementGate.special_exponent_le_rank_two :
    ∀ {N q P D β : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q →
      Odd (Nat.factorization N q) → P ∈ Nat.primeFactors N → q < P →
      (∀ p ∈ Nat.primeFactors N, p ≠ P → p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p < q → Nat.factorization N p ≤ D) →
      ∑ p ∈ Finset.filter (fun p => p < q) (Nat.primeFactors N),
        Nat.factorization (ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p)) q ≤ β →
        Nat.factorization N q ≤ max (β + Nat.factorization N P * D - 1)
          ((Nat.factorization N P + 1) * β + Nat.factorization N P - 1) :=
  @OddPerfect.special_exponent_le_rank_two

theorem StatementGate.special_exponent_le_41 :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      P ∈ Nat.primeFactors N → q < P → (∀ p ∈ Nat.primeFactors N, p ≠ P → p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) →
        Nat.factorization N q ≤ 41 :=
  @OddPerfect.special_exponent_le_41

theorem StatementGate.special_exponent_le_37_of_not_three_dvd :
    ∀ {N q P : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      P ∈ Nat.primeFactors N → q < P → (∀ p ∈ Nat.primeFactors N, p ≠ P → p ≤ q) →
      (∀ p ∈ Nat.primeFactors N, p ≠ q →
        Nat.factorization N p = 2 ∨ Nat.factorization N p = 4) → ¬ 3 ∣ N →
        Nat.factorization N q ≤ 37 :=
  @OddPerfect.special_exponent_le_37_of_not_three_dvd

theorem StatementGate.not_three_dvd_succ_special_exponent :
    ∀ {N q : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Odd (Nat.factorization N q) →
      ¬ 3 ∣ N → ¬ 3 ∣ Nat.factorization N q + 1 :=
  @OddPerfect.not_three_dvd_succ_special_exponent

theorem StatementGate.not_dvd_phi3_of_dvd_succ :
    ∀ {q t : ℕ}, 7 < q → t ∣ q + 1 → ¬ q ∣ t ^ 2 + t + 1 :=
  @OddPerfect.not_dvd_phi3_of_dvd_succ

theorem StatementGate.exists_sends_into :
    ∀ {N : ℕ}, _root_.OddPerfect N → ∀ {U : Finset ℕ}, U ⊆ Nat.primeFactors N → U.Nonempty →
      U ≠ Nat.primeFactors N →
        ∃ p ∈ Nat.primeFactors N, p ∉ U ∧
          ∃ t ∈ U, t ∣ ArithmeticFunction.sigma 1 (p ^ Nat.factorization N p) :=
  @OddPerfect.exists_sends_into

theorem StatementGate.exists_ball_eq :
    ∀ {N r : ℕ}, _root_.OddPerfect N → r ∈ Nat.primeFactors N →
      OddPerfect.ball N r (Nat.primeFactors N).card = Nat.primeFactors N :=
  @OddPerfect.exists_ball_eq

theorem StatementGate.restrained_three_lt :
    ∀ {N q r d : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
      OddPerfect.ball N 3 d = Nat.primeFactors N →
        Nat.factorization N 3 < 3 ^ (2 ^ d + 1) :=
  @OddPerfect.restrained_three_lt

theorem StatementGate.restrained_exists_far :
    ∀ {N q r : ℕ}, _root_.OddPerfect N → _root_.Nat.Prime q → Nat.factorization N q = 1 →
      _root_.Nat.Prime r → r ≠ q →
      (∀ p ∈ Nat.primeFactors N, p ≠ q → p ≠ r → Nat.factorization N p = 2) →
        ∃ p ∈ Nat.primeFactors N, p ∉ OddPerfect.ball N 3 3 :=
  @OddPerfect.restrained_exists_far

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
    ``OddPerfect.TwoExcEngine.rootKeysV, ``OddPerfect.TwoExcEngine.checkV,
    ``OddPerfect.ball]

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
    (`StatementGate.finite_oddPerfect_le,
      ``OddPerfect.finite_oddPerfect_le),
    (`StatementGate.ncard_oddPerfect_le_sqrt,
      ``OddPerfect.ncard_oddPerfect_le_sqrt),
    (`StatementGate.factorization_mod_three_ne_two_of_not_three_dvd,
      ``OddPerfect.factorization_mod_three_ne_two_of_not_three_dvd),
    (`StatementGate.even_factorization_of_mod_three_eq_two_of_not_three_dvd,
      ``OddPerfect.even_factorization_of_mod_three_eq_two_of_not_three_dvd),
    (`StatementGate.odd_card_one_mod_three_of_not_three_dvd,
      ``OddPerfect.odd_card_one_mod_three_of_not_three_dvd),
    (`StatementGate.exists_high_pure_row_of_le_special,
      ``OddPerfect.exists_high_pure_row_of_le_special),
    (`StatementGate.special_lt_of_noHighPureRow, ``OddPerfect.special_lt_of_noHighPureRow),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_six,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_six),
    (`StatementGate.card_primeFactors_le_five_excess_add_two_of_not_three_dvd,
      ``OddPerfect.card_primeFactors_le_five_excess_add_two_of_not_three_dvd),
    (`StatementGate.lt_two_pow_four_pow_excess_add_six,
      ``OddPerfect.lt_two_pow_four_pow_excess_add_six),
    (`StatementGate.phi3_both_shapes_mod_eight, ``OddPerfect.phi3_both_shapes_mod_eight),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_of_mod_ne),
    (`StatementGate.card_escapeRows_le_one, ``OddPerfect.card_escapeRows_le_one),
    (`StatementGate.two_sq_ne_one_add_sigma_of_lt_sixteen,
      ``OddPerfect.two_sq_ne_one_add_sigma_of_lt_sixteen),
    (`StatementGate.sixteen_le_exponent_of_le_special,
      ``OddPerfect.sixteen_le_exponent_of_le_special),
    (`StatementGate.nagellPrimePower_of_highPrimeExponent,
      ``OddPerfect.nagellPrimePower_of_highPrimeExponent),
    (`StatementGate.phi3_prime_pow_exponent, ``OddPerfect.phi3_prime_pow_exponent),
    (`StatementGate.orderOf_dvd_weight_of_shape, ``OddPerfect.orderOf_dvd_weight_of_shape),
    (`StatementGate.three_le_orderOf_of_shape, ``OddPerfect.three_le_orderOf_of_shape),
    (`StatementGate.not_dvd_weight_of_shape, ``OddPerfect.not_dvd_weight_of_shape),
    (`StatementGate.mod_eq_one_of_shape_of_fermat, ``OddPerfect.mod_eq_one_of_shape_of_fermat),
    (`StatementGate.prod_dvd_index_add_two_of_shape, ``OddPerfect.prod_dvd_index_add_two_of_shape),
    (`StatementGate.prod_primeFactors_mod_of_shape, ``OddPerfect.prod_primeFactors_mod_of_shape),
    (`StatementGate.two_mul_add_one_le_prod_primeFactors_of_shape,
      ``OddPerfect.two_mul_add_one_le_prod_primeFactors_of_shape),
    (`StatementGate.exists_row_not_mod_one_of_shape, ``OddPerfect.exists_row_not_mod_one_of_shape),
    (`StatementGate.conditional_card_primeFactors_add_two_mul_le_five_excess_add_five,
      ``OddPerfect.conditional_card_primeFactors_add_two_mul_le_five_excess_add_five),
    (`StatementGate.special_lt_of_noOrderPureRow, ``OddPerfect.special_lt_of_noOrderPureRow),
    (`StatementGate.phi3_eq_special_pow_exponent, ``OddPerfect.phi3_eq_special_pow_exponent),
    (`StatementGate.not_phi3_eq_special_and_three_mul_pow,
      ``OddPerfect.not_phi3_eq_special_and_three_mul_pow),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_five_all,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_five_all),
    (`StatementGate.special_lt_root, ``OddPerfect.special_lt_root),
    (`StatementGate.noSquareCycle, ``OddPerfect.noSquareCycle),
    (`StatementGate.repunit_rows_size, ``OddPerfect.repunit_rows_size),
    (`StatementGate.prime_index_of_sigma_prime_pow,
      ``OddPerfect.prime_index_of_sigma_prime_pow),
    (`StatementGate.nagellPrimePower, ``OddPerfect.nagellPrimePower),
    (`StatementGate.ljunggrenThreePrimePower, ``OddPerfect.ljunggrenThreePrimePower),
    (`StatementGate.three_mul_prime_pow_exponent_le_two,
      ``OddPerfect.three_mul_prime_pow_exponent_le_two),
    (`StatementGate.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent,
      ``OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_ten_add_exponent),
    (`StatementGate.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine,
      ``OddPerfect.two_mul_card_primeFactors_add_three_mul_le_seven_excess_add_nine),
    (`StatementGate.not_isSquare_eulerIndex, ``OddPerfect.not_isSquare_eulerIndex),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_two,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_two),
    (`StatementGate.card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd,
      ``OddPerfect.card_primeFactors_add_two_mul_le_five_excess_add_one_of_three_dvd),
    (`StatementGate.five_le_excess, ``OddPerfect.five_le_excess),
    (`StatementGate.five_le_cardFactors_sub, ``OddPerfect.five_le_cardFactors_sub),
    (`StatementGate.two_mul_omega_add_special_add_eight_le_Omega,
      ``OddPerfect.two_mul_omega_add_special_add_eight_le_Omega),
    (`StatementGate.six_le_excess, ``OddPerfect.six_le_excess),
    (`StatementGate.six_le_cardFactors_sub, ``OddPerfect.six_le_cardFactors_sub),
    (`StatementGate.two_mul_omega_add_special_add_ten_le_Omega,
      ``OddPerfect.two_mul_omega_add_special_add_ten_le_Omega),
    (`StatementGate.seven_le_excess, ``OddPerfect.seven_le_excess),
    (`StatementGate.seven_le_cardFactors_sub, ``OddPerfect.seven_le_cardFactors_sub),
    (`StatementGate.two_mul_omega_add_special_add_twelve_le_Omega,
      ``OddPerfect.two_mul_omega_add_special_add_twelve_le_Omega),
    (`StatementGate.le_succ_of_safe_prime_row, ``OddPerfect.le_succ_of_safe_prime_row),
    (`StatementGate.fermat_row, ``OddPerfect.fermat_row),
    (`StatementGate.exists_pow_dvd_of_safe_prime, ``OddPerfect.exists_pow_dvd_of_safe_prime),
    (`StatementGate.size_of_forall_gt_thousand, ``OddPerfect.size_of_forall_gt_thousand),
    (`StatementGate.restrained_one_ninety_eight_le_three,
      ``OddPerfect.restrained_one_ninety_eight_le_three),
    (`StatementGate.exists_component_gt_of_factorization_five_eq_one,
      ``OddPerfect.exists_component_gt_of_factorization_five_eq_one),
    (`StatementGate.restrained_omega_le, ``OddPerfect.restrained_omega_le),
    (`StatementGate.restrained_nineteen_thousand_le_three,
      ``OddPerfect.restrained_nineteen_thousand_le_three),
    (`StatementGate.restrained_omega_ge_sieve, ``OddPerfect.restrained_omega_ge_sieve),
    (`StatementGate.restrained_sieve_le_three, ``OddPerfect.restrained_sieve_le_three),
    (`StatementGate.restrained_Omega_ge_sieve, ``OddPerfect.restrained_Omega_ge_sieve),
    (`StatementGate.restrained_two_mod_three_cases, ``OddPerfect.restrained_two_mod_three_cases),
    (`StatementGate.restrained_clock, ``OddPerfect.restrained_clock),
    (`StatementGate.restrained_big_succ_lt, ``OddPerfect.restrained_big_succ_lt),
    (`StatementGate.restrained_big_pow_modEq_of_one_lt,
      ``OddPerfect.restrained_big_pow_modEq_of_one_lt),
    (`StatementGate.lt_two_pow_sq, ``OddPerfect.lt_two_pow_sq),
    (`StatementGate.exists_component_gt_ten_pow_thirty_three_of_factorization_five_eq_one,
      ``OddPerfect.exists_component_gt_ten_pow_thirty_three_of_factorization_five_eq_one),
    (`StatementGate.no_mutual_rows_five, ``OddPerfect.no_mutual_rows_five),
    (`StatementGate.factorization_largest_le_eight, ``OddPerfect.factorization_largest_le_eight),
    (`StatementGate.padicValNat_three_sigma_special_of_equal_exponents,
      ``OddPerfect.padicValNat_three_sigma_special_of_equal_exponents),
    (`StatementGate.prime_dvd_sigma_special_of_succ_succ,
      ``OddPerfect.prime_dvd_sigma_special_of_succ_succ),
    (`StatementGate.five_special_exponent_mod_twelve,
      ``OddPerfect.five_special_exponent_mod_twelve),
    (`StatementGate.restrained_omega_eq, ``OddPerfect.restrained_omega_eq),
    (`StatementGate.padicValNat_sigma_prime_pow_row, ``OddPerfect.padicValNat_sigma_prime_pow_row),
    (`StatementGate.restrained_omega_ge_tail, ``OddPerfect.restrained_omega_ge_tail),
    (`StatementGate.restrained_tail_le_three, ``OddPerfect.restrained_tail_le_three),
    (`StatementGate.restrained_Omega_ge_tail, ``OddPerfect.restrained_Omega_ge_tail),
    (`StatementGate.restrained_omega_ge_wheel, ``OddPerfect.restrained_omega_ge_wheel),
    (`StatementGate.restrained_three_ge_wheel, ``OddPerfect.restrained_three_ge_wheel),
    (`StatementGate.restrained_Omega_ge_wheel, ``OddPerfect.restrained_Omega_ge_wheel),
    (`StatementGate.restrained_big_special_fermat, ``OddPerfect.restrained_big_special_fermat),
    (`StatementGate.saturated_receiver, ``OddPerfect.saturated_receiver),
    (`StatementGate.sum_factorization_geom_sum_le_primeIndexCap,
      ``OddPerfect.sum_factorization_geom_sum_le_primeIndexCap),
    (`StatementGate.factorization_largest_le_sum_primeIndexCap,
      ``OddPerfect.factorization_largest_le_sum_primeIndexCap),
    (`StatementGate.factorization_largest_le_twentytwo,
      ``OddPerfect.factorization_largest_le_twentytwo),
    (`StatementGate.factorization_largest_le_fourteen,
      ``OddPerfect.factorization_largest_le_fourteen),
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
    (`StatementGate.exceptSmall_three, ``OddPerfect.exceptSmall_three),
    (`StatementGate.exceptSmall_bound, ``OddPerfect.exceptSmall_bound),
    (`StatementGate.exceptSmall_bound_of_card_le_six,
      ``OddPerfect.exceptSmall_bound_of_card_le_six),
    (`StatementGate.sum_factorization_geom_sum_five_le_six_of_primes,
      ``OddPerfect.sum_factorization_geom_sum_five_le_six_of_primes),
    (`StatementGate.sum_factorization_geom_sum_seven_le_eleven_of_primes,
      ``OddPerfect.sum_factorization_geom_sum_seven_le_eleven_of_primes),
    (`StatementGate.sum_factorization_geom_sum_eleven_le_nineteen_of_primes,
      ``OddPerfect.sum_factorization_geom_sum_eleven_le_nineteen_of_primes),
    (`StatementGate.factorization_largest_le_eighteen,
      ``OddPerfect.factorization_largest_le_eighteen),
    (`StatementGate.factorization_largest_le_twelve, ``OddPerfect.factorization_largest_le_twelve),
    (`StatementGate.special_exponent_eq_one_or_five, ``OddPerfect.special_exponent_eq_one_or_five),
    (`StatementGate.special_exponent_eq_one_of_not_three_dvd,
      ``OddPerfect.special_exponent_eq_one_of_not_three_dvd),
    (`StatementGate.special_mod_five_of_eq_five, ``OddPerfect.special_mod_five_of_eq_five),
    (`StatementGate.special_mod_three_or_mod_five, ``OddPerfect.special_mod_three_or_mod_five),
    (`StatementGate.lt_pow_mul_sigma_sub, ``OddPerfect.lt_pow_mul_sigma_sub),
    (`StatementGate.special_exponent_le_rank_two, ``OddPerfect.special_exponent_le_rank_two),
    (`StatementGate.special_exponent_le_41, ``OddPerfect.special_exponent_le_41),
    (`StatementGate.special_exponent_le_37_of_not_three_dvd,
      ``OddPerfect.special_exponent_le_37_of_not_three_dvd),
    (`StatementGate.not_three_dvd_succ_special_exponent,
      ``OddPerfect.not_three_dvd_succ_special_exponent),
    (`StatementGate.not_dvd_phi3_of_dvd_succ, ``OddPerfect.not_dvd_phi3_of_dvd_succ),
    (`StatementGate.exists_sends_into, ``OddPerfect.exists_sends_into),
    (`StatementGate.exists_ball_eq, ``OddPerfect.exists_ball_eq),
    (`StatementGate.restrained_three_lt, ``OddPerfect.restrained_three_lt),
    (`StatementGate.restrained_exists_far, ``OddPerfect.restrained_exists_far),
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
