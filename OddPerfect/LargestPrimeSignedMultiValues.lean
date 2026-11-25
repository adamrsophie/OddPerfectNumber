import OddPerfect.LargestPrimeSignedMulti
import OddPerfect.LargestPrimeSignedMore
import OddPerfect.Euler

/-!
# Values of the signed capacity with any number of senders

Values of `signedCapMulti m` computed by `decide +kernel`, and the resulting bounds on the
exponent `e_P` of the largest prime factor `P` of an odd perfect number when the odd part of
`P - 1` is `m`. Where the capacity is `3` modulo `4` the bound drops by one, since no exponent
of an odd perfect number is `3` modulo `4` (the special prime has exponent `1` modulo `4`, all
other exponents are even).

For `m = 13, 15, 21, 25` the new capacity equals the landed `signedCapFine m`; these are no
gains. The bounds for `m = 27, …, 101` improve on `signedCapFine m`.

These hold for every odd perfect number whose largest prime factor `P` has the stated odd part
of `P - 1`. The odd part is not bounded, so no contradiction follows and nothing is excluded.
Novelty was not verified.
-/

namespace OddPerfect

variable {N : ℕ}

/-- No exponent of an odd perfect number is `3` modulo `4`. -/
private theorem lpsm_factorization_mod_four_ne_three (h : OddPerfect N) {P : ℕ}
    (hP : P.Prime) : N.factorization P % 4 ≠ 3 := by
  obtain ⟨q, -, -, -, hq4, hev⟩ := exists_special_prime h
  by_cases hPq : P = q
  · subst hPq
    omega
  · obtain ⟨k, hk⟩ := hev P hP hPq
    omega

/-- For `m = 13` the capacity equals the landed one: `signedCapMulti 13 = signedCapFine 13 = 25`. -/
theorem signedCapMulti_eq_signedCapFine_thirteen : signedCapMulti 13 = signedCapFine 13 := by
  decide +kernel

/-- For `m = 15` the capacity equals the landed one: `signedCapMulti 15 = signedCapFine 15 = 23`. -/
theorem signedCapMulti_eq_signedCapFine_fifteen : signedCapMulti 15 = signedCapFine 15 := by
  decide +kernel

/-- For `m = 21` the capacity equals the landed one: `signedCapMulti 21 = signedCapFine 21 = 35`. -/
theorem signedCapMulti_eq_signedCapFine_twentyone : signedCapMulti 21 = signedCapFine 21 := by
  decide +kernel

/-- For `m = 25` the capacity equals the landed one: `signedCapMulti 25 = signedCapFine 25 = 47`. -/
theorem signedCapMulti_eq_signedCapFine_twentyfive : signedCapMulti 25 = signedCapFine 25 := by
  decide +kernel

/-- The value `signedCapMulti 27 = 48`. -/
theorem signedCapMulti_twentyseven : signedCapMulti 27 = 48 := by decide +kernel

/-- If the odd part of `P - 1` is `27`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 48`. -/
theorem factorization_largest_le_fortyeight_of_odd_part_twentyseven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 27) : N.factorization P ≤ 48 :=
  signedCapMulti_twentyseven ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 29 = 61`. -/
theorem signedCapMulti_twentynine : signedCapMulti 29 = 61 := by decide +kernel

/-- If the odd part of `P - 1` is `29`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 61`. -/
theorem factorization_largest_le_sixtyone_of_odd_part_twentynine (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 29) : N.factorization P ≤ 61 :=
  signedCapMulti_twentynine ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 31 = 66`. -/
theorem signedCapMulti_thirtyone : signedCapMulti 31 = 66 := by decide +kernel

/-- If the odd part of `P - 1` is `31`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 66`. -/
theorem factorization_largest_le_sixtysix_of_odd_part_thirtyone (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 31) : N.factorization P ≤ 66 :=
  signedCapMulti_thirtyone ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 33 = 58`. -/
theorem signedCapMulti_thirtythree : signedCapMulti 33 = 58 := by decide +kernel

/-- If the odd part of `P - 1` is `33`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 58`. -/
theorem factorization_largest_le_fiftyeight_of_odd_part_thirtythree (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 33) : N.factorization P ≤ 58 :=
  signedCapMulti_thirtythree ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 35 = 64`. -/
theorem signedCapMulti_thirtyfive : signedCapMulti 35 = 64 := by decide +kernel

/-- If the odd part of `P - 1` is `35`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 64`. -/
theorem factorization_largest_le_sixtyfour_of_odd_part_thirtyfive (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 35) : N.factorization P ≤ 64 :=
  signedCapMulti_thirtyfive ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 37 = 79`. -/
theorem signedCapMulti_thirtyseven : signedCapMulti 37 = 79 := by decide +kernel

/-- If the odd part of `P - 1` is `37`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 78`. The capacity is `79`, which is `3` modulo `4`. -/
theorem factorization_largest_le_seventyeight_of_odd_part_thirtyseven (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 37) : N.factorization P ≤ 78 := by
  have h1 := signedCapMulti_thirtyseven ▸
    factorization_largest_le_signedCapMulti h hP hmax hm (by decide)
  have h2 := lpsm_factorization_mod_four_ne_three h (Nat.prime_of_mem_primeFactors hP)
  omega

/-- The value `signedCapMulti 39 = 69`. -/
theorem signedCapMulti_thirtynine : signedCapMulti 39 = 69 := by decide +kernel

/-- If the odd part of `P - 1` is `39`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 69`. -/
theorem factorization_largest_le_sixtynine_of_odd_part_thirtynine (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 39) : N.factorization P ≤ 69 :=
  signedCapMulti_thirtynine ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 41 = 87`. -/
theorem signedCapMulti_fortyone : signedCapMulti 41 = 87 := by decide +kernel

/-- If the odd part of `P - 1` is `41`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 86`. The capacity is `87`, which is `3` modulo `4`. -/
theorem factorization_largest_le_eightysix_of_odd_part_fortyone (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 41) : N.factorization P ≤ 86 := by
  have h1 := signedCapMulti_fortyone ▸
    factorization_largest_le_signedCapMulti h hP hmax hm (by decide)
  have h2 := lpsm_factorization_mod_four_ne_three h (Nat.prime_of_mem_primeFactors hP)
  omega

/-- The value `signedCapMulti 45 = 76`. -/
theorem signedCapMulti_fortyfive : signedCapMulti 45 = 76 := by decide +kernel

/-- If the odd part of `P - 1` is `45`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 76`. -/
theorem factorization_largest_le_seventysix_of_odd_part_fortyfive (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 45) : N.factorization P ≤ 76 :=
  signedCapMulti_fortyfive ▸ factorization_largest_le_signedCapMulti h hP hmax hm (by decide)

/-- The value `signedCapMulti 63 = 111`. -/
theorem signedCapMulti_sixtythree : signedCapMulti 63 = 111 := by decide +kernel

/-- If the odd part of `P - 1` is `63`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 110`. The capacity is `111`, which is `3` modulo `4`. -/
theorem factorization_largest_le_onehundredten_of_odd_part_sixtythree (h : OddPerfect N) {P a : ℕ}
    (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 63) : N.factorization P ≤ 110 := by
  have h1 := signedCapMulti_sixtythree ▸
    factorization_largest_le_signedCapMulti h hP hmax hm (by decide)
  have h2 := lpsm_factorization_mod_four_ne_three h (Nat.prime_of_mem_primeFactors hP)
  omega

/-- The value `signedCapMulti 101 = 219`. -/
theorem signedCapMulti_onehundredone : signedCapMulti 101 = 219 := by decide +kernel

/-- If the odd part of `P - 1` is `101`, where `P` is the largest prime factor of an odd perfect
number `N`, then `v_P(N) ≤ 218`. The capacity is `219`, which is `3` modulo `4`. -/
theorem factorization_largest_le_twohundredeighteen_of_odd_part_onehundredone (h : OddPerfect N)
    {P a : ℕ} (hP : P ∈ N.primeFactors) (hmax : ∀ r ∈ N.primeFactors, r ≤ P)
    (hm : P - 1 = 2 ^ a * 101) : N.factorization P ≤ 218 := by
  have h1 := signedCapMulti_onehundredone ▸
    factorization_largest_le_signedCapMulti h hP hmax hm (by decide)
  have h2 := lpsm_factorization_mod_four_ne_three h (Nat.prime_of_mem_primeFactors hP)
  omega

end OddPerfect

#print axioms OddPerfect.signedCapMulti_eq_signedCapFine_thirteen
#print axioms OddPerfect.signedCapMulti_eq_signedCapFine_fifteen
#print axioms OddPerfect.signedCapMulti_eq_signedCapFine_twentyone
#print axioms OddPerfect.signedCapMulti_eq_signedCapFine_twentyfive
#print axioms OddPerfect.signedCapMulti_twentyseven
#print axioms OddPerfect.factorization_largest_le_fortyeight_of_odd_part_twentyseven
#print axioms OddPerfect.signedCapMulti_twentynine
#print axioms OddPerfect.factorization_largest_le_sixtyone_of_odd_part_twentynine
#print axioms OddPerfect.signedCapMulti_thirtyone
#print axioms OddPerfect.factorization_largest_le_sixtysix_of_odd_part_thirtyone
#print axioms OddPerfect.signedCapMulti_thirtythree
#print axioms OddPerfect.factorization_largest_le_fiftyeight_of_odd_part_thirtythree
#print axioms OddPerfect.signedCapMulti_thirtyfive
#print axioms OddPerfect.factorization_largest_le_sixtyfour_of_odd_part_thirtyfive
#print axioms OddPerfect.signedCapMulti_thirtyseven
#print axioms OddPerfect.factorization_largest_le_seventyeight_of_odd_part_thirtyseven
#print axioms OddPerfect.signedCapMulti_thirtynine
#print axioms OddPerfect.factorization_largest_le_sixtynine_of_odd_part_thirtynine
#print axioms OddPerfect.signedCapMulti_fortyone
#print axioms OddPerfect.factorization_largest_le_eightysix_of_odd_part_fortyone
#print axioms OddPerfect.signedCapMulti_fortyfive
#print axioms OddPerfect.factorization_largest_le_seventysix_of_odd_part_fortyfive
#print axioms OddPerfect.signedCapMulti_sixtythree
#print axioms OddPerfect.factorization_largest_le_onehundredten_of_odd_part_sixtythree
#print axioms OddPerfect.signedCapMulti_onehundredone
#print axioms OddPerfect.factorization_largest_le_twohundredeighteen_of_odd_part_onehundredone
