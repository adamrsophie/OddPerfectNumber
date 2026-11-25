import OddPerfect.EulerIndexPrimePower
import OddPerfect.EulerIndexSquare
import OddPerfect.SpecialBelowAll

/-!
# Prime support of the Euler index

Let `N = q ^ k * m ^ 2` be an odd perfect number in Euler's form, with `q` the special prime
and `q ∤ m`, and let `J = eulerIndex q k m = σ(m ^ 2) / q ^ k`. This module shows that `J` has
at least two distinct prime factors in several cases.

* `k = 1`: `J` is not a prime power, `2 m ≤ J`, `J` is not squarefree, and `J` has at least two
  distinct prime factors.
* Two half sum lemmas: for `U > 1` with `U ≡ 1 (mod 4)` neither `(U ^ 3 + 1) / 2` nor
  `(U ^ 5 + 1) / 2` is a square.
* `k ≠ 1`: if `S = (q ^ ℓ + 1) / 2` with `ℓ = (k + 1) / 2` is not a square, then two distinct
  primes have odd valuation in `J`. This applies when `q ≡ 5 (mod 8)`, `k ≡ 5 (mod 12)` or
  `k ≡ 9 (mod 20)`.
* A conditional form for every `k`, under the statement `HalfPowerNotSquare`. That statement
  is not proved in this module; it is proved in `OddPerfect.EulerIndexSupportAll`
  (`halfPowerNotSquare`), which also gives the form without hypothesis.

All of this is known mathematics or elementary; novelty not verified.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

variable {N q k m : ℕ}

/-! ## Private helpers -/

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma special_facts (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ k * m ^ 2)
    (hqm : ¬ q ∣ m) : q % 4 = 1 ∧ k % 4 = 1 := by
  have hm : m ≠ 0 := by rintro rfl; exact hqm (dvd_zero q)
  have hfac : N.factorization q = k := by
    rw [hN, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hm),
      Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply,
      Finsupp.smul_apply, hq.factorization_self, Nat.factorization_eq_zero_of_not_dvd hqm]
    simp
  have hk : Odd k := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ho
    · exact absurd ⟨q ^ j * m, by rw [hN, hj]; ring⟩ (not_isSquare h)
    · exact ho
  have h4 := special_mod_four h hq (hfac ▸ hk)
  rwa [hfac] at h4

/-- A coprime factor of a square is a square. -/
private lemma isSquare_left_of_coprime {a b c : ℕ} (hab : Nat.Coprime a b)
    (h : a * b = c ^ 2) : IsSquare a := by
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hab) h
  exact ⟨d, by rw [hd, sq]⟩

/-- If `A F = t ^ 2` and `gcd(A, F) ∣ p` for a prime `p`, then `F` is a square or `p` times a
square. -/
private lemma sq_or_mul_sq {A F t p : ℕ} (hp : p.Prime) (hg : Nat.gcd A F ∣ p)
    (h : A * F = t ^ 2) : IsSquare F ∨ ∃ s, F = p * s ^ 2 := by
  rcases (Nat.dvd_prime hp).mp hg with h1 | h1
  · left
    exact isSquare_left_of_coprime (Nat.Coprime.symm h1) (by rw [mul_comm]; exact h)
  · right
    obtain ⟨A', hA⟩ : p ∣ A := h1 ▸ Nat.gcd_dvd_left A F
    obtain ⟨F', hF⟩ : p ∣ F := h1 ▸ Nat.gcd_dvd_right A F
    have hc : Nat.Coprime A' F' := by
      have h2 : p * Nat.gcd A' F' = p * 1 := by
        rw [← Nat.gcd_mul_left, ← hA, ← hF, h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    have hpt : p ∣ t := hp.dvd_of_dvd_pow ⟨p * A' * F', by rw [← h, hA, hF]; ring⟩
    obtain ⟨s, rfl⟩ := hpt
    have hAF : A' * F' = s ^ 2 := by
      have h3 : p ^ 2 * (A' * F') = p ^ 2 * s ^ 2 := by rw [← mul_pow, ← h, hA, hF]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
    obtain ⟨d, hd⟩ := isSquare_left_of_coprime hc.symm (by rw [mul_comm]; exact hAF)
    exact ⟨d, by rw [hF, hd, sq]⟩

/-- Two distinct primes of odd valuation give two distinct prime factors. -/
private lemma two_le_card_of_odd {n p₁ p₂ : ℕ} (hne : p₁ ≠ p₂)
    (h₁ : Odd (n.factorization p₁)) (h₂ : Odd (n.factorization p₂)) :
    2 ≤ n.primeFactors.card := by
  have hm : ∀ p, Odd (n.factorization p) → p ∈ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0
    rw [h0] at hp
    exact Nat.not_odd_zero hp
  exact Finset.one_lt_card.mpr ⟨p₁, hm _ h₁, p₂, hm _ h₂, hne⟩

/-! ## Part A: special exponent one -/

/-- For an odd perfect number `q * m ^ 2` with special prime `q` and `q ∤ m`, the Euler index
`σ(m ^ 2) / q` is not a prime power `r ^ b` with `b > 0`. Known mathematics or elementary;
novelty not verified. -/
theorem eulerIndex_ne_prime_pow_of_exponent_one {r b : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) (hr : r.Prime) (hb : 0 < b) :
    eulerIndex q 1 m ≠ r ^ b := by
  intro hI
  obtain ⟨M, -, -, hMo, -, -, hσr, hq1, hσM, -⟩ :=
    eulerIndex_prime_pow_normal_form h hq hN hqm hr hb hI
  exact noSquareCycle r b M hr hb hMo hσM (by rw [hσr]; omega)

/-- For an odd perfect number `q * m ^ 2` with special prime `q` and `q ∤ m`, the Euler index
is at least `2 m`. Known mathematics or elementary; novelty not verified. -/
theorem two_mul_le_eulerIndex_of_exponent_one (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) : 2 * m ≤ eulerIndex q 1 m := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hi := sigma_special_mul_eulerIndex h hq hN1 hqm
  rw [sigma_one_apply_prime_pow hq] at hi
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, pow_zero,
    pow_one] at hi
  have hlt := special_lt_root h hq hN1 hqm
  have hm : 0 < m := by omega
  have h1 : m * (2 * m) ≤ m * eulerIndex q 1 m := by
    have : (1 + q) * eulerIndex q 1 m ≤ m * eulerIndex q 1 m :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  exact Nat.le_of_mul_le_mul_left h1 hm

/-- For an odd perfect number `q * m ^ 2` with special prime `q` and `q ∤ m`, the Euler index
is not squarefree. Known mathematics or elementary; novelty not verified. -/
theorem not_squarefree_eulerIndex_of_exponent_one (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) : ¬ Squarefree (eulerIndex q 1 m) := by
  intro hsf
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have hdv := (hsf.dvd_pow_iff_dvd two_ne_zero).mp (eulerIndex_dvd_sq h hq hN1 hqm)
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hqm (dvd_zero q))
  have := Nat.le_of_dvd hm hdv
  have := two_mul_le_eulerIndex_of_exponent_one h hq hN hqm
  omega

/-- For an odd perfect number `q * m ^ 2` with special prime `q` and `q ∤ m`, the Euler index
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem two_le_card_primeFactors_eulerIndex_of_exponent_one (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q * m ^ 2) (hqm : ¬ q ∣ m) :
    2 ≤ (eulerIndex q 1 m).primeFactors.card := by
  have hN1 : N = q ^ 1 * m ^ 2 := by rw [pow_one]; exact hN
  have h3 := three_le_eulerIndex h hq hN1 hqm
  by_contra hlt
  rcases (show (eulerIndex q 1 m).primeFactors.card = 0 ∨
      (eulerIndex q 1 m).primeFactors.card = 1 by omega) with h0 | h1
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h0
    omega
  · obtain ⟨r, b, hr, hb, hrb⟩ :=
      isPrimePow_nat_iff _ |>.mp (isPrimePow_iff_card_primeFactors_eq_one.mpr h1)
    exact eulerIndex_ne_prime_pow_of_exponent_one h hq hN hqm hr hb hrb.symm

/-! ## Part B: two half sums that are not squares -/

/-- For `U > 1` with `U ≡ 1 (mod 4)`, `(U ^ 3 + 1) / 2` is not a square. Known mathematics or
elementary; novelty not verified. -/
theorem not_isSquare_half_cube_succ {U : ℕ} (hU : 1 < U) (h4 : U % 4 = 1) :
    ¬ IsSquare ((U ^ 3 + 1) / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, U = 4 * a + 1 := ⟨U / 4, by omega⟩
  have ha : 1 ≤ a := by omega
  rintro ⟨t, ht⟩
  have hfac : ((4 * a + 1) ^ 3 + 1) / 2 = (2 * a + 1) * (16 * a ^ 2 + 4 * a + 1) := by
    rw [show (4 * a + 1) ^ 3 + 1 = 2 * ((2 * a + 1) * (16 * a ^ 2 + 4 * a + 1)) by ring]
    omega
  rw [hfac] at ht
  have hg : Nat.gcd (2 * a + 1) (16 * a ^ 2 + 4 * a + 1) ∣ 3 := by
    have h1 := Nat.gcd_dvd_left (2 * a + 1) (16 * a ^ 2 + 4 * a + 1)
    have h2 := Nat.gcd_dvd_right (2 * a + 1) (16 * a ^ 2 + 4 * a + 1)
    have he : 16 * a ^ 2 + 4 * a + 1 + 2 * (2 * a + 1) = (2 * a + 1) * (8 * a) + 3 := by ring
    have h3 := dvd_add h2 (dvd_mul_of_dvd_right h1 2)
    rw [he] at h3
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).mp h3
  rcases sq_or_mul_sq Nat.prime_three hg (by rw [ht, sq]) with ⟨s, hs⟩ | ⟨s, hs⟩
  · rcases le_or_gt s (4 * a) with hle | hlt
    · have := Nat.mul_le_mul hle hle
      nlinarith
    · have hle : 4 * a + 1 ≤ s := hlt
      have := Nat.mul_le_mul hle hle
      nlinarith
  · obtain ⟨w, c, hc, rfl⟩ : ∃ w c, c < 2 ∧ s = 2 * w + c :=
      ⟨s / 2, s % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases c <;> ring_nf at hs <;> omega

/-- For `U > 1` with `U ≡ 1 (mod 4)`, `(U ^ 5 + 1) / 2` is not a square. Known mathematics or
elementary; novelty not verified. -/
theorem not_isSquare_half_fifth_succ {U : ℕ} (hU : 1 < U) (h4 : U % 4 = 1) :
    ¬ IsSquare ((U ^ 5 + 1) / 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, U = 4 * a + 1 := ⟨U / 4, by omega⟩
  have ha : 1 ≤ a := by omega
  rintro ⟨t, ht⟩
  set F := 256 * a ^ 4 + 192 * a ^ 3 + 64 * a ^ 2 + 8 * a + 1 with hFdef
  have hfac : ((4 * a + 1) ^ 5 + 1) / 2 = (2 * a + 1) * F := by
    rw [show (4 * a + 1) ^ 5 + 1 = 2 * ((2 * a + 1) * F) by rw [hFdef]; ring]
    omega
  rw [hfac] at ht
  have hg : Nat.gcd (2 * a + 1) F ∣ 5 := by
    have h1 := Nat.gcd_dvd_left (2 * a + 1) F
    have h2 := Nat.gcd_dvd_right (2 * a + 1) F
    have he : F + 4 * (2 * a + 1) =
        (2 * a + 1) * (128 * a ^ 3 + 32 * a ^ 2 + 16 * a) + 5 := by rw [hFdef]; ring
    have h3 := dvd_add h2 (dvd_mul_of_dvd_right h1 4)
    rw [he] at h3
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).mp h3
  rcases sq_or_mul_sq Nat.prime_five hg (by rw [ht, sq]) with ⟨s, hs⟩ | ⟨s, hs⟩
  · -- with `T = 32 a ^ 2 + 12 a + 1` we have `T ^ 2 < 4 F < (T + 1) ^ 2`
    have hlo : (32 * a ^ 2 + 12 * a + 1) * (32 * a ^ 2 + 12 * a + 1) + (48 * a ^ 2 + 8 * a + 3)
        = 4 * F := by rw [hFdef]; ring
    have hhi : 4 * F + (16 * a ^ 2 + 16 * a) =
        (32 * a ^ 2 + 12 * a + 2) * (32 * a ^ 2 + 12 * a + 2) := by rw [hFdef]; ring
    have h4F : 4 * F = (2 * s) * (2 * s) := by rw [hs]; ring
    rcases le_or_gt (2 * s) (32 * a ^ 2 + 12 * a + 1) with hle | hlt
    · have := Nat.mul_le_mul hle hle
      omega
    · have hle : 32 * a ^ 2 + 12 * a + 2 ≤ 2 * s := hlt
      have := Nat.mul_le_mul hle hle
      have : 0 < 16 * a ^ 2 + 16 * a := by positivity
      omega
  · obtain ⟨w, c, hc, rfl⟩ : ∃ w c, c < 4 ∧ s = 4 * w + c :=
      ⟨s / 4, s % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [hFdef] at hs
    interval_cases c <;> ring_nf at hs <;> omega

/-! ## Part C: special exponent other than one -/

/-- The shared argument: if `S` is not both a square and `q ≡ 1 (mod 8)`, two distinct primes
have odd valuation in the index. -/
private lemma two_odd_core (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ k * m ^ 2)
    (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hS : ¬ (IsSquare ((q ^ ((k + 1) / 2) + 1) / 2) ∧ q % 8 = 1)) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂) := by
  obtain ⟨d₂, d₁, hd, hsf⟩ := Nat.sq_mul_squarefree (eulerIndex q k m)
  have hJ := three_le_eulerIndex h hq hN hqm
  have hd' : eulerIndex q k m = d₁ ^ 2 * d₂ := hd.symm
  have hd₁ : d₁ ≠ 0 := by rintro rfl; rw [hd'] at hJ; simp at hJ
  have hd₂ : d₂ ≠ 0 := hsf.ne_zero
  have hnc : ¬ Nat.Coprime d₂ ((q ^ ((k + 1) / 2) + 1) / 2) := fun hc =>
    hS (special_mod_eight_of_eulerIndex_coprime h hq hN hqm hd' hc)
  obtain ⟨p₁, hp₁, hp₁d, hp₁S⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hndvd : ¬ d₂ ∣ (q ^ ((k + 1) / 2) + 1) / 2 := fun hdS =>
    hk (exponent_eq_one_of_eulerIndex_eq_sq_mul h hq hN hqm hd' hdS)
  obtain ⟨p₂, hp₂, hp₂d, hp₂S⟩ :
      ∃ p, p.Prime ∧ p ∣ d₂ ∧ ¬ p ∣ (q ^ ((k + 1) / 2) + 1) / 2 := by
    by_contra hall
    push Not at hall
    apply hndvd
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => hall p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hval : ∀ p, p.Prime → p ∣ d₂ → Odd ((eulerIndex q k m).factorization p) := by
    intro p hp hpd
    rw [hd', Nat.factorization_mul (pow_ne_zero 2 hd₁) hd₂, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_one_of_squarefree hsf hp hpd]
    exact ⟨_, rfl⟩
  exact ⟨p₁, p₂, hp₁, hp₂, fun he => hp₂S (he ▸ hp₁S), hval _ hp₁ hp₁d, hval _ hp₂ hp₂d⟩

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and `k ≠ 1`, if
`(q ^ ℓ + 1) / 2` with `ℓ = (k + 1) / 2` is not a square, then two distinct primes have odd
valuation in the Euler index. Known mathematics or elementary; novelty not verified. -/
theorem exists_two_odd_valuation_of_half_not_square (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hS : ¬ IsSquare ((q ^ ((k + 1) / 2) + 1) / 2)) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂) :=
  two_odd_core h hq hN hqm hk fun h' => hS h'.1

/-- Item 7 together with the count of prime factors. -/
private lemma odd_and_card (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hS : ¬ IsSquare ((q ^ ((k + 1) / 2) + 1) / 2)) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩ :=
    exists_two_odd_valuation_of_half_not_square h hq hN hqm hk hS
  exact ⟨⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩, two_le_card_of_odd hne h₁ h₂⟩

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q ≡ 5 (mod 8)`, `q ∤ m` and
`k ≠ 1`, two distinct primes have odd valuation in the Euler index, which therefore has at
least two distinct prime factors. Known mathematics or elementary; novelty not verified. -/
theorem exists_two_odd_valuation_of_mod_eight_eq_five (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1) (h8 : q % 8 = 5) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩ := two_odd_core h hq hN hqm hk fun h' => by omega
  exact ⟨⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩, two_le_card_of_odd hne h₁ h₂⟩

/-- `q ^ n ≡ 1 (mod 4)` and `q ^ n > 1` for `q ≡ 1 (mod 4)` prime and `n > 0`. -/
private lemma pow_facts (hq : q.Prime) (hq4 : q % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    1 < q ^ n ∧ q ^ n % 4 = 1 := by
  refine ⟨Nat.one_lt_pow hn hq.one_lt, ?_⟩
  simp [Nat.pow_mod, hq4]

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and
`k ≡ 5 (mod 12)`, two distinct primes have odd valuation in the Euler index, which therefore
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem exists_two_odd_valuation_of_exponent_mod_twelve (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k % 12 = 5) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  have hq4 := (special_facts h hq hN hqm).1
  refine odd_and_card h hq hN hqm (by omega) ?_
  obtain ⟨hU, hU4⟩ := pow_facts hq hq4 (n := 2 * (k / 12) + 1) (by omega)
  rw [show (k + 1) / 2 = (2 * (k / 12) + 1) * 3 by omega, pow_mul]
  exact not_isSquare_half_cube_succ hU hU4

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and
`k ≡ 9 (mod 20)`, two distinct primes have odd valuation in the Euler index, which therefore
has at least two distinct prime factors. Known mathematics or elementary; novelty not
verified. -/
theorem exists_two_odd_valuation_of_exponent_mod_twenty (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k % 20 = 9) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  have hq4 := (special_facts h hq hN hqm).1
  refine odd_and_card h hq hN hqm (by omega) ?_
  obtain ⟨hU, hU4⟩ := pow_facts hq hq4 (n := 2 * (k / 20) + 1) (by omega)
  rw [show (k + 1) / 2 = (2 * (k / 20) + 1) * 5 by omega, pow_mul]
  exact not_isSquare_half_fifth_succ hU hU4

/-! ## A conditional form for every exponent -/

/-- The statement that `(q ^ ℓ + 1) / 2` is never a square for a prime `q ≡ 1 (mod 4)` and an
odd `ℓ ≥ 3`; equivalently, the equation `2 * x ^ 2 = q ^ ℓ + 1` has no solution in that range.
It is not proved in this module; the module `OddPerfect.EulerIndexSupportAll` proves it
(`halfPowerNotSquare`) by an elementary argument. For odd `ℓ ≥ 5` it is a case of Theorem 1.1
of M. A. Bennett and C. M. Skinner, Canad. J. Math. 56 (2004), on `x ^ n + y ^ n = 2 * z ^ 2`
with `n ≥ 4` (page checked); for `ℓ = 3` no published source was checked.
For `k > 1`, Y. Hirakawa (arXiv 2309.17084, abstract checked) states that the index is neither
a square nor a prime times a square. -/
def HalfPowerNotSquare : Prop :=
  ∀ q ℓ : ℕ, q.Prime → q % 4 = 1 → Odd ℓ → 3 ≤ ℓ → ¬ IsSquare ((q ^ ℓ + 1) / 2)

/-- Under `HalfPowerNotSquare` (not proved in this module; the form without hypothesis is
`OddPerfect.two_le_card_primeFactors_eulerIndex`), the Euler index of every odd perfect number
`q ^ k * m ^ 2` with special prime `q` and `q ∤ m` has at least two distinct prime factors.
Known mathematics or elementary; novelty not verified. -/
theorem two_le_card_primeFactors_eulerIndex_of_halfPowerNotSquare (hyp : HalfPowerNotSquare)
    (h : OddPerfect N) (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) :
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  obtain ⟨hq4, hk4⟩ := special_facts h hq hN hqm
  by_cases hk : k = 1
  · subst hk
    exact two_le_card_primeFactors_eulerIndex_of_exponent_one h hq (by rw [hN, pow_one]) hqm
  · refine (odd_and_card h hq hN hqm hk ?_).2
    exact hyp q _ hq hq4 ⟨k / 4, by omega⟩ (by omega)

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q` and `q ∤ m`, the Euler
index has at least two distinct prime factors when `k = 1`, `q ≡ 5 (mod 8)`, `k ≡ 5 (mod 12)`
or `k ≡ 9 (mod 20)`. Known mathematics or elementary; novelty not verified. -/
theorem two_le_card_primeFactors_eulerIndex_of_cases (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m)
    (hc : k = 1 ∨ q % 8 = 5 ∨ k % 12 = 5 ∨ k % 20 = 9) :
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  by_cases hk : k = 1
  · subst hk
    exact two_le_card_primeFactors_eulerIndex_of_exponent_one h hq (by rw [hN, pow_one]) hqm
  rcases hc with hc | hc | hc | hc
  · exact absurd hc hk
  · exact (exists_two_odd_valuation_of_mod_eight_eq_five h hq hN hqm hk hc).2
  · exact (exists_two_odd_valuation_of_exponent_mod_twelve h hq hN hqm hc).2
  · exact (exists_two_odd_valuation_of_exponent_mod_twenty h hq hN hqm hc).2

end OddPerfect

#print axioms OddPerfect.eulerIndex_ne_prime_pow_of_exponent_one
#print axioms OddPerfect.two_mul_le_eulerIndex_of_exponent_one
#print axioms OddPerfect.not_squarefree_eulerIndex_of_exponent_one
#print axioms OddPerfect.two_le_card_primeFactors_eulerIndex_of_exponent_one
#print axioms OddPerfect.not_isSquare_half_cube_succ
#print axioms OddPerfect.not_isSquare_half_fifth_succ
#print axioms OddPerfect.exists_two_odd_valuation_of_half_not_square
#print axioms OddPerfect.exists_two_odd_valuation_of_mod_eight_eq_five
#print axioms OddPerfect.exists_two_odd_valuation_of_exponent_mod_twelve
#print axioms OddPerfect.exists_two_odd_valuation_of_exponent_mod_twenty
#print axioms OddPerfect.two_le_card_primeFactors_eulerIndex_of_halfPowerNotSquare
#print axioms OddPerfect.two_le_card_primeFactors_eulerIndex_of_cases
