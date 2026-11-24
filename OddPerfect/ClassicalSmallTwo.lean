import OddPerfect.SpecialPrime
import OddPerfect.ExcessSupport
import OddPerfect.EscapeRowUnique

/-!
# Two coprime factors in the special row, and a counting corollary

* `sigma_special_split`: for a prime `q ≡ 1 (mod 4)` and an exponent `a ≡ 1 (mod 4)` with
  `1 < a`, write `a + 1 = 2 * k`. Then `σ(q ^ a) = 2 * d₁ * d₂` with
  `d₁ = 1 + q + ⋯ + q ^ (k - 1)` and `d₂ = (q ^ k + 1) / 2`, both odd, both greater than `1`, and
  coprime. Compare Levit, Bull. Amer. Math. Soc. 53 (1947), Lemma 2.
* `not_sigma_special_half_eq_prime_pow`: hence `σ(q ^ a) / 2` is not a power of a prime.
* `exists_two_primes_dvd_sigma_special`: for an odd perfect number with special prime `q` of
  exponent `a > 1`, two distinct prime factors of `N` divide `σ(q ^ a)`.
* `card_squarePrimes_le_one_add`: the counting lemma `card_squarePrimes_le` combined with
  `card_escapeRows_le_one_all`, for every odd perfect number.

The small exclusion `3 ∣ N → 11 ∣ N → v_5(N) ≠ 2` is already a consequence of the landed
`factorization_five_eq_one_of_eleven` and is not restated. No novelty is claimed.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The special row splits into two odd coprime factors greater than `1`: for a prime
`q ≡ 1 (mod 4)` and `a ≡ 1 (mod 4)`, `1 < a`, `a + 1 = 2 * k`, we have
`σ(q ^ a) = 2 * d₁ * d₂` with `d₁ = ∑_{i < k} q ^ i` and `d₂ = (q ^ k + 1) / 2`. Compare Levit,
Bull. Amer. Math. Soc. 53 (1947), Lemma 2. -/
theorem sigma_special_split {q a k : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (ha4 : a % 4 = 1)
    (ha : 1 < a) (hk : a + 1 = 2 * k) :
    σ 1 (q ^ a) = 2 * (∑ i ∈ range k, q ^ i) * ((q ^ k + 1) / 2) ∧
      Odd (∑ i ∈ range k, q ^ i) ∧ Odd ((q ^ k + 1) / 2) ∧
      1 < ∑ i ∈ range k, q ^ i ∧ 1 < (q ^ k + 1) / 2 ∧
      Nat.Coprime (∑ i ∈ range k, q ^ i) ((q ^ k + 1) / 2) := by
  have hsum : σ 1 (q ^ a) = (∑ i ∈ range k, q ^ i) * (q ^ k + 1) := by
    rw [sigma_one_apply_prime_pow hq, show a + 1 = k + k by omega, sum_range_add]
    simp only [pow_add, ← mul_sum]
    ring
  set d₁ := ∑ i ∈ range k, q ^ i with hd₁
  have hq5 : 5 ≤ q := by have := hq.two_le; omega
  have hk3 : 3 ≤ k := by omega
  have hkodd : k % 2 = 1 := by omega
  have hqk4 : q ^ k % 4 = 1 := by rw [Nat.pow_mod, hq4, one_pow]; rfl
  have hqk : q ≤ q ^ k := Nat.le_self_pow (by omega) q
  have h2d₂ : 2 * ((q ^ k + 1) / 2) = q ^ k + 1 := by omega
  -- `d₁` is odd
  have hd₁odd : d₁ % 2 = 1 := by
    have h1 : ∀ i ∈ range k, q ^ i % 2 = 1 := fun i _ => by
      rw [Nat.pow_mod, show q % 2 = 1 by omega, one_pow]; rfl
    rw [hd₁, sum_nat_mod, sum_congr rfl h1, sum_const, card_range, smul_eq_mul, mul_one]
    exact hkodd
  have hd₁gt : 1 < d₁ := by
    have := single_le_sum (f := fun i => q ^ i) (fun i _ => Nat.zero_le _)
      (mem_range.mpr (show 1 < k by omega))
    simp only [pow_one] at this
    omega
  refine ⟨by rw [hsum, mul_comm 2, mul_assoc, h2d₂], Nat.odd_iff.mpr hd₁odd,
    Nat.odd_iff.mpr (by omega), hd₁gt, by omega, ?_⟩
  -- coprimality through a Bezout identity in `ℤ`
  obtain ⟨t, ht⟩ : ∃ t, d₁ = 2 * t + 1 := ⟨d₁ / 2, by omega⟩
  rw [← Nat.isCoprime_iff_coprime]
  have e1 : (d₁ : ℤ) * ((q : ℤ) - 1) = (q : ℤ) ^ k - 1 := by
    rw [hd₁]; push_cast; exact geom_sum_mul _ _
  have e2 : 2 * (((q ^ k + 1) / 2 : ℕ) : ℤ) = (q : ℤ) ^ k + 1 := by exact_mod_cast h2d₂
  have e3 : (d₁ : ℤ) = 2 * t + 1 := by exact_mod_cast ht
  exact ⟨1 + t * ((q : ℤ) - 1), -2 * t, by linear_combination (t : ℤ) * e1 - (t : ℤ) * e2 + e3⟩

/-- `σ(q ^ a) / 2` is not a power of a prime when `q ≡ a ≡ 1 (mod 4)` and `1 < a`. Compare Levit,
Bull. Amer. Math. Soc. 53 (1947), Lemma 2. -/
theorem not_sigma_special_half_eq_prime_pow {q a : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (ha4 : a % 4 = 1) (ha : 1 < a) :
    ¬ ∃ r w : ℕ, r.Prime ∧ σ 1 (q ^ a) / 2 = r ^ w := by
  rintro ⟨r, w, hr, hw⟩
  obtain ⟨hs, -, -, h1, h2, hc⟩ :=
    sigma_special_split hq hq4 ha4 ha (show a + 1 = 2 * ((a + 1) / 2) by omega)
  set d₁ := ∑ i ∈ range ((a + 1) / 2), q ^ i
  set d₂ := (q ^ ((a + 1) / 2) + 1) / 2
  have hw' : d₁ * d₂ = r ^ w := by
    rw [← hw, hs, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have key : ∀ d, 1 < d → d ∣ r ^ w → r ∣ d := by
    intro d hd hdr
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    have := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow (hpd.trans hdr))
    exact this ▸ hpd
  have hr1 := key d₁ h1 (hw' ▸ dvd_mul_right _ _)
  have hr2 := key d₂ h2 (hw' ▸ dvd_mul_left _ _)
  have := Nat.dvd_gcd hr1 hr2
  rw [hc, Nat.dvd_one] at this
  exact hr.one_lt.ne' this

/-- For an odd perfect number `N` with special prime `q` of exponent `a > 1`, two distinct prime
factors of `N` divide `σ(q ^ a)`. Compare Levit, Bull. Amer. Math. Soc. 53 (1947), Lemma 2. -/
theorem exists_two_primes_dvd_sigma_special {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (ha : 1 < N.factorization q) :
    ∃ p₁ p₂ : ℕ, p₁ ≠ p₂ ∧ p₁ ∈ N.primeFactors ∧ p₂ ∈ N.primeFactors ∧
      p₁ ∣ σ 1 (q ^ N.factorization q) ∧ p₂ ∣ σ 1 (q ^ N.factorization q) := by
  obtain ⟨hq4, ha4⟩ := special_mod_four h hq hodd
  set a := N.factorization q
  obtain ⟨hs, o1, o2, h1, h2, hc⟩ :=
    sigma_special_split hq hq4 ha4 ha (show a + 1 = 2 * ((a + 1) / 2) by omega)
  set d₁ := ∑ i ∈ range ((a + 1) / 2), q ^ i
  set d₂ := (q ^ ((a + 1) / 2) + 1) / 2
  have hσ : σ 1 (q ^ a) ∣ 2 * N := OPNStarter.component_sigma_dvd h.perfect hq rfl
  have pick : ∀ d, 1 < d → Odd d → d ∣ σ 1 (q ^ a) →
      ∃ p, p.Prime ∧ p ∣ d ∧ p ∈ N.primeFactors ∧ p ∣ σ 1 (q ^ a) := by
    intro d hd od hdσ
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    have hpo : Odd p := od.of_dvd_nat hpd
    have hp2 : p.Coprime 2 := Nat.coprime_two_right.mpr hpo
    refine ⟨p, hp, hpd, Nat.mem_primeFactors.mpr ⟨hp, ?_, h.ne_zero⟩, hpd.trans hdσ⟩
    exact hp2.dvd_of_dvd_mul_left ((hpd.trans hdσ).trans hσ)
  obtain ⟨p₁, hp₁, hpd₁, hm₁, hσ₁⟩ := pick d₁ h1 o1 (hs ▸ (dvd_mul_left _ 2).mul_right _)
  obtain ⟨p₂, hp₂, hpd₂, hm₂, hσ₂⟩ := pick d₂ h2 o2 (hs ▸ dvd_mul_left _ _)
  refine ⟨p₁, p₂, ?_, hm₁, hm₂, hσ₁, hσ₂⟩
  rintro rfl
  have := Nat.dvd_gcd hpd₁ hpd₂
  rw [hc, Nat.dvd_one] at this
  exact hp₁.one_lt.ne' this

/-- For every odd perfect number `N` and its special prime `q`, the number of square primes is
at most `1` plus the total exponent of the prime factors `r ≠ q`, `r ≠ 3` with
`r ≡ 1 (mod 3)`. This combines `card_squarePrimes_le` with `card_escapeRows_le_one_all`. -/
theorem card_squarePrimes_le_one_add {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) :
    (squarePrimes N q).card ≤ 1 +
      ∑ r ∈ N.primeFactors.filter (fun r => r ≠ q ∧ r ≠ 3 ∧ r % 3 = 1), N.factorization r := by
  have h1 := card_squarePrimes_le (q := q) h
  have h2 := card_escapeRows_le_one_all h hq hodd
  omega

end OddPerfect

#print axioms OddPerfect.sigma_special_split
#print axioms OddPerfect.not_sigma_special_half_eq_prime_pow
#print axioms OddPerfect.exists_two_primes_dvd_sigma_special
#print axioms OddPerfect.card_squarePrimes_le_one_add
