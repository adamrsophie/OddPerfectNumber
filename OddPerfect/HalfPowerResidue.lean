import Mathlib.FieldTheory.Finite.Basic
import OddPerfect.SignedRepunit
import OddPerfect.EulerIndexSupport

/-!
# Necessary conditions for `(q ^ L + 1) / 2` to be a square

Let `q` be a prime with `q ≡ 1 (mod 4)` and `L ≥ 3` odd. This module shows that the equation
`q ^ L + 1 = 2 * y ^ 2` forces three congruences:

* `q ≡ 1 (mod 16)`;
* every prime factor of `L` is `1 (mod 8)`;
* the least prime factor of `L` divides `q + 1`.

These conditions contain the landed cases (`q ≡ 5 (mod 8)`, or `L` divisible by one of
`3, 5, 7, 11, 13`). They do not prove `HalfPowerNotSquare`; that proposition is proved in
`OddPerfect.EulerIndexSupportAll`, so the conditions here are never met. For odd `L ≥ 5` the
full statement is a case of Theorem 1.1 of M. A. Bennett and C. M. Skinner, Canad. J. Math. 56
(2004), on `x ^ n + y ^ n = 2 * z ^ 2` with `n ≥ 4` (page checked); for `L = 3` no published
source was checked. Nothing new is claimed.

Method, for a prime `p ∣ L` and `u = q ^ (L / p)`: with `F = (u ^ p + 1) / (u + 1)` we get
`((u + 1) / 2) * F = y ^ 2` and `F ≡ p (mod u + 1)`, so the gcd of the two factors divides `p`.
A coprime split makes `F` a square, which `alternating_sum_prime_pow_ne_sq` rules out. Hence
`p ∣ u + 1` and `F = p * s ^ 2`; comparing residues modulo `8` gives `p ≡ 1 (mod 8)`. For the
least prime factor `p`, `L / p` is prime to `p - 1`, so `q ^ (L / p) ≡ -1 (mod p)` gives
`q ≡ -1 (mod p)`.

As a corollary, under any one of the three negated conditions with `ℓ = (k + 1) / 2`, the Euler
index of an odd perfect number has two distinct primes of odd valuation.

All of this is known mathematics or elementary; novelty not verified.
-/

namespace OddPerfect

/-! ## Private helpers -/

/-- If `A * F = t ^ 2` and `gcd(A, F) ∣ p` for a prime `p`, then `F` is a square, or `p ∣ A`
and `F` is `p` times a square. -/
private lemma hpr_sq_or_mul_sq {A F t p : ℕ} (hp : p.Prime) (hg : Nat.gcd A F ∣ p)
    (h : A * F = t ^ 2) : IsSquare F ∨ (p ∣ A ∧ ∃ s, F = p * s ^ 2) := by
  rcases (Nat.dvd_prime hp).mp hg with h1 | h1
  · left
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow
      (Nat.isUnit_iff.mpr (Nat.Coprime.symm h1)) (by rw [mul_comm]; exact h)
    exact ⟨d, by rw [hd, sq]⟩
  · right
    obtain ⟨A', hA⟩ : p ∣ A := h1 ▸ Nat.gcd_dvd_left A F
    obtain ⟨F', hF⟩ : p ∣ F := h1 ▸ Nat.gcd_dvd_right A F
    refine ⟨⟨A', hA⟩, ?_⟩
    have hc : Nat.Coprime A' F' := by
      have h2 : p * Nat.gcd A' F' = p * 1 := by
        rw [← Nat.gcd_mul_left, ← hA, ← hF, h1, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hp.pos h2
    have hpt : p ∣ t := hp.dvd_of_dvd_pow ⟨p * A' * F', by rw [← h, hA, hF]; ring⟩
    obtain ⟨s, rfl⟩ := hpt
    have hAF : A' * F' = s ^ 2 := by
      have h3 : p ^ 2 * (A' * F') = p ^ 2 * s ^ 2 := by rw [← mul_pow, ← h, hA, hF]; ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
    obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow
      (Nat.isUnit_iff.mpr hc.symm) (by rw [mul_comm]; exact hAF)
    exact ⟨d, by rw [hF, hd]⟩

/-- For odd `p` with `(u + 1) * F = u ^ p + 1`, `u + 1` divides `F - p` in `ℤ`. -/
private lemma hpr_dvd_sub {u p F : ℕ} (hp : Odd p) (hF : u ^ p + 1 = (u + 1) * F) :
    ((u : ℤ) + 1) ∣ (F : ℤ) - p := by
  have hgs := geom_sum_mul (-(u : ℤ)) p
  have hneg : (-(u : ℤ)) ^ p = -((u : ℤ) ^ p) := hp.neg_pow _
  have hFz : ((u : ℤ) + 1) * F = (u : ℤ) ^ p + 1 := by exact_mod_cast hF.symm
  have hu0 : ((u : ℤ) + 1) ≠ 0 := by positivity
  have hsum : (F : ℤ) = ∑ i ∈ Finset.range p, (-(u : ℤ)) ^ i := by
    apply mul_left_cancel₀ hu0
    rw [hFz]
    linear_combination hgs + hneg
  have hd : -(u : ℤ) - 1 ∣ ∑ i ∈ Finset.range p, ((-(u : ℤ)) ^ i - 1) :=
    Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow (-(u : ℤ)) 1 i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    ← hsum] at hd
  have hx : -(u : ℤ) - 1 = -((u : ℤ) + 1) := by ring
  rw [hx, neg_dvd] at hd
  exact hd

/-- The split at a prime factor `p` of `L`: with `u = q ^ (L / p)`, the prime `p` divides
`u + 1`, and `(u ^ p + 1) / (u + 1)` is `p` times a square. -/
private lemma hpr_split {q L y p : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hL : Odd L)
    (hp : p.Prime) (hpL : p ∣ L) (hy : q ^ L + 1 = 2 * y ^ 2) :
    p ∣ q ^ (L / p) + 1 ∧
      ∃ F s, q ^ L + 1 = (q ^ (L / p) + 1) * F ∧ F = p * s ^ 2 := by
  have hpo : Odd p := Odd.of_dvd_nat hL hpL
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpo with ⟨j, hj⟩
    omega
  have hL0 : L ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hL)
  have hLh : L = L / p * p := (Nat.div_mul_cancel hpL).symm
  have hh : L / p ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hLh
    exact hL0 hLh
  set u := q ^ (L / p) with hu
  have hqL : q ^ L = u ^ p := by rw [hu, ← pow_mul, ← hLh]
  have hu4 : u % 4 = 1 := by rw [hu, Nat.pow_mod, hq4]; norm_num
  have hq5 : 5 ≤ q := by
    have := hq.two_le
    omega
  obtain ⟨F, hF⟩ : u + 1 ∣ u ^ p + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow u 1 hpo
  obtain ⟨A, hA⟩ : ∃ A, u + 1 = 2 * A := ⟨(u + 1) / 2, by omega⟩
  have hAF : A * F = y ^ 2 := by
    have h2 : 2 * (A * F) = 2 * y ^ 2 := by rw [← mul_assoc, ← hA, ← hF, ← hqL, hy]
    omega
  have hg : Nat.gcd A F ∣ p := by
    have hdz := hpr_dvd_sub hpo hF
    have h1 : ((Nat.gcd A F : ℕ) : ℤ) ∣ (u : ℤ) + 1 := by
      have : Nat.gcd A F ∣ u + 1 := (Nat.gcd_dvd_left A F).trans ⟨2, by rw [hA]; ring⟩
      exact_mod_cast this
    have h2 : ((Nat.gcd A F : ℕ) : ℤ) ∣ (F : ℤ) := Int.natCast_dvd_natCast.mpr
      (Nat.gcd_dvd_right A F)
    have h3 := dvd_sub h2 (h1.trans hdz)
    rw [sub_sub_cancel] at h3
    exact Int.natCast_dvd_natCast.mp h3
  rcases hpr_sq_or_mul_sq hp hg hAF with ⟨r, hr⟩ | ⟨hpA, s, hs⟩
  · exact absurd (show u ^ p + 1 = (u + 1) * r ^ 2 by rw [hF, hr, sq])
      (alternating_sum_prime_pow_ne_sq hq hq5 hh hu4 hpo hp3)
  · exact ⟨hpA.trans ⟨2, by rw [hA]; ring⟩, F, s, by rw [hqL, hF], hs⟩

/-- Step 1: a square forces `q ≡ 1 (mod 16)`. -/
private lemma hpr_mod_sixteen {q L y : ℕ} (hq4 : q % 4 = 1) (hL : Odd L)
    (hy : q ^ L + 1 = 2 * y ^ 2) : q % 16 = 1 := by
  have hc : q % 16 = 1 ∨ q % 16 = 5 ∨ q % 16 = 9 ∨ q % 16 = 13 := by omega
  have h4 : q ^ 4 % 16 = 1 := by
    rw [Nat.pow_mod]
    rcases hc with h | h | h | h <;> simp [h]
  have hLm : q ^ L % 16 = q ^ (L % 4) % 16 := by
    conv_lhs => rw [← Nat.div_add_mod L 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod, h4, one_pow]
    simp
  have hy16 : (q ^ L + 1) % 16 = 2 * ((y % 16) ^ 2 % 16) % 16 := by
    rw [hy, Nat.mul_mod, Nat.pow_mod]
  have key : ∀ b, b < 16 → 2 * (b ^ 2 % 16) % 16 = 0 ∨ 2 * (b ^ 2 % 16) % 16 = 2 ∨
      2 * (b ^ 2 % 16) % 16 = 8 := by decide
  have hb := key (y % 16) (Nat.mod_lt _ (by norm_num))
  have hL4 : L % 4 = 1 ∨ L % 4 = 3 := by
    rcases hL with ⟨j, hj⟩
    omega
  have h3 : q ^ 3 % 16 = (q % 16) ^ 3 % 16 := Nat.pow_mod _ _ _
  rcases hL4 with h | h <;> rw [h] at hLm
  · rw [pow_one] at hLm
    omega
  · rcases hc with hc | hc | hc | hc <;> rw [hc] at h3 <;> norm_num at h3 <;> omega

/-- Step 3: the prime factor `p` is `1 (mod 8)`. -/
private lemma hpr_mod_eight {q L y p : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hL : Odd L)
    (hp : p.Prime) (hpL : p ∣ L) (hy : q ^ L + 1 = 2 * y ^ 2) : p % 8 = 1 := by
  have h16 := hpr_mod_sixteen hq4 hL hy
  obtain ⟨-, F, s, hF, hs⟩ := hpr_split hq hq4 hL hp hpL hy
  have hL0 : L ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hL)
  have hu : q ^ (L / p) % 16 = 1 := by rw [Nat.pow_mod, h16]; norm_num
  have hqL : q ^ L % 16 = 1 := by rw [Nat.pow_mod, h16]; norm_num
  have hm : (q ^ (L / p) + 1) * F % 16 = 2 := by rw [← hF]; omega
  rw [Nat.mul_mod, show (q ^ (L / p) + 1) % 16 = 2 by omega] at hm
  have hF8 : F % 8 = 1 := by omega
  have key : ∀ a, a < 8 → ∀ b, b < 8 → a * (b ^ 2 % 8) % 8 = 1 → a = 1 := by decide
  apply key (p % 8) (Nat.mod_lt _ (by norm_num)) (s % 8) (Nat.mod_lt _ (by norm_num))
  rw [← Nat.pow_mod, ← Nat.mul_mod, ← hs, hF8]

/-- Step 4: the least prime factor of `L` divides `q + 1`. -/
private lemma hpr_minFac {q L y : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1) (hL : Odd L)
    (hL3 : 3 ≤ L) (hy : q ^ L + 1 = 2 * y ^ 2) : L.minFac ∣ q + 1 := by
  set p := L.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpL : p ∣ L := Nat.minFac_dvd L
  obtain ⟨hdv, -⟩ := hpr_split hq hq4 hL hp hpL hy
  have hpo : Odd p := Odd.of_dvd_nat hL hpL
  have hp3 : 2 < p := by
    have := hp.two_le
    rcases hpo with ⟨j, hj⟩
    omega
  have := Fact.mk hp
  have : Fact (2 < p) := ⟨hp3⟩
  set h := L / p with hh
  have hhL : h ∣ L := Nat.div_dvd_of_dvd hpL
  have hL0 : L ≠ 0 := by omega
  have hh0 : h ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel hpL
    rw [← hh, h0, zero_mul] at this
    exact hL0 this.symm
  have hcop : Nat.Coprime h (p - 1) := by
    apply Nat.coprime_of_dvd
    intro r hr hrh hrp
    have h1 : p ≤ r := Nat.minFac_le_of_dvd hr.two_le (hrh.trans hhL)
    have h2 : r ≤ p - 1 := Nat.le_of_dvd (by omega) hrp
    omega
  have hxh : (q : ZMod p) ^ h = -1 := by
    have : ((q ^ h + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdv
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hx0 : (q : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh0] at hxh
    exact one_ne_zero (neg_eq_zero.mp hxh.symm)
  have hx2h : (q : ZMod p) ^ (h * 2) = 1 := by rw [pow_mul, hxh]; norm_num
  have hxp : (q : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hg : Nat.gcd (h * 2) (p - 1) = 2 := by
    rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel 2 hcop]
    apply Nat.gcd_eq_left
    rcases hpo with ⟨j, hj⟩
    exact ⟨j, by omega⟩
  have hx2 : (q : ZMod p) * (q : ZMod p) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hx2h, hxp⟩
    rw [hg, sq] at this
    exact this
  rcases mul_self_eq_one_iff.mp hx2 with h1 | h1
  · rw [h1, one_pow] at hxh
    exact absurd hxh.symm ZMod.neg_one_ne_one
  · have : ((q + 1 : ℕ) : ZMod p) = 0 := by
      push_cast
      simp [h1]
    exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- Two distinct primes of odd valuation give two distinct prime factors. -/
private lemma hpr_two_le_card_of_odd {n p₁ p₂ : ℕ} (hne : p₁ ≠ p₂)
    (h₁ : Odd (n.factorization p₁)) (h₂ : Odd (n.factorization p₂)) :
    2 ≤ n.primeFactors.card := by
  have hm : ∀ p, Odd (n.factorization p) → p ∈ n.primeFactors := by
    intro p hp
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    intro h0
    rw [h0] at hp
    exact Nat.not_odd_zero hp
  exact Finset.one_lt_card.mpr ⟨p₁, hm _ h₁, p₂, hm _ h₂, hne⟩

/-- The special prime is `1 (mod 4)` and so is its exponent. -/
private lemma hpr_special_facts {N q k m : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) : q % 4 = 1 ∧ k % 4 = 1 := by
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

/-! ## Main results -/

/-- For a prime `q ≡ 1 (mod 4)`, an odd `L ≥ 3` and `q ^ L + 1 = 2 * y ^ 2`: `q ≡ 1 (mod 16)`,
every prime factor of `L` is `1 (mod 8)`, and the least prime factor of `L` divides `q + 1`.
These are necessary conditions only; `HalfPowerNotSquare` is not proved here (it is proved in
`OddPerfect.EulerIndexSupportAll`, so the hypothesis `hy` is never met). Known
mathematics or elementary; novelty not verified. -/
theorem half_pow_succ_sq_necessary {q L y : ℕ} (hq : q.Prime) (hq4 : q % 4 = 1)
    (hL : Odd L) (hL3 : 3 ≤ L) (hy : q ^ L + 1 = 2 * y ^ 2) :
    q % 16 = 1 ∧ (∀ p, p.Prime → p ∣ L → p % 8 = 1) ∧ L.minFac ∣ q + 1 :=
  ⟨hpr_mod_sixteen hq4 hL hy, fun _ hp hpL => hpr_mod_eight hq hq4 hL hp hpL hy,
    hpr_minFac hq hq4 hL hL3 hy⟩

/-- For an odd perfect number `q ^ k * m ^ 2` with special prime `q`, `q ∤ m` and `k ≠ 1`, put
`ℓ = (k + 1) / 2`. If `q ≢ 1 (mod 16)`, or some prime factor of `ℓ` is not `1 (mod 8)`, or the
least prime factor of `ℓ` does not divide `q + 1`, then two distinct primes have odd valuation
in the Euler index, which therefore has at least two distinct prime factors. Known mathematics
or elementary; novelty not verified. -/
theorem exists_two_odd_valuation_of_half_residue {N q k m : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hN : N = q ^ k * m ^ 2) (hqm : ¬ q ∣ m) (hk : k ≠ 1)
    (hc : q % 16 ≠ 1 ∨ (∃ p, p.Prime ∧ p ∣ (k + 1) / 2 ∧ p % 8 ≠ 1) ∨
      ¬ ((k + 1) / 2).minFac ∣ q + 1) :
    (∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      Odd ((eulerIndex q k m).factorization p₁) ∧
      Odd ((eulerIndex q k m).factorization p₂)) ∧
    2 ≤ (eulerIndex q k m).primeFactors.card := by
  obtain ⟨hq4, hk4⟩ := hpr_special_facts h hq hN hqm
  have hS : ¬ IsSquare ((q ^ ((k + 1) / 2) + 1) / 2) := by
    rintro ⟨r, hr⟩
    have hev : (q ^ ((k + 1) / 2) + 1) % 2 = 0 := by
      have : q ^ ((k + 1) / 2) % 2 = 1 := by
        rw [Nat.pow_mod, show q % 2 = 1 by omega]; norm_num
      omega
    have hy : q ^ ((k + 1) / 2) + 1 = 2 * r ^ 2 := by rw [sq, ← hr]; omega
    obtain ⟨h1, h2, h3⟩ := half_pow_succ_sq_necessary hq hq4 ⟨k / 4, by omega⟩ (by omega) hy
    rcases hc with hc | ⟨p, hp, hpd, hp8⟩ | hc
    · exact hc h1
    · exact hp8 (h2 p hp hpd)
    · exact hc h3
  obtain ⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩ :=
    exists_two_odd_valuation_of_half_not_square h hq hN hqm hk hS
  exact ⟨⟨p₁, p₂, hp₁, hp₂, hne, h₁, h₂⟩, hpr_two_le_card_of_odd hne h₁ h₂⟩

end OddPerfect

#print axioms OddPerfect.half_pow_succ_sq_necessary
#print axioms OddPerfect.exists_two_odd_valuation_of_half_residue
