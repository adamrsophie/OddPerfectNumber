import OddPerfect.Abundancy
import OddPerfect.Euler
import OddPerfect.Cyclotomic
import OddPerfect.Seed.Example

/-!
# Sylvester: an odd perfect number has at least four prime factors

With exactly three prime factors, the abundancy bound forces the support to be
`{3, 5, s}` with `s ∈ {7, 11, 13}`. In each case some prime `p` of even exponent has
a component divisor sum `σ 1 (p ^ e)` greater than one whose prime factors must lie
among the other two primes; multiplicative orders (and one extra prime, 3221 or 61)
rule every candidate out.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- If `p ∣ N` has even exponent and no odd prime `q ≠ p` dividing `N` divides
`σ 1 (p ^ e)`, we have a contradiction. -/
private theorem component_absurd {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N)
    (hev : Even (N.factorization p))
    (H : ∀ q, q.Prime → q ≠ 2 → q ≠ p → q ∣ N → q ∣ σ 1 (p ^ N.factorization p) → False) :
    False := by
  have he1 : 1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN
  have hgt : 1 < σ 1 (p ^ N.factorization p) := by
    rw [sigma_one_apply_prime_pow hp]
    obtain ⟨k, hk⟩ : ∃ k, N.factorization p = k + 1 := ⟨N.factorization p - 1, by omega⟩
    rw [hk, Finset.sum_range_succ', Finset.sum_range_succ']
    have := hp.one_lt
    simp only [pow_zero, zero_add, pow_one]
    omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hgt)
  obtain ⟨hqp, hcase⟩ := prime_dvd_sigma_prime_pow hp hq hqd
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hev
    rcases hcase with ⟨-, h2⟩ | ⟨h1, -, h3⟩
    · omega
    · exact absurd (Nat.le_of_dvd one_pos h3) (by omega)
  exact H q hq hq2 hqp (OPNStarter.force_prime h.perfect hp rfl hq hq2 hqd) hqd

/-- An even multiplicative order excludes a prime from the divisor sum of an even power. -/
private theorem not_dvd_of_even_order {p q e d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p % q ≠ 1) (hord : orderOf (p : ZMod q) = d) (hd : Even d) (he : Even e) :
    ¬ q ∣ σ 1 (p ^ e) := by
  intro hdiv
  rcases (prime_dvd_sigma_prime_pow hp hq hdiv).2 with ⟨h1, -⟩ | ⟨-, hd', -⟩
  · exact hpq h1
  · rw [hord] at hd'
    obtain ⟨k, hk⟩ := he
    obtain ⟨j, hj⟩ := hd.two_dvd.trans hd'
    omega

/-- When `p ≡ 1 (mod q)`, a prime `q` dividing `σ 1 (p ^ e)` divides `e + 1`. -/
private theorem dvd_succ_of_order_one {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hord : orderOf (p : ZMod q) = 1) (hdiv : q ∣ σ 1 (p ^ e)) : q ∣ e + 1 := by
  rcases (prime_dvd_sigma_prime_pow hp hq hdiv).2 with ⟨-, h⟩ | ⟨h1, -, -⟩
  · exact h
  · omega

/-- The bound `x/(x-1) ≤ m/(m-1)` for natural numbers `2 ≤ m ≤ x`. -/
private theorem div_sub_one_le' {m x : ℕ} (hm : 2 ≤ m) (hx : m ≤ x) :
    (x : ℚ) / (x - 1) ≤ (m : ℚ) / (m - 1) := by
  have hm' : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hx' : (m : ℚ) ≤ x := by exact_mod_cast hx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- With exactly three prime factors, the support is `{3, 5, s}` with `s ∈ {7, 11, 13}`. -/
private theorem three_primes {N : ℕ} (h : OddPerfect N) (hc : N.primeFactors.card = 3) :
    ∃ s, (s = 7 ∨ s = 11 ∨ s = 13) ∧ N.primeFactors = {3, 5, s} := by
  set P := N.primeFactors with hP
  set g : ℕ → ℚ := fun p => (p : ℚ) / (p - 1) with hg
  have hN : 1 < N := by
    have := h.pos
    by_contra h1
    have : N = 1 := by omega
    subst this
    simp [P] at hc
  have hlt : 2 < ∏ p ∈ P, g p := by
    have := abundancy_lt_prod hN
    rwa [(perfect_iff_abundancy_eq_two h.pos).mp h.perfect] at this
  have hpr : ∀ p ∈ P, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl; exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have h3le : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have := (hpr p hp).1.two_le
    have := (hpr p hp).2
    omega
  have hpos : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    have : (3 : ℚ) ≤ p := by exact_mod_cast h3le p hp
    simp only [hg]
    apply div_nonneg <;> linarith
  have gle : ∀ m p : ℕ, 2 ≤ m → m ≤ p → g p ≤ (m : ℚ) / (m - 1) :=
    fun m p hm hp => div_sub_one_le' hm hp
  -- Lower bounds for primes avoiding small values.
  have lb5 : ∀ p ∈ P, p ≠ 3 → 5 ≤ p := by
    intro p hp h3
    have := h3le p hp
    have hpp := (hpr p hp).1
    by_contra hlt
    interval_cases p <;> first | omega | norm_num at hpp
  have lb7 : ∀ p ∈ P, p ≠ 3 → p ≠ 5 → 7 ≤ p := by
    intro p hp h3 h5
    have := lb5 p hp h3
    have hpp := (hpr p hp).1
    by_contra hlt
    interval_cases p <;> first | omega | norm_num at hpp
  have lb11 : ∀ p ∈ P, p ≠ 3 → p ≠ 5 → p ≠ 7 → 11 ≤ p := by
    intro p hp h3 h5 h7
    have := lb7 p hp h3 h5
    have hpp := (hpr p hp).1
    by_contra hlt
    interval_cases p <;> first | omega | norm_num at hpp
  -- Step 1: 3 is a prime factor.
  have h3 : 3 ∈ P := by
    by_contra h3
    have hle : ∏ p ∈ P, g p ≤ ∏ _p ∈ P, (5 / 4 : ℚ) := by
      apply Finset.prod_le_prod₀ hpos
      intro p hp
      have := gle 5 p (by norm_num) (lb5 p hp (by rintro rfl; exact h3 hp))
      norm_num at this ⊢
      exact this
    rw [Finset.prod_const, hc] at hle
    norm_num at hle
    linarith
  set T := P.erase 3 with hT
  have hTc : T.card = 2 := by rw [hT, Finset.card_erase_of_mem h3, hc]
  have hprodT : ∏ p ∈ P, g p = 3 / 2 * ∏ p ∈ T, g p := by
    have : g 3 = 3 / 2 := by norm_num [hg]
    rw [← Finset.mul_prod_erase P g h3, this]
  have memT : ∀ p ∈ T, p ∈ P ∧ p ≠ 3 := fun p hp =>
    ⟨Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩
  -- Step 2: 5 is a prime factor.
  have h5 : 5 ∈ T := by
    by_contra h5
    obtain ⟨y, z, hyz, hTe⟩ := Finset.card_eq_two.mp hTc
    have hy : y ∈ T := by rw [hTe]; simp
    have hz : z ∈ T := by rw [hTe]; simp
    have hy5 : y ≠ 5 := by rintro rfl; exact h5 hy
    have hz5 : z ≠ 5 := by rintro rfl; exact h5 hz
    obtain ⟨hyP, hy3⟩ := memT y hy
    obtain ⟨hzP, hz3⟩ := memT z hz
    have hpair : ∏ p ∈ T, g p = g y * g z := by rw [hTe, Finset.prod_pair hyz]
    rw [hprodT, hpair] at hlt
    have gy0 := hpos y hyP
    have gz0 := hpos z hzP
    -- One of `y`, `z` is at least 11 and the other at least 7.
    obtain ⟨a, b, ha0, hb0, hab, ha, hb⟩ :
        ∃ a b : ℚ, 0 ≤ a ∧ 0 ≤ b ∧ a * b = g y * g z ∧ a ≤ 7 / 6 ∧ b ≤ 11 / 10 := by
      by_cases hy7 : y = 7
      · refine ⟨g y, g z, gy0, gz0, rfl, ?_, ?_⟩
        · have := gle 7 y (by norm_num) (by omega); norm_num at this ⊢; exact this
        · have := gle 11 z (by norm_num) (lb11 z hzP hz3 hz5 (by omega))
          norm_num at this ⊢; exact this
      · refine ⟨g z, g y, gz0, gy0, mul_comm _ _, ?_, ?_⟩
        · have := gle 7 z (by norm_num) (lb7 z hzP hz3 hz5); norm_num at this ⊢; exact this
        · have := gle 11 y (by norm_num) (lb11 y hyP hy3 hy5 hy7)
          norm_num at this ⊢; exact this
    rw [← hab] at hlt
    nlinarith [mul_le_mul ha hb hb0 (by norm_num)]
  set U := T.erase 5 with hU
  have hUc : U.card = 1 := by rw [hU, Finset.card_erase_of_mem h5, hTc]
  obtain ⟨z, hUe⟩ := Finset.card_eq_one.mp hUc
  have hzU : z ∈ U := by rw [hUe]; simp
  have hz5 : z ≠ 5 := Finset.ne_of_mem_erase hzU
  obtain ⟨hzP, hz3⟩ := memT z (Finset.mem_of_mem_erase hzU)
  have hprodU : ∏ p ∈ T, g p = 5 / 4 * g z := by
    have : g 5 = 5 / 4 := by norm_num [hg]
    rw [← Finset.mul_prod_erase T g h5, ← hU, hUe, Finset.prod_singleton, this]
  rw [hprodT, hprodU] at hlt
  have hz15 : z ≤ 15 := by
    by_contra hz
    have := gle 16 z (by norm_num) (by omega)
    norm_num at this
    linarith
  have hz7 := lb7 z hzP hz3 hz5
  have hzp := (hpr z hzP).1
  refine ⟨z, ?_, ?_⟩
  · interval_cases z <;> first | omega | norm_num at hzp
  · rw [← Finset.insert_erase h3, ← hT, ← Finset.insert_erase h5, ← hU, hUe]

/-- Sylvester (1888): an odd perfect number has at least four distinct prime factors. -/
theorem four_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 4 ≤ N.primeFactors.card := by
  have h3 := three_le_card_primeFactors h
  by_contra hlt
  have hc : N.primeFactors.card = 3 := by omega
  obtain ⟨s, hs, hpf⟩ := three_primes h hc
  have mem : ∀ q, q.Prime → q ∣ N → q = 3 ∨ q = 5 ∨ q = s := by
    intro q hq hqN
    have : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqN, h.ne_zero⟩
    rw [hpf] at this
    simpa using this
  have dvdN : ∀ p ∈ ({3, 5, s} : Finset ℕ), p ∣ N := fun p hp =>
    Nat.dvd_of_mem_primeFactors (hpf ▸ hp)
  obtain ⟨q0, -, -, hq04, -, hev⟩ := exists_special_prime h
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  rcases hs with rfl | rfl | rfl
  · -- `s = 7`: the component of 3 has no admissible prime factor.
    have he := hev 3 p3 (by rintro rfl; norm_num at hq04)
    refine component_absurd h p3 (dvdN 3 (by simp)) he ?_
    intro q hq hq2 hq3 hqN hdiv
    rcases mem q hq hqN with rfl | rfl | rfl
    · exact hq3 rfl
    · exact not_dvd_of_even_order p3 hq (by norm_num)
        ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨2, rfl⟩ he hdiv
    · exact not_dvd_of_even_order p3 hq (by norm_num)
        ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨3, rfl⟩ he hdiv
  · -- `s = 11`: the component of 11 forces the prime 3221.
    have p11 : Nat.Prime 11 := by norm_num
    have he := hev 11 p11 (by rintro rfl; norm_num at hq04)
    refine component_absurd h p11 (dvdN 11 (by simp)) he ?_
    intro q hq hq2 hq11 hqN hdiv
    rcases mem q hq hqN with rfl | rfl | rfl
    · exact not_dvd_of_even_order p11 hq (by norm_num)
        ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨1, rfl⟩ he hdiv
    · have h5 := dvd_succ_of_order_one p11 hq (orderOf_eq_one_iff.mpr (by decide)) hdiv
      have hs4 : σ 1 (11 ^ 4) ∣ σ 1 (11 ^ N.factorization 11) :=
        OPNExample.sigma_prime_pow_dvd p11 h5
      have hval : σ 1 (11 ^ 4) = 5 * 3221 := by
        rw [sigma_one_apply_prime_pow p11]
        simp [Finset.sum_range_succ]
      have hd : 3221 ∣ σ 1 (11 ^ N.factorization 11) :=
        (Dvd.intro_left 5 hval.symm).trans hs4
      have hN := OPNStarter.force_prime h.perfect p11 rfl (by norm_num) (by norm_num) hd
      rcases mem 3221 (by norm_num) hN with h' | h' | h' <;> norm_num at h'
    · exact hq11 rfl
  · -- `s = 13`: whichever of 5, 13 has even exponent gives a contradiction.
    have p13 : Nat.Prime 13 := by norm_num
    by_cases hq13 : q0 = 13
    · subst hq13
      have he := hev 5 p5 (by norm_num)
      refine component_absurd h p5 (dvdN 5 (by simp)) he ?_
      intro q hq hq2 hq5 hqN hdiv
      rcases mem q hq hqN with rfl | rfl | rfl
      · exact not_dvd_of_even_order p5 hq (by norm_num)
          ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨1, rfl⟩ he hdiv
      · exact hq5 rfl
      · exact not_dvd_of_even_order p5 hq (by norm_num)
          ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨2, rfl⟩ he hdiv
    · have he := hev 13 p13 (Ne.symm hq13)
      refine component_absurd h p13 (dvdN 13 (by simp)) he ?_
      intro q hq hq2 hq13' hqN hdiv
      rcases mem q hq hqN with rfl | rfl | rfl
      · have h3 := dvd_succ_of_order_one p13 hq (orderOf_eq_one_iff.mpr (by decide)) hdiv
        have hs2 : σ 1 (13 ^ 2) ∣ σ 1 (13 ^ N.factorization 13) :=
          OPNExample.sigma_prime_pow_dvd p13 h3
        have hval : σ 1 (13 ^ 2) = 3 * 61 := by
          rw [sigma_one_apply_prime_pow p13]
          simp [Finset.sum_range_succ]
        have hd : 61 ∣ σ 1 (13 ^ N.factorization 13) :=
          (Dvd.intro_left 3 hval.symm).trans hs2
        have hN := OPNStarter.force_prime h.perfect p13 rfl (by norm_num) (by norm_num) hd
        rcases mem 61 (by norm_num) hN with h' | h' | h' <;> norm_num at h'
      · exact not_dvd_of_even_order p13 hq (by norm_num)
          ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩) ⟨2, rfl⟩ he hdiv
      · exact hq13' rfl

end OddPerfect

#print axioms OddPerfect.four_le_card_primeFactors
