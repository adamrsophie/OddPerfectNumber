import OddPerfect.Certificate
import OddPerfect.OmegaFour
import OddPerfect.SmallestPrime
import OddPerfect.SpecialPrime
import OddPerfect.Zsigmondy

/-!
# Sylvester: an odd perfect number has at least five prime factors

Suppose an odd perfect number `N` has exactly four prime factors. Then `3 ∣ N`, and the
abundancy bound `2 < ∏ p/(p-1)` leaves the supports `{3, 5, r, s}` with `17 ≤ r ≤ 31`,
`s < 256`; `{3, 7, r, s}` with `11 ≤ r ≤ 15`, `s ≤ 26`; and the two infinite families
`{3, 5, 11, s}`, `{3, 5, 13, s}` (`{3, 5, 7, s}` is excluded since `105 ∤ N`). In the infinite
families, forced exponents and abundancy give `s ≤ 100` and `s ≤ 46`.

Each remaining support is closed by a kernel computation. For a prime `x` of the support
with exponent `e`, Euler's theorem and Bang's theorem (`exists_primeFactor_modEq_one`) give
`e = 1` or `(e + 1) ∣ y - 1` for some `y` in the support, a finite list of candidates. For
each candidate, `σ 1 (x ^ e)` divides `2 * N`, so all its prime factors divide twice the
product of the support; `checkSupport` verifies that this fails for every candidate of some
`x`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

open Cert (geom isPrimeB)

/-- Candidate exponents of `x` for a support `S`. -/
private def cands (S : List ℕ) (x : ℕ) : List ℕ :=
  (if x % 4 = 1 then [1] else []) ++
    S.flatMap fun y => ((List.range y).filter fun d =>
      3 ≤ d && y % d == 1 && ((d - 1) % 2 == 0 || (x % 4 == 1 && (d - 1) % 4 == 1))).map
        (· - 1)

/-- Every candidate exponent `e` of `x` has `σ 1 (x ^ e)` not dividing a power of twice
the product of the support. -/
private def checkX (S : List ℕ) (x : ℕ) : Bool :=
  (cands S x).all fun e => (2 * S.prod) ^ ((e + 1) * x) % geom x e != 0

/-- Some prime of the support admits no exponent. -/
private def checkSupport (S : List ℕ) : Bool := S.any (checkX S)

/-- Completeness of the trial division test. -/
private theorem isPrimeB_complete {n : ℕ} (hn : n.Prime) : isPrimeB n = true := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hn.two_le, fun d hd => ?_⟩
  by_cases h2 : d < 2
  · exact Or.inl h2
  · right
    intro h0
    have := (Nat.prime_def_lt.mp hn).2 d hd (Nat.dvd_of_mod_eq_zero h0)
    omega

/-- The geometric sum is below the next power. -/
private theorem geom_lt {x : ℕ} (hx : 2 ≤ x) (e : ℕ) : geom x e < x ^ (e + 1) := by
  induction e with
  | zero => simp [geom]; omega
  | succ e ih =>
    rw [geom, pow_succ x (e + 1)]
    nlinarith [pow_pos (by omega : 0 < x) (e + 1)]

/-- A number whose prime factors divide `M` divides `M ^ K` once `m < 2 ^ K`. -/
private theorem dvd_pow_of_primeFactors {m M K : ℕ} (hm : m ≠ 0) (hM : M ≠ 0)
    (hK : m < 2 ^ K) (h : ∀ p, p.Prime → p ∣ m → p ∣ M) : m ∣ M ^ K := by
  rw [← Nat.factorization_le_iff_dvd hm (pow_ne_zero _ hM)]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime ∧ p ∣ m
  · have h1 : 1 ≤ M.factorization p :=
      (hp.1.dvd_iff_one_le_factorization hM).mp (h p hp.1 hp.2)
    have h2 : m.factorization p < K := by
      have hle := Nat.ordProj_le p hm
      have h22 : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
        Nat.pow_le_pow_left hp.1.two_le _
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
    nlinarith
  · have : m.factorization p = 0 := by
      by_cases hpp : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd (fun hd => hp ⟨hpp, hd⟩)
      · exact Nat.factorization_eq_zero_of_not_prime m hpp
    rw [this]; exact Nat.zero_le _

/-- The exponent of a prime factor is one of the candidates. -/
private theorem mem_cands {N : ℕ} (h : OddPerfect N) {S : List ℕ}
    (hS : N.primeFactors = S.toFinset) {x : ℕ} (hx : x ∈ N.primeFactors) :
    N.factorization x ∈ cands S x := by
  have hxp := Nat.prime_of_mem_primeFactors hx
  have he1 : 1 ≤ N.factorization x :=
    (hxp.dvd_iff_one_le_factorization h.ne_zero).mp (Nat.dvd_of_mem_primeFactors hx)
  obtain ⟨q, -, -, hq4, hqe, hev⟩ := exists_special_prime h
  have hpar : N.factorization x % 2 = 0 ∨ (x % 4 = 1 ∧ N.factorization x % 4 = 1) := by
    by_cases hxq : x = q
    · subst hxq; exact Or.inr ⟨hq4, hqe⟩
    · exact Or.inl (Nat.even_iff.mp (hev x hxp hxq))
  simp only [cands, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  by_cases he : N.factorization x = 1
  · left
    have : x % 4 = 1 := by omega
    simp [this, he]
  · right
    obtain ⟨y, hy, -, hmod⟩ :=
      exists_primeFactor_modEq_one h hx (d := N.factorization x + 1) (by omega) dvd_rfl
    have hyS : y ∈ S := by rw [hS] at hy; exact List.mem_toFinset.mp hy
    have hy1 : y ≠ 1 := (Nat.prime_of_mem_primeFactors hy).ne_one
    have hlt : N.factorization x + 1 < y := by
      by_contra hle
      rcases Nat.eq_or_lt_of_le (not_lt.mp hle) with heq | hlt
      · rw [heq, Nat.mod_self] at hmod; omega
      · rw [Nat.mod_eq_of_lt hlt] at hmod; exact hy1 hmod
    refine ⟨y, hyS, N.factorization x + 1, ⟨hlt, ⟨⟨by omega, hmod⟩, ?_⟩⟩, by omega⟩
    simp only [Nat.add_sub_cancel]
    omega

/-- A support accepted by `checkSupport` carries no odd perfect number. -/
private theorem support_absurd {N : ℕ} (h : OddPerfect N) {S : List ℕ}
    (hS : N.primeFactors = S.toFinset) (hc : checkSupport S = true) : False := by
  obtain ⟨x, hxS, hx⟩ := List.any_eq_true.mp hc
  have hxN : x ∈ N.primeFactors := by rw [hS]; exact List.mem_toFinset.mpr hxS
  have hxp := Nat.prime_of_mem_primeFactors hxN
  have hmem := mem_cands h hS hxN
  set e := N.factorization x
  have hb := List.all_eq_true.mp hx e hmem
  simp only [bne_iff_ne, ne_eq] at hb
  apply hb
  apply Nat.mod_eq_zero_of_dvd
  have hS0 : S.prod ≠ 0 := by
    rw [Ne, List.prod_eq_zero_iff]
    intro h0
    have : (0 : ℕ) ∈ N.primeFactors := by rw [hS]; exact List.mem_toFinset.mpr h0
    exact Nat.not_prime_zero (Nat.prime_of_mem_primeFactors this)
  have hdvd := OPNStarter.component_sigma_dvd h.perfect hxp rfl
  rw [Cert.sigma_eq_geom hxp] at hdvd
  apply dvd_pow_of_primeFactors (by
      rw [Cert.geom_eq]; exact (Finset.sum_pos (fun i _ => pow_pos hxp.pos i)
        (by simp)).ne') (by omega)
  · calc geom x e < x ^ (e + 1) := geom_lt hxp.two_le e
      _ < (2 ^ x) ^ (e + 1) := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
      _ = 2 ^ ((e + 1) * x) := by rw [← pow_mul, mul_comm]
  · intro p hp hpd
    rcases (Nat.Prime.dvd_mul hp).mp (hpd.trans hdvd) with h2 | hN
    · exact h2.mul_right _
    · have : p ∈ S.toFinset := by
        rw [← hS]; exact Nat.mem_primeFactors.mpr ⟨hp, hN, h.ne_zero⟩
      exact (List.dvd_prod (List.mem_toFinset.mp this)).mul_left 2

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Supports `{3, 5, r, s}` with `17 ≤ r`. -/
private theorem tab5 : ∀ r < 32, 17 ≤ r → isPrimeB r = true → ∀ s < 256, r < s →
    16 * (r - 1) * (s - 1) < 15 * r * s → isPrimeB s = true →
    checkSupport [3, 5, r, s] = true := by
  decide +kernel


set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Supports `{3, 7, r, s}`. -/
private theorem tab7 : ∀ r < 16, 8 ≤ r → isPrimeB r = true → ∀ s < 27, r < s →
    8 * (r - 1) * (s - 1) < 7 * r * s → isPrimeB s = true →
    checkSupport [3, 7, r, s] = true := by
  decide +kernel

/-- Supports `{3, 5, 11, s}` with `s ≤ 100`. -/
private theorem tab11 : ∀ s < 101, 11 < s → isPrimeB s = true →
    checkSupport [3, 5, 11, s] = true := by
  decide +kernel

/-- Supports `{3, 5, 13, s}` with `s ≤ 46`. -/
private theorem tab13 : ∀ s < 47, 13 < s → isPrimeB s = true →
    checkSupport [3, 5, 13, s] = true := by
  decide +kernel

/-- Sorting a three element set. -/
private theorem sort3 {T : Finset ℕ} (hT : T.card = 3) :
    ∃ p r s, p < r ∧ r < s ∧ T = {p, r, s} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3 <;>
    first
    | omega
    | exact ⟨a, b, c, by omega, by omega, rfl⟩
    | exact ⟨a, c, b, by omega, by omega, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, a, c, by omega, by omega, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, c, a, by omega, by omega, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, a, b, by omega, by omega, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, b, a, by omega, by omega, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

/-- Abundancy two, split over a support of four primes. -/
private theorem abund4 {N a b c d : ℕ} (h : OddPerfect N) (hS : N.primeFactors = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    abundancy (a ^ N.factorization a) * (abundancy (b ^ N.factorization b) *
      (abundancy (c ^ N.factorization c) * abundancy (d ^ N.factorization d))) = 2 := by
  rw [← (perfect_iff_abundancy_eq_two h.pos).mp h.perfect, abundancy_eq_prod_primeFactors h.ne_zero,
    hS, Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
    Finset.prod_pair hcd]

/-- Abundancy is nonnegative. -/
private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy; positivity

/-- Abundancy of `p ^ 1`. -/
private theorem abundancy_prime_pow_one {p : ℕ} (hp : p.Prime) :
    abundancy (p ^ 1) = 1 + (p : ℚ)⁻¹ := by
  rw [abundancy_prime_pow hp]; simp [Finset.sum_range_succ]

/-- Four-term product bound. -/
private theorem prod4_le {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℚ} (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂)
    (h₃ : x₃ ≤ y₃) (h₄ : x₄ ≤ y₄) (h0₁ : 0 ≤ x₁) (h0₂ : 0 ≤ x₂) (h0₃ : 0 ≤ x₃) (h0₄ : 0 ≤ x₄) :
    x₁ * (x₂ * (x₃ * x₄)) ≤ y₁ * (y₂ * (y₃ * y₄)) := by
  have := mul_le_mul h₃ h₄ h0₄ (h0₃.trans h₃)
  have := mul_le_mul h₂ this (by positivity) (h0₂.trans h₂)
  exact mul_le_mul h₁ this (by positivity) (h0₁.trans h₁)

/-- A prime not congruent to 1 modulo 4 has even exponent. -/
private theorem fact_even {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hp4 : p % 4 ≠ 1) :
    Even (N.factorization p) := by
  obtain ⟨q, -, -, hq4, -, hev⟩ := exists_special_prime h
  exact hev p hp (by rintro rfl; exact hp4 hq4)

/-- A prime factor has positive exponent. -/
private theorem one_le_fact {N p : ℕ} (h : OddPerfect N) (hp : p.Prime) (hpN : p ∣ N) :
    1 ≤ N.factorization p := (hp.dvd_iff_one_le_factorization h.ne_zero).mp hpN

/-- A power up to the exponent divides `N`. -/
private theorem pow_dvd_of_le {N p k : ℕ} (h : OddPerfect N) (hp : p.Prime)
    (hk : k ≤ N.factorization p) : p ^ k ∣ N :=
  (hp.pow_dvd_iff_le_factorization h.ne_zero).mpr hk

/-- The family `{3, 5, 11, s}`: the bound `s ≤ 100`. -/
private theorem family_eleven {N s : ℕ} (h : OddPerfect N) (hS : N.primeFactors = {3, 5, 11, s})
    (hs : 13 < s) : s ≤ 100 := by
  have mem : ∀ q, q ∈ ({3, 5, 11, s} : Finset ℕ) → q ∣ N := fun q hq =>
    Nat.dvd_of_mem_primeFactors (hS ▸ hq)
  have hsP : s.Prime := Nat.prime_of_mem_primeFactors (hS ▸ (by simp : s ∈ ({3, 5, 11, s} : Finset ℕ)))
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have p11 : Nat.Prime 11 := by norm_num
  -- The exponent of 3 is at least 4.
  have ha : 4 ≤ N.factorization 3 := by
    obtain ⟨k, hk⟩ := fact_even h p3 (by norm_num)
    have h1 := one_le_fact h p3 (mem 3 (by simp))
    by_contra hlt
    have h2 : N.factorization 3 = 2 := by omega
    have h13 : 13 ∣ N := OPNStarter.force_prime h.perfect p3 h2 (by norm_num) (by norm_num)
      (by rw [Cert.sigma_eq_geom p3]; decide)
    have : (13 : ℕ) ∈ ({3, 5, 11, s} : Finset ℕ) := hS ▸ Nat.mem_primeFactors.mpr
      ⟨by norm_num, h13, h.ne_zero⟩
    simp at this; omega
  have hc : 2 ≤ N.factorization 11 := by
    obtain ⟨k, hk⟩ := fact_even h p11 (by norm_num)
    have := one_le_fact h p11 (mem 11 (by simp))
    omega
  have hb : N.factorization 5 = 1 := by
    have := one_le_fact h p5 (mem 5 (by simp))
    by_contra hne
    exact Cert.check_sound (s := [.powDvd 3 4, .powDvd 5 2, .powDvd 11 2])
      (c := .abundant [(3, 4), (5, 2), (11, 2)]) (by decide +kernel) N h
      (by
        simp only [Cert.State.Holds, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Cert.Fact.Holds]
        exact ⟨pow_dvd_of_le h p3 ha, pow_dvd_of_le h p5 (by omega), pow_dvd_of_le h p11 hc⟩)
  have hab := abund4 h hS (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega)
    (by omega)
  rw [hb, abundancy_prime_pow_one p5] at hab
  have key := prod4_le (abundancy_prime_pow_lt p3 (N.factorization 3)).le
    (le_rfl : (1 + ((5 : ℕ) : ℚ)⁻¹) ≤ 1 + ((5 : ℕ) : ℚ)⁻¹)
    (abundancy_prime_pow_lt p11 (N.factorization 11)).le
    (abundancy_prime_pow_lt hsP (N.factorization s)).le (abundancy_nonneg _) (by positivity)
    (abundancy_nonneg _) (abundancy_nonneg _)
  rw [hab] at key
  have hs1 : (0 : ℚ) < s - 1 := by have : (13 : ℚ) < s := by exact_mod_cast hs
                                   linarith
  have : (2 : ℚ) * (s - 1) * 50 ≤ 99 * s := by
    norm_num at key
    rw [div_eq_mul_inv] at key
    have := mul_le_mul_of_nonneg_right key hs1.le
    field_simp at this
    nlinarith
  have : (s : ℚ) ≤ 100 := by linarith
  exact_mod_cast this


/-- The family `{3, 5, 13, s}`: the bound `s ≤ 46`. -/
private theorem family_thirteen {N s : ℕ} (h : OddPerfect N)
    (hS : N.primeFactors = {3, 5, 13, s}) (hs : 13 < s) : s ≤ 46 := by
  have mem : ∀ q, q ∈ ({3, 5, 13, s} : Finset ℕ) → q ∣ N := fun q hq =>
    Nat.dvd_of_mem_primeFactors (hS ▸ hq)
  have hsP : s.Prime := Nat.prime_of_mem_primeFactors (hS ▸ (by simp : s ∈ ({3, 5, 13, s} : Finset ℕ)))
  have p3 : Nat.Prime 3 := by norm_num
  have p5 : Nat.Prime 5 := by norm_num
  have p13 : Nat.Prime 13 := by norm_num
  have hs1 : (0 : ℚ) < s - 1 := by
    have : (13 : ℚ) < s := by exact_mod_cast hs
    linarith
  have hab := abund4 h hS (by norm_num) (by norm_num) (by omega) (by norm_num) (by omega)
    (by omega)
  obtain ⟨k, hk⟩ := fact_even h p3 (by norm_num)
  have h1 := one_le_fact h p3 (mem 3 (by simp))
  have ha4 : N.factorization 3 ≠ 4 := by
    intro h4
    have h11 : 11 ∣ N := OPNStarter.force_prime h.perfect p3 h4 (by norm_num) (by norm_num)
      (by rw [Cert.sigma_eq_geom p3]; decide)
    have : (11 : ℕ) ∈ ({3, 5, 13, s} : Finset ℕ) := hS ▸ Nat.mem_primeFactors.mpr
      ⟨by norm_num, h11, h.ne_zero⟩
    simp at this; omega
  by_cases ha2 : N.factorization 3 = 2
  · rw [ha2] at hab
    have h32 : abundancy (3 ^ 2) = 13 / 9 := by
      rw [abundancy_prime_pow p3]; norm_num [Finset.sum_range_succ]
    rw [h32] at hab
    have key := prod4_le (le_rfl : (13 / 9 : ℚ) ≤ 13 / 9)
      (abundancy_prime_pow_lt p5 (N.factorization 5)).le
      (abundancy_prime_pow_lt p13 (N.factorization 13)).le
      (abundancy_prime_pow_lt hsP (N.factorization s)).le (by norm_num) (abundancy_nonneg _)
      (abundancy_nonneg _) (abundancy_nonneg _)
    rw [hab] at key
    have : (2 : ℚ) * (s - 1) * 432 ≤ 845 * s := by
      norm_num at key
      rw [div_eq_mul_inv] at key
      have := mul_le_mul_of_nonneg_right key hs1.le
      field_simp at this
      nlinarith
    have : (s : ℚ) ≤ 46 := by linarith
    exact_mod_cast this
  · have ha : 6 ≤ N.factorization 3 := by omega
    have hb : N.factorization 5 = 1 := by
      have := one_le_fact h p5 (mem 5 (by simp))
      by_contra hne
      exact Cert.check_sound (s := [.powDvd 3 6, .powDvd 5 2, .powDvd 13 1])
        (c := .abundant [(3, 6), (5, 2), (13, 1)]) (by decide +kernel) N h
        (by
          simp only [Cert.State.Holds, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq, Cert.Fact.Holds]
          exact ⟨pow_dvd_of_le h p3 ha, pow_dvd_of_le h p5 (by omega),
            pow_dvd_of_le h p13 (one_le_fact h p13 (mem 13 (by simp)))⟩)
    rw [hb, abundancy_prime_pow_one p5] at hab
    have key := prod4_le (abundancy_prime_pow_lt p3 (N.factorization 3)).le
      (le_rfl : (1 + ((5 : ℕ) : ℚ)⁻¹) ≤ 1 + ((5 : ℕ) : ℚ)⁻¹)
      (abundancy_prime_pow_lt p13 (N.factorization 13)).le
      (abundancy_prime_pow_lt hsP (N.factorization s)).le (abundancy_nonneg _) (by positivity)
      (abundancy_nonneg _) (abundancy_nonneg _)
    rw [hab] at key
    have : (2 : ℚ) * (s - 1) * 20 ≤ 39 * s := by
      norm_num at key
      rw [div_eq_mul_inv] at key
      have := mul_le_mul_of_nonneg_right key hs1.le
      field_simp at this
      nlinarith
    have : (s : ℚ) ≤ 46 := by linarith
    exact_mod_cast this

/-- From the abundancy bound to a polynomial inequality. -/
private theorem poly_of_prod {p r s : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r) (hs : 2 ≤ s)
    (h : 2 < (3 : ℚ) / 2 * ((p : ℚ) / (p - 1) * ((r : ℚ) / (r - 1) * ((s : ℚ) / (s - 1))))) :
    4 * (p - 1) * (r - 1) * (s - 1) < 3 * p * r * s := by
  have hp' : (1 : ℚ) < p := by exact_mod_cast hp
  have hr' : (1 : ℚ) < r := by exact_mod_cast hr
  have hs' : (1 : ℚ) < s := by exact_mod_cast hs
  have e : (3 : ℚ) / 2 * ((p : ℚ) / (p - 1) * ((r : ℚ) / (r - 1) * ((s : ℚ) / (s - 1)))) =
      (3 * p * r * s) / (2 * ((p - 1) * (r - 1) * (s - 1))) := by
    field_simp
  have hpos : (0 : ℚ) < 2 * ((p - 1) * (r - 1) * (s - 1)) := by
    have : (0 : ℚ) < p - 1 := by linarith
    have : (0 : ℚ) < r - 1 := by linarith
    have : (0 : ℚ) < s - 1 := by linarith
    positivity
  rw [e, lt_div_iff₀ hpos] at h
  have : ((4 * (p - 1) * (r - 1) * (s - 1) : ℕ) : ℚ) < ((3 * p * r * s : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub (by omega : 1 ≤ r),
      Nat.cast_sub (by omega : 1 ≤ s)]
    linarith
  exact_mod_cast this

/-- Two-factor version of the abundancy cut. -/
private theorem cut2 {r s a b c d k m : ℕ} (key : m * (r - 1) * (s - 1) < k * r * s)
    (h1 : a * r ≤ b * (r - 1)) (h2 : c * s ≤ d * (s - 1)) (hcoef : k * (b * d) ≤ m * (a * c))
    (ha : 0 < a) (hc : 0 < c) : False := by
  have H := Nat.mul_le_mul h1 h2
  generalize r - 1 = R at *
  generalize s - 1 = S at *
  have e1 : a * r * (c * s) = (a * c) * (r * s) := by ring
  have e2 : b * R * (d * S) = (b * d) * (R * S) := by ring
  have e3 : m * R * S = m * (R * S) := by ring
  have e4 : k * r * s = k * (r * s) := by ring
  rw [e1, e2] at H
  rw [e3, e4] at key
  generalize r * s = X at *
  generalize R * S = Y at *
  have hac : 0 < a * c := Nat.mul_pos ha hc
  have := Nat.mul_le_mul_left k H
  have := Nat.mul_le_mul_right Y hcoef
  have := Nat.mul_lt_mul_of_pos_left key hac
  nlinarith

/-- Three-factor version of the abundancy cut. -/
private theorem cut3 {p r s : ℕ} (key : 4 * (p - 1) * (r - 1) * (s - 1) < 3 * p * r * s)
    (hp : 11 ≤ p) (hr : 12 ≤ r) (hs : 13 ≤ s) : False := by
  have h1 : 10 * p ≤ 11 * (p - 1) := by omega
  have h2 : 11 * r ≤ 12 * (r - 1) := by omega
  have h3 : 12 * s ≤ 13 * (s - 1) := by omega
  have H := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  generalize p - 1 = P at *
  generalize r - 1 = R at *
  generalize s - 1 = S at *
  have e1 : 10 * p * (11 * r) * (12 * s) = 1320 * (p * r * s) := by ring
  have e2 : 11 * P * (12 * R) * (13 * S) = 1716 * (P * R * S) := by ring
  have e3 : 4 * P * R * S = 4 * (P * R * S) := by ring
  have e4 : 3 * p * r * s = 3 * (p * r * s) := by ring
  rw [e1, e2] at H
  rw [e3, e4] at key
  omega

/-- Sylvester (1888): an odd perfect number has at least five distinct prime factors. -/
theorem five_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 5 ≤ N.primeFactors.card := by
  have h4 := four_le_card_primeFactors h
  by_contra hlt
  have hc : N.primeFactors.card = 4 := by omega
  have h3 : 3 ∈ N.primeFactors := by
    by_contra h3
    have := seven_le_card_primeFactors_of_not_three_dvd h
      (fun hd => h3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hd, h.ne_zero⟩))
    omega
  obtain ⟨p, r, s, hpr, hrs, hT⟩ := sort3 (by
    rw [Finset.card_erase_of_mem h3, hc] : (N.primeFactors.erase 3).card = 3)
  have hS : N.primeFactors = {3, p, r, s} := by rw [← Finset.insert_erase h3, hT]
  have memT : ∀ x ∈ ({p, r, s} : Finset ℕ), x.Prime ∧ 5 ≤ x := by
    intro x hx
    have hx' : x ∈ N.primeFactors.erase 3 := hT ▸ hx
    have hxp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hx')
    have hx3 := Finset.ne_of_mem_erase hx'
    have hx2 : x ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase hx'))
    have hx4 : x ≠ 4 := by rintro rfl; norm_num at hxp
    refine ⟨hxp, ?_⟩
    have := hxp.two_le
    omega
  obtain ⟨pp, p5⟩ := memT p (by simp)
  obtain ⟨rp, r5⟩ := memT r (by simp)
  obtain ⟨sp, s5⟩ := memT s (by simp)
  have hprod := two_lt_prod_primeFactors h
  rw [hS, Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
    Finset.prod_pair (by omega)] at hprod
  norm_num only at hprod
  have key := poly_of_prod (by omega) (by omega) (by omega) hprod
  have dvdN : ∀ x ∈ ({3, p, r, s} : Finset ℕ), x ∣ N := fun x hx =>
    Nat.dvd_of_mem_primeFactors (hS ▸ hx)
  have hS' : ∀ a b c d : ℕ, N.primeFactors = {a, b, c, d} →
      N.primeFactors = [a, b, c, d].toFinset := by
    intro a b c d h; rw [h]; simp
  -- `p ≤ 7`
  have hp7 : p ≤ 7 := by
    by_contra hp
    have hp11 : 11 ≤ p := by
      by_contra hp'
      interval_cases p <;> norm_num at pp
    exact cut3 key hp11 (by omega) (by omega)
  interval_cases p
  · -- `p = 5`
    replace key : 16 * (r - 1) * (s - 1) < 15 * r * s := by
      have e1 : 4 * (5 - 1) * (r - 1) * (s - 1) = 16 * (r - 1) * (s - 1) := by ring
      have e2 : 3 * 5 * r * s = 15 * r * s := by ring
      rwa [e1, e2] at key
    by_cases hr17 : 17 ≤ r
    · have hr32 : r < 32 := by
        by_contra hr
        exact cut2 key (by omega : 31 * r ≤ 32 * (r - 1)) (by omega : 32 * s ≤ 33 * (s - 1))
          (by norm_num) (by norm_num) (by norm_num)
      have hs256 : s < 256 := by
        by_contra hs
        exact cut2 key (by omega : 16 * r ≤ 17 * (r - 1)) (by omega : 255 * s ≤ 256 * (s - 1))
          (by norm_num) (by norm_num) (by norm_num)
      exact support_absurd h (hS' _ _ _ _ hS) (tab5 r hr32 hr17 (isPrimeB_complete rp) s hs256
        hrs key (isPrimeB_complete sp))
    · interval_cases r <;> try norm_num at rp
      · exact not_105_dvd h (by
          have := dvdN 3 (by simp); have := dvdN 5 (by simp); have := dvdN 7 (by simp); omega)
      · have : s ≤ 100 := by
          by_cases hs13 : s = 13
          · omega
          · rcases (by omega : s = 12 ∨ 13 < s) with h12 | h12
            · subst h12; norm_num at sp
            · exact family_eleven h hS h12
        exact support_absurd h (hS' _ _ _ _ hS) (tab11 s (by omega) hrs (isPrimeB_complete sp))
      · have := family_thirteen h hS hrs
        exact support_absurd h (hS' _ _ _ _ hS) (tab13 s (by omega) hrs (isPrimeB_complete sp))
  · norm_num at pp
  · -- `p = 7`
    replace key : 8 * (r - 1) * (s - 1) < 7 * r * s := by
      have e1 : 4 * (7 - 1) * (r - 1) * (s - 1) = 3 * (8 * (r - 1) * (s - 1)) := by ring
      have e2 : 3 * 7 * r * s = 3 * (7 * r * s) := by ring
      rw [e1, e2] at key
      omega
    have hr11 : 11 ≤ r := by
      by_contra hr
      interval_cases r <;> norm_num at rp
    have hr16 : r < 16 := by
      by_contra hr
      exact cut2 key (by omega : 15 * r ≤ 16 * (r - 1)) (by omega : 16 * s ≤ 17 * (s - 1))
        (by norm_num) (by norm_num) (by norm_num)
    have hs27 : s < 27 := by
      by_contra hs
      exact cut2 key (by omega : 10 * r ≤ 11 * (r - 1)) (by omega : 26 * s ≤ 27 * (s - 1))
        (by norm_num) (by norm_num) (by norm_num)
    exact support_absurd h (hS' _ _ _ _ hS) (tab7 r hr16 (by omega) (isPrimeB_complete rp) s
      hs27 hrs key (isPrimeB_complete sp))

end OddPerfect

#print axioms OddPerfect.five_le_card_primeFactors
