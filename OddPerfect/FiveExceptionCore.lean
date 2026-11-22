import OddPerfect.ThreeFreeCount

/-!
# Five exceptional primes when the special prime is 13: the arithmetic core

Setting: `N` is an odd perfect number with `3 ∤ N` whose special prime is 13 (odd exponent),
and `19 ∣ N`, `31 ∣ N`. A prime factor `p ≠ 13` is exceptional when `3 ∤ e + 1` for its
exponent `e`. Then 7, 19 and 31 are exceptional. Assuming at most four exceptional primes, the
fourth one is a prime `t`, and every other prime factor `s` (a good prime) has `3 ∣ e + 1`.

This file proves the facts that do not depend on any computation:

* the configuration `Inst N t` and its derivation from the counting hypothesis;
* for a good prime `s`, `1 + s + s^2` is a product of powers of `7, 13, 19, 31, t`, the
  exponent of `t` is 0 unless `t ≡ 1 (mod 3)`, and the exponent vector determines `s`;
* the exponent classes: the exponent of 13 is 1 or at least 5, that of 7 is 4 or at least 6,
  those of 19, 31 and `t` are at least 4, and that of a good prime is 2 or at least 8;
* the abundancy identity `2 = A(13^a) A(7^b) A(19^c) A(31^d) A(t^e) ∏ A(s^{e_s})`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FiveException

/-- The configuration: `N` odd perfect, `3 ∤ N`, special prime 13, the prime factors
`7, 19, 31, t` are exceptional and distinct, and every other prime factor other than 13 has an
exponent `e` with `3 ∣ e + 1`. -/
structure Inst (N t : ℕ) : Prop where
  opn : OddPerfect N
  h3 : ¬ 3 ∣ N
  hodd : Odd (N.factorization 13)
  h13 : 13 ∈ N.primeFactors
  h7 : 7 ∈ N.primeFactors
  h19 : 19 ∈ N.primeFactors
  h31 : 31 ∈ N.primeFactors
  ht : t ∈ N.primeFactors
  ht7 : t ≠ 7
  ht13 : t ≠ 13
  ht19 : t ≠ 19
  ht31 : t ≠ 31
  htex : ¬ 3 ∣ N.factorization t + 1
  hgood : ∀ p ∈ N.primeFactors, p ≠ 13 → p ≠ 7 → p ≠ 19 → p ≠ 31 → p ≠ t →
    3 ∣ N.factorization p + 1

/-- The good primes. -/
def good (N t : ℕ) : Finset ℕ :=
  ((((N.primeFactors.erase 13).erase 7).erase 19).erase 31).erase t

theorem mem_good {N t s : ℕ} :
    s ∈ good N t ↔ s ∈ N.primeFactors ∧ s ≠ 13 ∧ s ≠ 7 ∧ s ≠ 19 ∧ s ≠ 31 ∧ s ≠ t := by
  simp only [good, Finset.mem_erase]
  tauto

variable {N t : ℕ}

/-- A prime factor `p ≡ 1 (mod 3)` of `N` with `3 ∤ N` has `3 ∤ e + 1`. -/
theorem not_dvd_of_one_mod {p : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) (hp : p ∈ N.primeFactors)
    (h1 : p % 3 = 1) : ¬ 3 ∣ N.factorization p + 1 := fun he => by
  have := (ThreeFreeThree.cyc_dvd_of_mod h h3 hp he).2
  omega

/-- Facts about a good prime. -/
theorem Inst.good_facts (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) :
    s.Prime ∧ 3 ∣ N.factorization s + 1 ∧ 1 + s + s ^ 2 ∣ N ∧ s % 3 = 2 := by
  obtain ⟨hsN, h1, h2, h3, h4, h5⟩ := mem_good.mp hs
  have he := c.hgood s hsN h1 h2 h3 h4 h5
  have := ThreeFreeThree.cyc_dvd_of_mod c.opn c.h3 hsN he
  exact ⟨Nat.prime_of_mem_primeFactors hsN, he, this.1, this.2⟩

theorem Inst.good_ge (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) : 5 ≤ s ∧ s % 6 = 5 := by
  obtain ⟨hp, -, -, h2⟩ := c.good_facts hs
  have hsN := (mem_good.mp hs).1
  have hodd : s % 2 = 1 := by
    have := c.opn.1.of_dvd_nat (Nat.dvd_of_mem_primeFactors hsN)
    exact Nat.odd_iff.mp this
  have h2le := hp.two_le
  refine ⟨?_, by omega⟩
  by_contra hc
  interval_cases s <;> simp_all

/-- Every prime factor of `1 + s + s^2`, for a good `s`, is one of `7, 13, 19, 31, t` and is
`1` modulo 3. -/
theorem Inst.tgt (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) {d : ℕ} (hd : d.Prime)
    (hdd : d ∣ 1 + s + s ^ 2) :
    (d = 7 ∨ d = 13 ∨ d = 19 ∨ d = 31 ∨ d = t) ∧ d % 3 = 1 := by
  obtain ⟨-, -, hF, -⟩ := c.good_facts hs
  have hdN : d ∣ N := hdd.trans hF
  have hd3' : d ≠ 3 := by rintro rfl; exact c.h3 hdN
  have hd3 : d % 3 = 1 := OPNThreeFree.target_mod_three hd hd3' hdd
  refine ⟨?_, hd3⟩
  by_contra hcon
  simp only [not_or] at hcon
  have hg : d ∈ good N t := mem_good.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hd, hdN, c.opn.ne_zero⟩, hcon.2.1, hcon.1, hcon.2.2.1,
      hcon.2.2.2.1, hcon.2.2.2.2⟩
  have := (c.good_facts hg).2.2.2
  omega

/-- The exponent vector of a good prime: the exponents of `7, 13, 19, 31, t` in
`1 + s + s^2`. -/
def vec (t s : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((1 + s + s ^ 2).factorization 7, (1 + s + s ^ 2).factorization 13,
    (1 + s + s ^ 2).factorization 19, (1 + s + s ^ 2).factorization 31,
    (1 + s + s ^ 2).factorization t)

/-- The value of an exponent vector. -/
def val5 (t : ℕ) (v : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  7 ^ v.1 * 13 ^ v.2.1 * 19 ^ v.2.2.1 * 31 ^ v.2.2.2.1 * t ^ v.2.2.2.2

theorem Inst.shape (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) :
    1 + s + s ^ 2 = val5 t (vec t s) := by
  have hne : 1 + s + s ^ 2 ≠ 0 := by positivity
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hne]
  rw [Finsupp.prod_of_support_subset _ (s := {7, 13, 19, 31, t}) _ _ (fun _ _ => pow_zero _),
    Finset.prod_insert (by simp [c.ht7.symm]),
    Finset.prod_insert (by simp [c.ht13.symm]),
    Finset.prod_insert (by simp [c.ht19.symm]),
    Finset.prod_pair c.ht31.symm]
  · simp only [val5, vec]; ring
  intro d hd
  rw [Nat.support_factorization] at hd
  have := (c.tgt hs (Nat.prime_of_mem_primeFactors hd) (Nat.dvd_of_mem_primeFactors hd)).1
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The exponent of `t` is 0 when `t ≡ 2 (mod 3)`. -/
theorem Inst.vec_t_zero (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) (h2 : t % 3 = 2) :
    (vec t s).2.2.2.2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have := (c.tgt hs (Nat.prime_of_mem_primeFactors c.ht) hd).2
  omega

/-- The exponent vector determines the good prime. -/
theorem Inst.vec_inj (c : Inst N t) : Set.InjOn (vec t) (good N t) := by
  intro x hx y hy hxy
  have hF : 1 + x + x ^ 2 = 1 + y + y ^ 2 := by rw [c.shape hx, c.shape hy, hxy]
  rcases lt_trichotomy x y with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

/-- The exponent of a good prime is 2 or at least 8. -/
theorem Inst.good_exp (c : Inst N t) {s : ℕ} (hs : s ∈ good N t) :
    N.factorization s = 2 ∨ 8 ≤ N.factorization s := by
  obtain ⟨hp, he, -, -⟩ := c.good_facts hs
  obtain ⟨hsN, h13, -⟩ := mem_good.mp hs
  obtain ⟨k, hk⟩ := even_factorization_of_ne c.opn (by norm_num) c.hodd hp h13
  have h1 := hp.factorization_pos_of_dvd c.opn.ne_zero (Nat.dvd_of_mem_primeFactors hsN)
  omega

/-- The set of exceptional primes. -/
def exc (N : ℕ) : Finset ℕ := (N.primeFactors.erase 13).filter fun p => ¬ 3 ∣ N.factorization p + 1

/-- An exceptional prime has exponent at least 4. -/
theorem four_le_of_exc (h : OddPerfect N) (hodd : Odd (N.factorization 13)) {p : ℕ}
    (hp : p ∈ exc N) : 4 ≤ N.factorization p :=
  four_le_factorization_of_mem_mod_exceptions h (by norm_num) hodd hp

theorem Inst.mem_exc (c : Inst N t) {p : ℕ} (hp : p = 7 ∨ p = 19 ∨ p = 31 ∨ p = t) :
    p ∈ exc N := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by rcases hp with rfl | rfl | rfl | rfl <;>
    first | exact c.ht13 | norm_num, ?_⟩, ?_⟩
  · rcases hp with rfl | rfl | rfl | rfl
    exacts [c.h7, c.h19, c.h31, c.ht]
  · rcases hp with rfl | rfl | rfl | rfl
    · exact not_dvd_of_one_mod c.opn c.h3 c.h7 (by norm_num)
    · exact not_dvd_of_one_mod c.opn c.h3 c.h19 (by norm_num)
    · exact not_dvd_of_one_mod c.opn c.h3 c.h31 (by norm_num)
    · exact c.htex

/-- Exponent classes of the exceptional primes and of 13. -/
theorem Inst.exps (c : Inst N t) :
    (N.factorization 13 = 1 ∨ 5 ≤ N.factorization 13) ∧
    (N.factorization 7 = 4 ∨ 6 ≤ N.factorization 7) ∧ 4 ≤ N.factorization 19 ∧
    4 ≤ N.factorization 31 ∧ 4 ≤ N.factorization t := by
  have e7 := four_le_of_exc c.opn c.hodd (c.mem_exc (p := 7) (by tauto))
  have e19 := four_le_of_exc c.opn c.hodd (c.mem_exc (p := 19) (by tauto))
  have e31 := four_le_of_exc c.opn c.hodd (c.mem_exc (p := 31) (by tauto))
  have et := four_le_of_exc c.opn c.hodd (c.mem_exc (p := t) (by tauto))
  obtain ⟨k, hk⟩ := even_factorization_of_ne c.opn (by norm_num) c.hodd (p := 7) (by norm_num)
    (by norm_num)
  have h13 : N.factorization 13 % 4 = 1 := by
    obtain ⟨q', hq', -, -, hk4, -⟩ := exists_special_prime c.opn
    have := (existsUnique_odd_exponent c.opn).unique ⟨hq', Nat.odd_iff.mpr (by omega)⟩
      ⟨(by norm_num : Nat.Prime 13), c.hodd⟩
    rw [← this]; exact hk4
  refine ⟨by omega, by omega, e19, e31, et⟩

/-- `7` divides `N`: `σ(13) = 14` divides `σ(13^e)` for odd `e`. -/
theorem seven_mem (h : OddPerfect N) (hodd : Odd (N.factorization 13)) : 7 ∈ N.primeFactors := by
  have hd : σ 1 (13 ^ 1) ∣ σ 1 (13 ^ N.factorization 13) :=
    OPNExample.sigma_prime_pow_dvd (by norm_num) (by
      obtain ⟨j, hj⟩ := hodd; exact ⟨j + 1, by omega⟩)
  have h1 : σ 1 (13 ^ 1) = 14 := by
    rw [sigma_one_apply_prime_pow (by norm_num)]; simp [Finset.sum_range_succ]
  have h2 := hd.trans (OPNStarter.component_sigma_dvd h.perfect (by norm_num) rfl)
  rw [h1] at h2
  have : 7 ∣ N := by
    have h7 : 7 ∣ 2 * N := (by norm_num : 7 ∣ 14).trans h2
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h7)
  exact Nat.mem_primeFactors.mpr ⟨by norm_num, this, h.ne_zero⟩

/-- From at most four exceptional primes to the configuration. -/
theorem inst_of_card (h : OddPerfect N) (hodd : Odd (N.factorization 13)) (h3 : ¬ 3 ∣ N)
    (h19 : 19 ∣ N) (h31 : 31 ∣ N) (hc : (exc N).card ≤ 4) : ∃ t, Inst N t := by
  have m7 := seven_mem h hodd
  have m13 : 13 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, Nat.dvd_of_factorization_pos hodd.pos.ne', h.ne_zero⟩
  have m19 : 19 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h19, h.ne_zero⟩
  have m31 : 31 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h31, h.ne_zero⟩
  have mem : ∀ p ∈ N.primeFactors, p % 3 = 1 → p ≠ 13 → p ∈ exc N := fun p hp h1 hne =>
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hp⟩, not_dvd_of_one_mod h h3 hp h1⟩
  have e7 := mem 7 m7 (by norm_num) (by norm_num)
  have e19 := mem 19 m19 (by norm_num) (by norm_num)
  have e31 := mem 31 m31 (by norm_num) (by norm_num)
  have h4 : 4 ≤ (exc N).card := four_le_card_mod_exceptions h (by norm_num) hodd h3
  have hsub : ({7, 19, 31} : Finset ℕ) ⊆ exc N := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ((exc N) \ {7, 19, 31}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; simp; omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  have htm : t ∈ (exc N) \ {7, 19, 31} := by rw [ht]; simp
  obtain ⟨hte, htn⟩ := Finset.mem_sdiff.mp htm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at htn
  obtain ⟨hte1, hte2⟩ := Finset.mem_filter.mp hte
  obtain ⟨ht13, htN⟩ := Finset.mem_erase.mp hte1
  refine ⟨t, h, h3, hodd, m13, m7, m19, m31, htN, htn.1, ht13, htn.2.1, htn.2.2, hte2, ?_⟩
  intro p hp p13 p7 p19 p31 pt
  by_contra hn
  have hpe : p ∈ exc N := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨p13, hp⟩, hn⟩
  have : p ∈ (exc N) \ {7, 19, 31} := Finset.mem_sdiff.mpr ⟨hpe, by simp [p7, p19, p31]⟩
  rw [ht] at this
  exact pt (Finset.mem_singleton.mp this)

/-- The abundancy identity. -/
theorem Inst.abund (c : Inst N t) :
    abundancy (13 ^ N.factorization 13) * abundancy (7 ^ N.factorization 7) *
      abundancy (19 ^ N.factorization 19) * abundancy (31 ^ N.factorization 31) *
      abundancy (t ^ N.factorization t) *
      ∏ s ∈ good N t, abundancy (s ^ N.factorization s) = 2 := by
  have hN0 := c.opn.ne_zero
  have hab := (perfect_iff_abundancy_eq_two c.opn.pos).mp c.opn.perfect
  have m1 : 7 ∈ N.primeFactors.erase 13 := Finset.mem_erase.mpr ⟨by norm_num, c.h7⟩
  have m2 : 19 ∈ (N.primeFactors.erase 13).erase 7 :=
    Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_erase.mpr ⟨by norm_num, c.h19⟩⟩
  have m3 : 31 ∈ ((N.primeFactors.erase 13).erase 7).erase 19 :=
    Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_erase.mpr ⟨by norm_num,
      Finset.mem_erase.mpr ⟨by norm_num, c.h31⟩⟩⟩
  have m4 : t ∈ (((N.primeFactors.erase 13).erase 7).erase 19).erase 31 :=
    Finset.mem_erase.mpr ⟨c.ht31, Finset.mem_erase.mpr ⟨c.ht19,
      Finset.mem_erase.mpr ⟨c.ht7, Finset.mem_erase.mpr ⟨c.ht13, c.ht⟩⟩⟩⟩
  rw [abundancy_eq_prod_primeFactors hN0, ← Finset.mul_prod_erase _ _ c.h13,
    ← Finset.mul_prod_erase _ _ m1, ← Finset.mul_prod_erase _ _ m2,
    ← Finset.mul_prod_erase _ _ m3, ← Finset.mul_prod_erase _ _ m4] at hab
  rw [← hab, good]
  ring

/-! ## Analytic part -/

/-- The weight of an exponent vector. -/
def wt5 (a b c d e : ℚ) (v : ℕ × ℕ × ℕ × ℕ × ℕ) : ℚ :=
  a ^ v.1 * b ^ v.2.1 * c ^ v.2.2.1 * d ^ v.2.2.2.1 * e ^ v.2.2.2.2

theorem wt5_nonneg {a b c d e : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (v : ℕ × ℕ × ℕ × ℕ × ℕ) : 0 ≤ wt5 a b c d e v := by
  unfold wt5; positivity

private theorem one_le_pow_of' {x : ℚ} (k : ℕ) (h : 1 ≤ x ∨ k = 0) : 1 ≤ x ^ k := by
  rcases h with h | h
  · exact one_le_pow₀ h
  · simp [h]

/-- The weight inequality: `wt^j · val ≥ 1`. -/
theorem wt5_pow_mul_ge {j t : ℕ} {a b c d e : ℚ} (v : ℕ × ℕ × ℕ × ℕ × ℕ)
    (h7 : 1 ≤ a ^ j * 7) (h13 : 1 ≤ b ^ j * 13) (h19 : 1 ≤ c ^ j * 19) (h31 : 1 ≤ d ^ j * 31)
    (ht : 1 ≤ e ^ j * t ∨ v.2.2.2.2 = 0) : 1 ≤ wt5 a b c d e v ^ j * (val5 t v : ℚ) := by
  have : wt5 a b c d e v ^ j * (val5 t v : ℚ) = (a ^ j * 7) ^ v.1 * (b ^ j * 13) ^ v.2.1 *
      (c ^ j * 19) ^ v.2.2.1 * (d ^ j * 31) ^ v.2.2.2.1 * (e ^ j * t) ^ v.2.2.2.2 := by
    simp only [wt5, val5]; push_cast; ring
  rw [this]
  refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ?_ ?_) ?_) ?_) ?_
  · exact one_le_pow₀ h7
  · exact one_le_pow₀ h13
  · exact one_le_pow₀ h19
  · exact one_le_pow₀ h31
  · exact one_le_pow_of' _ ht

private theorem le_of_sq_le_sq' {x y : ℚ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hc
  have := lt_of_not_ge hc
  nlinarith

/-- Quarter power form: from `W^4 F ≥ 1`, `F ≥ K^4` and `F ≤ κ^2 (s - 1)^2`,
`1/(s - 1) ≤ κ W / K`. -/
theorem inv_le_of_w4 {s : ℕ} (hs : 2 ≤ s) {W F K κ : ℚ} (hW : 0 ≤ W) (hWF : 1 ≤ W ^ 4 * F)
    (hK : 0 < K) (hFK : K ^ 4 ≤ F) (hκ : 0 ≤ κ) (hκF : F ≤ κ ^ 2 * ((s : ℚ) - 1) ^ 2) :
    1 / ((s : ℚ) - 1) ≤ κ / K * W := by
  have hy : (0 : ℚ) < (s : ℚ) - 1 := by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hs
    linarith
  set y := (s : ℚ) - 1
  have hF0 : 0 ≤ F := le_trans (by positivity) hFK
  have h1 : K ^ 4 ≤ (W ^ 2 * F) ^ 2 := by nlinarith
  have h2 : K ^ 2 ≤ W ^ 2 * F := by
    exact le_of_sq_le_sq' (by positivity) (by nlinarith)
  have h3 : K ^ 2 ≤ (κ * W * y) ^ 2 := by nlinarith [sq_nonneg W]
  have h4 : K ≤ κ * W * y := by
    exact le_of_sq_le_sq' (by positivity) h3
  rw [div_le_iff₀ hy, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hK]
  linarith

/-- Square root form: from `W^2 F ≥ 1` and `F ≤ κ^2 (s - 1)^2`, `1/(s - 1) ≤ κ W`. -/
theorem inv_le_of_w2 {s : ℕ} (hs : 2 ≤ s) {W F κ : ℚ} (hW : 0 ≤ W) (hWF : 1 ≤ W ^ 2 * F)
    (hκ : 0 ≤ κ) (hκF : F ≤ κ ^ 2 * ((s : ℚ) - 1) ^ 2) : 1 / ((s : ℚ) - 1) ≤ κ * W := by
  have hy : (0 : ℚ) < (s : ℚ) - 1 := by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hs
    linarith
  set y := (s : ℚ) - 1
  have h3 : 1 ≤ (κ * W * y) ^ 2 := by nlinarith [sq_nonneg W]
  have h4 : 1 ≤ κ * W * y := by
    exact le_of_sq_le_sq' (by positivity) (by simpa using h3)
  rw [div_le_iff₀ hy]
  linarith

/-- A sum of weights over vectors confined to a product of sets. -/
theorem sum_wt5_le {a b c d e : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (V : Finset (ℕ × ℕ × ℕ × ℕ × ℕ)) (A B C D E : Finset ℕ)
    (hV : ∀ v ∈ V, v.1 ∈ A ∧ v.2.1 ∈ B ∧ v.2.2.1 ∈ C ∧ v.2.2.2.1 ∈ D ∧ v.2.2.2.2 ∈ E) :
    ∑ v ∈ V, wt5 a b c d e v ≤ (∑ k ∈ A, a ^ k) * (∑ k ∈ B, b ^ k) * (∑ k ∈ C, c ^ k) *
      (∑ k ∈ D, d ^ k) * (∑ k ∈ E, e ^ k) := by
  have hprod : ∑ v ∈ A ×ˢ B ×ˢ C ×ˢ D ×ˢ E, wt5 a b c d e v = (∑ k ∈ A, a ^ k) *
      (∑ k ∈ B, b ^ k) * (∑ k ∈ C, c ^ k) * (∑ k ∈ D, d ^ k) * (∑ k ∈ E, e ^ k) := by
    rw [show (∑ k ∈ A, a ^ k) * (∑ k ∈ B, b ^ k) * (∑ k ∈ C, c ^ k) * (∑ k ∈ D, d ^ k) *
        (∑ k ∈ E, e ^ k) = (∑ k ∈ A, a ^ k) * ((∑ k ∈ B, b ^ k) * ((∑ k ∈ C, c ^ k) *
        ((∑ k ∈ D, d ^ k) * (∑ k ∈ E, e ^ k)))) by ring]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_product, wt5, mul_assoc]
  rw [← hprod]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun v _ _ => wt5_nonneg ha hb hc hd he v)
  intro v hv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hV v hv
  simp only [Finset.mem_product]
  exact ⟨h1, h2, h3, h4, h5⟩

theorem geom_range_le {a : ℚ} (ha : 0 ≤ a) (ha1 : a < 1) (M : ℕ) :
    ∑ k ∈ Finset.range M, a ^ k ≤ 1 / (1 - a) := by
  have h1 : 0 < 1 - a := by linarith
  rw [le_div_iff₀ h1, geom_sum_mul_neg]
  have : 0 ≤ a ^ M := pow_nonneg ha M
  linarith

theorem geom_Ico_le {a : ℚ} (ha : 0 ≤ a) (ha1 : a < 1) (M : ℕ) :
    ∑ k ∈ Finset.Ico 1 M, a ^ k ≤ a / (1 - a) := by
  rcases Nat.lt_or_ge M 1 with hM | hM
  · rw [Finset.Ico_eq_empty (by omega)]; simp only [Finset.sum_empty]
    exact div_nonneg ha (by linarith)
  rw [Finset.sum_Ico_eq_sum_range]
  have : ∑ k ∈ Finset.range (M - 1), a ^ (1 + k) = a * ∑ k ∈ Finset.range (M - 1), a ^ k := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  calc a * ∑ k ∈ Finset.range (M - 1), a ^ k ≤ a * (1 / (1 - a)) :=
        mul_le_mul_of_nonneg_left (geom_range_le ha ha1 _) ha
    _ = a / (1 - a) := by ring

theorem prod_one_add_le {ι : Type*} [DecidableEq ι] (T : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ T, 0 ≤ x i) : (∏ i ∈ T, (1 + x i)) * (1 - ∑ i ∈ T, x i) ≤ 1 := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hs := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hP : 0 ≤ ∏ i ∈ s, (1 + x i) :=
      Finset.prod_nonneg fun i hi => by linarith [hx i (Finset.mem_insert_of_mem hi)]
    have hsum : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg hP (add_nonneg (mul_nonneg hxa hxa) (mul_nonneg hxa hsum))]

theorem rv_eq {s : ℕ} (hs : 2 ≤ s) : ThreeFreeThree.rv s = 1 + 1 / ((s : ℚ) - 1) := by
  have : (0 : ℚ) < (s : ℚ) - 1 := by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hs
    linarith
  unfold ThreeFreeThree.rv
  field_simp
  ring

/-- `∏ s/(s - 1) ≤ 1/(1 - X)` when `∑ 1/(s - 1) ≤ X < 1`. -/
theorem prod_rv_le (G : Finset ℕ) (hG : ∀ s ∈ G, 2 ≤ s) {X : ℚ}
    (hX : ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤ X) (hX1 : X < 1) :
    ∏ s ∈ G, ThreeFreeThree.rv s ≤ 1 / (1 - X) := by
  have hx : ∀ s ∈ G, 0 ≤ 1 / ((s : ℚ) - 1) := fun s hs => by
    have : (2 : ℚ) ≤ s := by exact_mod_cast hG s hs
    exact div_nonneg zero_le_one (by linarith)
  have h := prod_one_add_le G _ hx
  rw [Finset.prod_congr rfl fun s hs => rv_eq (hG s hs)]
  have hP : 0 ≤ ∏ s ∈ G, (1 + 1 / ((s : ℚ) - 1)) :=
    Finset.prod_nonneg fun s hs => by linarith [hx s hs]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The tail sum over a set of good primes with a per prime weight bound. -/
theorem Inst.sum_le (c : Inst N t) (G : Finset ℕ) (hG : G ⊆ good N t) {a b c' d e κ : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c') (hd : 0 ≤ d) (he : 0 ≤ e) (hκ : 0 ≤ κ)
    (hs : ∀ s ∈ G, 1 / ((s : ℚ) - 1) ≤ κ * wt5 a b c' d e (vec t s))
    (A B C D E : Finset ℕ)
    (hV : ∀ s ∈ G, (vec t s).1 ∈ A ∧ (vec t s).2.1 ∈ B ∧ (vec t s).2.2.1 ∈ C ∧
      (vec t s).2.2.2.1 ∈ D ∧ (vec t s).2.2.2.2 ∈ E) :
    ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤ κ * ((∑ k ∈ A, a ^ k) * (∑ k ∈ B, b ^ k) *
      (∑ k ∈ C, c' ^ k) * (∑ k ∈ D, d ^ k) * (∑ k ∈ E, e ^ k)) := by
  calc ∑ s ∈ G, 1 / ((s : ℚ) - 1) ≤ ∑ s ∈ G, κ * wt5 a b c' d e (vec t s) :=
        Finset.sum_le_sum hs
    _ = κ * ∑ v ∈ G.image (vec t), wt5 a b c' d e v := by
        rw [Finset.sum_image (fun x hx y hy hxy => c.vec_inj (hG hx) (hG hy) hxy), Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hκ
        apply sum_wt5_le ha hb hc hd he
        intro v hv
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
        exact hV s hs

/-- Every good prime has `1 + s + s^2 ≤ 4 (s - 1)^2`. -/
theorem cyc_le_four {s : ℕ} (hs : 3 ≤ s) :
    ((1 + s + s ^ 2 : ℕ) : ℚ) ≤ 2 ^ 2 * ((s : ℚ) - 1) ^ 2 := by
  have : (3 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast; nlinarith

/-- For `s ≥ 10^6`, `1 + s + s^2 ≤ (1001/1000)^2 (s - 1)^2`. -/
theorem cyc_le_fine {s : ℕ} (hs : 1000000 ≤ s) :
    ((1 + s + s ^ 2 : ℕ) : ℚ) ≤ (1001 / 1000) ^ 2 * ((s : ℚ) - 1) ^ 2 := by
  have : (1000000 : ℚ) ≤ s := by exact_mod_cast hs
  push_cast; nlinarith

theorem one_le_abundancy_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : 1 ≤ abundancy (p ^ k) := by
  have := abundancy_prime_pow_mono hp (Nat.zero_le k)
  simpa [abundancy] using this

/-! ## Checks in natural number arithmetic and their soundness -/

/-- Newton iteration for an integer square root, with fuel. -/
def nsq : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | f + 1, m, x => if (x + m / x) / 2 < x then nsq f m ((x + m / x) / 2) else x

/-- The square test of `n`: if `4 n - 3 = r^2` with `r = 2 s + 1`, `s ≡ 5 (mod 6)` and
`s ≥ 5`, then `s` is in `hits`; if the candidate root is not exact, it certifies a non square. -/
def sqOK (hits : List ℕ) (n : ℕ) : Bool :=
  let m := 4 * n - 3
  let r := nsq 120 m (2 ^ 48)
  if r * r = m then
    !(decide (r % 2 = 1) && decide ((r / 2) % 6 = 5) && decide (5 ≤ r / 2)) ||
      decide (r / 2 ∈ hits)
  else decide (r * r < m ∧ m < (r + 1) * (r + 1))

theorem sqOK_sound {hits : List ℕ} {s : ℕ} (h : sqOK hits (1 + s + s ^ 2) = true)
    (h6 : s % 6 = 5) (_h5 : 5 ≤ s) : s ∈ hits := by
  have hm : 4 * (1 + s + s ^ 2) - 3 = (2 * s + 1) * (2 * s + 1) := by
    have : 4 * (1 + s + s ^ 2) = (2 * s + 1) * (2 * s + 1) + 3 := by ring
    omega
  simp only [sqOK, hm] at h
  set r := nsq 120 ((2 * s + 1) * (2 * s + 1)) (2 ^ 48)
  by_cases hr : r * r = (2 * s + 1) * (2 * s + 1)
  · rw [if_pos hr] at h
    have hr' : r = 2 * s + 1 := Nat.mul_self_inj.mp hr
    have h2 : r / 2 = s := by omega
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq] at h
    rcases h with ((h | h) | h) | h
    · omega
    · omega
    · omega
    · rwa [h2] at h
  · rw [if_neg hr] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have a1 : r < 2 * s + 1 := Nat.mul_self_lt_mul_self_iff.mp h1
    have a2 : 2 * s + 1 < r + 1 := Nat.mul_self_lt_mul_self_iff.mp h2
    omega

/-- A loop over `x, x p, x p^2, …` up to `B`, testing `f`; fails when the fuel runs out. -/
def loopK (f : ℕ → Bool) (p B : ℕ) : ℕ → ℕ → Bool
  | 0, x => decide (B < x)
  | k + 1, x => if x ≤ B then f x && loopK f p B k (x * p) else true

theorem loopK_sound {f : ℕ → Bool} {p B : ℕ} (hp : 1 ≤ p) :
    ∀ k x, loopK f p B k x = true → ∀ j, x * p ^ j ≤ B → f (x * p ^ j) = true := by
  have hpj : ∀ j, 1 ≤ p ^ j := fun j => Nat.one_le_pow _ _ hp
  intro k
  induction k with
  | zero =>
    intro x h j hj
    simp only [loopK, decide_eq_true_eq] at h
    have := Nat.le_mul_of_pos_right x (hpj j)
    omega
  | succ k ih =>
    intro x h j hj
    simp only [loopK] at h
    by_cases hx : x ≤ B
    · rw [if_pos hx, Bool.and_eq_true] at h
      cases j with
      | zero => simpa using h.1
      | succ j =>
        have := ih (x * p) h.2 j (by rw [pow_succ] at hj; linarith [hj, (by ring : x * (p ^ j * p) = x * p * p ^ j)])
        rwa [pow_succ, show x * (p ^ j * p) = x * p * p ^ j by ring]
    · have := Nat.le_mul_of_pos_right x (hpj j)
      omega

/-- The check of `P` on every product `x ∏ pᵢ^{eᵢ} ≤ B` over a list of primes. -/
def smoothOK (P : ℕ → Bool) (B : ℕ) : List ℕ → ℕ → Bool
  | [], x => P x
  | p :: ps, x => loopK (smoothOK P B ps) p B 100 x

theorem smoothOK_cons {P : ℕ → Bool} {B p : ℕ} {ps : List ℕ} {x : ℕ} (hp : 1 ≤ p)
    (h : smoothOK P B (p :: ps) x = true) (j : ℕ) (hj : x * p ^ j ≤ B) :
    smoothOK P B ps (x * p ^ j) = true :=
  loopK_sound hp 100 x h j hj

private theorem le_of_mul_le' {x y B : ℕ} (hy : 1 ≤ y) (h : x * y ≤ B) : x ≤ B :=
  le_trans (Nat.le_mul_of_pos_right x hy) h

theorem loopK_of {f : ℕ → Bool} {p B : ℕ} :
    ∀ k x, (∀ j < k, x * p ^ j ≤ B → f (x * p ^ j) = true) → B < x * p ^ k →
      loopK f p B k x = true := by
  intro k
  induction k with
  | zero => intro x _ h; simpa [loopK] using h
  | succ k ih =>
    intro x hf hB
    simp only [loopK]
    split_ifs with hx
    · rw [Bool.and_eq_true]
      refine ⟨by simpa using hf 0 (by omega) (by simpa using hx), ih (x * p) (fun j hj hle => ?_)
        (by rw [pow_succ] at hB; linarith [show x * p * p ^ k = x * (p ^ k * p) by ring])⟩
      have e : x * p * p ^ j = x * p ^ (j + 1) := by ring
      rw [e] at hle ⊢
      exact hf (j + 1) (by omega) hle
    · rfl

private theorem lt_mul_pow_of {x p B k j : ℕ} (hp : 1 ≤ p) (hk : k ≤ j) (h : B < x * p ^ k) :
    B < x * p ^ j :=
  lt_of_lt_of_le h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp hk))

/-- The check over `p :: q :: ps` from a list `L` of checked starting values. -/
theorem smoothOK_two_of {P : ℕ → Bool} {B p q x k₁ k₂ : ℕ} {ps : List ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hk₁ : k₁ ≤ 100) (hk₂ : k₂ ≤ 100) (h₁ : B < x * p ^ k₁) (h₂ : B < x * q ^ k₂)
    (L : List ℕ) (hL : L.all (smoothOK P B ps) = true)
    (hcov : ∀ j < k₁, ∀ i < k₂, x * p ^ j * q ^ i ≤ B → x * p ^ j * q ^ i ∈ L) :
    smoothOK P B (p :: q :: ps) x = true := by
  simp only [smoothOK]
  refine loopK_of 100 x (fun j _ hj => ?_) (lt_mul_pow_of hp hk₁ h₁)
  have hj1 : j < k₁ := by
    by_contra hc
    have := lt_mul_pow_of hp (not_lt.mp hc) h₁
    omega
  refine loopK_of 100 _ (fun i _ hi => ?_) ?_
  · have hi1 : i < k₂ := by
      by_contra hc
      have h3 := lt_mul_pow_of hq (not_lt.mp hc) h₂
      have : x * q ^ i ≤ x * p ^ j * q ^ i := by
        rw [mul_right_comm]; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hp)
      omega
    exact List.all_eq_true.mp hL _ (hcov j hj1 i hi1 hi)
  · have h3 := lt_mul_pow_of hq hk₂ h₂
    have : x * q ^ 100 ≤ x * p ^ j * q ^ 100 := by
      rw [mul_right_comm]; exact Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hp)
    omega

/-- Soundness of the check over `[7, 13, 19, 31]`. -/
theorem smoothOK4_sound {P : ℕ → Bool} {B x : ℕ} (h : smoothOK P B [7, 13, 19, 31] x = true)
    (a b c d : ℕ) (hB : x * (7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d) ≤ B) :
    P (x * (7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d)) = true := by
  have p1 : 1 ≤ 13 ^ b * 19 ^ c * 31 ^ d := Nat.pos_of_ne_zero (by positivity)
  have p2 : 1 ≤ 19 ^ c * 31 ^ d := Nat.pos_of_ne_zero (by positivity)
  have p3 : 1 ≤ 31 ^ d := Nat.pos_of_ne_zero (by positivity)
  have e : x * (7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d) =
      x * 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d := by ring
  rw [e] at hB ⊢
  have h1 := smoothOK_cons (by norm_num) h a
    (le_of_mul_le' p1 (by rw [show x * 7 ^ a * (13 ^ b * 19 ^ c * 31 ^ d) =
      x * 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d by ring]; exact hB))
  have h2 := smoothOK_cons (by norm_num) h1 b
    (le_of_mul_le' p2 (by rw [show x * 7 ^ a * 13 ^ b * (19 ^ c * 31 ^ d) =
      x * 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d by ring]; exact hB))
  have h3 := smoothOK_cons (by norm_num) h2 c (le_of_mul_le' p3 (by
    rw [show x * 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d = x * 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d from rfl]
      at hB; nlinarith))
  have h4 := smoothOK_cons (by norm_num) h3 d hB
  simpa [smoothOK] using h4

/-- Soundness of the check over `[t, 7, 13, 19, 31]`. -/
theorem smoothOK5_sound {P : ℕ → Bool} {B x t : ℕ} (ht : 1 ≤ t)
    (h : smoothOK P B [t, 7, 13, 19, 31] x = true)
    (e a b c d : ℕ) (hB : x * t ^ e * (7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d) ≤ B) :
    P (x * t ^ e * (7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d)) = true := by
  have p0 : 1 ≤ 7 ^ a * 13 ^ b * 19 ^ c * 31 ^ d := Nat.pos_of_ne_zero (by positivity)
  have h0 := smoothOK_cons ht h e (le_of_mul_le' p0 hB)
  exact smoothOK4_sound h0 a b c d hB

/-! ### The sender scan -/

/-- Removing the factor `p` from `n`, with fuel. -/
def stripF : ℕ → ℕ → ℕ → ℕ
  | 0, _, n => n
  | f + 1, p, n => if n % p = 0 then stripF f p (n / p) else n

theorem stripF_spec {p m : ℕ} (hp : 2 ≤ p) (hm : ¬ p ∣ m) :
    ∀ k f, k ≤ f → stripF f p (p ^ k * m) = m := by
  intro k
  induction k with
  | zero =>
    intro f _
    cases f with
    | zero => simp [stripF]
    | succ f =>
      simp only [stripF, pow_zero, one_mul]
      rw [if_neg (fun h => hm (Nat.dvd_of_mod_eq_zero h))]
  | succ k ih =>
    intro f hf
    cases f with
    | zero => omega
    | succ f =>
      simp only [stripF]
      have h0 : p ^ (k + 1) * m % p = 0 := Nat.mod_eq_zero_of_dvd ⟨p ^ k * m, by ring⟩
      rw [if_pos h0, show p ^ (k + 1) * m / p = p ^ k * m by
        rw [show p ^ (k + 1) * m = p * (p ^ k * m) by ring]; exact Nat.mul_div_cancel_left _ (by omega)]
      exact ih f (by omega)

/-- `1 + s + s^2` with the factors 7, 13, 19, 31 removed. -/
def rem0 (s : ℕ) : ℕ :=
  stripF 40 31 (stripF 40 19 (stripF 40 13 (stripF 40 7 (1 + s + s ^ 2))))

/-- Trial division from `d`; true once `d^2 > n`. -/
def tdF : ℕ → ℕ → ℕ → Bool
  | 0, n, d => decide (n < d * d)
  | f + 1, n, d => if n < d * d then true else if n % d = 0 then false else tdF f n (d + 1)

/-- A primality test by trial division. -/
def isPr (n : ℕ) : Bool := decide (2 ≤ n) && tdF 200 n 2

theorem tdF_sound {n : ℕ} (hn : 2 ≤ n) : ∀ f d, tdF f n d = true → 2 ≤ d →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → n.Prime := by
  have key : ∀ d, n < d * d → (∀ m, 2 ≤ m → m < d → ¬ m ∣ n) → n.Prime := by
    intro d hd hm
    refine Nat.prime_def.mpr ⟨hn, fun m hmn => ?_⟩
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨k, rfl⟩ := hmn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn
    have hk0 : k ≠ 0 := by rintro rfl; simp at hn
    have hm2 : 2 ≤ m := by omega
    have hk2 : 2 ≤ k := by
      by_contra hk; have : k = 1 := by omega
      subst this; exact hc.2 (by ring)
    by_cases hmd : m < d
    · exact hm m hm2 hmd ⟨k, rfl⟩
    · have hkd : k < d := by
        by_contra hkd; have hkd := le_of_not_gt hkd
        have : d * d ≤ m * k := Nat.mul_le_mul (by omega) hkd
        omega
      exact hm k hk2 hkd ⟨m, by ring⟩
  intro f
  induction f with
  | zero =>
    intro d h _ hm
    simp only [tdF, decide_eq_true_eq] at h
    exact key d h hm
  | succ f ih =>
    intro d h hd hm
    simp only [tdF] at h
    by_cases h1 : n < d * d
    · exact key d h1 hm
    · rw [if_neg h1] at h
      by_cases h2 : n % d = 0
      · rw [if_pos h2] at h; exact absurd h (by simp)
      · rw [if_neg h2] at h
        refine ih (d + 1) h (by omega) fun m hm2 hmd hmn => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp hmd with hlt | rfl
        · exact hm m hm2 hlt hmn
        · exact h2 (Nat.mod_eq_zero_of_dvd hmn)

theorem isPr_sound {n : ℕ} (h : isPr n = true) : n.Prime := by
  simp only [isPr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact tdF_sound h.1 200 2 h.2 le_rfl fun m hm hm2 => absurd hm2 (by omega)

theorem isPr_of_prime {p : ℕ} (hp : p.Prime) (hlt : p < 24500) : isPr p = true := by
  have main : ∀ f d, 2 ≤ d → 158 ≤ d + f → tdF f p d = true := by
    intro f
    induction f with
    | zero =>
      intro d _ hd
      simp only [tdF, decide_eq_true_eq]
      nlinarith
    | succ f ih =>
      intro d hd2 hd
      simp only [tdF]
      by_cases h1 : p < d * d
      · rw [if_pos h1]
      · rw [if_neg h1]
        have hdp : d < p := by nlinarith
        have h2 : ¬ p % d = 0 := fun h0 => by
          have := (Nat.prime_def.mp hp).2 d (Nat.dvd_of_mod_eq_zero h0)
          omega
        rw [if_neg h2]
        exact ih (d + 1) (by omega) (by omega)
  simp only [isPr, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp.two_le, main 200 2 le_rfl (by norm_num)⟩

/-- Whether `x` is a power of `g`, with fuel. -/
def powOf : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, g, x => if x = 1 then true else if x % g = 0 then powOf f g (x / g) else false

theorem powOf_spec {g : ℕ} (hg : 2 ≤ g) : ∀ e f, e < f → powOf f g (g ^ e) = true := by
  intro e
  induction e with
  | zero => intro f hf; cases f with
    | zero => omega
    | succ f => simp [powOf]
  | succ e ih =>
    intro f hf
    cases f with
    | zero => omega
    | succ f =>
      simp only [powOf]
      have h1 : g ^ (e + 1) ≠ 1 := by
        have : 1 < g ^ (e + 1) := Nat.one_lt_pow (by omega) (by omega)
        omega
      rw [if_neg h1, if_pos (Nat.mod_eq_zero_of_dvd (dvd_pow_self g (by omega))),
        pow_succ, Nat.mul_div_cancel _ (by omega)]
      exact ih f (by omega)

/-- The primes `x ≡ 1 (mod 6)` with `37 ≤ x < 24500`. -/
def primesP : List ℕ := (List.range' 37 24463).filter fun x => decide (x % 6 = 1) && isPr x

/-- A sender of `s`: the base `g` when `1 + s + s^2`, with 7, 13, 19, 31 removed, is a power of a
prime `g < 24500` dividing `P`. -/
def sender (P s : ℕ) : Option ℕ :=
  let r := rem0 s
  if r = 1 then none else
  let g := Nat.gcd r P
  if g = 1 then none else if 24500 ≤ g then none else
  if powOf 45 g r && isPr g then some g else none

/-- The scan over `s, s + 6, s + 12, …` (`k` values), listing the senders. -/
def scan (P : ℕ) : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, s => match sender P s with
    | some g => (s, g) :: scan P k (s + 6)
    | none => scan P k (s + 6)

theorem scan_spec (P : ℕ) : ∀ k s j g, j < k → sender P (s + 6 * j) = some g →
    (s + 6 * j, g) ∈ scan P k s := by
  intro k
  induction k with
  | zero => intro s j g hj; omega
  | succ k ih =>
    intro s j g hj hg
    cases j with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero] at hg ⊢
      simp [scan, hg]
    | succ j =>
      have := ih (s + 6) j g (by omega) (by rw [show s + 6 + 6 * j = s + 6 * (j + 1) by ring]; exact hg)
      rw [show s + 6 + 6 * j = s + 6 * (j + 1) by ring] at this
      simp only [scan]
      split <;> simp [this]

/-! ### Interval tables -/

/-- Product of two fractions. -/
def qmul (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.1, x.2 * y.2)

/-- The rational value of a fraction pair. -/
def qv (x : ℕ × ℕ) : ℚ := (x.1 : ℚ) / x.2

/-- Every combination of one interval per factor gives a product interval whose upper end is
below 2 or whose lower end is above 2. -/
def ivOK : List (List ((ℕ × ℕ) × (ℕ × ℕ))) → ℕ × ℕ → ℕ × ℕ → Bool
  | [], lo, hi => decide (0 < lo.2) && decide (0 < hi.2) &&
      (decide (hi.1 < 2 * hi.2) || decide (2 * lo.2 < lo.1))
  | o :: L, lo, hi => o.all fun ab => ivOK L (qmul lo ab.1) (qmul hi ab.2)

theorem qv_qmul (x y : ℕ × ℕ) : qv (qmul x y) = qv x * qv y := by
  simp only [qv, qmul]; push_cast; rw [div_mul_div_comm]

theorem qv_nonneg (x : ℕ × ℕ) : 0 ≤ qv x := by unfold qv; positivity

theorem ivOK_sound : ∀ (L : List (List ((ℕ × ℕ) × (ℕ × ℕ)))) (lo hi : ℕ × ℕ),
    ivOK L lo hi = true → ∀ xs : List ℚ,
    List.Forall₂ (fun x o => ∃ ab ∈ o, qv ab.1 ≤ x ∧ x ≤ qv ab.2) xs L →
    ∀ y, qv lo ≤ y → y ≤ qv hi → y * xs.prod ≠ 2 := by
  intro L
  induction L with
  | nil =>
    intro lo hi h xs hxs y hlo hhi
    cases hxs
    simp only [ivOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [List.prod_nil, mul_one]
    rcases h3 with h3 | h3
    · have : qv hi < 2 := by
        unfold qv; rw [div_lt_iff₀ (by exact_mod_cast h2)]; exact_mod_cast h3
      intro e; linarith
    · have : 2 < qv lo := by
        unfold qv; rw [lt_div_iff₀ (by exact_mod_cast h1)]; exact_mod_cast h3
      intro e; linarith
  | cons o L ih =>
    intro lo hi h xs hxs y hlo hhi
    cases hxs with
    | cons hx hrest =>
      rename_i x xs'
      obtain ⟨ab, hab, hxa, hxb⟩ := hx
      simp only [ivOK, List.all_eq_true] at h
      have hy0 : 0 ≤ y := le_trans (qv_nonneg lo) hlo
      have hx0 : 0 ≤ x := le_trans (qv_nonneg ab.1) hxa
      have := ih _ _ (h ab hab) xs' hrest (y * x)
        (by rw [qv_qmul]; exact mul_le_mul hlo hxa (qv_nonneg _) hy0)
        (by rw [qv_qmul]; exact mul_le_mul hhi hxb hx0 (le_trans hy0 hhi))
      rw [List.prod_cons, ← mul_assoc]
      exact this

/-- The fraction `(p^(e+1) - 1)/(p^e (p - 1))`, the abundancy of `p^e`. -/
def hp (p e : ℕ) : ℕ × ℕ := (p ^ (e + 1) - 1, p ^ e * (p - 1))

/-- Options of a hit `s`: absent, exponent 2, exponent at least 8. -/
def hitOpts (s : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  [((1, 1), (1, 1)), (hp s 2, hp s 2), (hp s 8, (s, s - 1))]

/-- Option of an exponent at least `b`. -/
def geOpts (p b : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) := [(hp p b, (p, p - 1))]

/-- Options of 13: exponent 1 or at least 5. -/
def opts13 : List ((ℕ × ℕ) × (ℕ × ℕ)) := [(hp 13 1, hp 13 1), (hp 13 5, (13, 12))]

/-- Options of 7: exponent 4 or at least 6. -/
def opts7 : List ((ℕ × ℕ) × (ℕ × ℕ)) := [(hp 7 4, hp 7 4), (hp 7 6, (7, 6))]

/-- The interval table for a pinned fourth prime `t` with hits `hs` and the bound `R` for the
remaining good primes. -/
def tabOf (t : ℕ) (hs : List ℕ) (R : ℕ × ℕ) : List (List ((ℕ × ℕ) × (ℕ × ℕ))) :=
  [opts13, opts7, geOpts 19 4, geOpts 31 4, geOpts t 4] ++ hs.map hitOpts ++ [[((1, 1), R)]]

theorem qv_hp {p : ℕ} (hp' : p.Prime) (e : ℕ) : qv (hp p e) = abundancy (p ^ e) := by
  have h2 : (2 : ℚ) ≤ p := by exact_mod_cast hp'.two_le
  have h1 : 1 ≤ p ^ (e + 1) := Nat.one_le_pow _ _ hp'.pos
  have hp1 : 1 ≤ p := hp'.pos
  simp only [qv, hp, abundancy, sigma_one_apply_prime_pow hp']
  push_cast [Nat.cast_sub h1, Nat.cast_sub hp1]
  have hne : (p : ℚ) - 1 ≠ 0 := by linarith
  rw [geom_sum_eq (by linarith : (p : ℚ) ≠ 1)]
  have : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp

theorem qv_rv {p : ℕ} (hp' : 2 ≤ p) : qv (p, p - 1) = ThreeFreeThree.rv p := by
  simp only [qv, ThreeFreeThree.rv]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  simp

end FiveException

end OddPerfect

#print axioms OddPerfect.FiveException.inst_of_card
#print axioms OddPerfect.FiveException.ivOK_sound
#print axioms OddPerfect.FiveException.smoothOK_two_of
