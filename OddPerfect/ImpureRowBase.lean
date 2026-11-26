import OddPerfect.PureRows
import OddPerfect.EqualExponents
import OddPerfect.KanoldGeneral
import OddPerfect.AbundancyTail

/-!
# Impure rows under a common odd prime in every ordinary index: shared lemmas

Let `N` be an odd perfect number with special prime `q` and let `l` be an odd prime dividing
every ordinary index `e_p + 1` (`p ≠ q` a prime factor of `N`). The row of `p` is
`σ(p ^ e_p)`; it is pure when it is a prime power and impure otherwise.

This module holds the lemmas shared by `ImpureRowCount` and `ImpureRowCountFour`:

* `impureRow_cover`: if every prime factor outside a finite set `X ∋ q` has a pure row and an
  index divisible by `l`, then the receiver of each such row lies in `X`;
* `impureRow_core_of`: given a packing statement (`PackingStatement`, a copy of the statement
  of `exists_centers_of_pure_cover`), the product `∏ p/(p-1)` over the prime factors of `N`
  is at most the product over a small set `C` of centers times an explicit factor
  `impureRowT l K`;
* elementary bounds on `p/(p-1)` and on `impureRowT`;
* the counts (A), (B) and the one hole statement (D) in a version that takes the packing
  statement as a hypothesis.

Restricted result; no published source was checked; novelty not verified. The odd perfect
number conjecture remains open.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

/-- The statement of `exists_centers_of_pure_cover` (the packing theorem), taken as a hypothesis
here so that this module does not depend on the packing module; `packingStatement_holds` in
`ImpureRowCount` discharges it. -/
def PackingStatement : Prop :=
  ∀ {l K : ℕ} {S X : Finset ℕ}, l.Prime → l ≠ 2 → (∀ p ∈ S, p.Prime ∧ p ≠ 2) → X.card ≤ K →
    K + 1 < 3 ^ (l - 1) →
    (∀ p ∈ S, p ∉ X → ∃ r ∈ X, ∃ w, r.Prime ∧ ∑ i ∈ Finset.range l, p ^ i = r ^ w) →
    ∃ C : Finset ℕ, C ⊆ S ∧ C.card ≤ K ∧
      (∀ p ∈ S, p % l ≠ 1 → p ≤ 3 ^ (l - 1) → p ∈ C) ∧
      ∏ p ∈ S \ C, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        (∏ j ∈ Finset.range K,
            (((2 * (j + 1) * l + 1 : ℕ) : ℚ) / ((2 * (j + 1) * l : ℕ) : ℚ))) *
          (((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ)))

/-- The factor `T(l, K)` of the packing statement. -/
def impureRowT (l K : ℕ) : ℚ :=
  (∏ j ∈ Finset.range K, (((2 * (j + 1) * l + 1 : ℕ) : ℚ) / ((2 * (j + 1) * l : ℕ) : ℚ))) *
    (((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ)))

/-- **Receivers of pure rows outside `X` lie in `X`.** Let `N` be an odd perfect number with
special prime `q`, `l` an odd prime and `X` a finite set containing `q`. If every prime factor
`p ∉ X` has `l ∣ e_p + 1` and a pure row `σ(p ^ e_p) = r ^ w`, then for every such `p` the row
equals `∑ i < l, p ^ i` and is a power of a prime in `X`. -/
theorem impureRow_cover {N q l : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2) {X : Finset ℕ} (hqX : q ∈ X)
    (hidx : ∀ p ∈ N.primeFactors, p ∉ X → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ∉ X →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) :
    ∀ p ∈ N.primeFactors, p ∉ X →
      ∃ r ∈ X, ∃ w, r.Prime ∧ ∑ i ∈ Finset.range l, p ^ i = r ^ w := by
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  -- Every index outside `X` equals `l`.
  have hidx' : ∀ p ∈ N.primeFactors, p ∉ X → N.factorization p + 1 = l := by
    intro p hp hpX
    have hpq : p ≠ q := fun e => hpX (e ▸ hqX)
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
    have he0 : N.factorization p ≠ 0 :=
      (hp'.factorization_pos_of_dvd h.ne_zero (Nat.dvd_of_mem_primeFactors hp)).ne'
    obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpX
    have hpr := prime_succ_of_sigma_prime_pow_eq_prime_pow hp' hp2
      (even_factorization_of_ne h hq hodd hp' hpq) he0 hr hrow
    exact ((Nat.prime_dvd_prime_iff_eq hl hpr).mp (hidx p hp hpX)).symm
  -- No prime factor outside `X` is `1` modulo `l`.
  have hnot : ∀ p ∈ N.primeFactors, p ∉ X → p % l ≠ 1 := by
    intro p hp hpX h1
    have : Fact l.Prime := ⟨hl⟩
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
    have he := hidx' p hp hpX
    obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpX
    have hv := padicValNat_sigma_of_mod_eq_one (a := N.factorization p) hp' hl hl2 h1
    rw [he, Nat.padicValNat_def (p := l) (n := l), Nat.Prime.multiplicity_self,
      Nat.padicValNat_def] at hv
    have hdvd : l ∣ r ^ w := hrow ▸ dvd_of_one_le_multiplicity (by omega)
    have hlr : l = r := (Nat.prime_dvd_prime_iff_eq hl hr).mp (hl.dvd_of_dvd_pow hdvd)
    have hmod := receiver_mod_index_of_pure hp' hp2 (by omega) hr hrow
    rw [he, ← hlr, Nat.mod_self] at hmod
    exact absurd hmod (by norm_num)
  intro p hp hpX
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)
  have he := hidx' p hp hpX
  obtain ⟨r, w, hr, hrow⟩ := hpure p hp hpX
  obtain ⟨hrP, -, -⟩ := receiver_of_pure_row h hp hr hrow
  have hmod := receiver_mod_index_of_pure hp' hp2 (by omega) hr hrow
  rw [he] at hmod
  by_cases hrX : r ∈ X
  · refine ⟨r, hrX, w, hr, ?_⟩
    have he' : N.factorization p = l - 1 := by omega
    rw [he', sigma_one_apply_prime_pow hp', Nat.sub_add_cancel (by omega)] at hrow
    exact hrow
  · exact absurd hmod (hnot r hrP hrX)

/-- `p/(p-1)` is at least `1` for `p ≥ 2`. -/
theorem impureRow_one_le_H {p : ℕ} (hp : 2 ≤ p) : 1 ≤ (p : ℚ) / ((p : ℚ) - 1) := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `p/(p-1)` is antitone on `p ≥ 2`. -/
theorem impureRow_H_anti {a p : ℕ} (ha : 2 ≤ a) (hap : a ≤ p) :
    (p : ℚ) / ((p : ℚ) - 1) ≤ (a : ℚ) / ((a : ℚ) - 1) := by
  have ha' : (2 : ℚ) ≤ a := by exact_mod_cast ha
  have hap' : (a : ℚ) ≤ p := by exact_mod_cast hap
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- A product of `p/(p-1)` over numbers at least `2` is nonnegative. -/
theorem impureRow_prod_H_nonneg {D : Finset ℕ} (hD : ∀ x ∈ D, 2 ≤ x) :
    0 ≤ ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) :=
  Finset.prod_nonneg fun x hx => zero_le_one.trans (impureRow_one_le_H (hD x hx))

/-- **Product of `p/(p-1)` over at most `k` odd numbers at least `a`.** It is at most
`∏ i < k, (a + 2i)/(a + 2i - 1)`. -/
theorem impureRow_prod_H_odd_le : ∀ (k : ℕ) {D : Finset ℕ} {a : ℕ}, 2 ≤ a → D.card ≤ k →
    (∀ x ∈ D, Odd x) → (∀ x ∈ D, a ≤ x) →
    ∏ x ∈ D, ((x : ℚ) / ((x : ℚ) - 1)) ≤
      ∏ i ∈ Finset.range k, (((a + 2 * i : ℕ) : ℚ) / (((a + 2 * i : ℕ) : ℚ) - 1))
  | 0, D, a, _, hD, _, _ => by
    rw [Finset.card_eq_zero.mp (show D.card = 0 by omega)]
    simp
  | k + 1, D, a, ha, hD, hodd, hge => by
    rcases D.eq_empty_or_nonempty with rfl | hne
    · rw [Finset.prod_empty]
      have h1 := Finset.prod_le_prod₀ (s := Finset.range (k + 1)) (f := fun _ => (1 : ℚ))
        (fun _ _ => zero_le_one) (fun i _ => impureRow_one_le_H (p := a + 2 * i) (by omega))
      simpa using h1
    · have hm : D.min' hne ∈ D := D.min'_mem hne
      have hrest := impureRow_prod_H_odd_le k (D := D.erase (D.min' hne)) (a := a + 2)
        (by omega) (by rw [Finset.card_erase_of_mem hm]; omega)
        (fun x hx => hodd x (Finset.mem_of_mem_erase hx)) (fun x hx => by
          obtain ⟨hxm, hxD⟩ := Finset.mem_erase.mp hx
          have hle : D.min' hne ≤ x := D.min'_le x hxD
          have ham := hge _ hm
          obtain ⟨u, hu⟩ := hodd x hxD
          obtain ⟨v, hv⟩ := hodd _ hm
          omega)
      have e : ∀ i, a + 2 * (i + 1) = a + 2 + 2 * i := fun i => by ring
      rw [← Finset.mul_prod_erase D _ hm, Finset.prod_range_succ']
      simp only [e, mul_zero, add_zero]
      have ham := hge _ hm
      exact (le_of_eq (mul_comm _ _)).trans (mul_le_mul hrest (impureRow_H_anti ha ham)
        (zero_le_one.trans (impureRow_one_le_H (by omega)))
        (Finset.prod_nonneg fun i _ => zero_le_one.trans (impureRow_one_le_H (by omega))))

/-- One factor of the packing product is antitone. -/
theorem impureRow_succ_div_le {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    ((b + 1 : ℕ) : ℚ) / ((b : ℕ) : ℚ) ≤ ((a + 1 : ℕ) : ℚ) / ((a : ℕ) : ℚ) := by
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) ha']
  push_cast
  nlinarith

/-- `impureRowT l K` is nonnegative when `K + 1 < 3 ^ (l - 1)`. -/
theorem impureRowT_nonneg {l K : ℕ} (hK : K + 1 < 3 ^ (l - 1)) : 0 ≤ impureRowT l K := by
  have hK' : (K : ℚ) + 1 < 3 ^ (l - 1) := by exact_mod_cast hK
  unfold impureRowT
  exact mul_nonneg (Finset.prod_nonneg fun j _ => by positivity)
    (div_nonneg (by linarith) (by linarith))

/-- **Monotonicity of `impureRowT`.** For `L ≤ l` and `m ≤ l - 1` with `K < 3 ^ m - 1`, the
factor `impureRowT l K` is at most the same expression with `l` replaced by `L` in the product
and `3 ^ (l - 1)` replaced by `3 ^ m` in the last factor. -/
theorem impureRowT_le {l L m K : ℕ} (hL : 0 < L) (hLl : L ≤ l) (hm : m ≤ l - 1)
    (hK : (K : ℚ) < 3 ^ m - 1) :
    impureRowT l K ≤
      (∏ j ∈ Finset.range K,
          (((2 * (j + 1) * L + 1 : ℕ) : ℚ) / ((2 * (j + 1) * L : ℕ) : ℚ))) *
        (((3 : ℚ) ^ m - 1) / ((3 : ℚ) ^ m - 1 - (K : ℚ))) := by
  have h3 : (3 : ℚ) ^ m ≤ 3 ^ (l - 1) := pow_le_pow_right₀ (by norm_num) hm
  have hK0 : (0 : ℚ) ≤ K := Nat.cast_nonneg K
  have hx : (3 : ℚ) ^ m - 1 - K > 0 := by linarith
  have hy : (3 : ℚ) ^ (l - 1) - 1 - K > 0 := by linarith
  have hP : (∏ j ∈ Finset.range K,
        (((2 * (j + 1) * l + 1 : ℕ) : ℚ) / ((2 * (j + 1) * l : ℕ) : ℚ))) ≤
      ∏ j ∈ Finset.range K,
        (((2 * (j + 1) * L + 1 : ℕ) : ℚ) / ((2 * (j + 1) * L : ℕ) : ℚ)) :=
    Finset.prod_le_prod₀ (fun j _ => by positivity)
      (fun j _ => impureRow_succ_div_le (by positivity) (Nat.mul_le_mul_left _ hLl))
  have hQ : ((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ)) ≤
      ((3 : ℚ) ^ m - 1) / ((3 : ℚ) ^ m - 1 - (K : ℚ)) := by
    rw [div_le_div_iff₀ hy hx]
    nlinarith [mul_le_mul_of_nonneg_right h3 hK0]
  have hQ0 : 0 ≤ ((3 : ℚ) ^ (l - 1) - 1) / ((3 : ℚ) ^ (l - 1) - 1 - (K : ℚ)) :=
    div_nonneg (by linarith) hy.le
  have hP0 : 0 ≤ ∏ j ∈ Finset.range K,
      (((2 * (j + 1) * L + 1 : ℕ) : ℚ) / ((2 * (j + 1) * L : ℕ) : ℚ)) :=
    Finset.prod_nonneg fun j _ => by positivity
  unfold impureRowT
  exact mul_le_mul hP hQ hQ0 hP0

/-- `n + 1 ≤ 3 ^ n`. -/
theorem impureRow_succ_le_three_pow : ∀ n : ℕ, n + 1 ≤ 3 ^ n
  | 0 => by norm_num
  | n + 1 => by
    have := impureRow_succ_le_three_pow n
    rw [pow_succ]
    omega

/-- **Core bound, assuming the packing statement.** Let `N` be an odd perfect number with
special prime `q`, `l` an odd prime and `X ∋ q` a finite set with at most `K` elements, where
`K + 1 < 3 ^ (l - 1)`. If every prime factor `p ∉ X` has `l ∣ e_p + 1` and a pure row, there
is a set `C` of at most `K` prime factors of `N`, containing every prime factor `p` with
`p % l ≠ 1` and `p ≤ 3 ^ (l - 1)`, such that
`∏ p ∈ N.primeFactors, p/(p-1) ≤ (∏ p ∈ C, p/(p-1)) * impureRowT l K`. -/
theorem impureRow_core_of (hpack : PackingStatement) {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    {X : Finset ℕ} (hqX : q ∈ X)
    (hidx : ∀ p ∈ N.primeFactors, p ∉ X → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ∉ X →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w)
    {K : ℕ} (hX : X.card ≤ K) (hK : K + 1 < 3 ^ (l - 1)) :
    ∃ C : Finset ℕ, C ⊆ N.primeFactors ∧ C.card ≤ K ∧
      (∀ p ∈ N.primeFactors, p % l ≠ 1 → p ≤ 3 ^ (l - 1) → p ∈ C) ∧
      ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        (∏ p ∈ C, ((p : ℚ) / ((p : ℚ) - 1))) * impureRowT l K := by
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hp)⟩
  obtain ⟨C, hCS, hCK, hmem, hT⟩ :=
    hpack hl hl2 hS hX hK (impureRow_cover h hq hodd hl hl2 hqX hidx hpure)
  refine ⟨C, hCS, hCK, hmem, ?_⟩
  have hC0 : 0 ≤ ∏ p ∈ C, ((p : ℚ) / ((p : ℚ) - 1)) :=
    impureRow_prod_H_nonneg fun x hx => (hS x (hCS hx)).1.two_le
  have h1 := mul_le_mul_of_nonneg_left hT hC0
  unfold impureRowT
  rw [← Finset.prod_sdiff hCS]
  linarith

/-- Monotone product of three nonnegative factors. -/
theorem impureRow_chain_le {Hl E T Hb Eb Tb : ℚ} (hHl0 : 0 ≤ Hl) (hE0 : 0 ≤ E) (hT0 : 0 ≤ T)
    (hHl : Hl ≤ Hb) (hE : E ≤ Eb) (hT : T ≤ Tb) : Hl * E * T ≤ Hb * Eb * Tb :=
  mul_le_mul (mul_le_mul hHl hE hE0 (hHl0.trans hHl)) hT hT0
    (mul_nonneg (hHl0.trans hHl) (hE0.trans hE))

/-- Shared setup of (A), (B), (C): with `X = insert q M`, the prime `l` lies in the set of
centers, and the product over the prime factors is bounded by
`l/(l-1) · ∏_{C \ {l}} p/(p-1) · impureRowT l K`. -/
theorem impureRow_setup_of (hpack : PackingStatement) {N q l : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime) (hl2 : l ≠ 2)
    (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1) (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w)
    {K : ℕ} (hX : M.card + 1 ≤ K) (hK : K + 1 < 3 ^ (l - 1)) :
    ∃ D : Finset ℕ, D.card + 1 ≤ K ∧ (∀ x ∈ D, x.Prime ∧ x ≠ 2 ∧ x ≠ l ∧ x ∣ N) ∧
      ∏ p ∈ N.primeFactors, ((p : ℚ) / ((p : ℚ) - 1)) ≤
        (l : ℚ) / ((l : ℚ) - 1) * (∏ p ∈ D, ((p : ℚ) / ((p : ℚ) - 1))) *
          impureRowT l K := by
  have hqX : q ∈ insert q M := Finset.mem_insert_self q M
  have hne : ∀ p, p ∉ insert q M → p ≠ q := fun p hpX e => hpX (e ▸ hqX)
  obtain ⟨C, hCS, hCK, hmem, hbound⟩ := impureRow_core_of hpack h hq hodd hl hl2 hqX
    (fun p hp hpX => hidx p hp (hne p hpX))
    (fun p hp hpX => hM p hp (hne p hpX) fun hpM => hpX (Finset.mem_insert_of_mem hpM))
    ((Finset.card_insert_le q M).trans hX) hK
  have hlN := dvd_of_dvd_succ h hq hodd hl hl2 hidx
  have hl1 : l % l ≠ 1 := by rw [Nat.mod_self]; omega
  have hlC : l ∈ C := hmem l (Nat.mem_primeFactors.mpr ⟨hl, hlN, h.ne_zero⟩) hl1
    (by have := impureRow_succ_le_three_pow (l - 1); have := hl.two_le; omega)
  refine ⟨C.erase l, ?_, fun x hx => ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hlC]
    have := Finset.card_pos.mpr ⟨l, hlC⟩
    omega
  · obtain ⟨hxl, hxC⟩ := Finset.mem_erase.mp hx
    have hxS := hCS hxC
    refine ⟨Nat.prime_of_mem_primeFactors hxS, ?_, hxl, Nat.dvd_of_mem_primeFactors hxS⟩
    rintro rfl
    exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors hxS)
  · rwa [← Finset.mul_prod_erase C _ hlC] at hbound

/-- Facts used to apply `impureRow_prod_H_odd_le` to a set of odd primes. -/
theorem impureRow_odd_of_prime {x : ℕ} (hx : x.Prime) (hx2 : x ≠ 2) : Odd x ∧ 3 ≤ x :=
  ⟨hx.odd_of_ne_two hx2, by have := hx.two_le; omega⟩

/-- **(A) with the packing statement as a hypothesis.** See `two_le_card_of_pure_outside`.
Restricted result; no published source was checked; novelty not verified. -/
theorem two_le_card_of_pure_outside_of (hpack : PackingStatement) {N q l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hl7 : 7 ≤ l) (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 2 ≤ M.card := by
  by_contra hlt
  have hK : 2 + 1 < 3 ^ (l - 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ l - 1))
  obtain ⟨D, hDc, hD, hbound⟩ :=
    impureRow_setup_of hpack h hq hodd hl (by omega) hidx M hM (by omega) hK
  have hE := impureRow_prod_H_odd_le 1 (D := D) (a := 3) (by norm_num) (by omega)
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2.1).1)
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2.1).2)
  have hT := impureRowT_le (L := 7) (m := 6) (by norm_num) hl7 (by omega)
    (by norm_num : ((2 : ℕ) : ℚ) < 3 ^ 6 - 1)
  have hc := impureRow_chain_le (zero_le_one.trans (impureRow_one_le_H (by omega)))
    (impureRow_prod_H_nonneg fun x hx => (hD x hx).1.two_le) (impureRowT_nonneg hK)
    (impureRow_H_anti (by norm_num) hl7) hE hT
  have h2 := two_lt_prod_primeFactors_div h
  have hnum : ((7 : ℕ) : ℚ) / (((7 : ℕ) : ℚ) - 1) *
      (∏ i ∈ Finset.range 1, (((3 + 2 * i : ℕ) : ℚ) / (((3 + 2 * i : ℕ) : ℚ) - 1))) *
      ((∏ j ∈ Finset.range 2,
          (((2 * (j + 1) * 7 + 1 : ℕ) : ℚ) / ((2 * (j + 1) * 7 : ℕ) : ℚ))) *
        (((3 : ℚ) ^ 6 - 1) / ((3 : ℚ) ^ 6 - 1 - ((2 : ℕ) : ℚ)))) < 2 := by
    norm_num [Finset.prod_range_succ]
  linarith

/-- **(B) with the packing statement as a hypothesis.** See
`three_le_card_of_pure_outside`.
Restricted result; no published source was checked; novelty not verified. -/
theorem three_le_card_of_pure_outside_of (hpack : PackingStatement) {N q l : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hl31 : 31 ≤ l) (hidx : ∀ p ∈ N.primeFactors, p ≠ q → l ∣ N.factorization p + 1)
    (M : Finset ℕ)
    (hM : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ M →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : 3 ≤ M.card := by
  by_contra hlt
  have hK : 3 + 1 < 3 ^ (l - 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ l - 1))
  obtain ⟨D, hDc, hD, hbound⟩ :=
    impureRow_setup_of hpack h hq hodd hl (by omega) hidx M hM (by omega) hK
  have hE := impureRow_prod_H_odd_le 2 (D := D) (a := 3) (by norm_num) (by omega)
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2.1).1)
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2.1).2)
  have hT := impureRowT_le (L := 31) (m := 30) (by norm_num) hl31 (by omega)
    (by norm_num : ((3 : ℕ) : ℚ) < 3 ^ 30 - 1)
  have hc := impureRow_chain_le (zero_le_one.trans (impureRow_one_le_H (by omega)))
    (impureRow_prod_H_nonneg fun x hx => (hD x hx).1.two_le) (impureRowT_nonneg hK)
    (impureRow_H_anti (by norm_num) hl31) hE hT
  have h2 := two_lt_prod_primeFactors_div h
  have hnum : ((31 : ℕ) : ℚ) / (((31 : ℕ) : ℚ) - 1) *
      (∏ i ∈ Finset.range 2, (((3 + 2 * i : ℕ) : ℚ) / (((3 + 2 * i : ℕ) : ℚ) - 1))) *
      ((∏ j ∈ Finset.range 3,
          (((2 * (j + 1) * 31 + 1 : ℕ) : ℚ) / ((2 * (j + 1) * 31 : ℕ) : ℚ))) *
        (((3 : ℚ) ^ 30 - 1) / ((3 : ℚ) ^ 30 - 1 - ((3 : ℕ) : ℚ)))) < 2 := by
    norm_num [Finset.prod_range_succ]
  linarith

/-- **(D) with the packing statement as a hypothesis.** See
`not_all_pure_common_index_one_hole`.
Restricted result; no published source was checked; novelty not verified. -/
theorem not_all_pure_common_index_one_hole_of (hpack : PackingStatement) {N q l d : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q)) (hl : l.Prime)
    (hl13 : 13 ≤ l) (hidx : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d → l ∣ N.factorization p + 1)
    (hpure : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ d →
      ∃ r w, r.Prime ∧ σ 1 (p ^ N.factorization p) = r ^ w) : False := by
  have hK : 2 + 1 < 3 ^ (l - 1) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ l - 1))
  have hqX : q ∈ ({q, d} : Finset ℕ) := Finset.mem_insert_self q {d}
  have hq' : ∀ p, p ∉ ({q, d} : Finset ℕ) → p ≠ q := fun p hpX e => hpX (by simp [e])
  have hd' : ∀ p, p ∉ ({q, d} : Finset ℕ) → p ≠ d := fun p hpX e => hpX (by simp [e])
  obtain ⟨C, hCS, hCK, -, hbound⟩ := impureRow_core_of hpack h hq hodd hl (by omega) hqX
    (fun p hp hpX => hidx p hp (hq' p hpX) (hd' p hpX))
    (fun p hp hpX => hpure p hp (hq' p hpX) (hd' p hpX)) Finset.card_le_two hK
  have hD : ∀ x ∈ C, x.Prime ∧ x ≠ 2 := fun x hx =>
    ⟨Nat.prime_of_mem_primeFactors (hCS hx), by
      rintro rfl
      exact h.not_two_dvd (Nat.dvd_of_mem_primeFactors (hCS hx))⟩
  have hE := impureRow_prod_H_odd_le 2 (D := C) (a := 3) (by norm_num) hCK
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2).1)
    (fun x hx => (impureRow_odd_of_prime (hD x hx).1 (hD x hx).2).2)
  have hT := impureRowT_le (L := 13) (m := 12) (by norm_num) hl13 (by omega)
    (by norm_num : ((2 : ℕ) : ℚ) < 3 ^ 12 - 1)
  have hc := impureRow_chain_le zero_le_one
    (impureRow_prod_H_nonneg fun x hx => (hD x hx).1.two_le) (impureRowT_nonneg hK)
    le_rfl hE hT
  have h2 := two_lt_prod_primeFactors_div h
  have hnum : (1 : ℚ) *
      (∏ i ∈ Finset.range 2, (((3 + 2 * i : ℕ) : ℚ) / (((3 + 2 * i : ℕ) : ℚ) - 1))) *
      ((∏ j ∈ Finset.range 2,
          (((2 * (j + 1) * 13 + 1 : ℕ) : ℚ) / ((2 * (j + 1) * 13 : ℕ) : ℚ))) *
        (((3 : ℚ) ^ 12 - 1) / ((3 : ℚ) ^ 12 - 1 - ((2 : ℕ) : ℚ)))) < 2 := by
    norm_num [Finset.prod_range_succ]
  linarith

end OddPerfect

#print axioms OddPerfect.impureRow_cover
#print axioms OddPerfect.impureRow_one_le_H
#print axioms OddPerfect.impureRow_H_anti
#print axioms OddPerfect.impureRow_prod_H_nonneg
#print axioms OddPerfect.impureRow_prod_H_odd_le
#print axioms OddPerfect.impureRow_succ_div_le
#print axioms OddPerfect.impureRowT_nonneg
#print axioms OddPerfect.impureRowT_le
#print axioms OddPerfect.impureRow_succ_le_three_pow
#print axioms OddPerfect.impureRow_core_of
#print axioms OddPerfect.impureRow_chain_le
#print axioms OddPerfect.impureRow_setup_of
#print axioms OddPerfect.impureRow_odd_of_prime
#print axioms OddPerfect.two_le_card_of_pure_outside_of
#print axioms OddPerfect.three_le_card_of_pure_outside_of
#print axioms OddPerfect.not_all_pure_common_index_one_hole_of
