import OddPerfect.TwoExceptionFourChains
import OddPerfect.Abundancy
import OddPerfect.EqualExponentsBound

/-!
# Two exceptional exponents, exponent 4 at 3: the family is empty

Let `N` be an odd perfect number with special prime `q`, `v_3(N) = 4`, and every prime factor
other than `q`, `r₁` and `r₂` of exponent exactly 2. This is a restricted family; the result does
not concern odd perfect numbers in general. We show that no such `N` exists, so `v_3(N) ≠ 4`.

By the landed modules the exceptions are `3` and `11` and `q ≡ 1 (mod 12)`
(`TwoExceptionFourChains.Ctx.of`), and by `TwoExceptionFourChains.small` every prime factor other
than `3` and `11` is at least `79`. Call a prime factor `p ∉ {3, 11, q}` a square prime and
`A` the square primes `≡ 1 (mod 3)`.

* Counting. `|A| ≤ 4` (`card_exact_sq_modEq_one_le`, since `v_3(N) = 4`). A square prime
  `p ≢ 1 (mod 3)` whose `p^2 + p + 1` is not a power of `q` has a prime factor of
  `p^2 + p + 1` in `A`; each `a ∈ A` has exponent 2, so it divides at most two rows
  (`card_feeders_le`). Hence at most `1 + 4 + 8 = 13` prime factors outside `{3, 11}` have rows
  that are not pure powers of `q`.
* Pure rows. If `p^2 + p + 1 = q^k` and `p'^2 + p' + 1 = q^k'` with `p < p'`, then `k < k'`, so
  `79 p^2 < q (p^2 + p + 1) ≤ p'^2 + p' + 1 < (p' + 1)^2` and `p' > 8 p`. An induction on the
  smallest element gives `∏ p/(p - 1) ≤ 1 + 6/(5 · 79)` over the pure rows.
* Abundancy. `2 = σ(N)/N ≤ (121/81) · (11/10) · (79/78)^13 · (401/395) < 1.97`.

Whether these statements are new was not verified against the literature.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExceptionFourEmpty

open TwoExceptionFourChains

/-- A pure row: `p ∉ {3, 11, q}` and `p^2 + p + 1` is a power of `q`. -/
def IsPure (q p : ℕ) : Prop := p ≠ 3 ∧ p ≠ 11 ∧ p ≠ q ∧ phi3 p = q ^ (phi3 p).factorization q

instance (q : ℕ) : DecidablePred (IsPure q) := fun p => by unfold IsPure; infer_instance

private theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem ratio_le {p : ℕ} (hp : 79 ≤ p) : (p : ℚ) / (p - 1) ≤ 79 / 78 := by
  have h : (79 : ℚ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

private theorem step_ineq (A : ℚ) (hA : 24 ≤ A) :
    A / (A - 1) * (1 + 6 / (5 * (8 * A))) ≤ 1 + 6 / (5 * A) := by
  have hA0 : 0 < A := by linarith
  have hA1 : 0 < A - 1 := by linarith
  have e1 : A / (A - 1) * (1 + 6 / (5 * (8 * A))) = (20 * A + 3) / (20 * (A - 1)) := by
    field_simp
    ring
  have e2 : 1 + 6 / (5 * A) = (5 * A + 6) / (5 * A) := by
    field_simp
  rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- If every element is at least `L ≥ 24` and any two elements `p < p'` satisfy `8 p < p'`,
then `∏ p/(p - 1) ≤ 1 + 6/(5 L)`. -/
theorem prod_ratio_le (P : Finset ℕ) : ∀ L : ℕ, 24 ≤ L → (∀ p ∈ P, L ≤ p) →
    (∀ p ∈ P, ∀ p' ∈ P, p < p' → 8 * p < p') →
    ∏ p ∈ P, ((p : ℚ) / (p - 1)) ≤ 1 + 6 / (5 * L) := by
  induction P using Finset.induction_on_min with
  | empty =>
    intro L _ _ _
    simp only [Finset.prod_empty, le_add_iff_nonneg_right]
    positivity
  | insert a s ha ih =>
    intro L hL hmem hsep
    have haL : L ≤ a := hmem a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    rw [Finset.prod_insert has]
    have hs := ih (8 * a) (by omega)
      (fun p hp => (hsep a (Finset.mem_insert_self a s) p (Finset.mem_insert_of_mem hp)
        (ha p hp)).le)
      (fun p hp p' hp' => hsep p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp'))
    have hA : (24 : ℚ) ≤ a := by exact_mod_cast le_trans hL haL
    have hLa : (L : ℚ) ≤ a := by exact_mod_cast haL
    have hL0 : (0 : ℚ) < L := by exact_mod_cast (by omega : 0 < L)
    have hf0 : (0 : ℚ) ≤ (a : ℚ) / (a - 1) := div_nonneg (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hs hf0
    push_cast at h1
    have h2 := step_ineq (a : ℚ) hA
    have h3 : 6 / (5 * (a : ℚ)) ≤ 6 / (5 * L) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith

variable {N q : ℕ}

/-- The contradiction in the context of `TwoExceptionFourChains`. -/
theorem false_of_ctx (C : Ctx N q) : False := by
  have hN0 := C.h.ne_zero
  have hP := C.h.perfect
  have hsmall : ∀ p ∈ N.primeFactors, p = 3 ∨ p = 11 ∨ 79 ≤ p := fun p hp =>
    small C (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hqN : q ∈ N.primeFactors := Nat.mem_primeFactors.mpr
    ⟨C.hq, Nat.dvd_of_factorization_pos C.hodd.pos.ne', hN0⟩
  have hq79 : 79 ≤ q := by
    have := C.hq12
    rcases hsmall q hqN with h | h | h <;> omega
  have hab := (perfect_iff_abundancy_eq_two C.h.pos).mp hP
  rw [abundancy_eq_prod_primeFactors hN0,
    ← Finset.prod_filter_mul_prod_filter_not N.primeFactors (IsPure q)] at hab
  -- the pure rows
  have hPure : ∏ p ∈ N.primeFactors with IsPure q p, abundancy (p ^ N.factorization p) ≤
      401 / 395 := by
    have sep : ∀ p ∈ N.primeFactors.filter (IsPure q), ∀ p' ∈ N.primeFactors.filter (IsPure q),
        p < p' → 8 * p < p' := by
      intro p hp p' hp' hlt
      obtain ⟨hpN, -, -, -, hpow⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, -, -, hpow'⟩ := Finset.mem_filter.mp hp'
      have hp79 : 79 ≤ p := by
        obtain ⟨-, h3, h11, -, -⟩ := Finset.mem_filter.mp hp
        rcases hsmall p hpN with h | h | h <;> omega
      set k := (phi3 p).factorization q
      set k' := (phi3 p').factorization q
      have hlt' : phi3 p < phi3 p' := phi3_strictMono hlt
      have hkk : k < k' := by
        by_contra hc
        have : q ^ k' ≤ q ^ k := Nat.pow_le_pow_right C.hq.pos (by omega)
        omega
      have hq1 : phi3 p * q ≤ phi3 p' := by
        rw [hpow, hpow', ← pow_succ]
        exact Nat.pow_le_pow_right C.hq.pos hkk
      have hsq := sq_lt_phi3 p
      have hsq' := phi3_lt_succ_sq (show 1 ≤ p' by omega)
      have hmul : 79 * phi3 p ≤ phi3 p * q := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ hq79
      by_contra hc
      have hle := Nat.pow_le_pow_left (show p' + 1 ≤ 8 * p + 1 by omega) 2
      nlinarith
    calc _ ≤ ∏ p ∈ N.primeFactors with IsPure q p, ((p : ℚ) / (p - 1)) :=
          Finset.prod_le_prod₀ (fun _ _ => abundancy_nonneg _) (fun p hp =>
            (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors
              (Finset.mem_filter.mp hp).1) _).le)
      _ ≤ 1 + 6 / (5 * ((79 : ℕ) : ℚ)) := prod_ratio_le _ 79 (by norm_num) (fun p hp => by
          obtain ⟨hpN, h3, h11, -, -⟩ := Finset.mem_filter.mp hp
          rcases hsmall p hpN with h | h | h <;> omega) sep
      _ = 401 / 395 := by norm_num
  -- the other rows
  have d11 : 11 ∣ N := OPNStarter.force_prime hP Nat.prime_three C.h34 (by norm_num)
    (by norm_num)
    (by rw [sigma_one_apply_prime_pow Nat.prime_three]; norm_num [Finset.sum_range_succ])
  set K := N.primeFactors.filter (fun p => ¬ IsPure q p) with hKdef
  have h3K : 3 ∈ K := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
    Nat.dvd_of_factorization_pos (by rw [C.h34]; norm_num), hN0⟩, fun h => h.1 rfl⟩
  have h11K : 11 ∈ K.erase 3 := Finset.mem_erase.mpr ⟨by norm_num, Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨by norm_num, d11, hN0⟩, fun h => h.2.1 rfl⟩⟩
  set K' := (K.erase 3).erase 11 with hK'def
  have hKprod : ∏ p ∈ K, abundancy (p ^ N.factorization p) =
      abundancy (3 ^ N.factorization 3) * (abundancy (11 ^ N.factorization 11) *
        ∏ p ∈ K', abundancy (p ^ N.factorization p)) := by
    rw [hK'def, ← Finset.mul_prod_erase K _ h3K, ← Finset.mul_prod_erase (K.erase 3) _ h11K]
  have hab3 : abundancy (3 ^ N.factorization 3) = 121 / 81 := by
    rw [C.h34, abundancy_prime_pow Nat.prime_three]
    norm_num [Finset.sum_range_succ]
  have hab11 : abundancy (11 ^ N.factorization 11) ≤ 11 / 10 :=
    calc _ ≤ ((11 : ℕ) : ℚ) / ((11 : ℕ) - 1) :=
          (abundancy_prime_pow_lt (by norm_num) _).le
      _ = 11 / 10 := by norm_num
  have hK'mem : ∀ p ∈ K', p ∈ N.primeFactors ∧ p ≠ 3 ∧ p ≠ 11 ∧ ¬ IsPure q p := by
    intro p hp
    obtain ⟨h11, hp'⟩ := Finset.mem_erase.mp hp
    obtain ⟨h3, hp''⟩ := Finset.mem_erase.mp hp'
    obtain ⟨hpN, hnp⟩ := Finset.mem_filter.mp hp''
    exact ⟨hpN, h3, h11, hnp⟩
  have hK'prod : ∏ p ∈ K', abundancy (p ^ N.factorization p) ≤ (79 / 78) ^ K'.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => abundancy_nonneg _) (fun p hp => by
      obtain ⟨hpN, h3, h11, -⟩ := hK'mem p hp
      have h79 : 79 ≤ p := by rcases hsmall p hpN with h | h | h <;> omega
      exact (abundancy_prime_pow_lt (Nat.prime_of_mem_primeFactors hpN) _).le.trans
        (ratio_le h79))
  -- counting the rows that are not pure
  set Afs := N.primeFactors.filter (fun p => N.factorization p = 2 ∧ p % 3 = 1) with hAdef
  have hAcard : Afs.card ≤ 4 := by
    have := card_exact_sq_modEq_one_le C.h
    rw [C.h34] at this
    exact this
  let fd : ℕ → Finset ℕ := fun a =>
    (N.primeFactors.erase a).filter (fun p => a ∣ σ 1 (p ^ N.factorization p))
  have hfd : ∀ a ∈ Afs, (fd a).card ≤ 2 := by
    intro a ha
    obtain ⟨haN, h2, -⟩ := Finset.mem_filter.mp ha
    have := card_feeders_le hP (Nat.prime_of_mem_primeFactors haN) (by
      rintro rfl
      exact C.h.not_two_dvd (Nat.dvd_of_mem_primeFactors haN))
    rw [h2] at this
    exact this
  have hsub : K' ⊆ insert q (Afs ∪ Afs.biUnion fd) := by
    intro p hp
    obtain ⟨hpN, h3, h11, hnp⟩ := hK'mem p hp
    rw [Finset.mem_insert, Finset.mem_union]
    by_cases hpq : p = q
    · exact Or.inl hpq
    right
    have hpP := Nat.prime_of_mem_primeFactors hpN
    have he := C.hsq p hpN hpq h3 h11
    by_cases hp1 : p % 3 = 1
    · exact Or.inl (Finset.mem_filter.mpr ⟨hpN, he, hp1⟩)
    right
    have hpow : phi3 p ≠ q ^ (phi3 p).factorization q := fun e => hnp ⟨h3, h11, hpq, e⟩
    obtain ⟨r, hr, hrd, hrq⟩ : ∃ r, r.Prime ∧ r ∣ phi3 p ∧ r ≠ q := by
      by_contra hc
      push Not at hc
      obtain ⟨m, hm⟩ : ∃ m, phi3 p = q ^ m :=
        ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by unfold phi3; positivity)
          (fun hd hdd => hc _ hd hdd)⟩
      apply hpow
      rw [hm, C.hq.factorization_pow, Finsupp.single_eq_same]
    have hr3 : r ≠ 3 := by
      rintro rfl
      exact hp1 ((three_dvd_phi3_iff p).mp hrd)
    have hr31 : r % 3 = 1 := prime_dvd_phi3_mod_three hr hr3 hrd
    have hrN : r ∣ N := C.sq hpP (Nat.dvd_of_mem_primeFactors hpN) hpq h3 h11 hr hrd
    have hrm := Nat.mem_primeFactors.mpr ⟨hr, hrN, hN0⟩
    have hrA : r ∈ Afs := Finset.mem_filter.mpr ⟨hrm, C.hsq r hrm hrq hr3 (by omega), hr31⟩
    refine Finset.mem_biUnion.mpr ⟨r, hrA, Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨?_, hpN⟩, ?_⟩⟩
    · rintro rfl
      exact hp1 hr31
    · rw [he, sigma_prime_sq hpP]
      exact hrd
  have hcard : K'.card ≤ 13 := by
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_insert_le q (Afs ∪ Afs.biUnion fd)
    have c3 := Finset.card_union_le Afs (Afs.biUnion fd)
    have c4 := Finset.card_biUnion_le (s := Afs) (t := fd)
    have c5 := Finset.sum_le_sum hfd
    rw [Finset.sum_const, smul_eq_mul] at c5
    omega
  have hK'b : ∏ p ∈ K', abundancy (p ^ N.factorization p) ≤ (79 / 78) ^ 13 :=
    hK'prod.trans (pow_le_pow_right₀ (by norm_num) hcard)
  -- the final inequality
  rw [hKprod, hab3] at hab
  have hX0 : 0 ≤ ∏ p ∈ K', abundancy (p ^ N.factorization p) :=
    Finset.prod_nonneg fun _ _ => abundancy_nonneg _
  have hY := mul_le_mul hab11 hK'b hX0 (by norm_num)
  have hfin : (2 : ℚ) ≤ 401 / 395 * (121 / 81 * (11 / 10 * (79 / 78) ^ 13)) := by
    rw [← hab]
    exact mul_le_mul hPure (mul_le_mul_of_nonneg_left hY (by norm_num))
      (mul_nonneg (by norm_num) (mul_nonneg (abundancy_nonneg _) hX0)) (by norm_num)
  norm_num at hfin

end TwoExceptionFourEmpty

/-- Let `N` be an odd perfect number with special prime `q` in which every prime factor other
than `q`, `r₁` and `r₂` has exponent exactly 2 (a restricted family with two exceptional
exponents). Then the exponent of 3 in `N` is not 4. This concerns only this restricted family,
not odd perfect numbers in general. Whether this statement is new was not verified against the
literature. -/
theorem two_exceptions_three_ne_four {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 4 := fun h34 =>
  TwoExceptionFourEmpty.false_of_ctx (TwoExceptionFourChains.Ctx.of h hq hodd h34 hsq)

end OddPerfect

#print axioms OddPerfect.TwoExceptionFourEmpty.prod_ratio_le
#print axioms OddPerfect.TwoExceptionFourEmpty.false_of_ctx
#print axioms OddPerfect.two_exceptions_three_ne_four
