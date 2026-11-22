import OddPerfect.RestrainedSix
import OddPerfect.RestrainedSevenData2
import OddPerfect.Phi3
import OddPerfect.SpecialPrime
import OddPerfect.ForcingClosed

/-!
# Restrained odd perfect numbers: no small prime factor other than 3

Setting of `restrained_exception_eq_three`: `N` is an odd perfect number with special prime
`q`, `r ≠ q` is a further prime, and every prime factor other than `q` and `r` has exponent
exactly 2. Then `r = 3`, `q ≡ 1 (mod 12)`, `5 ∤ N` and `7 ∤ N`.

This file proves `restrained_not_dvd_of_lt`: no prime `5 ≤ p < B` divides `N`, where `B` is the
bound of the generated rows. Each prime below the bound is excluded by an exclusion tree
(`OddPerfect.RestrainedSevenCheck`), checked by the kernel in the modules
`RestrainedSevenData*`; this file proves the checker sound (`chk_sound`, `rowsOK_sound`).

No novelty is claimed: this family is treated in depth by Ochem and Zelinsky (arXiv 2607.19746,
2026), who prove that the exponent of 3 is at least 23,000,000,000; that bound is not proved here,
and whether their methods already give this statement is not checked here.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace RestrainedSeven

/-- The family facts used by the checker. -/
structure Fam (N q : ℕ) : Prop where
  perf : OddPerfect N
  prime : q.Prime
  odd : Odd (N.factorization q)
  mod12 : q % 12 = 1
  sq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → N.factorization p = 2

/-- An odd divisor of `2N` divides `N`. -/
theorem dvd_of_dvd_two_mul {N t : ℕ} (ht : t % 2 = 1) (h : t ∣ 2 * N) : t ∣ N :=
  (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ht)).dvd_of_dvd_mul_left h

/-- The step at a prime `t ∣ N`, `t ≠ 3`: either `t = q`, and the branch `qb` closes the source
`t + 1`; or the exponent of `t` is 2, and the branch `ob` closes the source `t * t + t + 1`. -/
theorem at_sound {N q : ℕ} (F : Fam N q) {M : ℕ} {t qv : ℕ} {qb ob : Br} (htp : t.Prime)
    (htN : t ∣ N) (ht3 : t ≠ 3) (hqv : qv = 0 ∨ qv = q)
    (hqb : t = q → chk M t (t + 1) qb = true) (hob : chk M qv (t * t + t + 1) ob = true)
    (ihq : ∀ qv src, chk M qv src qb = true → src ∣ 2 * N → (qv = 0 ∨ qv = q) → False)
    (iho : ∀ qv src, chk M qv src ob = true → src ∣ 2 * N → (qv = 0 ∨ qv = q) → False) :
    False := by
  have htmem : t ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨htp, htN, F.perf.ne_zero⟩
  by_cases hq : t = q
  · have hk2 : 1 + 1 ∣ N.factorization t + 1 := by
      obtain ⟨m, hm⟩ := hq ▸ F.odd
      exact ⟨m + 1, by omega⟩
    have hdvd := (ForcingClosed.sigma_prime_pow_dvd_of_dvd htp hk2).trans
      (OPNStarter.component_sigma_dvd F.perf.perfect htp rfl)
    have h1 : σ 1 (t ^ 1) = t + 1 := by
      rw [sigma_one_apply_prime_pow htp]
      simp [Finset.sum_range_succ, add_comm]
    rw [h1] at hdvd
    exact ihq t (t + 1) (hqb hq) hdvd (Or.inr hq)
  · have he := F.sq t htmem hq ht3
    have hdvd := OPNStarter.component_sigma_dvd F.perf.perfect htp he
    rw [sigma_prime_sq htp, show phi3 t = t * t + t + 1 by unfold phi3; ring] at hdvd
    exact iho qv (t * t + t + 1) hob hdvd hqv

/-- Soundness of `chk`: an accepted branch for a source dividing `2N` is a contradiction, when
no prime with its bit set in `M` divides `N`. -/
theorem chk_sound {N q : ℕ} (F : Fam N q) {M : ℕ}
    (hM : ∀ t, M.testBit t = true → t.Prime → ¬ t ∣ N) :
    ∀ (b : Br) (qv src : ℕ), chk M qv src b = true → src ∣ 2 * N → (qv = 0 ∨ qv = q) → False
  | .skip, _, _, h, _, _ => by simp [chk] at h
  | .kill t, _, src, h, hs, _ => by
    simp only [chk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hts, htM⟩, hpr⟩ := h
    have ht2 : t % 2 = 1 := by
      have h' := hpr
      simp only [oddPrime, Bool.and_eq_true, beq_iff_eq] at h'
      exact h'.1.2
    exact hM t htM (oddPrime_sound hpr)
      (dvd_of_dvd_two_mul ht2 ((Nat.dvd_of_mod_eq_zero hts).trans hs))
  | .node t c qb ob, qv, src, h, hs, hqv => by
    simp only [chk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨ht2, ht3⟩, htq⟩, hts⟩, hps⟩, hqb⟩, hob⟩ := h
    simp only [beq_iff_eq] at ht2 hts
    simp only [bne_iff_ne, ne_eq] at ht3 htq
    have htN : t ∣ N := dvd_of_dvd_two_mul ht2 ((Nat.dvd_of_mod_eq_zero hts).trans hs)
    refine at_sound F (isPr_sound hps) htN ht3 hqv (fun hq => ?_) hob
      (chk_sound F hM qb) (chk_sound F hM ob)
    have hqv0 : qv = 0 := by
      rcases hqv with h0 | h0
      · exact h0
      · exact absurd (h0.trans hq.symm) (Ne.symm htq)
    rcases Bool.or_eq_true_iff.mp hqb with h1 | h1
    · simp [hqv0, hq, F.mod12] at h1
    · exact h1

/-- Soundness of `rowsOK`: if no prime with its bit set in `M` divides `N`, the same holds
for `M'`. -/
theorem rowsOK_sound {N q : ℕ} (F : Fam N q) :
    ∀ (M : ℕ) (rows : List (ℕ × Br × Br)) (M' : ℕ), rowsOK M rows M' = true →
      (∀ t, M.testBit t = true → t.Prime → ¬ t ∣ N) →
      ∀ t, M'.testBit t = true → t.Prime → ¬ t ∣ N
  | M, [], M', h, hM => by
    simp only [rowsOK, beq_iff_eq] at h
    exact h ▸ hM
  | M, (p, qb, ob) :: rest, M', h, hM => by
    simp only [rowsOK, Bool.and_eq_true] at h
    have h0 : p.Prime → ¬ p ∣ N := fun hp hd => by
      have hr := h.1
      simp only [chkRoot, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hr
      obtain ⟨⟨⟨-, hp3⟩, hqb⟩, hob⟩ := hr
      refine at_sound F hp hd hp3 (Or.inl rfl) (fun hq => ?_) hob
        (chk_sound F hM qb) (chk_sound F hM ob)
      rcases Bool.or_eq_true_iff.mp hqb with h1 | h1
      · simp [hq, F.mod12] at h1
      · exact h1
    refine rowsOK_sound F (M ||| 1 <<< p) rest M' h.2 fun t ht => ?_
    rcases testBit_or_shift ht with ht | rfl
    · exact hM t ht
    · exact h0

/-- The family facts from the hypotheses of `restrained_exception_eq_three`, with `5 ∤ N` and
`7 ∤ N`. -/
theorem fam_of {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) :
    Fam N q ∧ ¬ 5 ∣ N ∧ ¬ 7 ∣ N := by
  obtain ⟨rfl, -, -, hq3, h5, h7⟩ := restrained_exception_eq_three h hq hodd hr hrq hsq
  have hq4 := (special_mod_four h hq hodd).1
  exact ⟨⟨h, hq, hodd, by omega, hsq⟩, h5, h7⟩

/-- The starting mask: its set bits are `5` and `7`. -/
theorem testBit_start {t : ℕ} (h : (160 : ℕ).testBit t = true) : t = 5 ∨ t = 7 := by
  rcases Nat.lt_or_ge t 8 with ht | ht
  · interval_cases t <;> simp_all <;> revert h <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : (160 : ℕ) < 2 ^ 8)
      (Nat.pow_le_pow_right (by norm_num) ht))] at h
    exact absurd h (by simp)

end RestrainedSeven

open RestrainedSeven

/-- **Restrained odd perfect numbers have no prime factor `5 ≤ p < 132257`.** With the
hypotheses of `restrained_exception_eq_three` (special prime `q`, a further prime `r ≠ q`, every
other prime factor with exponent exactly 2), no prime `5 ≤ p < 132257` divides `N`; together
with `r = 3` this says that the smallest prime factor of `N` other than 3 is at least 132257.
Each prime is excluded by a kernel checked exclusion tree. No novelty is claimed: Ochem and
Zelinsky (arXiv 2607.19746, 2026) prove that the exponent of 3 in such `N` is at least
23,000,000,000, which is not proved here. -/
theorem restrained_not_dvd_of_lt {N q r p : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (hr : r.Prime) (hrq : r ≠ q)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2)
    (hp : p.Prime) (h5 : 5 ≤ p) (hlt : p < 132257) : ¬ p ∣ N := by
  obtain ⟨F, hn5, hn7⟩ := fam_of h hq hodd hr hrq hsq
  have h0 : ∀ t, (160 : ℕ).testBit t = true → t.Prime → ¬ t ∣ N := fun t ht _ => by
    rcases testBit_start ht with rfl | rfl
    · exact hn5
    · exact hn7
  have h1 := rowsOK_sound F 160 rows1 mask1 rows1_ok h0
  have h2 := rowsOK_sound F mask1 rows2 mask2 rows2_ok h1
  exact h2 p (cover_sound cover_ok hp h5 (by omega)) hp

end OddPerfect

#print axioms OddPerfect.RestrainedSeven.dvd_of_dvd_two_mul
#print axioms OddPerfect.RestrainedSeven.at_sound
#print axioms OddPerfect.RestrainedSeven.chk_sound
#print axioms OddPerfect.RestrainedSeven.rowsOK_sound
#print axioms OddPerfect.RestrainedSeven.fam_of
#print axioms OddPerfect.RestrainedSeven.testBit_start
#print axioms OddPerfect.restrained_not_dvd_of_lt
