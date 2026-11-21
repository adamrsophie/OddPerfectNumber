import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

/-!
A kernel-checked witness for the square-full-value question on the authors'
companion page for Ochem and Zelinsky, arXiv:2607.19746. Each large prime
below is certified by a Lucas witness and the complete factorization of
its predecessor. The final square-divisibility proof only needs the input
to be prime.
-/

namespace OPNSquarefull

private theorem prime_2 : Nat.Prime 2 := by norm_num

private theorem prime_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_3 : Nat.Prime 3 := by norm_num

private theorem prime_13 : Nat.Prime 13 := by norm_num

private theorem prime_61 : Nat.Prime 61 := by norm_num

private theorem prime_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_9701563 : Nat.Prime 9701563 := by
  apply lucas_primality 9701563 (5 : ZMod 9701563)
  · change (5 : ZMod 9701563) ^ 9701562 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 3 * 13 * 61 * 2039 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_13,
      Nat.prime_dvd_prime_iff_eq hq prime_61,
      Nat.prime_dvd_prime_iff_eq hq prime_2039] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl)
    · change (5 : ZMod 9701563) ^ 4850781 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 9701563) ^ 3233854 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 9701563) ^ 746274 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 9701563) ^ 159042 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 9701563) ^ 4758 ≠ 1
      reduce_mod_char
      decide

private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_19 : Nat.Prime 19 := by norm_num

private theorem prime_43 : Nat.Prime 43 := by norm_num

private theorem prime_27779 : Nat.Prime 27779 := by
  apply lucas_primality 27779 (2 : ZMod 27779)
  · change (2 : ZMod 27779) ^ 27778 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 17 * 19 * 43 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_17,
      Nat.prime_dvd_prime_iff_eq hq prime_19,
      Nat.prime_dvd_prime_iff_eq hq prime_43] at hd
    rcases hd with (((rfl | rfl) | rfl) | rfl)
    · change (2 : ZMod 27779) ^ 13889 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 27779) ^ 1634 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 27779) ^ 1462 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 27779) ^ 646 ≠ 1
      reduce_mod_char
      decide

private theorem prime_5 : Nat.Prime 5 := by norm_num

private theorem prime_23 : Nat.Prime 23 := by norm_num

private theorem prime_139 : Nat.Prime 139 := by norm_num

private theorem prime_7 : Nat.Prime 7 := by norm_num

private theorem prime_73 : Nat.Prime 73 := by norm_num

private theorem prime_1738423 : Nat.Prime 1738423 := by
  apply lucas_primality 1738423 (5 : ZMod 1738423)
  · change (5 : ZMod 1738423) ^ 1738422 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 3 * 3 * 3 * 3 * 3 * 7 * 7 * 73 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_7,
      Nat.prime_dvd_prime_iff_eq hq prime_73] at hd
    rcases hd with ((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · change (5 : ZMod 1738423) ^ 869211 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 579474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 579474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 579474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 579474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 579474 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 248346 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 248346 ≠ 1
      reduce_mod_char
      decide
    · change (5 : ZMod 1738423) ^ 23814 ≠ 1
      reduce_mod_char
      decide

private theorem prime_966563189 : Nat.Prime 966563189 := by
  apply lucas_primality 966563189 (2 : ZMod 966563189)
  · change (2 : ZMod 966563189) ^ 966563188 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 2 * 139 * 1738423 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_139,
      Nat.prime_dvd_prime_iff_eq hq prime_1738423] at hd
    rcases hd with (((rfl | rfl) | rfl) | rfl)
    · change (2 : ZMod 966563189) ^ 483281594 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 966563189) ^ 483281594 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 966563189) ^ 6953692 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 966563189) ^ 556 ≠ 1
      reduce_mod_char
      decide

private theorem prime_666928600411 : Nat.Prime 666928600411 := by
  apply lucas_primality 666928600411 (13 : ZMod 666928600411)
  · change (13 : ZMod 666928600411) ^ 666928600410 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 3 * 5 * 23 * 966563189 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_5,
      Nat.prime_dvd_prime_iff_eq hq prime_23,
      Nat.prime_dvd_prime_iff_eq hq prime_966563189] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl)
    · change (13 : ZMod 666928600411) ^ 333464300205 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 666928600411) ^ 222309533470 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 666928600411) ^ 133385720082 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 666928600411) ^ 28996895670 ≠ 1
      reduce_mod_char
      decide
    · change (13 : ZMod 666928600411) ^ 690 ≠ 1
      reduce_mod_char
      decide

private theorem prime_12004714807399 : Nat.Prime 12004714807399 := by
  apply lucas_primality 12004714807399 (6 : ZMod 12004714807399)
  · change (6 : ZMod 12004714807399) ^ 12004714807398 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 3 * 3 * 666928600411 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_3,
      Nat.prime_dvd_prime_iff_eq hq prime_666928600411] at hd
    rcases hd with (((rfl | rfl) | rfl) | rfl)
    · change (6 : ZMod 12004714807399) ^ 6002357403699 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 12004714807399) ^ 4001571602466 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 12004714807399) ^ 4001571602466 ≠ 1
      reduce_mod_char
      decide
    · change (6 : ZMod 12004714807399) ^ 18 ≠ 1
      reduce_mod_char
      decide

private theorem prime_192750846182877882539 : Nat.Prime 192750846182877882539 := by
  apply lucas_primality 192750846182877882539 (2 : ZMod 192750846182877882539)
  · change (2 : ZMod 192750846182877882539) ^ 192750846182877882538 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 17 * 17 * 27779 * 12004714807399 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_17,
      Nat.prime_dvd_prime_iff_eq hq prime_27779,
      Nat.prime_dvd_prime_iff_eq hq prime_12004714807399] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl)
    · change (2 : ZMod 192750846182877882539) ^ 96375423091438941269 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 192750846182877882539) ^ 11338285069581051914 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 192750846182877882539) ^ 11338285069581051914 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 192750846182877882539) ^ 6938725158676622 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 192750846182877882539) ^ 16056262 ≠ 1
      reduce_mod_char
      decide

theorem witness_prime : Nat.Prime 47116128896261596331524418282573 := by
  apply lucas_primality 47116128896261596331524418282573 (2 : ZMod 47116128896261596331524418282573)
  · change (2 : ZMod 47116128896261596331524418282573) ^ 47116128896261596331524418282572 = 1
    reduce_mod_char
  · intro q hq hd
    change q ∣ 2 * 2 * 6299 * 9701563 * 192750846182877882539 at hd
    simp only [hq.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hq prime_2,
      Nat.prime_dvd_prime_iff_eq hq prime_6299,
      Nat.prime_dvd_prime_iff_eq hq prime_9701563,
      Nat.prime_dvd_prime_iff_eq hq prime_192750846182877882539] at hd
    rcases hd with ((((rfl | rfl) | rfl) | rfl) | rfl)
    · change (2 : ZMod 47116128896261596331524418282573) ^ 23558064448130798165762209141286 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47116128896261596331524418282573) ^ 23558064448130798165762209141286 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47116128896261596331524418282573) ^ 7479937910185997195034833828 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47116128896261596331524418282573) ^ 4856550320423791128452644 ≠ 1
      reduce_mod_char
      decide
    · change (2 : ZMod 47116128896261596331524418282573) ^ 244440581348 ≠ 1
      reduce_mod_char
      decide

/-- The displayed prime x has square-full x²+x+1. -/
theorem exists_prime_squarefull :
    ∃ x : ℕ, x.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ x^2+x+1 → p^2 ∣ x^2+x+1 := by
  refine ⟨47116128896261596331524418282573, witness_prime, ?_⟩
  let b : ℕ := 7 * 43 * 3416683 * 12353161 * 1401752363863729
  have h : (47116128896261596331524418282573 : ℕ)^2+47116128896261596331524418282573+1
      = 7*b^2 := by decide +kernel
  intro p hp hdiv
  rw [h] at hdiv ⊢
  have hpb : p ∣ b := by
    obtain h7 | hb := hp.dvd_mul.mp hdiv
    · exact dvd_trans h7 (by
        dsimp [b]
        exact ⟨43*3416683*12353161*1401752363863729, by decide +kernel⟩)
    · exact hp.dvd_of_dvd_pow hb
  exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpb 2) 7

#print axioms witness_prime
#print axioms exists_prime_squarefull

end OPNSquarefull
