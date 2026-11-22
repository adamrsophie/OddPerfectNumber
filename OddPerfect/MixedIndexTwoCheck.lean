import OddPerfect.MixedIndexCheck

/-!
# The mixed index family 3, 5, 7 with special prime 5: a checker with a configurable root

Setting: `N` is an odd perfect number in which `5` has odd exponent (so `5` is the special
prime), and every prime `p ≠ 5` dividing `N` has an index `m_p = v_p(N) + 1` divisible by `3`,
`5` or `7`. This module generalizes `MixedIndex.chk` (same trees `MixedIndex.Tr`) to a root
given by:

* a list `B` of pairs `(t, e)` with `t ∈ {3, 5}` and `t ^ e ∣ N`, the fixed part of every
  abundant divisor;
* a flag `c3`: the capacity rule at `3` is used, which needs `v_3(N) = 2`;
* a flag `c5`: the capacity rule at `5` is used, which needs `v_5(N) = 1`.

The capacity rule at `3` uses that `σ(5) = 6` divides `σ(5 ^ k)` for odd `k`, so the special
component always sends a factor `3`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace MixedIndexTwo

open MixedIndex (Tr isAt isHd nd entOK nd_nodup isHd_of_isAt pow_dvd_of_le card_le_of_senders Inv)
open CommonFam (geomS geomS_eq pPow pSig not_perfect_of_pSig)
open MixedIndex.Tr

/-- The abundant divisor `∏ t ^ e` over `B ++ l`. -/
def abOK2 (B : List (ℕ × ℕ)) (K : List ℕ) (I : List (ℕ × ℕ)) (l : List (ℕ × ℕ)) : Bool :=
  l.all (entOK K I) && nd ((B ++ l).map Prod.fst) && decide (2 * pPow (B ++ l) < pSig (B ++ l))

/-- The checker with root data `B`, `c3`, `c5`. `P` is a list of certified primes. -/
def chk2 (P : List ℕ) (B : List (ℕ × ℕ)) (c3 c5 : Bool) :
    List ℕ → List (ℕ × ℕ) → ℕ → ℕ → Tr → Bool
  | K, I, _, _, .abund l => abOK2 B K I l
  | K, I, a3, a5, .node p t3 t5 t7 =>
      K.contains p && isAt p 3 t3 && isAt p 5 t5 && isAt p 7 t7 &&
        chk2 P B c3 c5 K I a3 a5 t3 && chk2 P B c3 c5 K I a3 a5 t5 && chk2 P B c3 c5 K I a3 a5 t7
  | K, I, a3, a5, .force p k rs next =>
      rs.all (fun r => P.contains r && r != 2 && r != 3 && r != 5 &&
          geomS p (k - 1) % r == 0) && !isHd next &&
        chk2 P B c3 c5 (rs ++ K) ((p, k) :: I) (if geomS p (k - 1) % 3 == 0 then p else a3)
          (if geomS p (k - 1) % 5 == 0 then p else a5) next
  | _, _, a3, a5, .shut p k =>
      geomS p (k - 1) % 7 == 0 || (c3 && geomS p (k - 1) % 3 == 0 && a3 != 0 && a3 != p) ||
        (c5 && geomS p (k - 1) % 5 == 0 && a5 != 0 && a5 != p)

/-- For odd `k`, `3 ∣ σ(5 ^ k)`, because `σ(5) = 6` divides it. -/
theorem three_dvd_sigma_five {k : ℕ} (hk : Odd k) : 3 ∣ σ 1 (5 ^ k) := by
  have h6 : σ 1 (5 ^ 1) ∣ σ 1 (5 ^ k) := OPNExample.sigma_prime_pow_dvd Nat.prime_five (by
    obtain ⟨j, rfl⟩ := hk
    exact ⟨j + 1, by ring⟩)
  refine Dvd.dvd.trans ?_ h6
  rw [sigma_one_apply_prime_pow Nat.prime_five]
  norm_num [Finset.sum_range_succ]

section

variable {N : ℕ} (h : OddPerfect N) (h5o : Odd (N.factorization 5))
  (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
    3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
  {P : List ℕ} (hP : ∀ t ∈ P, t.Prime) {B : List (ℕ × ℕ)}
  (hB : ∀ x ∈ B, (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N) {c3 c5 : Bool}
  (hc3 : c3 = true → N.factorization 3 = 2) (hc5 : c5 = true → N.factorization 5 = 1)
include h h5o hexp hP hB hc3 hc5

/-- Soundness of `chk2`: an accepted tree for a valid state is impossible. -/
theorem chk2_sound : ∀ (t : Tr) (K : List ℕ) (I : List (ℕ × ℕ)) (a3 a5 : ℕ), Inv N K I a3 a5 →
    (∀ p k, isAt p k t = true → p ∈ K ∧ k ∣ N.factorization p + 1) →
    chk2 P B c3 c5 K I a3 a5 t = true → False := by
  have hN0 := h.ne_zero
  have h35 : 3 ∣ σ 1 (5 ^ N.factorization 5) := three_dvd_sigma_five h5o
  have h3d : 3 ∣ N :=
    OPNStarter.force_prime h.2 Nat.prime_five rfl Nat.prime_three (by norm_num) h35
  have h5d : 5 ∣ N := Nat.dvd_of_factorization_pos (by obtain ⟨j, hj⟩ := h5o; omega)
  have hF : ∀ p k, p.Prime → k ∣ N.factorization p + 1 →
      geomS p (k - 1) ∣ σ 1 (p ^ N.factorization p) := by
    intro p k hp hk
    have hk1 : 1 ≤ k := Nat.pos_of_dvd_of_pos hk (by omega)
    rw [geomS_eq, ← sigma_one_apply_prime_pow hp]
    exact OPNExample.sigma_prime_pow_dvd hp (by rwa [Nat.sub_add_cancel hk1])
  intro t
  induction t with
  | abund l =>
    intro K I a3 a5 hinv _ hc
    simp only [chk2, abOK2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨⟨hent, hnd⟩, hlt⟩ := hc
    have hent' : ∀ x ∈ l, x.1 ∈ K ∧ x.1 ^ x.2 ∣ N := by
      intro x hx
      have hx' := hent x hx
      simp only [entOK, Bool.and_eq_true, List.contains_iff_mem, Bool.or_eq_true,
        decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hx'
      obtain ⟨hxK, hb⟩ := hx'
      obtain ⟨hxp, hxN, _, hx5⟩ := hinv.hK _ hxK
      refine ⟨hxK, pow_dvd_of_le ?_⟩
      rcases hb with hb | ⟨y, hyI, hy1, hy2⟩
      · have hm := hexp x.1 (Nat.mem_primeFactors.mpr ⟨hxp, hxN, hN0⟩) hx5
        have : 3 ≤ N.factorization x.1 + 1 := by
          rcases hm with hm | hm | hm <;> have := Nat.le_of_dvd (by omega) hm <;> omega
        omega
      · have := Nat.le_of_dvd (by omega) (hinv.hI y hyI)
        rw [hy1] at this
        omega
    refine not_perfect_of_pSig h.2 (B ++ l) ?_ (nd_nodup hnd) ?_ hlt
    · intro e he
      rcases List.mem_append.mp he with he | he
      · rcases (hB e he).1 with h' | h'
        · rw [h']; exact Nat.prime_three
        · rw [h']; exact Nat.prime_five
      · exact (hinv.hK _ (hent' e he).1).1
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact (hB e he).2
      · exact (hent' e he).2
  | node p t3 t5 t7 ih3 ih5 ih7 =>
    intro K I a3 a5 hinv _ hc
    simp only [chk2, Bool.and_eq_true, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨⟨hpK, hc3'⟩, hc5'⟩, hc7'⟩, hk3⟩, hk5⟩, hk7⟩ := hc
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hhead : ∀ (c : Tr) (k : ℕ), isAt p k c = true → k ∣ N.factorization p + 1 →
        ∀ p' k', isAt p' k' c = true → p' ∈ K ∧ k' ∣ N.factorization p' + 1 := by
      intro c k hc hk p' k' hc'
      cases c with
      | force q j _ _ =>
        simp only [isAt, Bool.and_eq_true, beq_iff_eq] at hc hc'
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨rfl, rfl⟩ := hc'
        exact ⟨hpK, hk⟩
      | shut q j =>
        simp only [isAt, Bool.and_eq_true, beq_iff_eq] at hc hc'
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨rfl, rfl⟩ := hc'
        exact ⟨hpK, hk⟩
      | abund _ => simp [isAt] at hc
      | node _ _ _ _ => simp [isAt] at hc
    rcases hexp p (Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩) hp5 with hk | hk | hk
    · exact ih3 K I a3 a5 hinv (hhead t3 3 hc3' hk) hk3
    · exact ih5 K I a3 a5 hinv (hhead t5 5 hc5' hk) hk5
    · exact ih7 K I a3 a5 hinv (hhead t7 7 hc7' hk) hk7
  | force p k rs next ih =>
    intro K I a3 a5 hinv hh hc
    obtain ⟨hpK, hk⟩ := hh p k (by simp [isAt])
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hFd := hF p k hp hk
    simp only [chk2, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.all_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hc
    obtain ⟨⟨hrs, hhd⟩, hnext⟩ := hc
    refine ih _ _ _ _ ?_ ?_ hnext
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨⟨⟨⟨hrP, hr2⟩, hr3⟩, hr5⟩, hrF⟩ := hrs r hr
          have hrp := hP r hrP
          refine ⟨hrp, ?_, hr3, hr5⟩
          exact OPNStarter.force_prime h.2 hp rfl hrp hr2
            ((Nat.dvd_of_mod_eq_zero hrF).trans hFd)
        · exact hinv.hK r hr
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hk
        · exact hinv.hI y hy
      · split_ifs with h3
        · exact Or.inr ⟨hp, hpN, hp5, (Nat.dvd_of_mod_eq_zero h3).trans hFd⟩
        · exact hinv.h3
      · split_ifs with h5
        · exact Or.inr ⟨hp, hpN, hp5, (Nat.dvd_of_mod_eq_zero h5).trans hFd⟩
        · exact hinv.h5
    · intro p' k' hat
      have := isHd_of_isAt hat
      simp_all
  | shut p k =>
    intro K I a3 a5 hinv hh hc
    obtain ⟨hpK, hk⟩ := hh p k (by simp [isAt])
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hFd := hF p k hp hk
    have hpF : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩
    simp only [chk2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    rcases hc with (h7 | ⟨⟨⟨hc3t, h3⟩, ha0⟩, hap⟩) | ⟨⟨⟨hc5t, h5⟩, ha0⟩, hap⟩
    · have h7N : 7 ∣ N := OPNStarter.force_prime h.2 hp rfl (by norm_num) (by norm_num)
        ((Nat.dvd_of_mod_eq_zero h7).trans hFd)
      exact not_seven_dvd_of_three_five h h3d h5d h7N
    · rcases hinv.h3 with h0 | ⟨haP, haN, ha5, ha3⟩
      · exact ha0 h0
      have h5F : 5 ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5d, hN0⟩
      have hcard := card_le_of_senders h.2 Nat.prime_three (by norm_num) {a3, p, 5}
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact Nat.mem_primeFactors.mpr ⟨haP, haN, hN0⟩
          · exact hpF
          · exact h5F)
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl
          · exact ha3
          · exact (Nat.dvd_of_mod_eq_zero h3).trans hFd
          · exact h35)
      rw [Finset.card_eq_three.mpr ⟨a3, p, 5, hap, ha5, hp5, rfl⟩, hc3 hc3t] at hcard
      omega
    · rcases hinv.h5 with h0 | ⟨haP, haN, ha5, ha5d⟩
      · exact ha0 h0
      have hcard := card_le_of_senders h.2 Nat.prime_five (by norm_num) {a5, p}
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Nat.mem_primeFactors.mpr ⟨haP, haN, hN0⟩
          · exact hpF)
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact ha5d
          · exact (Nat.dvd_of_mod_eq_zero h5).trans hFd)
      rw [Finset.card_pair hap, hc5 hc5t] at hcard
      omega

end

end MixedIndexTwo

end OddPerfect

#print axioms OddPerfect.MixedIndexTwo.three_dvd_sigma_five
#print axioms OddPerfect.MixedIndexTwo.chk2_sound
