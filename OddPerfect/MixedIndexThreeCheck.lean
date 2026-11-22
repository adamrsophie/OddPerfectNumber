import OddPerfect.MixedIndexTwoCheck

/-!
# The mixed index family 3, 5, 7 with special prime 5: a checker with a counting cap at 3

Setting as in `OddPerfect.MixedIndexTwoCheck`: `N` is an odd perfect number in which `5` has odd
exponent, and every prime `p ≠ 5` dividing `N` has an index `m_p = v_p(N) + 1` divisible by `3`,
`5` or `7`. The checker `MixedIndexThree.chk3` differs from `MixedIndexTwo.chk2` in two ways.

* The capacity rule at `3` takes a cap `c3`, used only when `v_3(N) = c3` (`c3 = 0` switches
  it off). The state keeps the list `A3` of the ordinary primes known to send a factor `3`. A
  branch is shut when one more sender would give, together with the special component (which
  always sends a factor `3`, as `σ(5) = 6` divides `σ(5 ^ k)` for odd `k`), more than `c3`
  distinct senders of `3`.
* A tree may end in `cut`: the current state is then one of a list `Acc` of states that are
  excluded separately (each by its own accepted tree). This splits a long kernel check into
  modules.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace MixedIndexThree

open MixedIndex (nd entOK nd_nodup pow_dvd_of_le card_le_of_senders)
open MixedIndexTwo (abOK2 three_dvd_sigma_five)
open CommonFam (geomS geomS_eq pPow pSig not_perfect_of_pSig)

/-- An exclusion tree: the rules of `MixedIndex.Tr` and the rule `cut`. -/
inductive Tr where
  | abund (l : List (ℕ × ℕ))
  | node (p : ℕ) (c3 c5 c7 : Tr)
  | force (p k : ℕ) (rs : List ℕ) (next : Tr)
  | shut (p k : ℕ)
  | cut

/-- `isAt p k t`: the tree `t` is a branch rule for the prime `p` and the index divisor `k`. -/
def isAt (p k : ℕ) : Tr → Bool
  | .force q j _ _ => q == p && j == k
  | .shut q j => q == p && j == k
  | _ => false

/-- `isHd t`: the tree `t` is a branch rule. -/
def isHd : Tr → Bool
  | .force _ _ _ _ => true
  | .shut _ _ => true
  | _ => false

/-- A state: known primes `K`, index divisors `I`, senders of `3` `A3`, sender of `5` `a5`. -/
abbrev St := List ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The checker. `P` is a list of certified primes, `B` the fixed part of abundant divisors,
`c3` the cap at `3` (`0`: off), `c5` the flag for the cap `1` at `5`, `Acc` the list of states
excluded separately. -/
def chk3 (P : List ℕ) (B : List (ℕ × ℕ)) (c3 : ℕ) (c5 : Bool) (Acc : List St) :
    List ℕ → List (ℕ × ℕ) → List ℕ → ℕ → Tr → Bool
  | K, I, _, _, .abund l => abOK2 B K I l
  | K, I, A3, a5, .node p t3 t5 t7 =>
      K.contains p && isAt p 3 t3 && isAt p 5 t5 && isAt p 7 t7 &&
        chk3 P B c3 c5 Acc K I A3 a5 t3 && chk3 P B c3 c5 Acc K I A3 a5 t5 &&
        chk3 P B c3 c5 Acc K I A3 a5 t7
  | K, I, A3, a5, .force p k rs next =>
      rs.all (fun r => P.contains r && r != 2 && r != 3 && r != 5 &&
          geomS p (k - 1) % r == 0) && !isHd next &&
        chk3 P B c3 c5 Acc (rs ++ K) ((p, k) :: I)
          (if geomS p (k - 1) % 3 == 0 then p :: A3 else A3)
          (if geomS p (k - 1) % 5 == 0 then p else a5) next
  | _, _, A3, a5, .shut p k =>
      geomS p (k - 1) % 7 == 0 ||
        (c3 != 0 && geomS p (k - 1) % 3 == 0 && nd (p :: A3) && decide (c3 < A3.length + 2)) ||
        (c5 && geomS p (k - 1) % 5 == 0 && a5 != 0 && a5 != p)
  | K, I, A3, a5, .cut => Acc.contains (K, I, A3, a5)

/-- The invariant of a state for a fixed `N`. -/
structure Inv (N : ℕ) (s : St) : Prop where
  hK : ∀ r ∈ s.1, r.Prime ∧ r ∣ N ∧ r ≠ 3 ∧ r ≠ 5
  hI : ∀ y ∈ s.2.1, y.2 ∣ N.factorization y.1 + 1
  h3 : ∀ q ∈ s.2.2.1, q.Prime ∧ q ∣ N ∧ q ≠ 5 ∧ 3 ∣ σ 1 (q ^ N.factorization q)
  h5 : s.2.2.2 = 0 ∨ (s.2.2.2.Prime ∧ s.2.2.2 ∣ N ∧ s.2.2.2 ≠ 5 ∧
    5 ∣ σ 1 (s.2.2.2 ^ N.factorization s.2.2.2))

/-- A tree that is a branch rule for some `p` and `k` is a branch rule. -/
theorem isHd_of_isAt {p k : ℕ} : ∀ {t : Tr}, isAt p k t = true → isHd t = true
  | .force _ _ _ _, _ => rfl
  | .shut _ _, _ => rfl
  | .abund _, h => by simp [isAt] at h
  | .node _ _ _ _, h => by simp [isAt] at h
  | .cut, h => by simp [isAt] at h

/-- The root invariant with one known prime `r`. -/
theorem inv_root {N r : ℕ} (hr : r.Prime) (hrN : r ∣ N) (hr3 : r ≠ 3) (hr5 : r ≠ 5) :
    Inv N ([r], [], [], 0) := by
  refine ⟨?_, by simp, by simp, Or.inl rfl⟩
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  exact ⟨hr, hrN, hr3, hr5⟩

section

variable {N : ℕ} (h : OddPerfect N) (h5o : Odd (N.factorization 5))
  (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
    3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
  {P : List ℕ} (hP : ∀ t ∈ P, t.Prime) {B : List (ℕ × ℕ)}
  (hB : ∀ x ∈ B, (x.1 = 3 ∨ x.1 = 5) ∧ x.1 ^ x.2 ∣ N) {c3 : ℕ} {c5 : Bool}
  (hc3 : c3 ≠ 0 → N.factorization 3 = c3) (hc5 : c5 = true → N.factorization 5 = 1)
  {Acc : List St} (hAcc : ∀ s ∈ Acc, Inv N s → False)
include h h5o hexp hP hB hc3 hc5 hAcc

/-- Soundness of `chk3`: an accepted tree for a valid state is impossible. -/
theorem chk3_sound : ∀ (t : Tr) (K : List ℕ) (I : List (ℕ × ℕ)) (A3 : List ℕ) (a5 : ℕ),
    Inv N (K, I, A3, a5) →
    (∀ p k, isAt p k t = true → p ∈ K ∧ k ∣ N.factorization p + 1) →
    chk3 P B c3 c5 Acc K I A3 a5 t = true → False := by
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
    intro K I A3 a5 hinv _ hc
    simp only [chk3, abOK2, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
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
    intro K I A3 a5 hinv _ hc
    simp only [chk3, Bool.and_eq_true, List.contains_iff_mem] at hc
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
      | cut => simp [isAt] at hc
    rcases hexp p (Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩) hp5 with hk | hk | hk
    · exact ih3 K I A3 a5 hinv (hhead t3 3 hc3' hk) hk3
    · exact ih5 K I A3 a5 hinv (hhead t5 5 hc5' hk) hk5
    · exact ih7 K I A3 a5 hinv (hhead t7 7 hc7' hk) hk7
  | force p k rs next ih =>
    intro K I A3 a5 hinv hh hc
    obtain ⟨hpK, hk⟩ := hh p k (by simp [isAt])
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hFd := hF p k hp hk
    simp only [chk3, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
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
      · intro q hq
        dsimp only at hq
        split_ifs at hq with h3
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact ⟨hp, hpN, hp5, (Nat.dvd_of_mod_eq_zero h3).trans hFd⟩
          · exact hinv.h3 q hq
        · exact hinv.h3 q hq
      · dsimp only
        split_ifs with h5
        · exact Or.inr ⟨hp, hpN, hp5, (Nat.dvd_of_mod_eq_zero h5).trans hFd⟩
        · exact hinv.h5
    · intro p' k' hat
      have := isHd_of_isAt hat
      simp_all
  | shut p k =>
    intro K I A3 a5 hinv hh hc
    obtain ⟨hpK, hk⟩ := hh p k (by simp [isAt])
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hFd := hF p k hp hk
    have hpF : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, hN0⟩
    simp only [chk3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hc
    rcases hc with (h7 | ⟨⟨⟨hc3t, h3⟩, hnd⟩, hlt⟩) | ⟨⟨⟨hc5t, h5⟩, ha0⟩, hap⟩
    · have h7N : 7 ∣ N := OPNStarter.force_prime h.2 hp rfl (by norm_num) (by norm_num)
        ((Nat.dvd_of_mod_eq_zero h7).trans hFd)
      exact not_seven_dvd_of_three_five h h3d h5d h7N
    · have hl := nd_nodup hnd
      have hmem : ∀ q ∈ p :: A3, q ∈ N.primeFactors ∧ q ≠ 5 ∧
          3 ∣ σ 1 (q ^ N.factorization q) := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hpF, hp5, (Nat.dvd_of_mod_eq_zero h3).trans hFd⟩
        · obtain ⟨hqP, hqN, hq5, hq3⟩ := hinv.h3 q hq
          exact ⟨Nat.mem_primeFactors.mpr ⟨hqP, hqN, hN0⟩, hq5, hq3⟩
      have h5n : 5 ∉ (p :: A3).toFinset := by
        intro h5m
        exact (hmem 5 (List.mem_toFinset.mp h5m)).2.1 rfl
      have hcard := card_le_of_senders h.2 Nat.prime_three (by norm_num)
        (insert 5 (p :: A3).toFinset)
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_five, h5d, hN0⟩
          · exact (hmem x (List.mem_toFinset.mp hx)).1)
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact h35
          · exact (hmem x (List.mem_toFinset.mp hx)).2.2)
      rw [Finset.card_insert_of_notMem h5n, List.toFinset_card_of_nodup hl, hc3 hc3t] at hcard
      simp only [List.length_cons] at hcard
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
  | cut =>
    intro K I A3 a5 hinv _ hc
    simp only [chk3, List.contains_iff_mem] at hc
    exact hAcc _ hc hinv

end

end MixedIndexThree

end OddPerfect

#print axioms OddPerfect.MixedIndexThree.isHd_of_isAt
#print axioms OddPerfect.MixedIndexThree.inv_root
#print axioms OddPerfect.MixedIndexThree.chk3_sound
