import OddPerfect.Pratt
import OddPerfect.SpecialPrime
import OddPerfect.CommonFamily

/-!
# The mixed index family 3, 5, 7 with special prime 5: the tree checker

Setting: `N` is an odd perfect number with `v_3(N) = 2` and `v_5(N) = 1` (so `5` is the special
prime), and every prime `p ≠ 5` dividing `N` has an index `m_p = v_p(N) + 1` divisible by `3`,
`5` or `7`. This module holds a Boolean checker for exclusion trees (`MixedIndex.chk`) and its
soundness theorem (`MixedIndex.chk_sound`). The tree data and the final theorem are in
`OddPerfect.MixedIndexData` and `OddPerfect.MixedIndex`.

A state records a list `K` of primes known to divide `N` (none is `3` or `5`), a list `I` of
pairs `(p, k)` with `k ∣ m_p`, and the ordinary senders `a3`, `a5` of a factor `3` or `5`
(`0` when there is none yet). Tree rules:

* `node p c3 c5 c7` at `p ∈ K`: the index of `p` is divisible by `3`, `5` or `7`; the branch
  `ck` handles `k ∣ m_p`;
* `force p k rs next`: with `k ∣ m_p`, `F = 1 + p + ⋯ + p ^ (k - 1)` divides `σ(p ^ v_p(N))`,
  hence `2N`; every listed odd prime `r ∣ F` divides `N`;
* `shut p k`: with `k ∣ m_p`, either `7 ∣ F` (then `3 * 5 * 7 ∣ N`, impossible), or `3 ∣ F`
  while another ordinary sender of `3` is known (with `σ(5) = 6` this sends three factors `3`
  into `v_3(N) = 2`), or `5 ∣ F` while another ordinary sender of `5` is known (two factors `5`
  into `v_5(N) = 1`);
* `abund l`: the divisor `3 ^ 2 * 5 * ∏ p ^ e` over `l` of `N` is abundant, where each `p ∈ K`
  and `e ≤ 2` (every ordinary index is at least `3`) or `e + 1 ≤ k` for a recorded `(p, k)`.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace MixedIndex

open CommonFam (geomS geomS_eq pPow pSig not_perfect_of_pSig)

/-- An exclusion tree; see the module documentation for the meaning of each rule. -/
inductive Tr where
  | abund (l : List (ℕ × ℕ))
  | node (p : ℕ) (c3 c5 c7 : Tr)
  | force (p k : ℕ) (rs : List ℕ) (next : Tr)
  | shut (p k : ℕ)

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

/-- No repeated entries. -/
def nd : List ℕ → Bool
  | [] => true
  | a :: l => !l.contains a && nd l

/-- An entry `(p, e)` of an abundant divisor: `p ∈ K`, and `e ≤ 2` or `e + 1 ≤ k` for a
recorded `(p, k)`. -/
def entOK (K : List ℕ) (I : List (ℕ × ℕ)) (x : ℕ × ℕ) : Bool :=
  K.contains x.1 && (decide (x.2 ≤ 2) || I.any fun y => y.1 == x.1 && decide (x.2 + 1 ≤ y.2))

/-- The abundant divisor `3 ^ 2 * 5 * ∏ p ^ e` over `l`. -/
def abOK (K : List ℕ) (I : List (ℕ × ℕ)) (l : List (ℕ × ℕ)) : Bool :=
  l.all (entOK K I) && nd (l.map Prod.fst) &&
    decide (2 * pPow ((3, 2) :: (5, 1) :: l) < pSig ((3, 2) :: (5, 1) :: l))

/-- The checker. `P` is a list of certified primes. -/
def chk (P : List ℕ) : List ℕ → List (ℕ × ℕ) → ℕ → ℕ → Tr → Bool
  | K, I, _, _, .abund l => abOK K I l
  | K, I, a3, a5, .node p c3 c5 c7 =>
      K.contains p && isAt p 3 c3 && isAt p 5 c5 && isAt p 7 c7 &&
        chk P K I a3 a5 c3 && chk P K I a3 a5 c5 && chk P K I a3 a5 c7
  | K, I, a3, a5, .force p k rs next =>
      (geomS p (k - 1) % 3 != 0 || a3 == 0) && (geomS p (k - 1) % 5 != 0 || a5 == 0) &&
        rs.all (fun r => P.contains r && r != 2 && r != 3 && r != 5 &&
          geomS p (k - 1) % r == 0) && !isHd next &&
        chk P (rs ++ K) ((p, k) :: I) (if geomS p (k - 1) % 3 == 0 then p else a3)
          (if geomS p (k - 1) % 5 == 0 then p else a5) next
  | _, _, a3, a5, .shut p k =>
      geomS p (k - 1) % 7 == 0 || (geomS p (k - 1) % 3 == 0 && a3 != 0 && a3 != p) ||
        (geomS p (k - 1) % 5 == 0 && a5 != 0 && a5 != p)

/-! ## Arithmetic facts -/

/-- An accepted `nd` test gives a list without repeated entries. -/
theorem nd_nodup : ∀ {l : List ℕ}, nd l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nd, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nd_nodup h.2⟩
    have hc := List.contains_iff_mem.mpr hm
    rw [h.1] at hc
    exact Bool.false_ne_true hc

/-- A tree that is a branch rule for some `p` and `k` is a branch rule. -/
theorem isHd_of_isAt {p k : ℕ} : ∀ {t : Tr}, isAt p k t = true → isHd t = true
  | .force _ _ _ _, _ => rfl
  | .shut _ _, _ => rfl
  | .abund _, h => by simp [isAt] at h
  | .node _ _ _ _, h => by simp [isAt] at h

/-- `p ^ e ∣ N` when `e ≤ v_p(N)`. -/
theorem pow_dvd_of_le {N p e : ℕ} (h : e ≤ N.factorization p) : p ^ e ∣ N :=
  (Nat.pow_dvd_pow p h).trans (Nat.ordProj_dvd N p)

/-- Capacity: primes of `N` each sending a factor `ℓ` number at most `v_ℓ(N)`. -/
theorem card_le_of_senders {N ℓ : ℕ} (hN : N.Perfect) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (hd : ∀ q ∈ S, ℓ ∣ σ 1 (q ^ N.factorization q)) : S.card ≤ N.factorization ℓ := by
  have hbal := OPNStarter.valuation_balance hN ℓ
  have h2 : Nat.factorization 2 ℓ = 0 := by
    rw [Nat.prime_two.factorization, Finsupp.single_apply, if_neg (Ne.symm hℓ2)]
  have hsub := Finset.sum_le_sum_of_subset (f := fun p => (σ 1 (p ^ N.factorization p)).factorization ℓ) hS
  have hone : ∀ q ∈ S, 1 ≤ (σ 1 (q ^ N.factorization q)).factorization ℓ := by
    intro q hq
    have hq' := Nat.prime_of_mem_primeFactors (hS hq)
    exact (hℓ.dvd_iff_one_le_factorization (sigma_pos 1 _ (pow_pos hq'.pos _).ne').ne').mp (hd q hq)
  have hc : S.card ≤ ∑ q ∈ S, (σ 1 (q ^ N.factorization q)).factorization ℓ := by
    simpa using Finset.card_nsmul_le_sum S _ 1 hone
  omega

/-! ## Soundness -/

/-- The invariant of a state for a fixed `N`. -/
structure Inv (N : ℕ) (K : List ℕ) (I : List (ℕ × ℕ)) (a3 a5 : ℕ) : Prop where
  hK : ∀ r ∈ K, r.Prime ∧ r ∣ N ∧ r ≠ 3 ∧ r ≠ 5
  hI : ∀ y ∈ I, y.2 ∣ N.factorization y.1 + 1
  h3 : a3 = 0 ∨ (a3.Prime ∧ a3 ∣ N ∧ a3 ≠ 5 ∧ 3 ∣ σ 1 (a3 ^ N.factorization a3))
  h5 : a5 = 0 ∨ (a5.Prime ∧ a5 ∣ N ∧ a5 ≠ 5 ∧ 5 ∣ σ 1 (a5 ^ N.factorization a5))

section

variable {N : ℕ} (h : OddPerfect N) (h3N : N.factorization 3 = 2) (h5N : N.factorization 5 = 1)
  (hexp : ∀ p ∈ N.primeFactors, p ≠ 5 →
    3 ∣ N.factorization p + 1 ∨ 5 ∣ N.factorization p + 1 ∨ 7 ∣ N.factorization p + 1)
  {P : List ℕ} (hP : ∀ t ∈ P, t.Prime)
include h h3N h5N hexp hP

/-- Soundness of the checker: an accepted tree for a valid state is impossible. -/
theorem chk_sound : ∀ (t : Tr) (K : List ℕ) (I : List (ℕ × ℕ)) (a3 a5 : ℕ), Inv N K I a3 a5 →
    (∀ p k, isAt p k t = true → p ∈ K ∧ k ∣ N.factorization p + 1) →
    chk P K I a3 a5 t = true → False := by
  have hN0 := h.ne_zero
  have h3d : 3 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  have h5d : 5 ∣ N := Nat.dvd_of_factorization_pos (by omega)
  -- the component sum at a branched prime
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
    simp only [chk, abOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
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
    refine not_perfect_of_pSig h.2 ((3, 2) :: (5, 1) :: l) ?_ ?_ ?_ hlt
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact Nat.prime_three
      · exact Nat.prime_five
      · exact (hinv.hK _ (hent' e he).1).1
    · have hl := nd_nodup hnd
      have h3l : 3 ∉ l.map Prod.fst := by
        simp only [List.mem_map, not_exists, not_and]
        intro x hx hx3
        exact (hinv.hK _ (hent' x hx).1).2.2.1 hx3
      have h5l : 5 ∉ l.map Prod.fst := by
        simp only [List.mem_map, not_exists, not_and]
        intro x hx hx5
        exact (hinv.hK _ (hent' x hx).1).2.2.2 hx5
      simp only [List.map_cons, List.nodup_cons, List.mem_cons]
      exact ⟨by simpa using h3l, h5l, hl⟩
    · intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact pow_dvd_of_le (by simp [h3N])
      · exact pow_dvd_of_le (by simp [h5N])
      · exact (hent' e he).2
  | node p c3 c5 c7 ih3 ih5 ih7 =>
    intro K I a3 a5 hinv _ hc
    simp only [chk, Bool.and_eq_true, List.contains_iff_mem] at hc
    obtain ⟨⟨⟨⟨⟨⟨hpK, hc3⟩, hc5⟩, hc7⟩, hk3⟩, hk5⟩, hk7⟩ := hc
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
    · exact ih3 K I a3 a5 hinv (hhead c3 3 hc3 hk) hk3
    · exact ih5 K I a3 a5 hinv (hhead c5 5 hc5 hk) hk5
    · exact ih7 K I a3 a5 hinv (hhead c7 7 hc7 hk) hk7
  | force p k rs next ih =>
    intro K I a3 a5 hinv hh hc
    obtain ⟨hpK, hk⟩ := hh p k (by simp [isAt])
    obtain ⟨hp, hpN, _, hp5⟩ := hinv.hK p hpK
    have hFd := hF p k hp hk
    simp only [chk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      List.all_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hc
    obtain ⟨⟨⟨⟨_, _⟩, hrs⟩, hhd⟩, hnext⟩ := hc
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
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    rcases hc with (h7 | ⟨⟨h3, ha0⟩, hap⟩) | ⟨⟨h5, ha0⟩, hap⟩
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
          · rw [h5N, sigma_one_apply_prime_pow Nat.prime_five]
            norm_num [Finset.sum_range_succ])
      rw [Finset.card_eq_three.mpr ⟨a3, p, 5, hap, ha5, hp5, rfl⟩, h3N] at hcard
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
      rw [Finset.card_pair hap, h5N] at hcard
      omega

end

end MixedIndex

end OddPerfect

#print axioms OddPerfect.MixedIndex.nd_nodup
#print axioms OddPerfect.MixedIndex.isHd_of_isAt
#print axioms OddPerfect.MixedIndex.pow_dvd_of_le
#print axioms OddPerfect.MixedIndex.card_le_of_senders
#print axioms OddPerfect.MixedIndex.chk_sound
