import OddPerfect.DefectTreeCode
import OddPerfect.DefectRules

/-!
# A certificate checker for factor chain trees with the defect ledger: soundness

This module gives the meaning `Holds` of a state of `OddPerfect.DefectTree` and proves the
soundness theorem `check_sound`: if `check P pc tab c = true`, then no odd perfect number `N`
with special prime `q` satisfies the hypotheses of the parameters `P`, namely
`P.w * ω(N) + supportDefect N q ≤ P.K`, every prime factor of `N` at least `P.u`,
`P.root ∣ N`, and `T ≤ c` for the total excess `T` when `P.cap = some c`.

The checker is a tool: the theorem carries no data, and every certificate is checked by the
kernel. The rule lemmas come from `OddPerfect.DefectRules`; the ledger rule rests on
`defect_lower_bound`.

## Choices

* A fact `(r, k)` of a row is used only through `r ^ k ∣ σ(p ^ v_p(N))` (or `r ^ k ∣ q + 1`),
  which makes `r` a prime factor of `N` and bounds the weight `sigmaWeight N p r` below by `k`.
* For the ledger the special prime may be unknown. The checker asks the bound for the candidate
  `0` and for every forced prime that is 1 modulo 4; the proof uses the candidate `q` when `q`
  is a forced prime and `0` otherwise, so every receiver other than the candidate differs
  from `q`.
* The case split of a branch is complete: the branch prime is either `q`, which is 1 modulo 4
  and leaves no special prime assigned, or an ordinary prime with an even exponent at least 2.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace DefectTree

/-! ### Specifications of the small functions -/

/-- `gs` is the geometric sum. -/
theorem gs_eq (p m : ℕ) : gs p m = ∑ i ∈ Finset.range (m + 1), p ^ i := by
  induction m with
  | zero => simp [gs]
  | succ m ih => rw [gs, ih, Finset.sum_range_succ _ (m + 1)]

/-- For a prime `p`, `σ(p ^ m) = gs p m`. -/
theorem sigma_eq_gs {p m : ℕ} (hp : p.Prime) : σ 1 (p ^ m) = gs p m := by
  rw [sigma_one_apply_prime_pow hp, gs_eq]

private theorem gs_one (p : ℕ) : gs p 1 = p + 1 := by simp [gs]; ring

/-- Soundness of `nodupB`. -/
theorem nodupB_sound : ∀ {l : List ℕ}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    unfold nodupB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodupB_sound h2⟩
    have hc : l.contains a = true := List.contains_iff_mem.mpr hm
    rw [hc] at h1
    exact absurd h1 (by decide)

private theorem find_spec {α : Type} {l : List α} {p : α → Bool} {y : α}
    (h : l.find? p = some y) : y ∈ l ∧ p y = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- `kOf` is bounded by any bound of the second components. -/
theorem kOf_le {fs : List (ℕ × ℕ)} {g : ℕ → ℕ} (h : ∀ y ∈ fs, y.2 ≤ g y.1) (r : ℕ) :
    kOf fs r ≤ g r := by
  unfold kOf
  split
  · rename_i y hy
    obtain ⟨h1, h2⟩ := find_spec hy
    rw [beq_iff_eq] at h2
    rw [← h2]
    exact h y h1
  · exact Nat.zero_le _

/-- Soundness of `isPr`. -/
theorem isPr_sound {pc : PCert} (hpc : Pratt.check pc = true) {r : ℕ} (h : isPr pc r = true) :
    r.Prime := by
  unfold isPr at h
  rw [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | h
  · exact Pratt.trialPrime_sound h.2
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
    exact Pratt.check_sound hpc e he

/-- Soundness of the table: the facts of a row are odd primes with positive exponents whose
powers divide the row, and their primes are distinct. -/
theorem look_sound {pc : PCert} {tab : Tab} (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) (p m : ℕ) :
    ((look tab p m).map Prod.fst).Nodup ∧
      ∀ y ∈ look tab p m, y.1.Prime ∧ y.1 ≠ 2 ∧ 1 ≤ y.2 ∧ y.1 ^ y.2 ∣ gs p m := by
  unfold look
  split
  · rename_i t hf
    obtain ⟨ht1, ht2⟩ := find_spec hf
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at ht2
    obtain ⟨e1, e2⟩ := ht2
    unfold tabOK at ht
    rw [List.all_eq_true] at ht
    have h := ht t ht1
    rw [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hnd, hall⟩ := h
    refine ⟨nodupB_sound hnd, fun y hy => ?_⟩
    have hy' := hall y hy
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at hy'
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy'
    refine ⟨isPr_sound hpc h1, h2, h3, ?_⟩
    rw [← e1, ← e2]
    exact Nat.dvd_of_mod_eq_zero h4
  · simp

/-! ### The meaning of a state -/

/-- The hypotheses carried by the whole tree. -/
structure Ctx (P : Params) (N q : ℕ) : Prop where
  h : OddPerfect N
  hq : q.Prime
  hodd : Odd (N.factorization q)
  h1 : ∀ c, P.cap = some c → (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) ≤ c
  h2 : P.w * N.primeFactors.card + supportDefect N q ≤ P.K
  h3 : ∀ p ∈ N.primeFactors, P.u ≤ p

/-- The meaning of a state: every entry is an ordinary prime factor of `N` with the stated
exponent (exactly, or at least `e ≥ 4`), the entry primes are distinct, and the special prime
is `q` when it is assigned. -/
def Holds (N q : ℕ) (st : St) : Prop :=
  (∀ x ∈ st.os, x.1 ∈ N.primeFactors ∧ x.1 ≠ q ∧
      (x.2.2 = true → N.factorization x.1 = x.2.1) ∧
      (x.2.2 = false → 4 ≤ x.2.1 ∧ x.2.1 ≤ N.factorization x.1)) ∧
    (st.os.map Prod.fst).Nodup ∧ (st.sp ≠ 0 → st.sp = q)

section Sound

variable {P : Params} {pc : PCert} {tab : Tab} {N q : ℕ}

private theorem two_ne (C : Ctx P N q) {p : ℕ} (hp : p ∈ N.primeFactors) : p ≠ 2 := by
  rintro rfl
  have h1 := Nat.dvd_of_mem_primeFactors hp
  have h2 := Nat.odd_iff.mp C.h.1
  omega

private theorem one_le_fac (C : Ctx P N q) {p : ℕ} (hp : p ∈ N.primeFactors) :
    1 ≤ N.factorization p :=
  (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd C.h.ne_zero
    (Nat.dvd_of_mem_primeFactors hp)

private theorem q_mem (C : Ctx P N q) : q ∈ N.primeFactors := by
  have : N.factorization q ≠ 0 := by obtain ⟨k, hk⟩ := C.hodd; omega
  exact Nat.mem_primeFactors.mpr ⟨C.hq, Nat.dvd_of_factorization_pos this, C.h.ne_zero⟩

private theorem le_fac {st : St} (hH : Holds N q st) {x : ℕ × ℕ × Bool} (hx : x ∈ st.os) :
    x.2.1 ≤ N.factorization x.1 := by
  obtain ⟨-, -, he, hi⟩ := hH.1 x hx
  cases hb : x.2.2
  · exact (hi hb).2
  · exact (he hb).ge

private theorem factsE_spec (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {x : ℕ × ℕ × Bool}
    (hx : x ∈ st.os) {y : ℕ × ℕ} (hy : y ∈ factsE tab x) :
    y.1 ∈ N.primeFactors ∧ y.2 ≤ sigmaWeight N x.1 y.1 := by
  unfold factsE at hy
  split_ifs at hy with hex
  · obtain ⟨hxN, -, he, -⟩ := hH.1 x hx
    have hxp := Nat.prime_of_mem_primeFactors hxN
    obtain ⟨hp, h2, hk, hd⟩ := (look_sound hpc ht x.1 x.2.1).2 y hy
    rw [← sigma_eq_gs hxp, ← he hex] at hd
    refine ⟨mem_primeFactors_of_dvd_sigma_component C.h hxN hp h2
      ((dvd_pow_self _ (by omega)).trans hd), le_sigmaWeight_of_pow_dvd hxp hp hd⟩
  · simp at hy

private theorem factsE_nodup (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true)
    (x : ℕ × ℕ × Bool) : ((factsE tab x).map Prod.fst).Nodup := by
  unfold factsE
  split_ifs
  · exact (look_sound hpc ht _ _).1
  · simp

private theorem spFacts_spec (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {y : ℕ × ℕ}
    (hy : y ∈ spFacts tab st) :
    st.sp = q ∧ y.1 ∈ N.primeFactors ∧ y.2 ≤ sigmaWeight N q y.1 := by
  unfold spFacts at hy
  split_ifs at hy with h0
  · simp at hy
  · have hsq := hH.2.2 h0
    rw [hsq] at hy
    obtain ⟨hp, h2, hk, hd⟩ := (look_sound hpc ht q 1).2 y hy
    rw [gs_one] at hd
    exact ⟨hsq, mem_primeFactors_of_dvd_succ_special C.h C.hq C.hodd hp h2
      ((dvd_pow_self _ (by omega)).trans hd),
      le_sigmaWeight_special_of_pow_dvd C.hq C.hodd hp hd⟩

private theorem spFacts_nodup (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true)
    (st : St) : ((spFacts tab st).map Prod.fst).Nodup := by
  unfold spFacts
  split_ifs
  · simp
  · exact (look_sound hpc ht _ _).1

private theorem mem_allFacts_sp {st : St} {y : ℕ × ℕ} (hy : y ∈ spFacts tab st) :
    y.1 ∈ (allFacts tab st).map Prod.fst :=
  List.mem_map.mpr ⟨y, List.mem_append_left _ hy, rfl⟩

private theorem mem_allFacts_e {st : St} {x : ℕ × ℕ × Bool} (hx : x ∈ st.os) {y : ℕ × ℕ}
    (hy : y ∈ factsE tab x) : y.1 ∈ (allFacts tab st).map Prod.fst :=
  List.mem_map.mpr ⟨y, List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hy⟩), rfl⟩

private theorem allFacts_mem (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {r : ℕ}
    (hr : r ∈ (allFacts tab st).map Prod.fst) : r ∈ N.primeFactors := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  rcases List.mem_append.mp hy with hy | hy
  · exact (spFacts_spec C hpc ht hH hy).2.1
  · obtain ⟨x, hx, hyx⟩ := List.mem_flatMap.mp hy
    exact (factsE_spec C hpc ht hH hx hyx).1

private theorem forcedB_spec {st : St} {r : ℕ} (h : forcedB tab st r = true) :
    r ∈ (allFacts tab st).map Prod.fst := by
  unfold forcedB at h
  obtain ⟨y, hy, hyr⟩ := List.any_eq_true.mp h
  rw [beq_iff_eq] at hyr
  exact List.mem_map.mpr ⟨y, hy, hyr⟩

private theorem freshB_spec {st : St} {r : ℕ} (h : freshB st r = true) :
    r ∉ st.os.map Prod.fst ∧ r ≠ st.sp := by
  unfold freshB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro hm
    obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hm
    have ha : (st.os.any fun x => x.1 == r) = true :=
      List.any_eq_true.mpr ⟨x, hx, beq_iff_eq.mpr hxr⟩
    rw [ha] at h1
    exact absurd h1 (by decide)
  · intro e
    rw [e, bne_self_eq_false] at h2
    exact absurd h2 (by decide)

private theorem list_sum_le_finset {l : List ℕ} (hl : l.Nodup) {S : Finset ℕ}
    (hS : ∀ x ∈ l, x ∈ S) (f : ℕ → ℕ) : (l.map f).sum ≤ ∑ x ∈ S, f x := by
  rw [← List.sum_toFinset f hl]
  exact Finset.sum_le_sum_of_subset fun x hx => hS x (List.mem_toFinset.mp hx)

/-! ### The leaves -/

private theorem cap_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {r : ℕ}
    (hl : leafB P tab st (.cap r) = true) : False := by
  simp only [leafB] at hl
  split at hl
  · rename_i x hx
    obtain ⟨hxm, hxp⟩ := find_spec hx
    rw [Bool.and_eq_true, beq_iff_eq] at hxp
    obtain ⟨hr, hex⟩ := hxp
    rw [decide_eq_true_eq] at hl
    obtain ⟨hxN, -, hxe, -⟩ := hH.1 x hxm
    have hv := hxe hex
    subst hr
    have hrP := Nat.prime_of_mem_primeFactors hxN
    have hr2 := two_ne C hxN
    have hA : kOf (spFacts tab st) x.1 ≤ (if st.sp = 0 then 0 else sigmaWeight N q x.1) := by
      apply kOf_le (g := fun r => if st.sp = 0 then 0 else sigmaWeight N q r)
      intro y hy
      by_cases h0 : st.sp = 0
      · simp [spFacts, h0] at hy
      · simp only [h0, if_false]
        exact (spFacts_spec C hpc ht hH hy).2.2
    have hB : (st.os.map fun y => kOf (factsE tab y) x.1).sum ≤
        (st.os.map fun y => sigmaWeight N y.1 x.1).sum :=
      List.sum_le_sum fun y hy => kOf_le (fun z hz => (factsE_spec C hpc ht hH hy hz).2) _
    have e : (st.os.map fun y => sigmaWeight N y.1 x.1) =
        (st.os.map Prod.fst).map (fun p => sigmaWeight N p x.1) := by
      rw [List.map_map]; rfl
    have hsub : ∀ p ∈ (st.os.map Prod.fst).toFinset, p ∈ N.primeFactors := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      exact (hH.1 y hy).1
    have hC : (if st.sp = 0 then 0 else sigmaWeight N q x.1) +
        (st.os.map fun y => sigmaWeight N y.1 x.1).sum ≤ N.factorization x.1 := by
      rw [e, ← List.sum_toFinset _ hH.2.1]
      by_cases h0 : st.sp = 0
      · simp only [h0, if_true, zero_add]
        exact sum_sigmaWeight_le_factorization C.h hrP hr2 hsub
      · simp only [h0, if_false]
        have hqn : q ∉ (st.os.map Prod.fst).toFinset := by
          intro hm
          obtain ⟨y, hy, hyq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
          exact (hH.1 y hy).2.1 hyq
        have := sum_sigmaWeight_le_factorization C.h hrP hr2
          (S := insert q (st.os.map Prod.fst).toFinset)
          (Finset.insert_subset (q_mem C) hsub)
        rwa [Finset.sum_insert hqn] at this
    omega
  · simp at hl

private theorem small_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {r : ℕ}
    (hl : leafB P tab st (.small r) = true) : False := by
  simp only [leafB, Bool.and_eq_true, decide_eq_true_eq] at hl
  have := C.h3 r (allFacts_mem C hpc ht hH (forcedB_spec hl.1))
  omega

private theorem budget_sound (C : Ctx P N q) {st : St} (hH : Holds N q st)
    (hl : leafB P tab st .budget = true) : False := by
  simp only [leafB] at hl
  split at hl
  · rename_i c hc
    rw [decide_eq_true_eq] at hl
    have h1 : (st.os.map fun x => x.2.1 / 2 - 1).sum ≤
        (st.os.map fun x => N.factorization x.1 / 2 - 1).sum :=
      List.sum_le_sum fun x hx => Nat.sub_le_sub_right (Nat.div_le_div_right (le_fac hH hx)) _
    have e : (st.os.map fun x => N.factorization x.1 / 2 - 1) =
        (st.os.map Prod.fst).map (fun p => N.factorization p / 2 - 1) := by
      rw [List.map_map]; rfl
    have h2 : (st.os.map fun x => N.factorization x.1 / 2 - 1).sum ≤
        ∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1) := by
      rw [e]
      refine list_sum_le_finset hH.2.1 (fun p hp => ?_) _
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      exact Finset.mem_erase.mpr ⟨(hH.1 y hy).2.1, (hH.1 y hy).1⟩
    have := C.h1 c hc
    omega
  · simp at hl

/-- The receiver weight of a list of facts of `p` other than the candidate `c` is at most
`recvWeight N q p`, when every receiver other than `c` differs from `q`. -/
private theorem recvL_le {fs : List (ℕ × ℕ)} {p c : ℕ}
    (hf : ∀ y ∈ fs, y.1 ∈ N.primeFactors ∧ y.2 ≤ sigmaWeight N p y.1 ∧ (y.1 ≠ c → y.1 ≠ q))
    (hnd : (fs.map Prod.fst).Nodup) : recvL fs c ≤ recvWeight N q p := by
  unfold recvL
  have hsub : (fs.filter fun y => y.1 % 3 == 1 && y.1 != c).Sublist fs := List.filter_sublist
  have hnd' := hnd.sublist (hsub.map Prod.fst)
  have h1 : ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map Prod.snd).sum ≤
      ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map fun y => sigmaWeight N p y.1).sum :=
    List.sum_le_sum fun y hy => (hf y (hsub.subset hy)).2.1
  have e : ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map fun y => sigmaWeight N p y.1) =
      ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map Prod.fst).map (sigmaWeight N p) := by
    rw [List.map_map]; rfl
  have h2 : ((fs.filter fun y => y.1 % 3 == 1 && y.1 != c).map fun y => sigmaWeight N p y.1).sum
      ≤ recvWeight N q p := by
    rw [e, ← List.sum_toFinset _ hnd']
    apply sum_sigmaWeight_le_recvWeight
    intro r hr
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    have hy' := List.mem_filter.mp hy
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hy'
    obtain ⟨hyf, hy3, hyc⟩ := hy'
    obtain ⟨hyN, -, hyq⟩ := hf y hyf
    exact Finset.mem_filter.mpr ⟨hyN, hyq hyc, by omega, hy3⟩
  omega

/-- The terms of one prime in the lower bound of `defect_lower_bound`. -/
noncomputable def gAll (N q p : ℕ) : ℕ :=
  (if N.factorization p = 2 then recvWeight N q p - 1 else 0) +
    (if 4 ≤ N.factorization p ∧ p ≠ 3 then 3 * (N.factorization p / 2 - 2) else 0) +
    (if 4 ≤ N.factorization p ∧ p % 3 = 2 then N.factorization p else 0) +
    2 * (if 4 ≤ N.factorization p then sigmaWeight N p 3 else 0) +
    (if 4 ≤ N.factorization p then recvWeight N q p else 0)

/-- `defect_lower_bound` summed over the entries of a state. -/
theorem defect_list {st : St} (hH : Holds N q st) :
    threeExcessDefect N + (st.os.map fun x => gAll N q x.1).sum + recvWeight N q q +
      (if 3 ∣ N then 0 else 4) ≤ supportDefect N q := by
  set S := (st.os.map Prod.fst).toFinset with hS
  have hmem : ∀ p ∈ S, p ∈ N.primeFactors ∧ p ≠ q := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact ⟨(hH.1 y hy).1, (hH.1 y hy).2.1⟩
  have h₂ : S.filter (fun p => N.factorization p = 2) ⊆ squarePrimes N q := by
    intro p hp
    obtain ⟨hpS, hp2⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(hmem p hpS).1, (hmem p hpS).2, hp2⟩
  have h₄ : S.filter (fun p => 4 ≤ N.factorization p) ⊆ highPrimes N q := by
    intro p hp
    obtain ⟨hpS, hp4⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨(hmem p hpS).2, (hmem p hpS).1⟩, hp4⟩
  have hm := defect_lower_bound h₂ h₄
  simp only [Finset.filter_filter, Finset.sum_filter] at hm
  have e : (st.os.map fun x => gAll N q x.1) = (st.os.map Prod.fst).map (gAll N q) := by
    rw [List.map_map]; rfl
  rw [e, ← List.sum_toFinset _ hH.2.1, ← hS]
  unfold gAll
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

private theorem entB_le (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {c : ℕ}
    (hc : ∀ r ∈ (allFacts tab st).map Prod.fst, r ≠ c → r ≠ q) {x : ℕ × ℕ × Bool}
    (hx : x ∈ st.os) : entB tab c x ≤ gAll N q x.1 := by
  have hR : recvL (factsE tab x) c ≤ recvWeight N q x.1 :=
    recvL_le (fun y hy => ⟨(factsE_spec C hpc ht hH hx hy).1,
      (factsE_spec C hpc ht hH hx hy).2, hc y.1 (mem_allFacts_e hx hy)⟩) (factsE_nodup hpc ht x)
  have hK : kOf (factsE tab x) 3 ≤ sigmaWeight N x.1 3 :=
    kOf_le (fun y hy => (factsE_spec C hpc ht hH hx hy).2) 3
  have hle := le_fac hH hx
  obtain ⟨-, -, he, hi⟩ := hH.1 x hx
  unfold entB gAll
  by_cases h2 : x.2.1 = 2
  · have hv : N.factorization x.1 = 2 := by
      cases hb : x.2.2
      · have := (hi hb).1; omega
      · rw [he hb, h2]
    rw [if_pos h2, if_pos hv]
    omega
  · rw [if_neg h2]
    by_cases h4 : 4 ≤ x.2.1
    · have hv4 : 4 ≤ N.factorization x.1 := le_trans h4 hle
      have hv2 : N.factorization x.1 ≠ 2 := by omega
      rw [if_pos h4, if_neg hv2, if_pos hv4, if_pos hv4]
      split_ifs <;> omega
    · rw [if_neg h4]
      exact Nat.zero_le _

private theorem threeT_le {st : St} (hH : Holds N q st) : threeT st ≤ threeExcessDefect N := by
  unfold threeT threeExcessDefect
  split
  · rename_i x hx
    obtain ⟨hxm, hx3⟩ := find_spec hx
    rw [beq_iff_eq] at hx3
    have := le_fac hH hxm
    rw [hx3] at this
    omega
  · exact Nat.zero_le _

/-- The ledger bound is at most the support defect, for a candidate `c` such that every forced
prime other than `c` differs from `q`. -/
theorem bound_le (C : Ctx P N q) (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true)
    {st : St} (hH : Holds N q st) {c : ℕ}
    (hc : ∀ r ∈ (allFacts tab st).map Prod.fst, r ≠ c → r ≠ q) :
    bound P tab st c ≤ supportDefect N q := by
  unfold bound
  have h3 := threeT_le hH
  have hI : (if 3 < P.u then 4 else 0) ≤ (if 3 ∣ N then 0 else 4) := by
    by_cases hu : 3 < P.u
    · have hn : ¬ 3 ∣ N := fun h3 => by
        have := C.h3 3 (Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3, C.h.ne_zero⟩)
        omega
      simp [hu, hn]
    · simp [hu]
  have hS : (if st.sp = 0 then 0 else recvL (spFacts tab st) c) ≤ recvWeight N q q := by
    by_cases h0 : st.sp = 0
    · simp [h0]
    · rw [if_neg h0]
      exact recvL_le (fun y hy => ⟨(spFacts_spec C hpc ht hH hy).2.1,
        (spFacts_spec C hpc ht hH hy).2.2, hc y.1 (mem_allFacts_sp hy)⟩)
        (spFacts_nodup hpc ht st)
  have hE : (st.os.map (entB tab c)).sum ≤ (st.os.map fun x => gAll N q x.1).sum :=
    List.sum_le_sum fun x hx => entB_le C hpc ht hH hc hx
  have hD := defect_list hH
  omega

private theorem knownB_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {p : ℕ}
    (h : knownB tab st p = true) : p ∈ N.primeFactors := by
  unfold knownB at h
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with (h | ⟨hp, h0⟩) | h
  · obtain ⟨x, hx, hxp⟩ := List.any_eq_true.mp h
    rw [beq_iff_eq] at hxp
    rw [← hxp]
    exact (hH.1 x hx).1
  · rw [hp, hH.2.2 (hp ▸ h0)]
    exact q_mem C
  · exact allFacts_mem C hpc ht hH (forcedB_spec h)

private theorem ledger_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {ks : List ℕ}
    (hl : leafB P tab st (.ledger ks) = true) : False := by
  simp only [leafB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨hnd, hks⟩, hall⟩ := hl
  have hlen : ks.length ≤ N.primeFactors.card := by
    rw [← List.toFinset_card_of_nodup (nodupB_sound hnd)]
    exact Finset.card_le_card fun p hp =>
      knownB_sound C hpc ht hH (hks p (List.mem_toFinset.mp hp))
  have hmul : P.w * ks.length ≤ P.w * N.primeFactors.card := Nat.mul_le_mul_left _ hlen
  have hfin : ∀ c ∈ cands tab st, (∀ r ∈ (allFacts tab st).map Prod.fst, r ≠ c → r ≠ q) →
      False := by
    intro c hcm hc
    have h1 := hall c hcm
    have h2 := bound_le C hpc ht hH hc
    have := C.h2
    omega
  by_cases h0 : st.sp = 0
  · by_cases hqf : q ∈ (allFacts tab st).map Prod.fst
    · refine hfin q ?_ (fun r _ hr => hr)
      unfold cands
      rw [if_pos h0]
      refine List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hqf, ?_⟩)
      rw [beq_iff_eq]
      exact (special_mod_four C.h C.hq C.hodd).1
    · refine hfin 0 ?_ (fun r hr _ hrq => hqf (hrq ▸ hr))
      unfold cands
      rw [if_pos h0]
      exact List.mem_cons_self
  · have hsq := hH.2.2 h0
    refine hfin q ?_ (fun r _ hr => hr)
    unfold cands
    rw [if_neg h0, hsq]
    exact List.mem_singleton_self _

private theorem allowB_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {p f : ℕ}
    (hl : allowB tab st p f = true) : p.Prime ∧ f ≤ N.factorization p := by
  unfold allowB at hl
  split at hl
  · rename_i x hx
    obtain ⟨hxm, hxp⟩ := find_spec hx
    rw [beq_iff_eq] at hxp
    rw [decide_eq_true_eq] at hl
    have := le_fac hH hxm
    rw [hxp] at this
    obtain ⟨hxN, -⟩ := hH.1 x hxm
    rw [hxp] at hxN
    exact ⟨Nat.prime_of_mem_primeFactors hxN, by omega⟩
  · split_ifs at hl with hsp
    · rw [decide_eq_true_eq] at hl
      obtain ⟨hp, h0⟩ := hsp
      have hsq := hH.2.2 (hp ▸ h0)
      rw [hp, hsq]
      have := one_le_fac C (q_mem C)
      exact ⟨C.hq, by omega⟩
    · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
        ne_eq] at hl
      obtain ⟨hfo, hfr⟩ := hl
      have hpN := allFacts_mem C hpc ht hH (forcedB_spec hfo)
      have hp1 := one_le_fac C hpN
      refine ⟨Nat.prime_of_mem_primeFactors hpN, ?_⟩
      rcases hfr with hf | ⟨hf, hne⟩
      · omega
      · have hpq : p ≠ q := by
          rintro rfl
          rcases hne with h0 | h4
          · exact hsp ⟨(hH.2.2 h0).symm, C.hq.ne_zero⟩
          · exact h4 (special_mod_four C.h C.hq C.hodd).1
        obtain ⟨j, hj, -⟩ := even_pos_factorization_of_ne C.h C.hq C.hodd hpN hpq
        omega

private theorem abund_sound (C : Ctx P N q) (hpc : Pratt.check pc = true)
    (ht : tabOK pc tab = true) {st : St} (hH : Holds N q st) {ws : List (ℕ × ℕ)}
    (hl : leafB P tab st (.abund ws) = true) : False := by
  simp only [leafB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hl
  obtain ⟨⟨hnd, hall⟩, hlt⟩ := hl
  have hnd' := nodupB_sound hnd
  have hpr : ∀ p ∈ (ws.map Prod.fst).toFinset, p.Prime := fun p hp =>
    (allowB_sound C hpc ht hH (hall p (List.mem_toFinset.mp hp))).1
  have hf : ∀ p ∈ (ws.map Prod.fst).toFinset, kOf ws p ≤ N.factorization p := fun p hp =>
    (allowB_sound C hpc ht hH (hall p (List.mem_toFinset.mp hp))).2
  have hle := prod_geom_sum_le_two_mul_prod C.h hpr hf
  simp only [← gs_eq] at hle
  rw [List.prod_toFinset _ hnd', List.prod_toFinset _ hnd'] at hle
  omega

/-- Soundness of the leaf checks. -/
theorem leaf_sound (C : Ctx P N q) (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true)
    {st : St} (hH : Holds N q st) : ∀ l, leafB P tab st l = true → False
  | .cap _, hl => cap_sound C hpc ht hH hl
  | .small _, hl => small_sound C hpc ht hH hl
  | .budget, hl => budget_sound C hH hl
  | .ledger _, hl => ledger_sound C hpc ht hH hl
  | .abund _, hl => abund_sound C hpc ht hH hl

/-! ### The tree -/

/-- The meaning of a position: a state that holds, at the root also `P.root ∣ N`, in a chain for
the prime `r` at the exponent `e` also that `r` is an ordinary prime factor of `N` that is not an
entry, with even exponent at least the even number `e`. -/
def Inv (P : Params) (N q : ℕ) : Mode → St → Prop
  | .node, st => Holds N q st
  | .root, st => Holds N q st ∧ P.root ∣ N
  | .chain r e, st => Holds N q st ∧ r ∈ N.primeFactors ∧ r ≠ q ∧ r ∉ st.os.map Prod.fst ∧
      e ≤ N.factorization r ∧ e % 2 = 0 ∧ N.factorization r % 2 = 0

private theorem holds_cons {st : St} (hH : Holds N q st) {r e : ℕ} {b : Bool}
    (hrN : r ∈ N.primeFactors) (hrq : r ≠ q) (hrf : r ∉ st.os.map Prod.fst)
    (hb1 : b = true → N.factorization r = e) (hb2 : b = false → 4 ≤ e ∧ e ≤ N.factorization r) :
    Holds N q ⟨(r, e, b) :: st.os, st.sp⟩ := by
  refine ⟨fun y hy => ?_, ?_, hH.2.2⟩
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hrN, hrq, hb1, hb2⟩
    · exact hH.1 y hy
  · rw [List.map_cons]
    exact List.nodup_cons.mpr ⟨hrf, hH.2.1⟩

/-- Soundness of the tree check. -/
theorem go_sound (C : Ctx P N q) (hpc : Pratt.check pc = true) (ht : tabOK pc tab = true) :
    ∀ (c : Cert) (st : St) (m : Mode), go P pc tab c st m = true → Inv P N q m st → False
  | .leaf l, st, m, hg, hI => by
    simp only [go, Bool.and_eq_true] at hg
    cases m with
    | node => exact leaf_sound C hpc ht hI l hg.2
    | root => simp [isNode] at hg
    | chain _ _ => simp [isNode] at hg
  | .br r spk ch, st, m, hg, hI => by
    simp only [go, Bool.and_eq_true] at hg
    obtain ⟨⟨hh, hs⟩, hc⟩ := hg
    have hX : Holds N q st ∧ r ∈ N.primeFactors ∧ freshB st r = true := by
      cases m with
      | node =>
        simp only [brHead, Bool.and_eq_true] at hh
        exact ⟨hI, allFacts_mem C hpc ht hI (forcedB_spec hh.1), hh.2⟩
      | root =>
        simp only [brHead, Bool.and_eq_true, beq_iff_eq] at hh
        obtain ⟨⟨hr, hp⟩, hf⟩ := hh
        refine ⟨hI.1, Nat.mem_primeFactors.mpr ⟨isPr_sound hpc hp, ?_, C.h.ne_zero⟩, hf⟩
        rw [hr]
        exact hI.2
      | chain _ _ => simp [brHead] at hh
    obtain ⟨hH, hrN, hfr⟩ := hX
    obtain ⟨hrf, hrs⟩ := freshB_spec hfr
    by_cases hrq : r = q
    · have hsp0 : st.sp = 0 := by
        by_contra h0
        exact hrs (hrq.trans (hH.2.2 h0).symm)
      have h4 : r % 4 = 1 := hrq ▸ (special_mod_four C.h C.hq C.hodd).1
      rw [if_pos ⟨hsp0, h4⟩] at hs
      exact go_sound C hpc ht spk ⟨st.os, r⟩ .node hs ⟨hH.1, hH.2.1, fun _ => hrq⟩
    · obtain ⟨j, hj, hpos⟩ := even_pos_factorization_of_ne C.h C.hq C.hodd hrN hrq
      exact go_sound C hpc ht ch st (.chain r 2) hc
        ⟨hH, hrN, hrq, hrf, by omega, rfl, by omega⟩
  | .ord kid rest, st, m, hg, hI => by
    cases m with
    | chain r e =>
      simp only [go, Bool.and_eq_true] at hg
      obtain ⟨hH, hrN, hrq, hrf, hle, he2, hv2⟩ := hI
      by_cases hv : N.factorization r = e
      · exact go_sound C hpc ht kid _ .node hg.1
          (holds_cons hH hrN hrq hrf (fun _ => hv) (fun h => absurd h (by decide)))
      · exact go_sound C hpc ht rest st (.chain r (e + 2)) hg.2
          ⟨hH, hrN, hrq, hrf, by omega, by omega, hv2⟩
    | node => simp [go] at hg
    | root => simp [go] at hg
  | .high kid, st, m, hg, hI => by
    cases m with
    | chain r e =>
      simp only [go, Bool.and_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hH, hrN, hrq, hrf, hle, -, -⟩ := hI
      exact go_sound C hpc ht kid _ .node hg.2
        (holds_cons hH hrN hrq hrf (fun h => absurd h (by decide)) (fun _ => ⟨hg.1, hle⟩))
    | node => simp [go] at hg
    | root => simp [go] at hg
  | .nil, _, _, hg, _ => by simp [go] at hg

end Sound

/-- Soundness of the checker. If `check P pc tab c = true`, then there is no odd perfect number
`N` with special prime `q` (a prime with odd exponent) such that, with `T` the total excess,
`T ≤ c` whenever `P.cap = some c`, `P.w * ω(N) + supportDefect N q ≤ P.K`, every prime factor
of `N` is at least `P.u`, and `P.root ∣ N`. -/
theorem check_sound {P : Params} {pc : PCert} {tab : Tab} {c : Cert}
    (hc : check P pc tab c = true) {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (h1 : ∀ c, P.cap = some c → (∑ p ∈ N.primeFactors.erase q, (N.factorization p / 2 - 1)) ≤ c)
    (h2 : P.w * N.primeFactors.card + supportDefect N q ≤ P.K)
    (h3 : ∀ p ∈ N.primeFactors, P.u ≤ p) (hroot : P.root ∣ N) : False := by
  simp only [check, Bool.and_eq_true] at hc
  obtain ⟨⟨hpc, ht⟩, hg⟩ := hc
  exact go_sound ⟨h, hq, hodd, h1, h2, h3⟩ hpc ht c _ _ hg
    ⟨⟨by simp, by simp, by simp⟩, hroot⟩

end DefectTree

end OddPerfect

#print axioms OddPerfect.DefectTree.gs_eq
#print axioms OddPerfect.DefectTree.sigma_eq_gs
#print axioms OddPerfect.DefectTree.nodupB_sound
#print axioms OddPerfect.DefectTree.kOf_le
#print axioms OddPerfect.DefectTree.isPr_sound
#print axioms OddPerfect.DefectTree.look_sound
#print axioms OddPerfect.DefectTree.defect_list
#print axioms OddPerfect.DefectTree.bound_le
#print axioms OddPerfect.DefectTree.leaf_sound
#print axioms OddPerfect.DefectTree.go_sound
#print axioms OddPerfect.DefectTree.check_sound
