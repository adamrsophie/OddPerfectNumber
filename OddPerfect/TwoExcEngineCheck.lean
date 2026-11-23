import OddPerfect.TwoExcEngineState
import OddPerfect.Network
import OddPerfect.ThreeSquareCapacity
import OddPerfect.TwoExceptionFour
import OddPerfect.TwoExceptionThreeB
import OddPerfect.Cyclotomic

/-!
# A certificate checker for families "at most E exceptional primes, fixed exponent at 3": soundness

This module proves `check_sound`: if `TwoExcEngine.check P pr done c` returns `true`, then no
odd perfect number lies in the family `Fam P.E N q`. The hypotheses are the deficient leaf
theorem `DefSound P` (proved in its own module), a sound primality oracle `pr`, a sound
recognizer `done` of states refuted elsewhere, and `P.E ≤ 2` when the landed facts are used
(`P.landed`), because those facts are library theorems about two named exceptions. It also
proves `checkV_sound`, the same statement for `checkV` and the family `FamV P N q` of the
parameters, and the bridges `famV_S1`, `famV_S2a`, `famV_S2b` from named exceptions of
exponent 4 to that family. The landed facts are used only when `P.lan`, that is with exponent
2 at 3.

The engine is a tool. An accepted certificate refutes exactly the states it is run on. The
one exception statement that the pilot certificate reproduces was already in the library before
this engine was written; the pilot is a test of the engine, not a new result.

## Structure

* Specifications of the fast functions of `TwoExcEngineCode`: modular powers (`powModE_eq`),
  trial division (`smallPrime_sound`), the prime table (`pmask_ok`, checked once for all
  `i < 4096` by one kernel evaluation), the scan (`scanNext_spec`: the scan returns the least
  prime at least `x` that is not a key, so no prime is skipped), and the item test
  (`gdivB_sound`: one modular power gives `n ∣ σ(c ^ v_c(N))`).
* The meaning `PendOK` of pending items and the preservation of `Holds` under the state
  changes of the checker (contributions, roles, new keys, larger `x`).
* One lemma per rule: items and budgets (`applyItems_sound`, with `csum_le` from the
  conservation law `sigmaWeight_sum_eq`), the roles of a forced or decided prime with
  exhaustiveness (`roles_exh`, using the landed facts on `q` only when `P.lan`), the receipt
  rule (`receipt_exists`, `ordOK_dvd`, `infeasible_false`, `nextAllowed_le`), exponent
  splitting (inside `go_sound`), abundancy (`abundant_false`) and rule L (`landedL_false`).
* `go_sound`: every checker context `ctx` with `go P pr done ctx c = true` refutes the states
  that `CtxOK` assigns to it, by induction on the certificate.
* The bridge `fam_of_named` from named exceptions to the family, for every `E`, with the cases
  `fam_one` and `fam_two`, and the bridge `famV_of_named` to the family of the parameters.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace TwoExcEngine

/-! ## Primitive operations -/

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by simp [Nat.beq_eq]
private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by simp [Nat.blt_eq]
private theorem ble_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by simp [Nat.ble_eq]

/-! ## Modular powers -/

private theorem powModR_spec (n : ℕ) :
    ∀ f b e acc, e < 2 ^ f → powModR n f b e acc = acc * b ^ e % n
  | 0, b, e, acc, h => by
    have : e = 0 := by simpa using h
    subst this
    show acc % n = _
    simp
  | f + 1, b, e, acc, h => by
    show cond (Nat.beq e 0) (acc % n) (powModR n f (b * b % n) (e / 2)
      (cond (Nat.beq (e % 2) 1) (acc * b % n) acc)) = _
    cases he : Nat.beq e 0
    · have he' : e ≠ 0 := fun h0 => by simp [h0] at he
      simp only [cond_false]
      rw [powModR_spec n f _ _ _ (by rw [pow_succ] at h; omega)]
      have hb : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add, Nat.div_add_mod]
      have hacc : cond (Nat.beq (e % 2) 1) (acc * b % n) acc ≡ acc * b ^ (e % 2) [MOD n] := by
        rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
        · have : Nat.beq (e % 2) 1 = false := by rw [h2]; rfl
          rw [this, h2]; simp [Nat.ModEq]
        · have : Nat.beq (e % 2) 1 = true := by rw [h2]; rfl
          rw [this, h2]; simp [Nat.ModEq]
      have hp : (b * b % n) ^ (e / 2) ≡ (b * b) ^ (e / 2) [MOD n] :=
        (Nat.mod_modEq _ _).pow _
      have := hacc.mul hp
      rw [hb]
      calc _ = acc * b ^ (e % 2) * (b * b) ^ (e / 2) % n := this
        _ = _ := by ring_nf
    · have : e = 0 := by simpa using he
      subst this
      simp

theorem powModE_eq (b e n : ℕ) : powModE b e n = b ^ e % n := by
  unfold powModE
  rw [powModR_spec]
  · simp
  · exact (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by simp))

/-! ## Trial division and the prime table -/

private theorem findDiv_succ (f n d : ℕ) : findDiv (f + 1) n d =
    cond (Nat.blt n (Nat.mul d d)) n (cond (Nat.beq (Nat.mod n d) 0) d (findDiv f n (Nat.add d 1))) :=
  rfl

private theorem findDiv_prime : ∀ f n d, 2 ≤ d → (∀ e, 2 ≤ e → e < d → ¬ e ∣ n) → 2 ≤ n →
    findDiv f n d = n → n.Prime
  | 0, n, d, _, _, hn, h => by
    have : (0 : ℕ) = n := h
    omega
  | f + 1, n, d, hd, hnd, hn, h => by
    rw [findDiv_succ] at h
    cases h1 : Nat.blt n (Nat.mul d d)
    · rw [h1] at h
      simp only [cond_false] at h
      cases h2 : Nat.beq (Nat.mod n d) 0
      · rw [h2] at h
        simp only [cond_false] at h
        refine findDiv_prime f n (d + 1) (by omega) ?_ hn h
        intro e he1 he2
        rcases Nat.lt_succ_iff_lt_or_eq.mp he2 with he | rfl
        · exact hnd e he1 he
        · intro hdv
          have : Nat.mod n e = 0 := Nat.mod_eq_zero_of_dvd hdv
          rw [this] at h2
          exact absurd h2 (by decide)
      · rw [h2] at h
        simp only [cond_true] at h
        have hge : ¬ n < d * d := fun hh => by
          rw [show Nat.mul d d = d * d from rfl, blt_iff.mpr hh] at h1
          exact absurd h1 (by decide)
        subst h
        nlinarith
    · have hlt : n < d * d := blt_iff.mp h1
      by_contra hnp
      have hmf := Nat.minFac_prime (show n ≠ 1 by omega)
      have hsq := Nat.minFac_sq_le_self (by omega) hnp
      have hge : d ≤ n.minFac := by
        by_contra hlt'
        exact hnd _ hmf.two_le (by omega) (Nat.minFac_dvd n)
      have : d * d ≤ n.minFac ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hge hge
      omega

theorem smallPrime_sound {n : ℕ} (h : smallPrime n = true) : n.Prime := by
  simp only [smallPrime, Bool.and_eq_true] at h
  exact findDiv_prime 65536 n 2 le_rfl (fun e h1 h2 => by omega) (ble_iff.mp h.1) (beq_iff.mp h.2)

/-- Bit `i` of the table. -/
private def bitP (i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight PMASK i) 1) 1

/-- The table test for one entry: a set bit is confirmed prime by trial division, a clear bit
has a found proper divisor (or the entry is below 2). -/
private def bitOK (i : ℕ) : Bool :=
  cond (bitP i) (smallPrime i)
    (Nat.blt i 2 || (Nat.ble 2 (findDiv 65536 i 2) && Nat.blt (findDiv 65536 i 2) i &&
      Nat.beq (Nat.mod i (findDiv 65536 i 2)) 0))

/-- All entries in `[i, i + f)` pass the table test. -/
private def tableAux : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true) (fun _ ih i => bitOK i && ih (Nat.add i 1))

private theorem tableAux_4096 : tableAux 4096 0 = true := by decide +kernel

private theorem tableAux_spec : ∀ f i, tableAux f i = true → ∀ j, i ≤ j → j < i + f → bitOK j = true
  | 0, i, _, j, h1, h2 => absurd h2 (by omega)
  | f + 1, i, h, j, h1, h2 => by
    have h' : (bitOK i && tableAux f (i + 1)) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h'.1
    · exact tableAux_spec f (i + 1) h'.2 j h1 (by omega)

private theorem bitOK_iff {i : ℕ} (h : bitOK i = true) : bitP i = true ↔ i.Prime := by
  unfold bitOK at h
  cases hb : bitP i
  · rw [hb] at h
    simp only [cond_false, Bool.or_eq_true, Bool.and_eq_true] at h
    simp only [Bool.false_eq_true, false_iff]
    intro hp
    rcases h with h | ⟨⟨h1, h2⟩, h3⟩
    · exact absurd (blt_iff.mp h) (by have := hp.two_le; omega)
    · have h1 := ble_iff.mp h1
      have h2 := blt_iff.mp h2
      have h3 : i % findDiv 65536 i 2 = 0 := beq_iff.mp h3
      rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h3) with h4 | h4 <;> omega
  · rw [hb] at h
    simp only [cond_true] at h
    exact ⟨fun _ => smallPrime_sound h, fun _ => rfl⟩

/-- The prime table: bit `i` of `PMASK` is set exactly when `i < 4096` is prime. -/
theorem pmask_ok {i : ℕ} (hi : i < 4096) :
    Nat.beq (Nat.land (Nat.shiftRight PMASK i) 1) 1 = true ↔ i.Prime :=
  bitOK_iff (tableAux_spec 4096 0 tableAux_4096 i (Nat.zero_le _) (by omega))

theorem primeB_sound {n : ℕ} (h : primeB n = true) : n.Prime := by
  unfold primeB at h
  cases hb : Nat.blt n 4096
  · rw [hb] at h; exact smallPrime_sound h
  · rw [hb] at h; exact (pmask_ok (blt_iff.mp hb)).mp h

/-! ## Keys -/

private theorem findKey_some {p : ℕ} {k : Key} : ∀ {ks : List Key}, findKey p ks = some k → k ∈ ks ∧ k.p = p
  | [], h => by cases h
  | k' :: l, h => by
    change cond (Nat.beq k'.p p) (some k') (findKey p l) = some k at h
    cases hb : Nat.beq k'.p p
    · rw [hb] at h
      have := findKey_some h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · rw [hb] at h
      cases h
      exact ⟨List.mem_cons_self .., beq_iff.mp hb⟩

private theorem findKey_none {p : ℕ} : ∀ {ks : List Key}, findKey p ks = none → p ∉ ks.map Key.p
  | [], _ => by simp
  | k' :: l, h => by
    change cond (Nat.beq k'.p p) (some k') (findKey p l) = none at h
    cases hb : Nat.beq k'.p p
    · rw [hb] at h
      have := findKey_none h
      simp only [List.map_cons, List.mem_cons, not_or]
      refine ⟨fun he => ?_, this⟩
      rw [he, show Nat.beq k'.p k'.p = true from beq_iff.mpr rfl] at hb
      cases hb
    · rw [hb] at h; cases h

private theorem isKey_iff {p : ℕ} : ∀ {ks : List Key}, isKey ks p = true ↔ p ∈ ks.map Key.p
  | [] => by simp [isKey]
  | k' :: l => by
    change cond (Nat.beq k'.p p) true (isKey l p) = true ↔ _
    rw [List.map_cons, List.mem_cons, ← isKey_iff]
    cases hb : Nat.beq k'.p p
    · have : p ≠ k'.p := fun he => by rw [he, beq_iff.mpr rfl] at hb; cases hb
      simp [this]
    · simp [beq_iff.mp hb]

private theorem insertKey_perm (k : Key) : ∀ ks : List Key, (insertKey k ks).Perm (k :: ks)
  | [] => List.Perm.refl _
  | k' :: l => by
    change (cond (Nat.blt k.p k'.p) (k :: k' :: l) (k' :: insertKey k l)).Perm _
    cases Nat.blt k.p k'.p
    · exact ((insertKey_perm k l).cons k').trans (List.Perm.swap k k' l)
    · exact List.Perm.refl _

private theorem replaceKey_map (k : Key) : ∀ ks : List Key, (replaceKey k ks).map Key.p = ks.map Key.p
  | [] => rfl
  | k' :: l => by
    change (cond (Nat.beq k'.p k.p) (k :: l) (k' :: replaceKey k l)).map Key.p = _
    cases hb : Nat.beq k'.p k.p
    · simp [replaceKey_map k l]
    · simp [beq_iff.mp hb]

private theorem mem_replaceKey (k : Key) : ∀ {ks : List Key} {k' : Key}, k' ∈ replaceKey k ks → k' = k ∨ k' ∈ ks
  | [], _, h => by cases h
  | k0 :: l, k', h => by
    change k' ∈ cond (Nat.beq k0.p k.p) (k :: l) (k0 :: replaceKey k l) at h
    cases hb : Nat.beq k0.p k.p <;> simp only [hb, cond_false, cond_true] at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_replaceKey k h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem setRole_map (p : ℕ) (r : Role) : ∀ ks : List Key, (setRole p r ks).map Key.p = ks.map Key.p
  | [] => rfl
  | k' :: l => by
    change (cond (Nat.beq k'.p p) (⟨k'.p, r, k'.cs⟩ :: l) (k' :: setRole p r l)).map Key.p = _
    cases Nat.beq k'.p p
    · simp [setRole_map p r l]
    · simp

private theorem mem_setRole (p : ℕ) (r : Role) : ∀ {ks : List Key} {k' : Key}, k' ∈ setRole p r ks →
    k' ∈ ks ∨ ∃ k0 ∈ ks, k0.p = p ∧ k' = ⟨p, r, k0.cs⟩
  | [], _, h => by cases h
  | k0 :: l, k', h => by
    change k' ∈ cond (Nat.beq k0.p p) (⟨k0.p, r, k0.cs⟩ :: l) (k0 :: setRole p r l) at h
    cases hb : Nat.beq k0.p p
    · rw [hb] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl (List.mem_cons_self ..)
      · rcases mem_setRole p r h with h | ⟨k1, hk1, h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr ⟨k1, List.mem_cons_of_mem _ hk1, h1, h2⟩
    · rw [hb] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr ⟨k0, List.mem_cons_self .., beq_iff.mp hb, by rw [beq_iff.mp hb]⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)

/-! ## Contribution lists -/

private theorem mem_setW (c w : ℕ) : ∀ {l : List (ℕ × ℕ)} {e : ℕ × ℕ}, e ∈ setW c w l → e = (c, w) ∨ e ∈ l
  | [], e, h => by
    change e ∈ [(c, w)] at h
    exact Or.inl (List.mem_singleton.mp h)
  | e0 :: l, e, h => by
    change e ∈ cond (Nat.beq e0.1 c) ((c, w) :: l) (e0 :: setW c w l) at h
    cases hb : Nat.beq e0.1 c <;> simp only [hb, cond_false, cond_true] at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_setW c w h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem setW_map (c w : ℕ) : ∀ l : List (ℕ × ℕ),
    (setW c w l).map Prod.fst = l.map Prod.fst ∨ (setW c w l).map Prod.fst = l.map Prod.fst ++ [c] ∧
      c ∉ l.map Prod.fst
  | [] => Or.inr ⟨rfl, by simp⟩
  | e0 :: l => by
    change (cond (Nat.beq e0.1 c) ((c, w) :: l) (e0 :: setW c w l)).map Prod.fst = _ ∨
      (cond (Nat.beq e0.1 c) ((c, w) :: l) (e0 :: setW c w l)).map Prod.fst = _ ∧ _
    cases hb : Nat.beq e0.1 c
    · have hne : e0.1 ≠ c := fun he => by rw [he, beq_iff.mpr rfl] at hb; cases hb
      rcases setW_map c w l with h | ⟨h, hn⟩
      · left; simp [h]
      · right; simp [h, hn, Ne.symm hne]
    · left; simp [beq_iff.mp hb]

private theorem setW_nodup (c w : ℕ) {l : List (ℕ × ℕ)} (h : (l.map Prod.fst).Nodup) :
    ((setW c w l).map Prod.fst).Nodup := by
  rcases setW_map c w l with h' | ⟨h', hn⟩
  · rwa [h']
  · rw [h', List.nodup_append]
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      List.mem_singleton, true_and, h]
    intro a ha b hb
    subst hb
    exact fun he => hn (he ▸ ha)

/-- The key of a pending entry. -/
def pk (e : ℕ × ℕ × ℕ) : ℕ × ℕ := (e.1, e.2.1)

private theorem mem_setP (p c w : ℕ) : ∀ {l : List (ℕ × ℕ × ℕ)} {e : ℕ × ℕ × ℕ}, e ∈ setP p c w l →
    e = (p, c, w) ∨ e ∈ l
  | [], e, h => by
    change e ∈ [(p, c, w)] at h
    exact Or.inl (List.mem_singleton.mp h)
  | e0 :: l, e, h => by
    change e ∈ cond (Nat.beq e0.1 p && Nat.beq e0.2.1 c) ((p, c, w) :: l) (e0 :: setP p c w l) at h
    cases hb : (Nat.beq e0.1 p && Nat.beq e0.2.1 c) <;> simp only [hb, cond_false, cond_true] at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_cons_self ..)
      · rcases mem_setP p c w h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem setP_map (p c w : ℕ) : ∀ l : List (ℕ × ℕ × ℕ),
    (setP p c w l).map pk = l.map pk ∨ (setP p c w l).map pk = l.map pk ++ [(p, c)] ∧
      (p, c) ∉ l.map pk
  | [] => Or.inr ⟨rfl, by simp⟩
  | e0 :: l => by
    change (cond (Nat.beq e0.1 p && Nat.beq e0.2.1 c) ((p, c, w) :: l)
      (e0 :: setP p c w l)).map pk = _ ∨ (cond (Nat.beq e0.1 p && Nat.beq e0.2.1 c) ((p, c, w) :: l)
      (e0 :: setP p c w l)).map pk = _ ∧ _
    cases hb : (Nat.beq e0.1 p && Nat.beq e0.2.1 c)
    · have hne : pk e0 ≠ (p, c) := by
        intro he
        simp only [pk, Prod.mk.injEq] at he
        rw [he.1, he.2, beq_iff.mpr rfl, beq_iff.mpr rfl] at hb
        cases hb
      rcases setP_map p c w l with h | ⟨h, hn⟩
      · left; simp [h]
      · right; simp [h, hn, Ne.symm hne]
    · left
      simp only [Bool.and_eq_true] at hb
      simp [pk, beq_iff.mp hb.1, beq_iff.mp hb.2]

private theorem setP_nodup (p c w : ℕ) {l : List (ℕ × ℕ × ℕ)} (h : (l.map pk).Nodup) :
    ((setP p c w l).map pk).Nodup := by
  rcases setP_map p c w l with h' | ⟨h', hn⟩
  · rwa [h']
  · rw [h', List.nodup_append]
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      List.mem_singleton, true_and, h]
    intro a ha b hb
    subst hb
    exact fun he => hn (he ▸ ha)

/-! ## The scan -/

/-- What a successful scan from `y` gives: the least prime `z ≥ y` that is not a key. -/
def ScanP (ks : List Key) (y z : ℕ) : Prop :=
  y ≤ z ∧ z.Prime ∧ z ∉ ks.map Key.p ∧ ∀ w, y ≤ w → w < z → w.Prime → w ∈ ks.map Key.p

private theorem scanP_skip {ks : List Key} {y z : ℕ} (hy : y.Prime → y ∈ ks.map Key.p)
    (h : ScanP ks (y + 1) z) : ScanP ks y z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, h2, h3, fun w hw1 hw2 hw3 => ?_⟩
  rcases Nat.eq_or_lt_of_le hw1 with rfl | hw1
  · exact hy hw3
  · exact h4 w hw1 hw2 hw3

private theorem scanAux_spec (ks : List Key) : ∀ f y z, scanAux ks f y = some z → ScanP ks y z
  | 0, y, z, h => by cases h
  | f + 1, y, z, h => by
    change cond (isKey ks y || Nat.blt y 2) (scanAux ks f (Nat.add y 1))
      (cond (Nat.blt y 4096)
        (cond (Nat.beq (Nat.land (Nat.shiftRight PMASK y) 1) 1) (some y) (scanAux ks f (Nat.add y 1)))
        (cond (Nat.beq (findDiv 65536 y 2) y) (some y)
          (cond (Nat.ble 2 (findDiv 65536 y 2) && Nat.blt (findDiv 65536 y 2) y &&
            Nat.beq (Nat.mod y (findDiv 65536 y 2)) 0) (scanAux ks f (Nat.add y 1)) none))) = some z at h
    cases h1 : (isKey ks y || Nat.blt y 2)
    · rw [h1] at h
      simp only [Bool.or_eq_false_iff] at h1
      have hk : y ∉ ks.map Key.p := fun hm => by rw [isKey_iff.mpr hm] at h1; exact absurd h1.1 (by decide)
      have hy2 : 2 ≤ y := by
        by_contra hc
        rw [blt_iff.mpr (by omega)] at h1
        exact absurd h1.2 (by decide)
      simp only [cond_false] at h
      cases h2 : Nat.blt y 4096
      · rw [h2] at h
        simp only [cond_false] at h
        cases h3 : Nat.beq (findDiv 65536 y 2) y
        · rw [h3] at h
          simp only [cond_false] at h
          cases h4 : (Nat.ble 2 (findDiv 65536 y 2) && Nat.blt (findDiv 65536 y 2) y &&
            Nat.beq (Nat.mod y (findDiv 65536 y 2)) 0)
          · rw [h4] at h; cases h
          · rw [h4] at h
            simp only [cond_true] at h
            simp only [Bool.and_eq_true] at h4
            refine scanP_skip (fun hp => ?_) (scanAux_spec ks f (y + 1) z h)
            have e1 := ble_iff.mp h4.1.1
            have e2 := blt_iff.mp h4.1.2
            have e3 : y % findDiv 65536 y 2 = 0 := beq_iff.mp h4.2
            rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero e3) with e4 | e4 <;> omega
        · rw [h3] at h
          simp only [cond_true, Option.some.injEq] at h
          subst h
          refine ⟨le_rfl, findDiv_prime 65536 y 2 le_rfl (fun e h1 h2 => by omega) hy2
            (beq_iff.mp h3), hk, fun w h1 h2 _ => absurd h2 (by omega)⟩
      · rw [h2] at h
        simp only [cond_true] at h
        have hlt := blt_iff.mp h2
        cases h3 : Nat.beq (Nat.land (Nat.shiftRight PMASK y) 1) 1
        · rw [h3] at h
          simp only [cond_false] at h
          refine scanP_skip (fun hp => ?_) (scanAux_spec ks f (y + 1) z h)
          rw [(pmask_ok hlt).mpr hp] at h3
          cases h3
        · rw [h3] at h
          simp only [cond_true, Option.some.injEq] at h
          subst h
          exact ⟨le_rfl, (pmask_ok hlt).mp h3, hk, fun w h1 h2 _ => absurd h2 (by omega)⟩
    · rw [h1] at h
      simp only [cond_true] at h
      refine scanP_skip (fun hp => ?_) (scanAux_spec ks f (y + 1) z h)
      simp only [Bool.or_eq_true] at h1
      rcases h1 with h1 | h1
      · exact isKey_iff.mp h1
      · exact absurd (blt_iff.mp h1) (by have := hp.two_le; omega)

theorem scanNext_spec {ks : List Key} {x y : ℕ} (h : scanNext ks x = some y) : ScanP ks x y :=
  scanAux_spec ks 1000 x y h

/-! ## Divisor sums -/

private theorem sigma_dvd_of_role {r : Role} {k : ℕ} {hq : Prop} {c : ℕ} (hc : c.Prime)
    (hr : RoleHolds r k hq) : σ 1 (c ^ r.m) ∣ σ 1 (c ^ k) := by
  cases r with
  | sq =>
    obtain ⟨-, rfl⟩ := hr
    exact dvd_rfl
  | fr isQ D no3 kmin ex =>
    obtain ⟨-, hD, -, -, hex, -, -⟩ := hr
    cases ex with
    | true =>
      rw [hex rfl]
      exact dvd_rfl
    | false =>
      have hD0 : D ≠ 0 := by rintro rfl; simp at hD
      show σ 1 (c ^ (D - 1)) ∣ _
      exact OPNExample.sigma_prime_pow_dvd hc (by rwa [Nat.sub_add_cancel (by omega)])

theorem gdivB_sound {N q : ℕ} {ks : List Key} (hk : ∀ k ∈ ks, KeyHolds N q ks k) {c n : ℕ}
    (h : gdivB ks c n = true) : c ∈ ks.map Key.p ∧ n ∣ σ 1 (c ^ N.factorization c) := by
  unfold gdivB at h
  split at h
  · cases h
  · rename_i k hf
    obtain ⟨hkm, rfl⟩ := findKey_some hf
    obtain ⟨hp, -, hr, -, -⟩ := hk k hkm
    refine ⟨List.mem_map_of_mem hkm, ?_⟩
    simp only [Bool.and_eq_true] at h
    have h2 : (k.p ^ (k.role.m + 1)) % (n * (k.p - 1)) = 1 % (n * (k.p - 1)) := by
      have := beq_iff.mp h.2
      rwa [powModE_eq] at this
    have hdv : n * (k.p - 1) ∣ k.p ^ (k.role.m + 1) - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h2.symm
    rw [← sigma_prime_pow_mul_pred hp] at hdv
    have hn : n ∣ σ 1 (k.p ^ k.role.m) :=
      Nat.dvd_of_mul_dvd_mul_right (by have := hp.two_le; omega) hdv
    exact hn.trans (sigma_dvd_of_role hp hr)

/-! ## Orders -/

private theorem mem_of_dvd_prod {r : ℕ} (hr : r.Prime) : ∀ {fs : List ℕ}, (∀ a ∈ fs, a.Prime) →
    r ∣ fs.prod → r ∈ fs
  | [], _, h => by
    simp only [List.prod_nil, Nat.dvd_one] at h
    exact absurd h hr.one_lt.ne'
  | a :: t, ha, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hr (ha a (List.mem_cons_self ..))).mp h]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_dvd_prod hr (fun b hb => ha b (List.mem_cons_of_mem _ hb)) h)

private theorem pow_eq_one_of_dvd_sigma {p g k : ℕ} (hg : g.Prime) (h : p ∣ σ 1 (g ^ k)) :
    ((g : ZMod p)) ^ (k + 1) = 1 := by
  have h1 : p ∣ g ^ (k + 1) - 1 := by
    rw [← sigma_prime_pow_mul_pred hg]
    exact h.mul_right _
  have h2 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hg.pos)).mpr h1
  have h3 := (ZMod.natCast_eq_natCast_iff' 1 (g ^ (k + 1)) p).mpr h2
  push_cast at h3
  exact h3.symm

theorem ordOK_dvd {d g p k : ℕ} (hp : p.Prime) (hg : g.Prime) (h : ordOK d g p = true)
    (hdiv : p ∣ σ 1 (g ^ k)) : d ∣ k + 1 := by
  unfold ordOK at h
  split at h
  · rename_i h1
    have hd : d = p := by simpa using h
    subst hd
    have hg1 : ((g : ZMod d)) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff' g 1 d).mpr (by
        rw [beq_iff_eq] at h1; rw [h1]; exact (Nat.mod_eq_of_lt hp.one_lt).symm)
      simpa using this
    have hs : ((σ 1 (g ^ k) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    rw [sigma_one_apply_prime_pow hg] at hs
    push_cast at hs
    simp only [hg1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
    exact (ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast hs)
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hd1, hpow⟩, hprod⟩, hprime⟩, hnot⟩ := h
    have cast_one : ∀ e, powModE g e p = 1 % p → ((g : ZMod p)) ^ e = 1 := by
      intro e he
      rw [powModE_eq] at he
      have := (ZMod.natCast_eq_natCast_iff' (g ^ e) 1 p).mpr he
      push_cast at this
      exact this
    have hord : orderOf ((g : ZMod p)) = d := by
      refine orderOf_eq_of_pow_and_pow_div_prime (by omega) (cast_one d hpow) ?_
      intro r hr hrd hone
      have hmem := mem_of_dvd_prod hr (fun a ha => primeB_sound (hprime a ha)) (by rw [hprod]; exact hrd)
      apply hnot r hmem
      rw [powModE_eq]
      have := (ZMod.natCast_eq_natCast_iff' (g ^ (d / r)) 1 p).mp (by push_cast; exact hone)
      exact this
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (pow_eq_one_of_dvd_sigma hg hdiv)

/-! ## Allowed exponents -/

private theorem nextAux_le {isQ : Bool} {D : ℕ} {no3 : Bool} : ∀ f j n, nextAux isQ D no3 f j = some n →
    ∀ i, j ≤ i → allowedB isQ D no3 (D * i) = true → n ≤ D * i
  | 0, _, _, h, _, _, _ => by cases h
  | f + 1, j, n, h, i, hi, ha => by
    unfold nextAux at h
    split at h
    · rename_i hj
      cases h
      exact Nat.mul_le_mul_left _ hi
    · rename_i hj
      rcases Nat.eq_or_lt_of_le hi with rfl | hi
      · exact absurd ha hj
      · exact nextAux_le f (j + 1) n h i hi ha

theorem nextAllowed_le {isQ : Bool} {D : ℕ} {no3 : Bool} {s n m : ℕ}
    (h : nextAllowed isQ D no3 s = some n) (hm : allowedB isQ D no3 m = true) (hD : D ∣ m)
    (hs : s ≤ m) : n ≤ m := by
  unfold nextAllowed at h
  split at h
  · cases h
  · rename_i hD0
    have hD0 : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · subst h0; simp at hD0
      · exact h0
    obtain ⟨i, rfl⟩ := hD
    refine nextAux_le 64 _ n h i ?_ hm
    have : (s + D - 1) / D < i + 1 := by
      rw [Nat.div_lt_iff_lt_mul hD0]
      have e : (i + 1) * D = D * i + D := by ring
      rw [e]
      generalize D * i = t at hs
      omega
    omega

theorem allowed_of_role {isQ : Bool} {D : ℕ} {no3 : Bool} {kmin : ℕ} {ex : Bool} {k : ℕ}
    {hq : Prop} (hr : RoleHolds (.fr isQ D no3 kmin ex) k hq) {L : ℕ} (hL : L ∣ k + 1) :
    allowedB isQ L no3 (k + 1) = true := by
  obtain ⟨-, -, -, h3, -, h4, h5⟩ := hr
  have hA : (k + 1) % L = 0 := Nat.mod_eq_zero_of_dvd hL
  have hB : no3 = true → (k + 1) % 3 ≠ 0 := fun h h' => h3 h (Nat.dvd_of_mod_eq_zero h')
  cases isQ
  · obtain ⟨⟨j, hj⟩, h6⟩ := h5 rfl
    have h1 : (k + 1) % 2 = 1 := by omega
    have h2 : 5 ≤ k + 1 := by omega
    cases no3
    · simp [allowedB, hA, h1, h2]
    · simp [allowedB, hA, h1, h2, hB rfl]
  · have h1 := h4 rfl
    cases no3
    · simp [allowedB, hA, h1]
    · simp [allowedB, hA, h1, hB rfl]

theorem infeasible_false {r : Role} {k d : ℕ} {hq : Prop} (hr : RoleHolds r k hq)
    (hd : d ∣ k + 1) (h : infeasibleB r d = true) : False := by
  cases r with
  | sq => cases h
  | fr isQ D no3 kmin ex =>
    obtain ⟨hiq, hD, -, h3, hex, h4, h5⟩ := hr
    have hL : Nat.lcm D d ∣ k + 1 := Nat.lcm_dvd hD hd
    simp only [infeasibleB, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      Bool.not_eq_true'] at h
    rcases h with ((⟨he, h⟩ | ⟨hi, h⟩) | ⟨hi, h⟩) | ⟨hn, h⟩
    · rw [← hex he] at h
      exact h (Nat.mod_eq_zero_of_dvd hL)
    · have := h4 hi
      have : 4 ∣ k + 1 := (Nat.dvd_of_mod_eq_zero h).trans hL
      omega
    · obtain ⟨j, hj⟩ := (h5 hi).1
      have : 2 ∣ k + 1 := (Nat.dvd_of_mod_eq_zero h).trans hL
      omega
    · exact h3 hn ((Nat.dvd_of_mod_eq_zero h).trans hL)

/-! ## Meaning of pending items and preservation of `Holds` -/

/-- The meaning of the pending list: each entry `(p, c, w)` has a key `c`, `w ≥ 1`, and
`p ^ w ∣ σ(c ^ v_c(N))`; the pairs `(p, c)` are distinct. The number `p` need not be prime. -/
def PendOK (N : ℕ) (ks : List Key) (pend : List (ℕ × ℕ × ℕ)) : Prop :=
  (∀ e ∈ pend, e.2.1 ∈ ks.map Key.p ∧ 1 ≤ e.2.2 ∧
    e.1 ^ e.2.2 ∣ σ 1 (e.2.1 ^ N.factorization e.2.1)) ∧ (pend.map pk).Nodup

variable {P : Params} {N q : ℕ}

private theorem pendOK_nil {ks : List Key} : PendOK N ks [] := ⟨by simp, List.nodup_nil⟩

private theorem pendOK_mono {ks ks' : List Key} (h : ∀ a ∈ ks.map Key.p, a ∈ ks'.map Key.p)
    {pend : List (ℕ × ℕ × ℕ)} (hP : PendOK N ks pend) : PendOK N ks' pend :=
  ⟨fun e he => let ⟨a, b, c⟩ := hP.1 e he; ⟨h _ a, b, c⟩, hP.2⟩

private theorem keyHolds_mono {ks ks' : List Key} (h : ∀ a ∈ ks.map Key.p, a ∈ ks'.map Key.p) {k : Key}
    (hk : KeyHolds N q ks k) : KeyHolds N q ks' k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk
  exact ⟨h1, h2, h3, fun e he => let ⟨a, b, c, d⟩ := h4 e he; ⟨a, b, h _ c, d⟩, h5⟩

private theorem key_prime {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) {c : ℕ}
    (hc : c ∈ ks.map Key.p) : c.Prime ∧ c ∣ N := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  exact ⟨(hH.2.1 k hk).1, (hH.2.1 k hk).2.1⟩

private theorem keyHolds_setW {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) {kp : Key} (hkp : kp ∈ ks)
    {c w : ℕ} (hc : c ∈ ks.map Key.p) (hw : kp.p ^ w ∣ σ 1 (c ^ N.factorization c)) :
    KeyHolds N q ks ⟨kp.p, kp.role, setW c w kp.cs⟩ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH.2.1 kp hkp
  refine ⟨h1, h2, h3, fun e he => ?_, setW_nodup _ _ h5⟩
  rcases mem_setW _ _ he with rfl | he
  · exact ⟨(key_prime hH hc).1, (key_prime hH hc).2, hc, hw⟩
  · exact h4 e he

private theorem holds_replace {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) {kp : Key} (hkp : kp ∈ ks)
    {c w : ℕ} (hc : c ∈ ks.map Key.p) (hw : kp.p ^ w ∣ σ 1 (c ^ N.factorization c)) :
    Holds P N q (replaceKey ⟨kp.p, kp.role, setW c w kp.cs⟩ ks) x := by
  have hm := replaceKey_map ⟨kp.p, kp.role, setW c w kp.cs⟩ ks
  have hsub : ∀ a ∈ ks.map Key.p, a ∈ (replaceKey ⟨kp.p, kp.role, setW c w kp.cs⟩ ks).map Key.p :=
    fun a ha => by rw [hm]; exact ha
  refine ⟨hH.1, fun k hk => ?_, by rw [hm]; exact hH.2.2.1,
    fun p hp hpx hpN => hsub _ (hH.2.2.2 p hp hpx hpN)⟩
  rcases mem_replaceKey _ hk with rfl | hk
  · exact keyHolds_mono hsub (keyHolds_setW hH hkp hc hw)
  · exact keyHolds_mono hsub (hH.2.1 k hk)

private theorem holds_setRole {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) {p : ℕ} {r : Role}
    (hr : RoleHolds r (N.factorization p) (p = q)) : Holds P N q (setRole p r ks) x := by
  have hm := setRole_map p r ks
  have hsub : ∀ a ∈ ks.map Key.p, a ∈ (setRole p r ks).map Key.p := fun a ha => by rw [hm]; exact ha
  refine ⟨hH.1, fun k hk => ?_, by rw [hm]; exact hH.2.2.1,
    fun p hp hpx hpN => hsub _ (hH.2.2.2 p hp hpx hpN)⟩
  rcases mem_setRole p r hk with hk | ⟨k0, hk0, h0, rfl⟩
  · exact keyHolds_mono hsub (hH.2.1 k hk)
  · obtain ⟨h1, h2, -, h4, h5⟩ := hH.2.1 k0 hk0
    subst h0
    exact keyHolds_mono hsub ⟨h1, h2, hr, h4, h5⟩

private theorem holds_insert {ks : List Key} {x x' : ℕ} (hH : Holds P N q ks x) {f : ℕ} {r : Role}
    {cs : List (ℕ × ℕ)} (hf : f.Prime) (hfN : f ∣ N) (hfk : f ∉ ks.map Key.p)
    (hr : RoleHolds r (N.factorization f) (f = q))
    (hcs : ∀ e ∈ cs, e.1.Prime ∧ e.1 ∣ N ∧ e.1 ∈ ks.map Key.p ∧
      f ^ e.2 ∣ σ 1 (e.1 ^ N.factorization e.1))
    (hnd : (cs.map Prod.fst).Nodup)
    (hx : ∀ p, p.Prime → p < x' → p ∣ N → p ∈ ks.map Key.p ∨ p = f) :
    Holds P N q (insertKey ⟨f, r, cs⟩ ks) x' := by
  have hperm := insertKey_perm ⟨f, r, cs⟩ ks
  have hmem : ∀ a, a ∈ (insertKey ⟨f, r, cs⟩ ks).map Key.p ↔ a = f ∨ a ∈ ks.map Key.p := by
    intro a
    rw [(hperm.map Key.p).mem_iff]
    simp
  refine ⟨hH.1, fun k hk => ?_, ?_, fun p hp hpx hpN => ?_⟩
  · rcases List.mem_cons.mp (hperm.mem_iff.mp hk) with rfl | hk
    · exact ⟨hf, hfN, hr, fun e he => let ⟨a, b, c, d⟩ := hcs e he;
        ⟨a, b, (hmem _).mpr (Or.inr c), d⟩, hnd⟩
    · exact keyHolds_mono (fun a ha => (hmem a).mpr (Or.inr ha)) (hH.2.1 k hk)
  · rw [(hperm.map Key.p).nodup_iff]
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨hfk, hH.2.2.1⟩
  · rcases hx p hp hpx hpN with h | h
    · exact (hmem p).mpr (Or.inr h)
    · exact (hmem p).mpr (Or.inl h)

private theorem mem_insertKey_map {k : Key} {ks : List Key} {a : ℕ} (h : a ∈ ks.map Key.p) :
    a ∈ (insertKey k ks).map Key.p := by
  rw [((insertKey_perm k ks).map Key.p).mem_iff]
  exact List.mem_cons_of_mem _ h

/-! ## Budgets -/

private theorem csum_le_aux {p : ℕ} (hp : p.Prime) (hN0 : N ≠ 0) : ∀ l : List (ℕ × ℕ),
    (l.map Prod.fst).Nodup →
    (∀ e ∈ l, e.1.Prime ∧ e.1 ∣ N ∧ p ^ e.2 ∣ σ 1 (e.1 ^ N.factorization e.1)) →
    (l.map Prod.fst).toFinset ⊆ N.primeFactors ∧
      csum l ≤ ∑ c ∈ (l.map Prod.fst).toFinset, sigmaWeight N c p
  | [], _, _ => by simp [csum]
  | e :: l, hnd, he => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ih := csum_le_aux hp hN0 l hnd.2 (fun e' h' => he e' (List.mem_cons_of_mem _ h'))
    obtain ⟨h1, h2, h3⟩ := he e (List.mem_cons_self ..)
    have hw : e.2 ≤ sigmaWeight N e.1 p :=
      (hp.pow_dvd_iff_le_factorization (sigma_pos 1 _ (pow_ne_zero _ h1.ne_zero)).ne').mp h3
    change _ ∧ e.2 + csum l ≤ _
    simp only [List.map_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hnd.1)]
    exact ⟨Finset.insert_subset (Nat.mem_primeFactors.mpr ⟨h1, h2, hN0⟩) ih.1, by omega⟩

theorem csum_le (hN : OddPerfect N) {ks : List Key} {k : Key} (hk : KeyHolds N q ks k) :
    csum k.cs ≤ N.factorization k.p := by
  obtain ⟨hp, hpN, -, h4, h5⟩ := hk
  have hp2 : k.p ≠ 2 := by
    rintro h2
    rw [h2] at hpN
    exact hN.not_two_dvd hpN
  obtain ⟨hsub, hle⟩ := csum_le_aux hp hN.ne_zero k.cs h5 (fun e he =>
    ⟨(h4 e he).1, (h4 e he).2.1, (h4 e he).2.2.2⟩)
  rw [← sigmaWeight_sum_eq hN.perfect hp hp2]
  exact hle.trans (Finset.sum_le_sum_of_subset hsub)

/-! ## Items -/

/-- The meaning of the result of applying items. -/
def ResOK (P : Params) (N q x : ℕ) : Res → Prop
  | .rej => True
  | .contra => False
  | .ok ks pend => Holds P N q ks x ∧ PendOK N ks pend

private theorem applyOne_sound {pr : ℕ → Bool} (hpr : ∀ n, pr n = true → n.Prime) {x c p e : ℕ}
    {ks : List Key} {pend : List (ℕ × ℕ × ℕ)} {K : List Key → List (ℕ × ℕ × ℕ) → Res}
    (hK : ∀ ks' pend', Holds P N q ks' x → PendOK N ks' pend' → ResOK P N q x (K ks' pend'))
    (hH : Holds P N q ks x) (hP : PendOK N ks pend) :
    ResOK P N q x (applyOne pr x c p e ks pend K) := by
  have hOP := hH.1.1
  unfold applyOne
  cases h1 : (Nat.ble 1 e && Nat.beq (Nat.mod p 2) 1)
  · trivial
  simp only [Bool.and_eq_true] at h1
  have he : 1 ≤ e := ble_iff.mp h1.1
  have hp2 : p % 2 = 1 := beq_iff.mp h1.2
  simp only [cond_true]
  cases hf : findKey p ks with
  | some kp =>
    obtain ⟨hkp, hkpp⟩ := findKey_some hf
    subst hkpp
    dsimp only
    cases hg : gdivB ks c (kp.p ^ (Nat.add (lookupW c kp.cs) e))
    · trivial
    obtain ⟨hc, hdvd⟩ := gdivB_sound hH.2.1 hg
    simp only [cond_true]
    cases hob : overBudget ⟨kp.p, kp.role, setW c (Nat.add (lookupW c kp.cs) e) kp.cs⟩
    · exact hK _ _ (holds_replace hH hkp hc hdvd)
        (pendOK_mono (fun a ha => by rw [replaceKey_map]; exact ha) hP)
    · have hk' := keyHolds_setW hH hkp hc hdvd
      have hle := csum_le hOP hk'
      obtain ⟨-, -, hr, -, -⟩ := hk'
      simp only [overBudget] at hob hle hr
      revert hob hle hr
      cases kp.role with
      | sq =>
        intro hob hle hr
        have := blt_iff.mp hob
        have := hr.2
        omega
      | fr isQ D no3 kmin ex =>
        intro hob hle hr
        simp only [Bool.and_eq_true] at hob
        have := blt_iff.mp hob.2
        have := hr.2.2.2.2.1 hob.1
        omega
  | none =>
    dsimp only
    cases hg : gdivB ks c (p ^ (Nat.add (lookupP p c pend) e))
    · trivial
    obtain ⟨hc, hdvd⟩ := gdivB_sound hH.2.1 hg
    simp only [cond_true]
    cases hlt : Nat.blt p x
    · simp only [cond_false]
      refine hK _ _ hH ⟨fun e' he' => ?_, setP_nodup _ _ _ hP.2⟩
      rcases mem_setP _ _ _ he' with rfl | he'
      · exact ⟨hc, by simp only [Nat.add_eq]; omega, hdvd⟩
      · exact hP.1 e' he'
    · simp only [cond_true]
      cases hprp : pr p
      · trivial
      · simp only [cond_true]
        have hpp := hpr p hprp
        obtain ⟨hcp, hcN⟩ := key_prime hH hc
        have hpd : p ∣ σ 1 (c ^ N.factorization c) :=
          (dvd_pow_self p (by simp only [Nat.add_eq]; omega)).trans hdvd
        have hpN := OPNStarter.force_prime hOP.perfect hcp rfl hpp (by omega) hpd
        exact findKey_none hf (hH.2.2.2 p hpp (blt_iff.mp hlt) hpN)

theorem applyItems_sound {pr : ℕ → Bool} (hpr : ∀ n, pr n = true → n.Prime) {x c : ℕ} :
    ∀ (items : List (ℕ × ℕ)) (ks : List Key) (pend : List (ℕ × ℕ × ℕ)),
      Holds P N q ks x → PendOK N ks pend → ResOK P N q x (applyItems pr x c items ks pend)
  | [], _, _, hH, hP => ⟨hH, hP⟩
  | _ :: rest, _, _, hH, hP =>
    applyOne_sound hpr (fun ks' pend' hH' hP' => applyItems_sound hpr rest ks' pend' hH' hP') hH hP

/-! ## Exceptions and the special prime -/

/-- The exceptional prime factors of `N`. -/
def excSet (N q : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2

/-- An exception key. -/
def isExcB (k : Key) : Bool :=
  match k.role with
  | .fr false _ _ _ _ => true
  | _ => false

private theorem nexc_eq : ∀ ks : List Key, nexc ks = (ks.filter isExcB).length
  | [] => rfl
  | ⟨p, role, cs⟩ :: ks => by
    rw [List.filter_cons]
    cases role with
    | sq => simp [nexc, isExcB, nexc_eq ks]
    | fr isQ D no3 kmin ex =>
      cases isQ
      · simp [nexc, isExcB, nexc_eq ks]; omega
      · simp [nexc, isExcB, nexc_eq ks]

private theorem exc_sub {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) :
    ((ks.filter isExcB).map Key.p).toFinset ⊆ excSet N q := by
  intro a ha
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at ha
  obtain ⟨⟨kp, role, kcs⟩, ⟨hk, hex⟩, rfl⟩ := ha
  obtain ⟨hp, hpN, hr, -, -⟩ := hH.2.1 _ hk
  refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpN, hH.1.1.ne_zero⟩, ?_⟩
  cases role with
  | sq => simp [isExcB] at hex
  | fr isQ D no3 kmin ex =>
    cases isQ
    · obtain ⟨hiq, -, -, -, -, -, h5⟩ := hr
      refine ⟨fun h => absurd (hiq.mpr h) (by decide), ?_⟩
      have := (h5 rfl).2
      omega
    · simp [isExcB] at hex

private theorem exc_new {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) {f : ℕ} (hf : f ∈ excSet N q)
    (hfk : f ∉ ks.map Key.p) : nexc ks + 1 ≤ P.E := by
  have hnd : ((ks.filter isExcB).map Key.p).Nodup :=
    hH.2.2.1.sublist ((List.filter_sublist).map _)
  have hfT : f ∉ ((ks.filter isExcB).map Key.p).toFinset := by
    intro h
    simp only [List.mem_toFinset] at h
    exact hfk (((List.filter_sublist).map _).subset h)
  have hsub : insert f ((ks.filter isExcB).map Key.p).toFinset ⊆ excSet N q :=
    Finset.insert_subset hf (exc_sub hH)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hfT, List.toFinset_card_of_nodup hnd, List.length_map,
    ← nexc_eq] at h1
  exact h1.trans hH.1.2.2.2.2.1

theorem exc_all {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) (hE : nexc ks = P.E) {f : ℕ}
    (hf : f ∈ excSet N q) : f ∈ ks.map Key.p := by
  by_contra h
  have := exc_new hH hf h
  omega

theorem qDec_key {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) (h : qDec ks = true) :
    q ∈ ks.map Key.p := by
  unfold qDec at h
  obtain ⟨⟨kp, role, kcs⟩, hk, hr⟩ := List.any_eq_true.mp h
  obtain ⟨-, -, hrole, -, -⟩ := hH.2.1 _ hk
  refine List.mem_map.mpr ⟨_, hk, ?_⟩
  cases role with
  | sq => simp at hr
  | fr isQ D no3 kmin ex =>
    cases isQ
    · simp at hr
    · exact hrole.1.mp rfl

private theorem exists_two {s : Finset ℕ} (h : s.card ≤ 2) : ∃ r₁ r₂, ∀ p ∈ s, p = r₁ ∨ p = r₂ := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, 0, by simp⟩
  rcases (s.erase a).eq_empty_or_nonempty with he | ⟨b, hb⟩
  · refine ⟨a, a, fun p hp => Or.inl ?_⟩
    by_contra hne
    have : p ∈ s.erase a := Finset.mem_erase.mpr ⟨hne, hp⟩
    rw [he] at this
    simp at this
  · refine ⟨a, b, fun p hp => ?_⟩
    by_cases hpa : p = a
    · exact Or.inl hpa
    · right
      have h1 : (s.erase a).card ≤ 1 := by rw [Finset.card_erase_of_mem ha]; omega
      exact Finset.card_le_one.mp h1 p (Finset.mem_erase.mpr ⟨hpa, hp⟩) b hb

/-- With exponent 2 at 3 the family of the parameters gives the family `Fam`. -/
theorem fam_of_famV {P : Params} (hF : FamV P N q) (h : P.V3 = 2) : Fam P.E N q :=
  ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1.trans h, hF.2.2.2.2.1⟩

/-- The landed facts are used only with exponent 2 at 3. -/
theorem lan_spec {P : Params} (h : P.lan = true) : P.landed = true ∧ P.V3 = 2 := by
  simpa [Params.lan] using h

/-- With at most two exceptions they can be named. -/
theorem named_two {E : ℕ} (hF : Fam E N q) (hE : E ≤ 2) :
    ∃ r₁ r₂, ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2 := by
  obtain ⟨r₁, r₂, h⟩ := exists_two (hF.2.2.2.2.trans hE)
  refine ⟨r₁, r₂, fun p hp hpq h1 h2 => ?_⟩
  by_contra hv
  rcases h p (Finset.mem_filter.mpr ⟨hp, hpq, hv⟩) with h | h
  · exact h1 h
  · exact h2 h

private theorem nine_dvd_sigma_five {q : ℕ} (hq : q.Prime) (h3 : q % 3 = 2) : 9 ∣ σ 1 (q ^ 5) := by
  rw [sigma_one_apply_prime_pow hq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  apply (ZMod.natCast_eq_zero_iff _ 9).mp
  have h9 : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
  have hc : (q : ZMod 9) = ((q % 9 : ℕ) : ZMod 9) := (ZMod.natCast_mod q 9).symm
  push_cast
  rcases h9 with h | h | h <;> rw [hc, h] <;> decide

/-! ## Roles -/

private theorem mem_rolesOf_q {ks : List Key} {f : ℕ}
    (hc : (!qDec ks && f % 4 == 1 && (!P.lan || (f != 5 && f % 9 != 8))) = true) {r : Role}
    (hr : r ∈ (if f % 3 == 1 then [Role.fr true 2 true 1 false, .fr true 6 false 5 false]
      else [.fr true 2 P.lan 1 false])) : r ∈ rolesOf P ks f := by
  unfold rolesOf
  rw [if_pos hc]
  exact List.mem_append_left _ (List.mem_append_right _ hr)

private theorem mem_rolesOf_e {ks : List Key} {f : ℕ} (hc : nexc ks < P.E)
    (hn : (P.e4 && f != 3) = false) {r : Role}
    (hr : r ∈ (if f % 3 == 1 then [Role.fr false 1 true 4 false, .fr false 3 false 8 false]
      else [.fr false 1 false 4 false])) : r ∈ rolesOf P ks f := by
  unfold rolesOf
  rw [if_pos hc, if_neg (show ¬ (P.e4 && f != 3) = true by simp [hn])]
  exact List.mem_append_right _ hr

private theorem mem_rolesOf_e4 {ks : List Key} {f : ℕ} (hc : nexc ks < P.E)
    (hn : (P.e4 && f != 3) = true) : Role.fr false 5 true 4 true ∈ rolesOf P ks f := by
  unfold rolesOf
  rw [if_pos hc, if_pos hn]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Exhaustiveness of the roles: a prime factor of `N` that is not a key has one of the roles
listed by `rolesOf`. The landed facts on the special prime are used only when `P.lan` (they need
`P.E ≤ 2` and exponent 2 at 3). When `P.e4`, a prime other than 3 with exponent other than 2
has exponent 4 by the family `FamV`. -/
theorem roles_exh (hL : P.landed = true → P.E ≤ 2) {ks : List Key} {x : ℕ}
    (hH : Holds P N q ks x) {f : ℕ} (hf : f.Prime) (hfN : f ∣ N) (hfk : f ∉ ks.map Key.p) :
    ∃ r ∈ rolesOf P ks f, RoleHolds r (N.factorization f) (f = q) := by
  obtain ⟨hOP, hq, hodd, h3, -⟩ := hH.1
  have hk1 : 1 ≤ N.factorization f := (hf.dvd_iff_one_le_factorization hOP.ne_zero).mp hfN
  by_cases hfq : f = q
  · subst hfq
    obtain ⟨hq4, hk4⟩ := special_mod_four hOP hq hodd
    have hqD : qDec ks = false := by
      cases h : qDec ks
      · rfl
      · exact absurd (qDec_key hH h) hfk
    have hf3 : f ≠ 3 := fun h => hH.1.2.2.2.2.2.1 h.symm
    have hland : P.lan = true → f ≠ 5 ∧ f % 9 ≠ 8 ∧ (f % 3 = 2 → ¬ 3 ∣ N.factorization f + 1) := by
      intro hl
      obtain ⟨hl1, hl2⟩ := lan_spec hl
      have h3 := h3.trans hl2
      obtain ⟨r₁, r₂, hsq⟩ := named_two (fam_of_famV hH.1 hl2) (hL hl1)
      refine ⟨?_, fun h9 => two_exceptions_three_ne_two_of_mod_nine hOP hq hodd h9 hsq h3,
        fun h32 h3d => ?_⟩
      · rintro rfl
        exact two_exceptions_five_three_ne_two hOP hodd hsq h3
      · refine two_exceptions_three_ne_two_of_nine_dvd hOP hq hodd h32 ?_ hsq h3
        refine (nine_dvd_sigma_five hq h32).trans (OPNExample.sigma_prime_pow_dvd hq ?_)
        obtain ⟨j, hj⟩ := hodd
        omega
    have hc : (!qDec ks && f % 4 == 1 && (!P.lan || (f != 5 && f % 9 != 8))) = true := by
      cases hl : P.lan
      · simp [hqD, hq4]
      · obtain ⟨h5, h9, -⟩ := hland hl
        simp [hqD, hq4, h5, h9]
    obtain ⟨j, hj⟩ := hodd
    by_cases hm3 : f % 3 = 1
    · by_cases h3k : 3 ∣ N.factorization f + 1
      · refine ⟨.fr true 6 false 5 false, mem_rolesOf_q hc (by simp [hm3]), ?_⟩
        refine ⟨by simp, ?_, ?_, by simp, by simp, fun _ => by omega, by simp⟩
        · omega
        · omega
      · refine ⟨.fr true 2 true 1 false, mem_rolesOf_q hc (by simp [hm3]), ?_⟩
        exact ⟨by simp, ⟨j + 1, by omega⟩, hk1, fun _ => h3k, by simp, fun _ => by omega, by simp⟩
    · refine ⟨.fr true 2 P.lan 1 false, mem_rolesOf_q hc (by simp [hm3]), ?_⟩
      refine ⟨by simp, ⟨j + 1, by omega⟩, hk1, fun hl => ?_, by simp, fun _ => by omega, by simp⟩
      have : f % 3 ≠ 0 := fun h => hf3
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hf).mp (Nat.dvd_of_mod_eq_zero h)).symm
      exact (hland hl).2.2 (by omega)
  · by_cases hk2 : N.factorization f = 2
    · exact ⟨.sq, by simp [rolesOf], hfq, hk2⟩
    have hfe : f ∈ excSet N q :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hf, hfN, hOP.ne_zero⟩, hfq, hk2⟩
    have hn := exc_new hH hfe hfk
    have hev := even_factorization_of_ne hOP hq hodd hf hfq
    obtain ⟨j, hj⟩ := hev
    have hiq : (false = true ↔ f = q) := iff_of_false (by decide) hfq
    cases he4 : (P.e4 && f != 3)
    case true =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at he4
      have hv4 := hH.1.2.2.2.2.2.2 he4.1 f (Nat.mem_primeFactors.mpr ⟨hf, hfN, hOP.ne_zero⟩) hfq
        he4.2 hk2
      refine ⟨.fr false 5 true 4 true, mem_rolesOf_e4 (by omega) (by simp [he4]), ?_⟩
      rw [hv4]
      exact ⟨hiq, dvd_rfl, le_rfl, fun _ => by decide, fun _ => rfl, by simp,
        fun _ => ⟨⟨2, rfl⟩, le_rfl⟩⟩
    by_cases hm3 : f % 3 = 1
    · by_cases h3k : 3 ∣ N.factorization f + 1
      · refine ⟨.fr false 3 false 8 false, mem_rolesOf_e (by omega) he4 (by simp [hm3]), ?_⟩
        refine ⟨hiq, h3k, by omega, by simp, by simp, by simp, fun _ => ⟨⟨j, hj⟩, by omega⟩⟩
      · refine ⟨.fr false 1 true 4 false, mem_rolesOf_e (by omega) he4 (by simp [hm3]), ?_⟩
        exact ⟨hiq, one_dvd _, by omega, fun _ => h3k, by simp, by simp,
          fun _ => ⟨⟨j, hj⟩, by omega⟩⟩
    · refine ⟨.fr false 1 false 4 false, mem_rolesOf_e (by omega) he4 (by simp [hm3]), ?_⟩
      exact ⟨hiq, one_dvd _, by omega, by simp, by simp, by simp, fun _ => ⟨⟨j, hj⟩, by omega⟩⟩

/-! ## The receipt rule -/

/-- A prime `p ≡ 2 (mod 3)` of `N` receives from a free prime: a square `c` sends only to `3`
and to primes `≡ 1 (mod 3)`. When the special prime is a key and all `E` exceptions are listed,
every free prime is a key. -/
theorem receipt_exists {ks : List Key} {x : ℕ} (hH : Holds P N q ks x) (hqd : qDec ks = true)
    (hE : nexc ks = P.E) {p : ℕ} (hpk : p ∈ ks.map Key.p) (hp3 : p % 3 = 2) :
    ∃ g ∈ freeOthers ks p, p ∣ σ 1 (g ^ N.factorization g) := by
  obtain ⟨hp, hpN⟩ := key_prime hH hpk
  have hOP := hH.1.1
  have hp2 : p ≠ 2 := by rintro rfl; exact hOP.not_two_dvd hpN
  have hv : N.factorization p ≠ 0 :=
    (Nat.one_le_iff_ne_zero.mp ((hp.dvd_iff_one_le_factorization hOP.ne_zero).mp hpN))
  rw [← sigmaWeight_sum_eq hOP.perfect hp hp2] at hv
  obtain ⟨c, hc, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have hcd : p ∣ σ 1 (c ^ N.factorization c) := Nat.dvd_of_factorization_pos hw
  obtain ⟨hcp, hcN, -⟩ := Nat.mem_primeFactors.mp hc
  have hcne : c ≠ p := by
    rintro rfl
    exact hw (sigmaWeight_self hcp)
  have hfree : c = q ∨ N.factorization c ≠ 2 := by
    by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    rw [hcon.2, sigma_prime_sq hcp] at hcd
    have := prime_dvd_phi3_mod_three hp (by omega) hcd
    omega
  have hck : c ∈ ks.map Key.p := by
    by_cases hcq : c = q
    · rw [hcq]; exact qDec_key hH hqd
    · exact exc_all hH hE (Finset.mem_filter.mpr ⟨hc, hcq, hfree.resolve_left hcq⟩)
  obtain ⟨⟨kp, role, kcs⟩, hkc, hkp⟩ := List.mem_map.mp hck
  simp only at hkp
  subst hkp
  obtain ⟨-, -, hr, -, -⟩ := hH.2.1 _ hkc
  refine ⟨kp, ?_, hcd⟩
  cases role with
  | sq => exact hfree.elim (fun h => absurd h hr.1) (fun h => absurd hr.2 h)
  | fr isQ D no3 kmin ex =>
    refine List.mem_filterMap.mpr ⟨_, hkc, ?_⟩
    simp [hcne]

/-! ## Rule L -/

private theorem findKey_isSome {p : ℕ} {ks : List Key} (h : p ∈ ks.map Key.p) : ∃ k, findKey p ks = some k := by
  cases hf : findKey p ks with
  | none => exact absurd h (findKey_none hf)
  | some k => exact ⟨k, rfl⟩

/-- Rule L: by `false_of_three_sq_of_index_three` some prime of `L` dividing `N`, other than
`q`, has `3 ∤ v + 1`; it is an exception. If every listed exception in `L` has `3 ∣ D` and no
unlisted one can appear, this fails. -/
theorem landedL_false {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    (h : landedLB P ks x = true) : False := by
  unfold landedLB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hlan, -⟩, hall⟩, hcomp⟩ := h
  obtain ⟨hOP, hq, hodd, h3, -⟩ := hH.1
  have h3 := h3.trans (lan_spec hlan).2
  refine false_of_three_sq_of_index_three hOP hq hodd h3 (fun p hpL hpN hpq => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpL
  have hpL' : p ∈ LSET := by
    simp only [LSET, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hp : p.Prime := by
    rcases hpL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  by_cases hv : N.factorization p = 2
  · rw [hv]
  have hpe : p ∈ excSet N q :=
    Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpN, hOP.ne_zero⟩, hpq, hv⟩
  have hpk : p ∈ ks.map Key.p := by
    rcases hcomp with hE | hall2
    · exact exc_all hH hE hpe
    · rcases hall2 p hpL' with h | h
      · exact hH.2.2.2 p hp h hpN
      · exact isKey_iff.mp h
  obtain ⟨k, hfk⟩ := findKey_isSome hpk
  obtain ⟨hk, hkp⟩ := findKey_some hfk
  have hap := hall p hpL'
  rw [hfk] at hap
  obtain ⟨kp, role, kcs⟩ := k
  simp only at hkp
  subst hkp
  obtain ⟨-, -, hr, -, -⟩ := hH.2.1 _ hk
  cases role with
  | sq => exact absurd hr.2 hv
  | fr isQ D no3 kmin ex =>
    cases isQ
    · simp only [beq_iff_eq] at hap
      exact (Nat.dvd_of_mod_eq_zero hap).trans hr.2.1
    · exact absurd (hr.1.mp rfl) hpq

/-! ## The abundant rule -/

private theorem sig_eq {p : ℕ} (hp : p.Prime) (e : ℕ) : sig p e = σ 1 (p ^ e) := by
  unfold sig
  rw [← sigma_prime_pow_mul_pred hp]
  exact Nat.mul_div_cancel _ (by have := hp.two_le; omega)

private theorem abPair_spec (hN0 : N ≠ 0) : ∀ l : List Key,
    (∀ k ∈ l, k.p.Prime ∧ abExp P k.role ≤ N.factorization k.p) → (l.map Key.p).Nodup →
    (abPair P l).2 ∣ N ∧ σ 1 (abPair P l).2 = (abPair P l).1 ∧
      ∀ r, r.Prime → r ∉ l.map Key.p → ¬ r ∣ (abPair P l).2
  | [], _, _ => by
    refine ⟨one_dvd _, by simp [abPair], fun r hr _ hd => ?_⟩
    exact hr.one_lt.ne' (Nat.dvd_one.mp hd)
  | k :: l, h, hnd => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, he⟩ := h k (List.mem_cons_self ..)
    obtain ⟨ih1, ih2, ih3⟩ := abPair_spec hN0 l (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')) hnd.2
    have hcop : Nat.Coprime (k.p ^ abExp P k.role) (abPair P l).2 :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr (ih3 k.p hp hnd.1))
    simp only [abPair]
    refine ⟨hcop.mul_dvd_of_dvd_of_dvd ((hp.pow_dvd_iff_le_factorization hN0).mpr he) ih1, ?_,
      fun r hr hrn hd => ?_⟩
    · rw [isMultiplicative_sigma.map_mul_of_coprime hcop, ih2, sig_eq hp]
    · simp only [List.map_cons, List.mem_cons, not_or] at hrn
      rcases (Nat.Prime.dvd_mul hr).mp hd with hd | hd
      · exact hrn.1 ((Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hd))
      · exact ih3 r hr hrn.2 hd

theorem abundant_false {ks : List Key} {x : ℕ} (hH : Holds P N q ks x)
    (h : abundantB P ks = true) : False := by
  have hOP := hH.1.1
  have hkeys : ∀ k ∈ ks, k.p.Prime ∧ abExp P k.role ≤ N.factorization k.p := by
    intro k hk
    obtain ⟨hp, -, hr, -, -⟩ := hH.2.1 k hk
    refine ⟨hp, ?_⟩
    revert hr
    cases k.role with
    | sq => intro hr; simp [abExp, hr.2]
    | fr isQ D no3 kmin ex => intro hr; simp only [abExp]; exact (min_le_left _ _).trans hr.2.2.1
  obtain ⟨hd, hσ, -⟩ := abPair_spec (P := P) hOP.ne_zero ks hkeys hH.2.2.1
  simp only [abundantB, decide_eq_true_eq] at h
  have hlt : 2 * (abPair P ks).2 < σ 1 (abPair P ks).2 := hσ ▸ h
  rw [sigma_one_apply] at hlt
  have hab := (Nat.abundant_iff_sum_divisors.mpr hlt).of_dvd hd hOP.ne_zero
  exact ((Nat.perfect_iff_not_abundant_and_not_deficient hOP.pos.ne).mp hOP.perfect).1 hab

/-! ## Forcing -/

private theorem pmin_mem : ∀ l : List (ℕ × ℕ × ℕ), l ≠ [] → ∃ e ∈ l, e.1 = pmin l
  | [], h => absurd rfl h
  | [(p, c, w)], _ => ⟨(p, c, w), by simp, rfl⟩
  | (p, c, w) :: b :: t, _ => by
    obtain ⟨e, he, he1⟩ := pmin_mem (b :: t) (by simp)
    rw [show pmin ((p, c, w) :: b :: t) = min p (pmin (b :: t)) from rfl]
    rcases le_total p (pmin (b :: t)) with h | h
    · exact ⟨(p, c, w), List.mem_cons_self .., (min_eq_left h).symm⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, by rw [min_eq_right h]; exact he1⟩

private theorem mem_csOf {f : ℕ} {pend : List (ℕ × ℕ × ℕ)} {e' : ℕ × ℕ} (h : e' ∈ csOf f pend) :
    ∃ e ∈ pend, e.1 = f ∧ e' = (e.2.1, e.2.2) := by
  unfold csOf at h
  obtain ⟨e, he, h2⟩ := List.mem_filterMap.mp h
  by_cases hef : e.1 = f
  · simp only [hef, beq_self_eq_true, if_true, Option.some.injEq] at h2
    exact ⟨e, he, hef, h2.symm⟩
  · simp [hef] at h2

private theorem csOf_nodup {f : ℕ} : ∀ pend : List (ℕ × ℕ × ℕ), (pend.map pk).Nodup →
    ((csOf f pend).map Prod.fst).Nodup
  | [], _ => by simp [csOf]
  | e :: l, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    have ih := csOf_nodup (f := f) l h.2
    by_cases hef : e.1 = f
    · have : csOf f (e :: l) = (e.2.1, e.2.2) :: csOf f l := by simp [csOf, hef]
      rw [this, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      obtain ⟨e2, he2, hpe⟩ := List.mem_map.mp hm
      obtain ⟨e3, he3, h3, rfl⟩ := mem_csOf he2
      apply h.1
      refine List.mem_map.mpr ⟨e3, he3, ?_⟩
      simp only [pk, Prod.mk.injEq]
      exact ⟨h3.trans hef.symm, hpe⟩
    · have : csOf f (e :: l) = csOf f l := by simp [csOf, hef]
      rw [this]
      exact ih

/-! ## Steps -/

private theorem holds_of_scan {ks : List Key} {x y : ℕ} (hH : Holds P N q ks x) (hs : ScanP ks x y) :
    Holds P N q ks y :=
  ⟨hH.1, hH.2.1, hH.2.2.1, fun p hp hpy hpN => by
    by_cases hpx : p < x
    · exact hH.2.2.2 p hp hpx hpN
    · exact hs.2.2.2 p (by omega) hpy hp⟩

private theorem holds_succ {ks : List Key} {y : ℕ} (hH : Holds P N q ks y) (hyN : ¬ y ∣ N) :
    Holds P N q ks (y + 1) :=
  ⟨hH.1, hH.2.1, hH.2.2.1, fun p hp hpy hpN => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hpy with h | rfl
    · exact hH.2.2.2 p hp h hpN
    · exact absurd hpN hyN⟩

/-! ## Soundness of the checker -/

/-- The meaning of a checker context: each context says which states it refutes. -/
def CtxOK (P : Params) (N q : ℕ) : Ctx → Prop
  | .apply ks x pend _ => Holds P N q ks x → PendOK N ks pend → False
  | .out ks x pend => Holds P N q ks x → PendOK N ks pend → False
  | .roles ks x pend f cs rs => ∀ r ∈ rs, Holds P N q (insertKey ⟨f, r, cs⟩ ks) x →
      PendOK N (insertKey ⟨f, r, cs⟩ ks) pend → False
  | .senders ks x p gs => ∀ g ∈ gs, Holds P N q ks x → p.Prime →
      p ∣ σ 1 (g ^ N.factorization g) → False
  | .sender ks x p g => Holds P N q ks x → p.Prime → p ∣ σ 1 (g ^ N.factorization g) → False
  | .step ks x => Holds P N q ks x → False

theorem go_sound {pr : ℕ → Bool} {done : List Key → ℕ → Bool} (hdef : DefSound P)
    (hpr : ∀ n, pr n = true → n.Prime)
    (hdone : ∀ ks x, done ks x = true → Holds P N q ks x → False)
    (hL : P.landed = true → P.E ≤ 2) :
    ∀ (c : Cert) (ctx : Ctx), go P pr done ctx c = true → CtxOK P N q ctx := by
  intro c
  induction c with
  | leaf => intro ctx h; cases ctx <;> simp [go] at h
  | abundant =>
    intro ctx h
    cases ctx
    case out ks x pend =>
      intro hH _
      simp only [go] at h
      exact abundant_false hH h
    all_goals simp [go] at h
  | landedL =>
    intro ctx h
    cases ctx
    case out ks x pend =>
      intro hH _
      simp only [go] at h
      exact landedL_false hH h
    all_goals simp [go] at h
  | apply items out ih =>
    intro ctx h
    cases ctx
    case apply ks x pend c =>
      intro hH hP
      have hres := applyItems_sound (P := P) (N := N) (q := q) hpr (x := x) (c := c) items ks pend
        hH hP
      simp only [go] at h
      split at h
      · cases h
      · rename_i heq
        rw [heq] at hres
        exact hres
      · rename_i ks' pend' heq
        rw [heq] at hres
        exact ih _ h hres.1 hres.2
    all_goals simp [go] at h
  | force ch ih =>
    intro ctx h
    cases ctx
    case out ks x pend =>
      intro hH hP
      simp only [go, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨hne, hprf⟩, hodd⟩, hnk⟩, hgo⟩ := h
      have hne' : pend ≠ [] := by
        rintro rfl
        cases hne
      have hodd' : pmin pend % 2 = 1 := beq_iff_eq.mp hodd
      have hfk : pmin pend ∉ ks.map Key.p := fun hm => by
        rw [isKey_iff.mpr hm] at hnk
        cases hnk
      obtain ⟨e, he, he1⟩ := pmin_mem pend hne'
      obtain ⟨hck, hw1, hdv⟩ := hP.1 e he
      rw [he1] at hdv
      obtain ⟨hcp, -⟩ := key_prime hH hck
      have hf := hpr _ hprf
      have hfd : pmin pend ∣ σ 1 (e.2.1 ^ N.factorization e.2.1) :=
        (dvd_pow_self _ (by omega)).trans hdv
      have hfN := OPNStarter.force_prime hH.1.1.perfect hcp rfl hf (by omega) hfd
      obtain ⟨r, hr, hrh⟩ := roles_exh hL hH hf hfN hfk
      refine ih _ hgo r hr ?_ ?_
      · refine holds_insert hH hf hfN hfk hrh (fun e' he' => ?_) (csOf_nodup pend hP.2)
          (fun p hp hpx hpN => Or.inl (hH.2.2.2 p hp hpx hpN))
        obtain ⟨e0, he0, h0, rfl⟩ := mem_csOf he'
        obtain ⟨a, -, c⟩ := hP.1 e0 he0
        exact ⟨(key_prime hH a).1, (key_prime hH a).2, a, by rw [← h0]; exact c⟩
      · exact ⟨fun e' he' => let ⟨a, b, c⟩ := hP.1 e' (List.mem_of_mem_filter he');
          ⟨mem_insertKey_map a, b, c⟩, hP.2.sublist ((List.filter_sublist).map _)⟩
    all_goals simp [go] at h
  | nil =>
    intro ctx h
    cases ctx
    case roles ks x pend f cs rs =>
      simp only [go, List.isEmpty_iff] at h
      subst h
      intro r hr
      cases hr
    case senders ks x p gs =>
      simp only [go, List.isEmpty_iff] at h
      subst h
      intro g hg
      cases hg
    all_goals simp [go] at h
  | cons hd tl ihd ihl =>
    intro ctx h
    cases ctx
    case roles ks x pend f cs rs =>
      cases rs with
      | nil => simp [go] at h
      | cons r rs' =>
        simp only [go, Bool.and_eq_true] at h
        intro r0 hr0
        rcases List.mem_cons.mp hr0 with rfl | hr0
        · exact ihd _ h.1
        · exact ihl _ h.2 r0 hr0
    case senders ks x p gs =>
      cases gs with
      | nil => simp [go] at h
      | cons g gs' =>
        simp only [go, Bool.and_eq_true] at h
        intro g0 hg0
        rcases List.mem_cons.mp hg0 with rfl | hg0
        · exact ihd _ h.1
        · exact ihl _ h.2 g0 hg0
    all_goals simp [go] at h
  | receipt p ss ih =>
    intro ctx h
    cases ctx
    case out ks x pend =>
      intro hH _
      simp only [go, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hqd, hE⟩, hpk⟩, hp3⟩, hgo⟩ := h
      obtain ⟨g, hg, hdv⟩ := receipt_exists hH hqd hE (isKey_iff.mp hpk) hp3
      exact ih _ hgo g hg hH (key_prime hH (isKey_iff.mp hpk)).1 hdv
    all_goals simp [go] at h
  | inf g' d =>
    intro ctx h
    cases ctx
    case sender ks x p g =>
      intro hH hp hdv
      simp only [go, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨-, h2⟩ := h
      split at h2
      · rename_i k hfk
        obtain ⟨hk, hkp⟩ := findKey_some hfk
        simp only [Bool.and_eq_true] at h2
        obtain ⟨hp', -, hr, -, -⟩ := hH.2.1 k hk
        rw [hkp] at hp' hr
        exact infeasible_false hr (ordOK_dvd hp hp' h2.1 hdv) h2.2
      · cases h2
    all_goals simp [go] at h
  | snd g' d child ih =>
    intro ctx h
    cases ctx
    case sender ks x p g =>
      intro hH hp hdv
      simp only [go, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨-, h2⟩ := h
      split at h2
      · rename_i kp' isQ D no3 kmin ex kcs hfk
        obtain ⟨hk, hkp⟩ := findKey_some hfk
        simp only at hkp
        subst hkp
        obtain ⟨hg, -, hr, -, -⟩ := hH.2.1 _ hk
        dsimp only at hg hr
        simp only [Bool.and_eq_true] at h2
        obtain ⟨hord, h3⟩ := h2
        have hd := ordOK_dvd hp hg hord hdv
        have hL' : Nat.lcm D d ∣ N.factorization kp' + 1 := Nat.lcm_dvd hr.2.1 hd
        cases ex
        · simp only [Bool.false_eq_true, if_false] at h3
          split at h3
          · rename_i n hn
            have hle := nextAllowed_le hn (allowed_of_role hr hL') hL'
              (by have := hr.2.2.1; omega)
            exact ih _ h3 (holds_setRole hH ⟨hr.1, hL', by omega, hr.2.2.2.1, by simp,
              hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩) pendOK_nil
          · cases h3
        · simp only [if_true, Bool.and_eq_true] at h3
          exact ih _ h3.2 hH pendOK_nil
      · cases h2
    all_goals simp [go] at h
  | closed st ih =>
    intro ctx h
    cases ctx
    case out ks x pend =>
      intro hH _
      simp only [go] at h
      exact ih _ h hH
    all_goals simp [go] at h
  | decide ch ab ihc iha =>
    intro ctx h
    cases ctx
    case step ks x =>
      intro hH
      simp only [go] at h
      split at h
      · rename_i y hy
        simp only [Bool.and_eq_true] at h
        have hs := scanNext_spec hy
        have hHy := holds_of_scan hH hs
        by_cases hyN : y ∣ N
        · obtain ⟨r, hr, hrh⟩ := roles_exh hL hHy hs.2.1 hyN hs.2.2.1
          exact ihc _ h.1 r hr (holds_insert hHy hs.2.1 hyN hs.2.2.1 hrh (by simp)
            List.nodup_nil (fun p hp hpx hpN => Or.inl (hHy.2.2.2 p hp hpx hpN))) pendOK_nil
        · exact iha _ h.2 (holds_succ hHy hyN)
      · cases h
    all_goals simp [go] at h
  | check dd =>
    intro ctx h
    cases ctx
    case step ks x =>
      intro hH
      simp only [go] at h
      split at h
      · rename_i y hy
        exact hdef ks y dd N q h (holds_of_scan hH (scanNext_spec hy))
      · cases h
    all_goals simp [go] at h
  | checkL =>
    intro ctx h
    cases ctx
    case step ks x =>
      intro hH
      simp only [go] at h
      split at h
      · rename_i y hy
        exact landedL_false (holds_of_scan hH (scanNext_spec hy)) h
      · cases h
    all_goals simp [go] at h
  | split p ex atl ihe iha =>
    intro ctx h
    cases ctx
    case step ks x =>
      intro hH
      simp only [go] at h
      split at h
      · rename_i kp' isQ D no3 kmin kcs hfk
        obtain ⟨hk, hkp⟩ := findKey_some hfk
        simp only at hkp
        subst hkp
        obtain ⟨-, -, hr, -, -⟩ := hH.2.1 _ hk
        dsimp only at hr
        simp only [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        by_cases hke : N.factorization kp' = kmin
        · exact ihe _ h1 (holds_setRole hH ⟨hr.1, by rw [hke], by omega, hr.2.2.2.1,
            fun _ => hke, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩) pendOK_nil
        · split at h2
          · rename_i n hn
            have hle := nextAllowed_le hn (allowed_of_role hr hr.2.1) hr.2.1
              (by have := hr.2.2.1; omega)
            exact iha _ h2 (holds_setRole hH ⟨hr.1, hr.2.1, by omega, hr.2.2.2.1, by simp,
              hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩) pendOK_nil
          · cases h2
      · cases h
    all_goals simp [go] at h
  | ext =>
    intro ctx h
    cases ctx
    case step ks x =>
      intro hH
      simp only [go] at h
      exact hdone ks x h hH
    all_goals simp [go] at h

/-- Soundness of the checker. If `check` accepts a certificate, no member of the family exists.
The hypotheses are the deficient leaf theorem `DefSound P`, a sound primality oracle, a sound
recognizer `done` of states refuted elsewhere, and `E ≤ 2` when the landed facts are used. -/
theorem check_sound {P : Params} {pr : ℕ → Bool} {done : List Key → ℕ → Bool}
    (hdef : DefSound P) (hpr : ∀ n, pr n = true → n.Prime)
    (hdone : ∀ ks x N q, done ks x = true → Holds P N q ks x → False)
    (hL : P.landed = true → P.E ≤ 2) {c : Cert} (hc : check P pr done c = true) {N q : ℕ}
    (hF : Fam P.E N q) : False := by
  unfold check at hc
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨hP, hc⟩ := hc
  exact go_sound (N := N) (q := q) hdef hpr (fun ks x => hdone ks x N q) hL c _ hc
    (holds_root hP hF) pendOK_nil

/-- Soundness of the checker for any admissible parameters: if `checkV` accepts a certificate,
no member of the family `FamV P` exists. The hypotheses are those of `check_sound`. -/
theorem checkV_sound {P : Params} {pr : ℕ → Bool} {done : List Key → ℕ → Bool}
    (hdef : DefSound P) (hpr : ∀ n, pr n = true → n.Prime)
    (hdone : ∀ ks x N q, done ks x = true → Holds P N q ks x → False)
    (hL : P.landed = true → P.E ≤ 2) {c : Cert} (hc : checkV P pr done c = true) {N q : ℕ}
    (hF : FamV P N q) : False := by
  unfold checkV at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨hP, hc⟩ := hc
  exact go_sound (N := N) (q := q) hdef hpr (fun ks x => hdone ks x N q) hL c _ hc
    (holds_rootV hP hF) pendOK_nil

/-! ## The bridge to named exceptions -/

/-- Named exceptions give the family: if every prime factor `p ≠ q` of `N` outside a list of
at most `E` numbers has exponent 2, then `Fam E N q`. -/
theorem fam_of_named {E N q : ℕ} (rs : List ℕ) (hlen : rs.length ≤ E) (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ∉ rs → N.factorization p = 2) : Fam E N q := by
  refine ⟨h, hq, hodd, h3, ?_⟩
  have hsub : (N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2) ⊆ rs.toFinset := by
    intro p hp
    obtain ⟨hpN, hpq, hv⟩ := Finset.mem_filter.mp hp
    by_contra hpr
    exact hv (hsq p hpN hpq (by simpa using hpr))
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le rs).trans hlen)

/-- Named exceptions of exponent 4 give the family of the parameters: the exponent of 3 is
`P.V3` (even), every prime factor `p ≠ q`, `p ≠ 3` of `N` outside the list `rs` has exponent
2, and each listed number that divides `N` has exponent 4. The prime 3 counts as one more
exception when `P.V3 ≠ 2`. -/
theorem famV_of_named {P : Params} {N q : ℕ} (rs : List ℕ)
    (hlen : rs.length + (if P.V3 = 2 then 0 else 1) ≤ P.E) (hV : P.V3 % 2 = 0)
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (h3 : N.factorization 3 = P.V3) (hr : ∀ r ∈ rs, r ∈ N.primeFactors → N.factorization r = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ∉ rs → N.factorization p = 2) :
    FamV P N q := by
  classical
  have h3q : (3 : ℕ) ≠ q := by
    rintro rfl
    rw [h3] at hodd
    obtain ⟨j, hj⟩ := hodd
    omega
  refine ⟨h, hq, hodd, h3, ?_, h3q, fun _ p hp hpq hp3 hv => ?_⟩
  · have hsub : (N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2) ⊆
        insert 3 rs.toFinset := by
      intro p hp
      obtain ⟨hpN, hpq, hv⟩ := Finset.mem_filter.mp hp
      by_cases hp3 : p = 3
      · exact Finset.mem_insert.mpr (Or.inl hp3)
      by_contra hpr
      exact hv (hsq p hpN hpq hp3 (by simpa [hp3] using hpr))
    by_cases h2 : P.V3 = 2
    · rw [if_pos h2] at hlen
      have hsub2 : (N.primeFactors.filter fun p => p ≠ q ∧ N.factorization p ≠ 2) ⊆
          rs.toFinset := by
        intro p hp
        have hp' := hsub hp
        rcases Finset.mem_insert.mp hp' with rfl | hp'
        · exact absurd (h3.trans h2) (Finset.mem_filter.mp hp).2.2
        · exact hp'
      exact (Finset.card_le_card hsub2).trans ((List.toFinset_card_le rs).trans hlen)
    · rw [if_neg h2] at hlen
      exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
        (by have := List.toFinset_card_le rs; omega))
  · by_cases hpr : p ∈ rs
    · exact hr p hpr hp
    · exact absurd (hsq p hp hpq hp3 hpr) hv

/-- The family of the parameters from the hypotheses of `ExcessS1`: exponent 6 at 3, one
further prime `r` of exponent 4 if it divides `N`, every other prime factor except `q` of
exponent 2. -/
theorem famV_S1 {P : Params} (hV : P.V3 = 6) (hE : 2 ≤ P.E) {N q r : ℕ} (h : OddPerfect N)
    (hq : q.Prime) (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 = 6)
    (hr : r ∈ N.primeFactors → N.factorization r = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ r → N.factorization p = 2) :
    FamV P N q :=
  famV_of_named [r] (by simp [hV]; omega) (by omega) h hq hodd (h3.trans hV.symm)
    (fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hr)
    fun p hp hpq hp3 hpr => hsq p hp hpq hp3 (by simpa using hpr)

/-- The family of the parameters from the hypotheses of `ExcessS2a`: exponent 4 at 3, two
further primes of exponent 4 if they divide `N`, every other prime factor except `q` of
exponent 2. -/
theorem famV_S2a {P : Params} (hV : P.V3 = 4) (hE : 3 ≤ P.E) {N q r₁ r₂ : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (h3 : N.factorization 3 = 4) (hr₁ : r₁ ∈ N.primeFactors → N.factorization r₁ = 4)
    (hr₂ : r₂ ∈ N.primeFactors → N.factorization r₂ = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ 3 → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    FamV P N q :=
  famV_of_named [r₁, r₂] (by simp [hV]; omega) (by omega) h hq hodd (h3.trans hV.symm)
    (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hr₁
      · exact hr₂)
    fun p hp hpq hp3 hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpr
      exact hsq p hp hpq hp3 hpr.1 hpr.2

/-- The family of the parameters from the hypotheses of `ExcessS2b`: exponent 2 at 3, three
primes of exponent 4 if they divide `N`, every other prime factor except `q` of exponent 2. -/
theorem famV_S2b {P : Params} (hV : P.V3 = 2) (hE : 3 ≤ P.E) {N q r₁ r₂ r₃ : ℕ}
    (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (h3 : N.factorization 3 = 2) (hr₁ : r₁ ∈ N.primeFactors → N.factorization r₁ = 4)
    (hr₂ : r₂ ∈ N.primeFactors → N.factorization r₂ = 4)
    (hr₃ : r₃ ∈ N.primeFactors → N.factorization r₃ = 4)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2) :
    FamV P N q :=
  famV_of_named [r₁, r₂, r₃] (by simp [hV]; omega) (by omega) h hq hodd (h3.trans hV.symm)
    (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact hr₁
      · exact hr₂
      · exact hr₃)
    fun p hp hpq _ hpr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpr
      exact hsq p hp hpq hpr.1 hpr.2.1 hpr.2.2

/-- The bridge for one named exception. -/
theorem fam_one {N q r : ℕ} (h : OddPerfect N) (hq : q.Prime) (hodd : Odd (N.factorization q))
    (h3 : N.factorization 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r → N.factorization p = 2) : Fam 1 N q :=
  fam_of_named [r] (by simp) h hq hodd h3 fun p hp hpq hpr => hsq p hp hpq (by simpa using hpr)

/-- The bridge for two named exceptions. -/
theorem fam_two {N q r₁ r₂ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : N.factorization 3 = 2)
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    Fam 2 N q :=
  fam_of_named [r₁, r₂] (by simp) h hq hodd h3 fun p hp hpq hpr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpr
    exact hsq p hp hpq hpr.1 hpr.2

/-- Soundness of the search tree lookup: a found number is an element of the tree. The search
order is not needed for this direction. -/
theorem PTree.mem_toList {n : ℕ} : ∀ {t : PTree}, t.mem n = true → n ∈ t.toList
  | .leaf, h => by cases h
  | .node l p r, h => by
    change cond (Nat.beq n p) true (cond (Nat.blt n p) (l.mem n) (r.mem n)) = true at h
    simp only [PTree.toList, List.mem_append, List.mem_cons]
    cases hb : Nat.beq n p
    · rw [hb] at h
      simp only [cond_false] at h
      cases hl : Nat.blt n p
      · rw [hl] at h; exact Or.inr (Or.inr (PTree.mem_toList h))
      · rw [hl] at h; exact Or.inl (PTree.mem_toList h)
    · exact Or.inr (Or.inl (beq_iff.mp hb))

end TwoExcEngine

end OddPerfect


#print axioms OddPerfect.TwoExcEngine.powModE_eq
#print axioms OddPerfect.TwoExcEngine.smallPrime_sound
#print axioms OddPerfect.TwoExcEngine.pmask_ok
#print axioms OddPerfect.TwoExcEngine.primeB_sound
#print axioms OddPerfect.TwoExcEngine.scanNext_spec
#print axioms OddPerfect.TwoExcEngine.gdivB_sound
#print axioms OddPerfect.TwoExcEngine.ordOK_dvd
#print axioms OddPerfect.TwoExcEngine.nextAllowed_le
#print axioms OddPerfect.TwoExcEngine.allowed_of_role
#print axioms OddPerfect.TwoExcEngine.infeasible_false
#print axioms OddPerfect.TwoExcEngine.csum_le
#print axioms OddPerfect.TwoExcEngine.applyItems_sound
#print axioms OddPerfect.TwoExcEngine.exc_all
#print axioms OddPerfect.TwoExcEngine.qDec_key
#print axioms OddPerfect.TwoExcEngine.named_two
#print axioms OddPerfect.TwoExcEngine.roles_exh
#print axioms OddPerfect.TwoExcEngine.receipt_exists
#print axioms OddPerfect.TwoExcEngine.landedL_false
#print axioms OddPerfect.TwoExcEngine.abundant_false
#print axioms OddPerfect.TwoExcEngine.go_sound
#print axioms OddPerfect.TwoExcEngine.check_sound
#print axioms OddPerfect.TwoExcEngine.checkV_sound
#print axioms OddPerfect.TwoExcEngine.fam_of_famV
#print axioms OddPerfect.TwoExcEngine.lan_spec
#print axioms OddPerfect.TwoExcEngine.famV_of_named
#print axioms OddPerfect.TwoExcEngine.famV_S1
#print axioms OddPerfect.TwoExcEngine.famV_S2a
#print axioms OddPerfect.TwoExcEngine.famV_S2b
#print axioms OddPerfect.TwoExcEngine.fam_of_named
#print axioms OddPerfect.TwoExcEngine.fam_one
#print axioms OddPerfect.TwoExcEngine.fam_two
#print axioms OddPerfect.TwoExcEngine.PTree.mem_toList
