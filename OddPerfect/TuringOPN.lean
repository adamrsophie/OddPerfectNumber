import OddPerfect.Basic
import OddPerfect.TuringOPNMacro

/-!
# A 24 state Turing machine halts exactly when an odd perfect number exists

The machine is the 24 state, 2 symbol Turing machine of P. Ochem's page on odd perfect numbers
(https://www.lirmm.fr/~ochem/opn/ , file `opn24.py`), listed among the "Cryptids" of the
bbchallenge project; its definition, with the standard semantics, is in
`OddPerfect/TuringOPNCode.lean`. A Lean proof for this machine was published first on P. Ochem's
page (`OddPerfect24.lean`). The proof here is an independent second formalization, stated against
this library's definition `OddPerfect` and the integer tape `Int → Bool`; it claims no priority.

The theorem `halts_iff_exists_oddPerfect` is about this machine only. It gives no information on
whether an odd perfect number exists: that question is open, and nothing here bears on it.

Outline. From the blank tape the machine reaches `restart 5` (`mL0`). From `restart n` the
machine tries `m = 2, 3, ..., n`: a cyclic pass decides `m ∣ n`, and each divisor `m` is charged
against a budget of `n` units, one unit at a time. The budget runs out exactly at the last
divisor `n` itself when `n` is perfect, and then the machine halts; otherwise it reaches
`restart (n + 2)` (`candidate`).
-/

namespace OddPerfect

namespace TuringOPN

/-- Rewrite both ends of a run along equalities. -/
theorem Reaches.cast {c d c' d' : SC} (h : Reaches c d) (h1 : c = c') (h2 : d = d') :
    Reaches c' d' := by
  subst h1 h2
  exact h

/-- The sum of the divisors of `N` below `m`. -/
def divSumBelow (N m : ℕ) : ℕ := ∑ d ∈ Finset.range m, if d ∣ N then d else 0

/-- Recursion for `divSumBelow`. -/
theorem divSumBelow_succ (N m : ℕ) :
    divSumBelow N (m + 1) = divSumBelow N m + if m ∣ N then m else 0 :=
  Finset.sum_range_succ _ _

/-- The only divisor below 2 that counts is 1. -/
theorem divSumBelow_two (N : ℕ) : divSumBelow N 2 = 1 := by
  rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, divSumBelow_succ, divSumBelow_succ]
  simp [divSumBelow]

/-- `divSumBelow N` is monotone. -/
theorem divSumBelow_mono {N m m' : ℕ} (h : m ≤ m') : divSumBelow N m ≤ divSumBelow N m' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

/-- Below `N`, `divSumBelow` is the sum of the proper divisors. -/
theorem divSumBelow_self {N : ℕ} (hN : 0 < N) :
    divSumBelow N N = ∑ i ∈ N.properDivisors, i := by
  rw [divSumBelow, Finset.sum_range_eq_add_Ico _ hN, Nat.properDivisors, Finset.sum_filter]
  simp

/-- A positive `N` is perfect iff the sum of its divisors below `N` is `N`. -/
theorem perfect_iff_divSumBelow {N : ℕ} (hN : 0 < N) : N.Perfect ↔ divSumBelow N N = N := by
  rw [Nat.perfect_iff_sum_properDivisors hN, divSumBelow_self hN]

/-- The divisibility pass: after `i ≤ a` round trips the hole of the second block (of `m` cells)
is at position `i % m + 1`. -/
theorem pass (s r a m : ℕ) (hm : 0 < m) : ∀ i, i ≤ a →
    Reaches (cQ1 s r 0 a 0 (m - 1)) (cQ1 s r i (a - i) (i % m) (m - 1 - i % m)) := by
  intro i
  induction i with
  | zero => intro _; exact Reaches.of_eq (by simp)
  | succ i ih =>
    intro hi
    have hlt : i % m < m := Nat.mod_lt _ hm
    refine (ih (by omega)).trans ?_
    by_cases h : i % m + 1 < m
    · have e : (i + 1) % m = i % m + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < m by omega)]
        exact Nat.mod_eq_of_lt h
      exact (mL1 s r i (a - i - 1) (i % m) (m - 2 - i % m)).cast
        (by congr 1 <;> omega) (by congr 1 <;> omega)
    · have e : (i + 1) % m = 0 := by
        have h3 : i + 1 = m * (i / m + 1) := by
          have := Nat.div_add_mod i m
          rw [Nat.mul_add, Nat.mul_one]
          omega
        rw [h3, Nat.mul_mod_right]
      exact (mL2 s r i (a - i - 1) (i % m)).cast (by congr 1 <;> omega) (by congr 1 <;> omega)

/-- The charge of a divisor from its second unit on: either the budget runs out (and the machine
restarts with the next candidate) or the whole divisor is charged. -/
theorem chargeB (a : ℕ) : ∀ v s r t : ℕ, s + r = a + (t + 2 + v) →
    (r ≤ v → Reaches (cS1b s r a t v) (rQ (s + r))) ∧
    (v < r → 0 < a →
      Reaches (cS1b s r a t v) (cI2 (s + v + 1) (r - v - 1) (a - 1) (t + v + 2))) := by
  intro v
  induction v with
  | zero =>
    intro s r t hsr
    refine ⟨fun hr => ?_, fun hr ha => ?_⟩
    · exact (mL8b a t 0).cast (by congr 1 <;> omega) (by congr 1; omega)
    · exact (mL6b s (r - 1) (a - 1) t).cast (by congr 1 <;> omega) (by congr 1)
  | succ v ih =>
    intro s r t hsr
    refine ⟨fun hr => ?_, fun hr ha => ?_⟩
    · by_cases hr0 : r = 0
      · exact (mL8b a t (v + 1)).cast (by congr 1 <;> omega) (by congr 1; omega)
      · have h5 : Reaches (cS1b s r a t (v + 1)) (cS1b (s + 1) (r - 1) a (t + 1) v) :=
          (mL5b s (r - 1) a t v).cast (by congr 1; omega) rfl
        exact h5.trans (((ih (s + 1) (r - 1) (t + 1) (by omega)).1 (by omega)).cast rfl
          (by congr 1; omega))
    · have h5 : Reaches (cS1b s r a t (v + 1)) (cS1b (s + 1) (r - 1) a (t + 1) v) :=
        (mL5b s (r - 1) a t v).cast (by congr 1; omega) rfl
      exact h5.trans (((ih (s + 1) (r - 1) (t + 1) (by omega)).2 (by omega) ha).cast rfl
        (by congr 1 <;> omega))

/-- The charge of a divisor `v + 1` from its first unit on. -/
theorem chargeA (s r a v : ℕ) (hsr : s + r = a + (v + 1)) :
    (r ≤ v → (0 < a ∨ 0 < r) → Reaches (cS1a s r a v) (rQ (s + r))) ∧
    (a = 0 → r = 0 → HaltsFrom (cS1a s r a v)) ∧
    (v < r → 0 < a → Reaches (cS1a s r a v) (cI2 (s + v + 1) (r - v - 1) (a - 1) (v + 1))) := by
  refine ⟨fun hr hpos => ?_, fun ha hr => ?_, fun hr ha => ?_⟩
  · by_cases hr0 : r = 0
    · exact (mL8a (a - 1) v).cast (by congr 1 <;> omega) (by congr 1; omega)
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have h5 : Reaches (cS1a s r a (w + 1)) (cS1b (s + 1) (r - 1) a 0 w) :=
        (mL5a s (r - 1) a w).cast (by congr 1; omega) rfl
      exact h5.trans (((chargeB a w (s + 1) (r - 1) 0 (by omega)).1 (by omega)).cast rfl
        (by congr 1; omega))
  · subst ha hr
    exact ⟨_, mL10 s v, mL10_halt s v⟩
  · rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv
      exact (mL6a s (r - 1) (a - 1)).cast (by congr 1 <;> omega) (by congr 1)
    · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have h5 : Reaches (cS1a s r a (w + 1)) (cS1b (s + 1) (r - 1) a 0 w) :=
        (mL5a s (r - 1) a w).cast (by congr 1; omega) rfl
      exact h5.trans (((chargeB a w (s + 1) (r - 1) 0 (by omega)).2 (by omega) ha).cast rfl
        (by congr 1 <;> omega))

/-- One candidate `N`, from the trial of the divisor `m` on (spent budget `s`, remaining `r`,
first block of `a` cells): the machine halts if `N` is perfect and otherwise reaches the restart
configuration of `N + 2`. -/
theorem trial (N : ℕ) : ∀ d m s r a : ℕ, N - m = d → 2 ≤ m → a + m = N → s + r = N →
    s = divSumBelow N m →
    (N.Perfect → HaltsFrom (cQ1 s r 0 a 0 (m - 1))) ∧
    (¬ N.Perfect → Reaches (cQ1 s r 0 a 0 (m - 1)) (rQ N)) := by
  intro d
  induction d with
  | zero =>
    intro m s r a hd hm ham hsr hs
    have ha : a = 0 := by omega
    subst ha
    have hmN : m = N := by omega
    have hs1 : 1 ≤ s := by
      rw [hs, ← divSumBelow_two N]
      exact divSumBelow_mono hm
    have hperf : N.Perfect ↔ s = N := by
      rw [perfect_iff_divSumBelow (by omega), hs, hmN]
    have h3 := mL3 s r 0 (m - 1)
    have hA := chargeA s r 0 (m - 1) (by omega)
    by_cases hr : r = 0
    · subst hr
      have hsN : s = N := by omega
      exact ⟨fun _ => HaltsFrom.of_reaches h3 (hA.2.1 rfl rfl),
        fun hp => absurd (hperf.2 hsN) hp⟩
    · have hreach := h3.trans (hA.1 (by omega) (Or.inr (by omega)))
      rw [hsr] at hreach
      exact ⟨fun hp => absurd (hperf.1 hp) (by omega), fun _ => hreach⟩
  | succ d ih =>
    intro m s r a hd hm ham hsr hs
    have hm0 : 0 < m := by omega
    have hpass := pass s r a m hm0 a (Nat.le_refl a)
    have hdvd : m ∣ N ↔ a % m = 0 := by
      rw [← ham, Nat.dvd_add_self_right, Nat.dvd_iff_mod_eq_zero]
    have hnext : divSumBelow N (m + 1) = s + if m ∣ N then m else 0 := by
      rw [divSumBelow_succ, hs]
    by_cases hmod : a % m = 0
    · rw [if_pos (hdvd.2 hmod)] at hnext
      have h3 : Reaches (cQ1 s r 0 a 0 (m - 1)) (cS1a s r a (m - 1)) :=
        hpass.trans ((mL3 s r a (m - 1)).cast (by congr 1 <;> omega) rfl)
      have hA := chargeA s r a (m - 1) (by omega)
      by_cases hrm : r < m
      · have hreach := h3.trans (hA.1 (by omega) (Or.inl (by omega)))
        rw [hsr] at hreach
        have hnp : ¬ N.Perfect := by
          intro hpf
          have h1 := (perfect_iff_divSumBelow (by omega)).1 hpf
          have h2 := divSumBelow_mono (N := N) (show m + 1 ≤ N by omega)
          omega
        exact ⟨fun hpf => absurd hpf hnp, fun _ => hreach⟩
      · have h6 := hA.2.2 (by omega) (by omega)
        have h7 := mL7 (s + (m - 1) + 1) (r - (m - 1) - 1) (a - 1) (m - 1 + 1)
        have hIH := ih (m + 1) (s + m) (r - m) (a - 1) (by omega) (by omega) (by omega) (by omega)
          (by omega)
        have hstart :
            Reaches (cQ1 s r 0 a 0 (m - 1)) (cQ1 (s + m) (r - m) 0 (a - 1) 0 (m + 1 - 1)) :=
          (h3.trans h6).trans (h7.cast rfl (by congr 1 <;> omega))
        exact ⟨fun hpf => HaltsFrom.of_reaches hstart (hIH.1 hpf),
          fun hpf => hstart.trans (hIH.2 hpf)⟩
    · rw [if_neg (fun h => hmod (hdvd.1 h))] at hnext
      have hlt : a % m < m := Nat.mod_lt _ hm0
      have ha : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          exact absurd (Nat.zero_mod m) hmod
        · exact h
      have h4 := mL4 s r (a - 1) (a % m - 1) (m - 1 - a % m)
      have h7 := mL7 s r (a - 1) m
      have hIH := ih (m + 1) s r (a - 1) (by omega) (by omega) (by omega) hsr (by omega)
      have hstart : Reaches (cQ1 s r 0 a 0 (m - 1)) (cQ1 s r 0 (a - 1) 0 (m + 1 - 1)) :=
        (hpass.trans (h4.cast (by congr 1 <;> omega) (by congr 1; omega))).trans
          (h7.cast rfl (by congr 1))
      exact ⟨fun hpf => HaltsFrom.of_reaches hstart (hIH.1 hpf),
        fun hpf => hstart.trans (hIH.2 hpf)⟩

/-- The restart configuration of the candidate `n` (for `3 ≤ n`): state `B` on the tape
`1 0 1^(n - 1) 0 1^(n - 2) 0 0 1` (all other cells 0), the head on the first cell of the block
`1^(n - 2)`. -/
def restart (n : ℕ) : SC := rQ (n - 2)

/-- The per candidate lemma: from `restart n` the machine halts if `n` is perfect and otherwise
reaches `restart (n + 2)`. -/
theorem candidate (n : ℕ) (hn : 3 ≤ n) :
    (n.Perfect → HaltsFrom (restart n)) ∧
    (¬ n.Perfect → Reaches (restart n) (restart (n + 2))) := by
  have h := trial n (n - 2) 2 1 (n - 1) (n - 2) rfl (Nat.le_refl 2) (by omega) (by omega)
    (divSumBelow_two n).symm
  have e1 : cQ1 1 (n - 1) 0 (n - 2) 0 (2 - 1) = restart n := by
    unfold restart rQ
    congr 1; omega
  have e2 : restart (n + 2) = rQ n := by
    unfold restart
    rw [Nat.add_sub_cancel]
  rw [e1] at h
  rw [e2]
  exact h

/-- Consecutive restart configurations differ. -/
theorem rQ_ne (n : ℕ) : rQ n ≠ rQ (n + 2) := by
  intro h
  have h1 : (rQ n).R n = (rQ (n + 2)).R n := by rw [h]
  change ones n (cons false (ones 0 (cons false (ones 1 zeros)))) n =
    ones (n + 2) (cons false (ones 0 (cons false (ones 1 zeros)))) n at h1
  rw [ones_apply_self, ones_apply_lt (k := n + 2) (i := n) (by omega)] at h1
  exact Bool.false_ne_true h1

/-- From the blank tape, either a perfect number `2 i + 5` with `i < k` exists, or the machine
reaches `restart (2 k + 5)` after at least `k` steps. -/
theorem reach_restart (k : ℕ) : (∃ i < k, (2 * i + 5).Perfect) ∨
    ∃ j z, k ≤ j ∧ run j init = some (toZ z (rQ (2 * k + 3))) := by
  induction k with
  | zero =>
    right
    obtain ⟨j, z, hj, -⟩ := reaches_run mL0 0
    rw [toZ_blank] at hj
    exact ⟨j, z, Nat.zero_le _, hj⟩
  | succ k ih =>
    rcases ih with ⟨i, hi, hp⟩ | ⟨j, z, hj, hrun⟩
    · exact Or.inl ⟨i, by omega, hp⟩
    · by_cases hp : (2 * k + 5).Perfect
      · exact Or.inl ⟨k, by omega, hp⟩
      · right
        have hc := (candidate (2 * k + 5) (by omega)).2 hp
        unfold restart at hc
        rw [show 2 * k + 5 - 2 = 2 * k + 3 by omega, show 2 * k + 5 + 2 - 2 = 2 * k + 5 by omega]
          at hc
        obtain ⟨j', z', hj', h0⟩ := reaches_run hc z
        have hne : rQ (2 * k + 3) ≠ rQ (2 * k + 5) := rQ_ne (2 * k + 3)
        have hpos : j' ≠ 0 := fun h => hne (h0 h)
        refine ⟨j + j', z', by omega, ?_⟩
        rw [show 2 * (k + 1) + 3 = 2 * k + 5 by omega, run_add, hrun]
        exact hj'

/-- The 24 state machine of `OddPerfect/TuringOPNCode.lean` halts from the blank tape if and only
if an odd perfect number exists. This is a statement about this machine only: it does not decide
whether an odd perfect number exists, which is open. -/
theorem halts_iff_exists_oddPerfect : Halts ↔ ∃ N : ℕ, OddPerfect N := by
  constructor
  · rintro ⟨K, c, hK, hc⟩
    by_contra hno
    have hnp : ∀ i, ¬ (2 * i + 5).Perfect := fun i hp =>
      hno ⟨2 * i + 5, ⟨⟨i + 2, by omega⟩, hp⟩⟩
    rcases reach_restart (K + 1) with ⟨i, -, hp⟩ | ⟨j, z, hj, hrun⟩
    · exact hnp i hp
    · obtain ⟨t, rfl⟩ : ∃ t, j = K + 1 + t := ⟨j - (K + 1), by omega⟩
      have h1 : run (K + 1) init = none := by
        rw [run_add, hK]
        show (step c).bind (run 0) = none
        rw [hc]
        rfl
      rw [run_add, h1] at hrun
      exact absurd hrun (by simp)
  · rintro ⟨N, ⟨m, hm⟩, hperf⟩
    have h1 : N ≠ 1 := by
      rintro rfl
      have := hperf.1
      rw [Nat.properDivisors_one, Finset.sum_empty] at this
      omega
    have h3 : N ≠ 3 := by
      rintro rfl
      have := Nat.sum_properDivisors_eq_one_iff_prime.2 Nat.prime_three
      rw [hperf.1] at this
      omega
    have ex : ∃ i, (2 * i + 5).Perfect :=
      ⟨m - 2, by rw [show 2 * (m - 2) + 5 = N by omega]; exact hperf⟩
    classical
    obtain ⟨i0, hi0, hmin⟩ :
        ∃ i0, (2 * i0 + 5).Perfect ∧ ∀ i < i0, ¬ (2 * i + 5).Perfect :=
      ⟨Nat.find ex, Nat.find_spec ex, fun i hi => Nat.find_min ex hi⟩
    rcases reach_restart i0 with ⟨i, hi, hp⟩ | ⟨j, z, -, hrun⟩
    · exact absurd hp (hmin i hi)
    · have hc := (candidate (2 * i0 + 5) (by omega)).1 hi0
      unfold restart at hc
      rw [show 2 * i0 + 5 - 2 = 2 * i0 + 3 by omega] at hc
      obtain ⟨k, c', hk, hstep⟩ := haltsFrom_run hc z
      refine ⟨j + k, c', ?_, hstep⟩
      rw [run_add, hrun]
      exact hk

end TuringOPN

end OddPerfect

#print axioms OddPerfect.TuringOPN.Reaches.cast
#print axioms OddPerfect.TuringOPN.divSumBelow_succ
#print axioms OddPerfect.TuringOPN.divSumBelow_two
#print axioms OddPerfect.TuringOPN.divSumBelow_mono
#print axioms OddPerfect.TuringOPN.divSumBelow_self
#print axioms OddPerfect.TuringOPN.perfect_iff_divSumBelow
#print axioms OddPerfect.TuringOPN.pass
#print axioms OddPerfect.TuringOPN.chargeB
#print axioms OddPerfect.TuringOPN.chargeA
#print axioms OddPerfect.TuringOPN.trial
#print axioms OddPerfect.TuringOPN.candidate
#print axioms OddPerfect.TuringOPN.rQ_ne
#print axioms OddPerfect.TuringOPN.reach_restart
#print axioms OddPerfect.TuringOPN.halts_iff_exists_oddPerfect
