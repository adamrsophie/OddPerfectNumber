import OddPerfect.TuringOPNCode

/-!
# A 24 state Turing machine for odd perfect numbers: tapes seen from the head

The machine of `OddPerfect/TuringOPNCode.lean` is simulated here on configurations that store
the two halves of the tape as streams read outward from the head (`SC`). Blocks of ones are
written `ones k s`, so a macro step can move over a block of any length. The bridge lemmas
`reaches_run` and `haltsFrom_run` carry a run of the stream machine back to `run` and `step` of
the trusted definitions.
-/

namespace OddPerfect

namespace TuringOPN

/-- One half of the tape, read from the head outward. -/
abbrev Strm := Nat → Bool

/-- Put a symbol in front of a stream. -/
def cons (b : Bool) (s : Strm) : Strm := fun n =>
  match n with
  | 0 => b
  | n + 1 => s n

/-- Drop the first symbol of a stream. -/
def tl (s : Strm) : Strm := fun n => s (n + 1)

/-- The blank half tape. -/
def zeros : Strm := fun _ => false

/-- `ones k s` is a block of `k` ones followed by `s`. -/
def ones : Nat → Strm → Strm
  | 0, s => s
  | k + 1, s => cons true (ones k s)

/-- The first symbol of `cons b s` is `b`. -/
theorem cons_zero (b : Bool) (s : Strm) : cons b s 0 = b := rfl

/-- Dropping the first symbol of `cons b s` gives `s`. -/
theorem tl_cons (b : Bool) (s : Strm) : tl (cons b s) = s := rfl

/-- Every cell of the blank half tape is 0. -/
theorem zeros_apply (n : Nat) : zeros n = false := rfl

/-- The blank half tape without its first cell is blank. -/
theorem tl_zeros : tl zeros = zeros := rfl

/-- A 0 in front of the blank half tape changes nothing. -/
theorem cons_false_zeros : cons false zeros = zeros := by
  funext n
  cases n <;> rfl

/-- A block of no ones is empty. -/
theorem ones_zero (s : Strm) : ones 0 s = s := rfl

/-- A single 1 is a block of one 1. -/
theorem cons_true (s : Strm) : cons true s = ones 1 s := rfl

/-- A nonempty block of ones starts with 1. -/
theorem ones_apply_zero {k : Nat} (h : 0 < k) (s : Strm) : ones k s 0 = true := by
  cases k with
  | zero => omega
  | succ k => rfl

/-- Dropping the first cell of a nonempty block of ones shortens it by one. -/
theorem tl_ones {k : Nat} (h : 0 < k) (s : Strm) : tl (ones k s) = ones (k - 1) s := by
  cases k with
  | zero => omega
  | succ k =>
    show ones k s = ones (k + 1 - 1) s
    rw [Nat.add_sub_cancel]

/-- Two adjacent blocks of ones merge. -/
theorem ones_ones (a b : Nat) (s : Strm) : ones a (ones b s) = ones (a + b) s := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih =>
    rw [Nat.add_right_comm]
    show cons true (ones a (ones b s)) = cons true (ones (a + b) s)
    rw [ih]

/-- A 1 after a block of ones lengthens the block. -/
theorem ones_cons_true (k : Nat) (s : Strm) : ones k (cons true s) = ones (k + 1) s := by
  rw [cons_true, ones_ones]

/-- The cells inside a block of ones are 1. -/
theorem ones_apply_lt {k i : Nat} (h : i < k) (s : Strm) : ones k s i = true := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (by omega)

/-- The cell just after a block of ones is the first cell of what follows. -/
theorem ones_apply_self (k : Nat) (s : Strm) : ones k s k = s 0 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Congruence for `ones`. -/
theorem ones_congr {a b : Nat} {s t : Strm} (h : a = b) (h' : s = t) : ones a s = ones b t := by
  subst h h'
  rfl

/-- Congruence for `cons`. -/
theorem cons_congr (b : Bool) {s t : Strm} (h : s = t) : cons b s = cons b t := by
  subst h
  rfl

/-- A configuration with the tape seen from the head: the state, the left half (nearest cell
first) and the right half starting with the cell under the head. -/
structure SC where
  /-- The state. -/
  q : St
  /-- The cells left of the head, nearest first. -/
  L : Strm
  /-- The cell under the head, then the cells to its right. -/
  R : Strm

/-- Equality of configurations seen from the head, field by field. -/
theorem SC.ext' {q q' : St} {L L' R R' : Strm} (hq : q = q') (hL : L = L') (hR : R = R') :
    (⟨q, L, R⟩ : SC) = ⟨q', L', R'⟩ := by
  subst hq hL hR
  rfl

/-- One step on configurations seen from the head. -/
def sstep (c : SC) : Option SC :=
  match table c.q (c.R 0) with
  | none => none
  | some (w, Dir.R, q) => some ⟨q, cons w c.L, tl c.R⟩
  | some (w, Dir.L, q) => some ⟨q, tl c.L, cons (c.L 0) (cons w (tl c.R))⟩

/-- The successor configuration, or the configuration itself if there is none. -/
def nxt (c : SC) : SC := (sstep c).getD c

/-- A step with a right move. -/
theorem sstep_R {q q' : St} {w : Bool} {L R : Strm} (h : table q (R 0) = some (w, Dir.R, q')) :
    sstep ⟨q, L, R⟩ = some ⟨q', cons w L, tl R⟩ := by
  simp only [sstep, h]

/-- A step with a left move. -/
theorem sstep_L {q q' : St} {w : Bool} {L R : Strm} (h : table q (R 0) = some (w, Dir.L, q')) :
    sstep ⟨q, L, R⟩ = some ⟨q', tl L, cons (L 0) (cons w (tl R))⟩ := by
  simp only [sstep, h]

/-- Reachability in finitely many steps. -/
inductive Reaches : SC → SC → Prop
  | refl (c : SC) : Reaches c c
  | step {c d e : SC} : sstep c = some d → Reaches d e → Reaches c e

/-- Reachability is transitive. -/
theorem Reaches.trans {c d e : SC} : Reaches c d → Reaches d e → Reaches c e
  | .refl _, h2 => h2
  | .step h h1, h2 => .step h (h1.trans h2)

/-- Equal configurations reach each other. -/
theorem Reaches.of_eq {c d : SC} (h : c = d) : Reaches c d := h ▸ Reaches.refl c

/-- If `c` has a successor, then `c` reaches whatever its successor reaches. -/
theorem Reaches.adv {c e : SC} (h : sstep c ≠ none) (h2 : Reaches (nxt c) e) : Reaches c e := by
  unfold nxt at h2
  cases hc : sstep c with
  | none => exact absurd hc h
  | some d =>
    rw [hc] at h2
    exact Reaches.step hc h2

/-- The machine halts from `c`. -/
def HaltsFrom (c : SC) : Prop := ∃ d, Reaches c d ∧ sstep d = none

/-- Halting is inherited backward along a run. -/
theorem HaltsFrom.of_reaches {c d : SC} (h : Reaches c d) (h' : HaltsFrom d) : HaltsFrom c := by
  obtain ⟨e, h1, h2⟩ := h'
  exact ⟨e, h.trans h1, h2⟩

/-- A state that moves right over ones crosses a whole block of ones. -/
theorem skipR {q : St} (hq : table q true = some (true, Dir.R, q)) {k : Nat} {L R : Strm}
    {e : SC} (h : Reaches ⟨q, ones k L, R⟩ e) : Reaches ⟨q, L, ones k R⟩ e := by
  induction k generalizing L with
  | zero => exact h
  | succ k ih =>
    refine Reaches.step (sstep_R (L := L) (R := ones (k + 1) R) hq) ?_
    exact ih (by rw [ones_cons_true]; exact h)

/-- A state that moves left over ones crosses a whole block of ones. -/
theorem skipL {q : St} (hq : table q true = some (true, Dir.L, q)) {k j : Nat} {L R : Strm}
    {e : SC} (hj : 0 < j) (h : Reaches ⟨q, L, ones (k + j) R⟩ e) :
    Reaches ⟨q, ones k L, ones j R⟩ e := by
  induction k generalizing j with
  | zero => rw [Nat.zero_add] at h; exact h
  | succ k ih =>
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    refine Reaches.step (sstep_L (L := ones (k + 1) L) (R := ones (j' + 1) R) hq) ?_
    have h' : Reaches ⟨q, L, ones (k + (j' + 2)) R⟩ e := by
      have e1 : k + (j' + 2) = k + 1 + (j' + 1) := by omega
      rw [e1]
      exact h
    exact ih (j := j' + 2) (by omega) h'

/-- The configuration on the integer tape with the head at `z`. -/
def toZ (z : Int) (c : SC) : Cfg :=
  ⟨c.q, z, fun x => if x < z then c.L (z - 1 - x).toNat else c.R (x - z).toNat⟩

/-- The symbol under the head of `toZ z c` is the first cell of `c.R`. -/
theorem toZ_read (z : Int) (q : St) (L R : Strm) :
    (toZ z ⟨q, L, R⟩).tape (toZ z ⟨q, L, R⟩).pos = R 0 := by
  show (if z < z then L (z - 1 - z).toNat else R (z - z).toNat) = R 0
  rw [if_neg (Int.lt_irrefl z), Int.sub_self]
  rfl

/-- The integer tape after a write at the head followed by a right move. -/
theorem tape_R (q q' : St) (z : Int) (w : Bool) (L R : Strm) :
    (fun x => if x = z then w else (toZ z ⟨q, L, R⟩).tape x) =
      (toZ (z + 1) ⟨q', cons w L, tl R⟩).tape := by
  funext x
  show (if x = z then w else if x < z then L (z - 1 - x).toNat else R (x - z).toNat) =
    (if x < z + 1 then cons w L (z + 1 - 1 - x).toNat else tl R (x - (z + 1)).toNat)
  by_cases h1 : x = z
  · rw [if_pos h1, if_pos (by omega), show (z + 1 - 1 - x).toNat = 0 by omega]
    rfl
  · rw [if_neg h1]
    by_cases h2 : x < z
    · rw [if_pos h2, if_pos (by omega),
        show (z + 1 - 1 - x).toNat = (z - 1 - x).toNat + 1 by omega]
      rfl
    · rw [if_neg h2, if_neg (by omega), show (x - z).toNat = (x - (z + 1)).toNat + 1 by omega]
      rfl

/-- The integer tape after a write at the head followed by a left move. -/
theorem tape_L (q q' : St) (z : Int) (w : Bool) (L R : Strm) :
    (fun x => if x = z then w else (toZ z ⟨q, L, R⟩).tape x) =
      (toZ (z + -1) ⟨q', tl L, cons (L 0) (cons w (tl R))⟩).tape := by
  funext x
  show (if x = z then w else if x < z then L (z - 1 - x).toNat else R (x - z).toNat) =
    (if x < z + -1 then tl L (z + -1 - 1 - x).toNat
      else cons (L 0) (cons w (tl R)) (x - (z + -1)).toNat)
  by_cases h1 : x = z
  · rw [if_pos h1, if_neg (by omega), show (x - (z + -1)).toNat = 0 + 1 by omega]
    rfl
  · rw [if_neg h1]
    by_cases h2 : x < z
    · rw [if_pos h2]
      by_cases h3 : x < z + -1
      · rw [if_pos h3, show (z - 1 - x).toNat = (z + -1 - 1 - x).toNat + 1 by omega]
        rfl
      · rw [if_neg h3, show (z - 1 - x).toNat = 0 by omega,
          show (x - (z + -1)).toNat = 0 by omega]
        rfl
    · rw [if_neg h2, if_neg (by omega), show (x - z).toNat = (x - z - 1).toNat + 1 by omega,
        show (x - (z + -1)).toNat = (x - z - 1).toNat + 1 + 1 by omega]
      rfl

/-- A right move of the stream machine is a step of the machine on the integer tape. -/
theorem step_toZ_R {q q' : St} {w : Bool} {L R : Strm}
    (ht : table q (R 0) = some (w, Dir.R, q')) (z : Int) :
    step (toZ z ⟨q, L, R⟩) = some (toZ (z + 1) ⟨q', cons w L, tl R⟩) := by
  unfold step
  rw [toZ_read, show (toZ z ⟨q, L, R⟩).state = q from rfl, ht]
  exact congrArg some (congrArg (Cfg.mk q' (z + 1)) (tape_R q q' z w L R))

/-- A left move of the stream machine is a step of the machine on the integer tape. -/
theorem step_toZ_L {q q' : St} {w : Bool} {L R : Strm}
    (ht : table q (R 0) = some (w, Dir.L, q')) (z : Int) :
    step (toZ z ⟨q, L, R⟩) =
      some (toZ (z + -1) ⟨q', tl L, cons (L 0) (cons w (tl R))⟩) := by
  unfold step
  rw [toZ_read, show (toZ z ⟨q, L, R⟩).state = q from rfl, ht]
  exact congrArg some (congrArg (Cfg.mk q' (z + -1)) (tape_L q q' z w L R))

/-- Each step of the stream machine is a step of the machine on the integer tape. -/
theorem step_toZ {c d : SC} (h : sstep c = some d) (z : Int) :
    ∃ z', step (toZ z c) = some (toZ z' d) := by
  obtain ⟨q, L, R⟩ := c
  cases ht : table q (R 0) with
  | none => simp [sstep, ht] at h
  | some x =>
    obtain ⟨w, dd, q'⟩ := x
    cases dd with
    | R =>
      rw [sstep_R ht] at h
      have := Option.some.inj h
      subst this
      exact ⟨_, step_toZ_R ht z⟩
    | L =>
      rw [sstep_L ht] at h
      have := Option.some.inj h
      subst this
      exact ⟨_, step_toZ_L ht z⟩

/-- A configuration without successor has none on the integer tape either. -/
theorem step_toZ_none {c : SC} (h : sstep c = none) (z : Int) : step (toZ z c) = none := by
  obtain ⟨q, L, R⟩ := c
  cases ht : table q (R 0) with
  | none =>
    unfold step
    rw [toZ_read, show (toZ z ⟨q, L, R⟩).state = q from rfl, ht]
  | some x =>
    obtain ⟨w, dd, q'⟩ := x
    cases dd with
    | R => rw [sstep_R ht] at h; cases h
    | L => rw [sstep_L ht] at h; cases h

/-- Runs compose. -/
theorem run_add (j k : Nat) (c : Cfg) : run (j + k) c = (run j c).bind (run k) := by
  induction j generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    rw [Nat.add_right_comm]
    show (step c).bind (run (j + k)) = ((step c).bind (run j)).bind (run k)
    cases step c with
    | none => rfl
    | some d => exact ih d

/-- A run of the stream machine is a run of the machine on the integer tape. -/
theorem reaches_run {c d : SC} (h : Reaches c d) (z : Int) :
    ∃ k z', run k (toZ z c) = some (toZ z' d) ∧ (k = 0 → c = d) := by
  induction h generalizing z with
  | refl c => exact ⟨0, z, rfl, fun _ => rfl⟩
  | @step c1 d1 e1 hs _ ih =>
    obtain ⟨z1, h1⟩ := step_toZ hs z
    obtain ⟨k, z', hk, -⟩ := ih z1
    refine ⟨k + 1, z', ?_, fun h => absurd h (Nat.succ_ne_zero k)⟩
    show (step (toZ z c1)).bind (run k) = _
    rw [h1]
    exact hk

/-- Halting of the stream machine is halting on the integer tape. -/
theorem haltsFrom_run {c : SC} (h : HaltsFrom c) (z : Int) :
    ∃ k c', run k (toZ z c) = some c' ∧ step c' = none := by
  obtain ⟨d, hd, hn⟩ := h
  obtain ⟨k, z', hk, -⟩ := reaches_run hd z
  exact ⟨k, _, hk, step_toZ_none hn z'⟩

/-- The blank stream configuration in state `A` is the initial configuration. -/
theorem toZ_blank : toZ 0 ⟨.A, zeros, zeros⟩ = init := by
  unfold toZ init
  congr 1
  funext x
  split <;> rfl

end TuringOPN

end OddPerfect

#print axioms OddPerfect.TuringOPN.cons_zero
#print axioms OddPerfect.TuringOPN.tl_cons
#print axioms OddPerfect.TuringOPN.zeros_apply
#print axioms OddPerfect.TuringOPN.tl_zeros
#print axioms OddPerfect.TuringOPN.cons_false_zeros
#print axioms OddPerfect.TuringOPN.ones_zero
#print axioms OddPerfect.TuringOPN.cons_true
#print axioms OddPerfect.TuringOPN.ones_apply_zero
#print axioms OddPerfect.TuringOPN.tl_ones
#print axioms OddPerfect.TuringOPN.ones_ones
#print axioms OddPerfect.TuringOPN.ones_cons_true
#print axioms OddPerfect.TuringOPN.ones_apply_lt
#print axioms OddPerfect.TuringOPN.ones_apply_self
#print axioms OddPerfect.TuringOPN.ones_congr
#print axioms OddPerfect.TuringOPN.cons_congr
#print axioms OddPerfect.TuringOPN.SC.ext'
#print axioms OddPerfect.TuringOPN.sstep_R
#print axioms OddPerfect.TuringOPN.sstep_L
#print axioms OddPerfect.TuringOPN.Reaches.trans
#print axioms OddPerfect.TuringOPN.Reaches.of_eq
#print axioms OddPerfect.TuringOPN.Reaches.adv
#print axioms OddPerfect.TuringOPN.HaltsFrom.of_reaches
#print axioms OddPerfect.TuringOPN.skipR
#print axioms OddPerfect.TuringOPN.skipL
#print axioms OddPerfect.TuringOPN.toZ_read
#print axioms OddPerfect.TuringOPN.tape_R
#print axioms OddPerfect.TuringOPN.tape_L
#print axioms OddPerfect.TuringOPN.step_toZ_R
#print axioms OddPerfect.TuringOPN.step_toZ_L
#print axioms OddPerfect.TuringOPN.step_toZ
#print axioms OddPerfect.TuringOPN.step_toZ_none
#print axioms OddPerfect.TuringOPN.run_add
#print axioms OddPerfect.TuringOPN.reaches_run
#print axioms OddPerfect.TuringOPN.haltsFrom_run
#print axioms OddPerfect.TuringOPN.toZ_blank
