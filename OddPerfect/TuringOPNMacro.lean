import OddPerfect.TuringOPNTape

/-!
# A 24 state Turing machine for odd perfect numbers: macro steps

Tape layouts (left to right, `0^∞` on both ends) used by the machine of
`OddPerfect/TuringOPNCode.lean` while it tests one candidate `N`:
`1^s 0 1^r 0 [first block, a cells] 0 [second block, m cells]` with `s + r = N` (spent and
remaining budget) and `a + m = N` (`m` is the trial divisor). The layouts below are configurations
seen from the head (`SC`). Each macro step is proved by the same stepping script: single steps
are computed by `simp`, blocks of ones are crossed with `skipR` and `skipL`, and the run stops
at the first configuration equal to the target.
-/

set_option maxRecDepth 20000

namespace OddPerfect

namespace TuringOPN

/-- State `B` inside the divisibility pass: `1^s 0 1^r 0 1^i [head] 1^(k - 1) 0 1^u 0 1^v`, the
head on the first cell after the `i` cells already passed (on the separator if `k = 0`). -/
def cQ1 (s r i k u v : Nat) : SC :=
  ⟨.B, ones i (cons false (ones r (cons false (ones s zeros)))),
    ones k (cons false (ones u (cons false (ones v zeros))))⟩

/-- State `K` at the first unit of a charge: the head on the separator before the second block,
whose first cell is the hole. -/
def cS1a (s r a v : Nat) : SC :=
  ⟨.K, ones a (cons false (ones r (cons false (ones s zeros)))),
    cons false (cons false (ones v zeros))⟩

/-- State `K` at a later unit of a charge: the hole of the second block at position `t + 2`. -/
def cS1b (s r a t v : Nat) : SC :=
  ⟨.K, ones t (cons false (ones a (cons false (ones r (cons false (ones s zeros)))))),
    ones 1 (cons false (ones v zeros))⟩

/-- State `A` on the last cell of the first block (of `a + 1` cells); the second block is full. -/
def cI2 (s r a m : Nat) : SC :=
  ⟨.A, ones a (cons false (ones r (cons false (ones s zeros)))),
    ones 1 (cons false (ones m zeros))⟩

/-- The restart configuration of the candidate `n + 2`: state `B` on the tape
`1 0 1^(n + 1) 0 [1^n] 0 0 1`, the head on the first cell of the bracketed block. -/
def rQ (n : Nat) : SC := cQ1 1 (n + 1) 0 n 0 1

/-- A block of zero ones is empty. -/
theorem ones_eq_self {k : Nat} (h : k = 0) (s : Strm) : ones k s = s := by
  subst h
  rfl

/-- One round trip of the divisibility pass, without wrap of the hole in the second block. -/
theorem mL1 (s r i k u v : Nat) :
    Reaches (cQ1 s r i (k + 1) u (v + 1)) (cQ1 s r (i + 1) k (u + 1) v) := by
  rcases k with _ | k
  all_goals
  (
    simp only [cQ1]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [ones_eq_self, Nat.zero_add])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_apply_zero,
             tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
             Nat.zero_add, ones_eq_self, Nat.sub_self, ne_eq, Option.some_ne_none,
             not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             ones_apply_zero, tl_ones, ones_ones, cons_true, Nat.add_sub_cancel,
             Nat.add_sub_cancel_left, Nat.zero_add, ones_eq_self, Nat.sub_self])
  )

/-- One round trip of the divisibility pass, with wrap of the hole in the second block. -/
theorem mL2 (s r i k u : Nat) :
    Reaches (cQ1 s r i (k + 1) u 0) (cQ1 s r (i + 1) k 0 u) := by
  rcases k with _ | k
  all_goals
  (
    simp only [cQ1]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [cons_false_zeros, ones_eq_self,
              Nat.zero_add])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
             ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
             Nat.add_sub_cancel_left, Nat.zero_add, ones_eq_self, Nat.sub_self, ne_eq,
             Option.some_ne_none, not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true,
             cons_false_zeros, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.zero_add,
             ones_eq_self, Nat.sub_self])
  )

/-- End of the pass with the hole back at its start: the trial divisor divides. -/
theorem mL3 (s r a v : Nat) :
    Reaches (cQ1 s r a 0 0 v) (cS1a s r a v) := by
  simp only [cQ1, cS1a]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_eq_self, ne_eq,
           Option.some_ne_none, not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           ones_eq_self])

/-- End of the pass with the hole elsewhere: the trial divisor does not divide. -/
theorem mL4 (s r a u v : Nat) :
    Reaches (cQ1 s r (a + 1) 0 (u + 1) v) (cI2 s r a (u + v + 2)) := by
  simp only [cQ1, cI2]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_apply_zero, tl_ones,
           ones_ones, cons_true, Nat.add_sub_cancel, ones_eq_self, ne_eq, Option.some_ne_none,
           not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           ones_apply_zero, tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, ones_eq_self])

/-- First unit of the charge of a divisor against the budget. -/
theorem mL5a (s r a v : Nat) :
    Reaches (cS1a s (r + 1) a (v + 1)) (cS1b (s + 1) r a 0 v) := by
  rcases a with _ | a
  all_goals
  (
    simp only [cS1a, cS1b]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [ones_eq_self])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_apply_zero,
             tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
             ones_eq_self, Nat.sub_self, ne_eq, Option.some_ne_none, not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             ones_apply_zero, tl_ones, ones_ones, cons_true, Nat.add_sub_cancel,
             Nat.add_sub_cancel_left, ones_eq_self, Nat.sub_self])
  )

/-- A further unit of the charge. -/
theorem mL5b (s r a t v : Nat) :
    Reaches (cS1b s (r + 1) a t (v + 1)) (cS1b (s + 1) r a (t + 1) v) := by
  rcases a with _ | a
  all_goals
  (
    simp only [cS1b]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [ones_eq_self])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_apply_zero,
             tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
             ones_eq_self, ne_eq, Option.some_ne_none, not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             ones_apply_zero, tl_ones, ones_ones, cons_true, Nat.add_sub_cancel,
             Nat.add_sub_cancel_left, ones_eq_self])
  )

/-- Last unit of the charge of the divisor 1 (not used from a restart, kept for completeness). -/
theorem mL6a (s r a : Nat) :
    Reaches (cS1a s (r + 1) (a + 1) 0) (cI2 (s + 1) r a 1) := by
  simp only [cS1a, cI2]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
           ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
           Nat.add_sub_cancel_left, ones_eq_self, Nat.sub_self, ne_eq, Option.some_ne_none,
           not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros,
           Nat.add_sub_cancel, Nat.add_sub_cancel_left, ones_eq_self, Nat.sub_self])

/-- Last unit of the charge of a divisor at least 2. -/
theorem mL6b (s r a t : Nat) :
    Reaches (cS1b s (r + 1) (a + 1) t 0) (cI2 (s + 1) r a (t + 2)) := by
  simp only [cS1b, cI2]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [cons_true, ones_ones, cons_false_zeros,
            ones_zero, ones_eq_self, Nat.sub_self, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
            Nat.sub_add_cancel, Nat.add_zero, Nat.zero_add])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
           ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
           Nat.add_sub_cancel_left, ones_eq_self, ne_eq, Option.some_ne_none, not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros,
           Nat.add_sub_cancel, Nat.add_sub_cancel_left, ones_eq_self])

/-- Next trial divisor: the first block shrinks by one cell, the second grows by one. -/
theorem mL7 (s r a m : Nat) :
    Reaches (cI2 s r a m) (cQ1 s r 0 a 0 m) := by
  rcases a with _ | a
  all_goals
  (
    simp only [cQ1, cI2]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_apply_zero,
             tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, ones_eq_self, Nat.sub_self, ne_eq,
             Option.some_ne_none, not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             ones_apply_zero, tl_ones, ones_ones, cons_true, Nat.add_sub_cancel, ones_eq_self,
             Nat.sub_self])
  )

/-- Budget exhausted at the first unit of a charge: restart with the next candidate. -/
theorem mL8a (a v : Nat) :
    Reaches (cS1a (a + v + 2) 0 (a + 1) v) (rQ (a + v + 2)) := by
  simp only [cQ1, cS1a, rQ]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [cons_true, ones_ones, cons_false_zeros,
            ones_zero, ones_eq_self, Nat.sub_self, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
            Nat.sub_add_cancel, Nat.add_zero, Nat.zero_add])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
           ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
           Nat.add_sub_cancel_left, Nat.sub_add_cancel, ones_eq_self, Nat.sub_self, ne_eq,
           Option.some_ne_none, not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros,
           Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_add_cancel, ones_eq_self,
           Nat.sub_self])

/-- Budget exhausted at a later unit of a charge: restart with the next candidate. -/
theorem mL8b (a t v : Nat) :
    Reaches (cS1b (a + t + v + 2) 0 a t v) (rQ (a + t + v + 2)) := by
  rcases a with _ | a
  all_goals
  (
    simp only [cQ1, cS1b, rQ]
    repeat
      first
        | (focus
            refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
            all_goals (try simp (disch := omega) only [cons_true, ones_ones, cons_false_zeros,
              ones_zero, ones_eq_self, Nat.sub_self, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
              Nat.sub_add_cancel, Nat.add_zero, Nat.zero_add])
            all_goals
              (repeat
                (first
                  | (refine ones_congr (by omega) ?_)
                  | (refine cons_congr _ ?_)
                  | rfl))
            done)
        | (refine skipR (by exact rfl) ?_)
        | (refine skipL (by exact rfl) (by omega) ?_)
        | (refine Reaches.adv ?_ ?_
           · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
             ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
             Nat.add_sub_cancel_left, Nat.sub_add_cancel, Nat.zero_add, ones_eq_self, Nat.sub_self,
             ne_eq, Option.some_ne_none, not_false_eq_true]
           simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
             zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true,
             cons_false_zeros, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_add_cancel,
             Nat.zero_add, ones_eq_self, Nat.sub_self])
  )

/-- Budget exhausted exactly when the last divisor (the candidate itself) is to be charged. -/
theorem mL10 (s v : Nat) :
    Reaches (cS1a s 0 0 v)
      ⟨.V, cons false (cons false (ones (s + 1) zeros)), cons false (ones v zeros)⟩ := by
  simp only [cS1a]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, ones_ones, cons_true,
           ones_eq_self, ne_eq, Option.some_ne_none, not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           ones_ones, cons_true, ones_eq_self])

/-- From the blank tape the machine reaches the restart configuration of the candidate 5. -/
theorem mL0 :
    Reaches ⟨.A, zeros, zeros⟩ (rQ 3) := by
  simp only [cQ1, rQ]
  repeat
    first
      | (focus
          refine Reaches.of_eq (SC.ext' rfl ?_ ?_)
          all_goals (try simp (disch := omega) only [])
          all_goals
            (repeat
              (first
                | (refine ones_congr (by omega) ?_)
                | (refine cons_congr _ ?_)
                | rfl))
          done)
      | (refine skipR (by exact rfl) ?_)
      | (refine skipL (by exact rfl) (by omega) ?_)
      | (refine Reaches.adv ?_ ?_
         · simp (disch := omega) only [sstep, table, cons_zero, tl_cons, zeros_apply, tl_zeros,
           ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros, Nat.add_sub_cancel,
           Nat.add_sub_cancel_left, ones_eq_self, Nat.sub_self, ne_eq, Option.some_ne_none,
           not_false_eq_true]
         simp (disch := omega) only [sstep, table, nxt, Option.getD_some, cons_zero, tl_cons,
           zeros_apply, tl_zeros, ones_apply_zero, tl_ones, ones_ones, cons_true, cons_false_zeros,
           Nat.add_sub_cancel, Nat.add_sub_cancel_left, ones_eq_self, Nat.sub_self])

/-- The configuration reached in `mL10` has no successor: state `V` reads 0. -/
theorem mL10_halt (s v : Nat) :
    sstep ⟨.V, cons false (cons false (ones (s + 1) zeros)), cons false (ones v zeros)⟩ =
      none :=
  rfl

end TuringOPN

end OddPerfect

#print axioms OddPerfect.TuringOPN.mL1
#print axioms OddPerfect.TuringOPN.mL2
#print axioms OddPerfect.TuringOPN.mL3
#print axioms OddPerfect.TuringOPN.mL4
#print axioms OddPerfect.TuringOPN.mL5a
#print axioms OddPerfect.TuringOPN.mL5b
#print axioms OddPerfect.TuringOPN.mL6a
#print axioms OddPerfect.TuringOPN.mL6b
#print axioms OddPerfect.TuringOPN.mL7
#print axioms OddPerfect.TuringOPN.mL8a
#print axioms OddPerfect.TuringOPN.mL8b
#print axioms OddPerfect.TuringOPN.mL10
#print axioms OddPerfect.TuringOPN.mL0
#print axioms OddPerfect.TuringOPN.mL10_halt
#print axioms OddPerfect.TuringOPN.ones_eq_self
