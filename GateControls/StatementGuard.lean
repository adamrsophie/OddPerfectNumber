import StatementGateLib

/-!
# Gate control: a restatement that uses a definition outside the allowed list

A control for the statement gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles
`StatementGate.lean` as the module `StatementGateLib`.

The restatement below matches its theorem, but it is stated about the local definition
`GateControls.OddPerfect` instead of `_root_.OddPerfect`. The check of `StatementGate.lean`
looks at every theorem `StatementGate.*`, the restatements it imports included, and must
reject this one.

Expected result: the file fails with exactly one problem, the line
`StatementGate.shadowed: mentions GateControls.OddPerfect, a project definition outside the
allowed list`.
-/

namespace GateControls

/-- A predicate with the name of the project's, true of no number. -/
def OddPerfect (_ : ℕ) : Prop := False

/-- Reads like the headline theorem, but `OddPerfect` here is the local definition. -/
theorem seven_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 7 ≤ N.primeFactors.card :=
  h.elim

end GateControls

theorem StatementGate.shadowed :
    ∀ {N : ℕ}, GateControls.OddPerfect N → 7 ≤ (Nat.primeFactors N).card :=
  @GateControls.seven_le_card_primeFactors

run_cmd StatementGate.check
