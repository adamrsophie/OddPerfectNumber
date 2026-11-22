import StatementGateLib

/-!
# Gate control: a restatement without an inventory entry

A control for the statement gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles
`StatementGate.lean` as the module `StatementGateLib`.

The restatement below is correct and mentions only allowed definitions, but the inventory
`StatementGate.expected` has no entry for it. The check with the inventory of the gate must
reject it.

Expected result: the file fails with exactly one problem, the line
`StatementGate.extra: restated but not in the expected list`.
-/

theorem StatementGate.extra :
    ∀ {N : ℕ}, _root_.OddPerfect N → 10 ^ 79 < N :=
  @OddPerfect.LowerBound.lower_bound

run_cmd StatementGate.check
