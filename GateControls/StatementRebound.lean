import StatementGateLib

/-!
# Gate control: an inventory entry paired with another library theorem

A control for the statement gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles
`StatementGate.lean` as the module `StatementGateLib`.

The check runs with the inventory of the gate in which the entry of `StatementGate.lower_bound`
names `OddPerfect.LowerBound.lower_bound` (the bound `10 ^ 79`) instead of the theorem that
proves the restatement, `OddPerfect.LowerBoundTwo.lower_bound`.

Expected result: the file fails with exactly one problem, the line
`StatementGate.lower_bound: proved by OddPerfect.LowerBoundTwo.lower_bound, expected
OddPerfect.LowerBound.lower_bound`.
-/

run_cmd StatementGate.checkWith (StatementGate.expected.map fun e =>
  if e.1 == `StatementGate.lower_bound then (e.1, ``OddPerfect.LowerBound.lower_bound) else e)
