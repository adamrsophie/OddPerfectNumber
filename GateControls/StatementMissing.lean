import StatementGateLib

/-!
# Gate control: an inventory entry without its restatement

A control for the statement gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles
`StatementGate.lean` as the module `StatementGateLib`.

The check runs with the inventory of the gate plus one entry, `StatementGate.lower_bound_79`
for the theorem `OddPerfect.LowerBound.lower_bound` (the bound `10 ^ 79`), which no theorem of
the environment restates. This is the state of a gate file from which a restatement was
deleted while its inventory entry stayed.

Expected result: the file fails with exactly one problem, the line
`StatementGate.lower_bound_79: expected restatement of OddPerfect.LowerBound.lower_bound is
missing`.
-/

run_cmd StatementGate.checkWith (StatementGate.expected ++
  [(`StatementGate.lower_bound_79, ``OddPerfect.LowerBound.lower_bound)])
