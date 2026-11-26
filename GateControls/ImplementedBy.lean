import AxiomGateLib

/-!
# Gate control: `@[implemented_by]` on an ordinary definition

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

Expected result: the gate rejects this file with exactly two problems,
`GateControls.slowId: has @[implemented_by]` and `GateControls.fastId: is unsafe`.
-/

namespace GateControls

unsafe def fastId (n : Nat) : Nat := n

@[implemented_by fastId]
def slowId (n : Nat) : Nat := n

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
