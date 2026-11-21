import AxiomGateLib

/-!
# Gate control: unused private axiom

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file declares an axiom on purpose; files in
`GateControls/` mention the words axiom and unsafe intentionally, and scans for those words
exclude this folder by path.

Expected result: the gate rejects this file with exactly two problems, both about the axiom
itself (`...unusedAxiom: is an axiom` and its dependence on itself), although no theorem uses
it.
-/

namespace GateControls

private axiom unusedAxiom : (0 : Nat) = 1

theorem unrelated : 1 + 1 = 2 := rfl

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
