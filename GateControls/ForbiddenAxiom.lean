import AxiomGateLib

/-!
# Gate control: theorem depending on a forbidden axiom

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file declares an axiom on purpose; files in
`GateControls/` mention the words axiom and unsafe intentionally, and scans for those words
exclude this folder by path.

Expected result: the gate rejects this file with three problems, two about the axiom itself
(it is an axiom and depends on itself) and the line
`GateControls.usesBadAxiom: depends on [GateControls.badAxiom]`.
-/

namespace GateControls

axiom badAxiom : (1 : Nat) = 2

theorem usesBadAxiom : (1 : Nat) = 2 := badAxiom

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
