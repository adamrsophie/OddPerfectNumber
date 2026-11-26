import AxiomGateLib

/-!
# Gate control: `T.ctorIdx` with another safe body

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`Qux` is declared without the generated `Qux.ctorIdx`. The hand written pair has the generated
shape except that the safe `Qux.ctorIdx` returns the constant 7 instead of the constructor index.

Expected result: the gate rejects this file with exactly two problems, one for each constant
of the pair, both with the reason `safe body is not the generated casesOn`.
-/

namespace GateControls

set_option genCtorIdx false in
inductive Qux where
  | a
  | b

unsafe def Qux.ctorIdx._impl (x : Qux) : Nat := getObjTagNat x

@[implemented_by Qux.ctorIdx._impl]
def Qux.ctorIdx : Qux → Nat := fun _ => 7

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
