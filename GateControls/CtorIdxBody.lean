import AxiomGateLib

/-!
# Gate control: `T.ctorIdx._impl` with another body

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`Baz` is declared without the generated `Baz.ctorIdx`. The hand written pair has the generated
shape except that the body of `Baz.ctorIdx._impl` is a constant, not `getObjTagNat`.

Expected result: the gate rejects this file with exactly two problems, one for each constant
of the pair, both with the reason `_impl body is not getObjTagNat`.
-/

namespace GateControls

set_option genCtorIdx false in
inductive Baz where
  | a
  | b

unsafe def Baz.ctorIdx._impl (_ : Baz) : Nat := 7

@[implemented_by Baz.ctorIdx._impl]
def Baz.ctorIdx : Baz → Nat
  | .a => 0
  | .b => 1

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
