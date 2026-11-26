import AxiomGateLib

/-!
# Gate control: `T.ctorIdx._impl` without the attribute on `T.ctorIdx`

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition on purpose; files in
`GateControls/` mention that word intentionally, and scans for it exclude this folder by path.

`Bar` is declared without the generated `Bar.ctorIdx`. `Bar.ctorIdx` is an ordinary safe
definition with no `implemented_by`; beside it, an unsafe `Bar.ctorIdx._impl` of the generated
shape is not the partner of an exempt `Bar.ctorIdx`.

Expected result: the gate rejects this file with exactly one problem,
`GateControls.Bar.ctorIdx._impl: is unsafe (not a generated ctorIdx: ...)`.
-/

namespace GateControls

set_option genCtorIdx false in
inductive Bar where
  | a
  | b

def Bar.ctorIdx : Bar → Nat
  | .a => 0
  | .b => 1

unsafe def Bar.ctorIdx._impl (x : Bar) : Nat := getObjTagNat x

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
