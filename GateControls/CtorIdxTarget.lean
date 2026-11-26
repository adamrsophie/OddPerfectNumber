import AxiomGateLib

/-!
# Gate control: `T.ctorIdx` implemented by another function

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds unsafe definitions and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`Foo` is declared without the generated `Foo.ctorIdx`. The hand written pair has the generated
shape except that `Foo.ctorIdx` is implemented by `Foo.otherImpl`, not by `Foo.ctorIdx._impl`.

Expected result: the gate rejects this file with exactly three problems: `Foo.ctorIdx` keeps
its `@[implemented_by]` complaint (reason: the target), `Foo.otherImpl` is unsafe, and
`Foo.ctorIdx._impl` is unsafe (it is not the partner of an exempt `Foo.ctorIdx`).
-/

namespace GateControls

set_option genCtorIdx false in
inductive Foo where
  | a
  | b

unsafe def Foo.ctorIdx._impl (x : Foo) : Nat := getObjTagNat x

unsafe def Foo.otherImpl (x : Foo) : Nat := getObjTagNat x

@[implemented_by Foo.otherImpl]
def Foo.ctorIdx : Foo → Nat
  | .a => 0
  | .b => 1

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
