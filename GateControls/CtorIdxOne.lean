import AxiomGateLib

/-!
# Gate control: a `ctorIdx` pair for a type with one constructor

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`Single` has one constructor, so Lean generates `Single.ctorIdx` without `implemented_by` and
without a partner. Here the generated function is switched off and a pair is written by hand,
with the safe function equal to cases on `Single` returning 0.

Expected result: the gate rejects this file with exactly two problems, one for each constant
of the pair, both with the reason `T has one constructor`.
-/

namespace GateControls

set_option genCtorIdx false in
inductive Single where
  | only

unsafe def Single.ctorIdx._impl (x : Single) : Nat := getObjTagNat x

@[implemented_by Single.ctorIdx._impl]
def Single.ctorIdx : Single → Nat :=
  fun x => Single.casesOn (motive := fun _ => Nat) x (nat_lit 0)

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
