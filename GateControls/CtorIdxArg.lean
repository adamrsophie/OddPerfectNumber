import AxiomGateLib

/-!
# Gate control: `T.ctorIdx` with another argument type

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`Arg` is declared without the generated `Arg.ctorIdx`. The hand written pair has the generated
shape except that both functions take a `Bool` instead of an `Arg`.

Expected result: the gate rejects this file with exactly two problems, one for each constant
of the pair, both with the reason `argument type is not T applied to its parameters and
indices`.
-/

namespace GateControls

set_option genCtorIdx false in
inductive Arg where
  | a
  | b

unsafe def Arg.ctorIdx._impl (x : Bool) : Nat := getObjTagNat x

@[implemented_by Arg.ctorIdx._impl]
def Arg.ctorIdx : Bool → Nat :=
  fun x => Bool.casesOn (motive := fun _ => Nat) x (nat_lit 0) (nat_lit 1)

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
