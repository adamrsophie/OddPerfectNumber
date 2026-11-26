import AxiomGateLib
import GateSecondLib

/-!
# Gate control: a `ctorIdx` pair in another module than its type

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds an unsafe definition and an `implemented_by`
attribute on purpose; files in `GateControls/` mention those words intentionally, and scans
for them exclude this folder by path.

`GateSecondLib.Far` is declared in the module `GateSecondLib` (compiled by `run.sh` from
`GateControls/GateSecondLib.lean`) without the generated `Far.ctorIdx`. This file adds the pair
by hand, with the generated shape, in its own module.

Expected result: the gate rejects this file with exactly two problems, one for each constant
of the pair, both with the reason `T is defined in another module`.
-/

namespace GateSecondLib

unsafe def Far.ctorIdx._impl (x : Far) : Nat := getObjTagNat x

@[implemented_by Far.ctorIdx._impl]
def Far.ctorIdx : Far → Nat :=
  fun x => Far.casesOn (motive := fun _ => Nat) x (nat_lit 0) (nat_lit 1)

end GateSecondLib

run_cmd AxiomGate.run AxiomGate.controlConfig
