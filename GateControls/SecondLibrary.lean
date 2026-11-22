import AxiomGateLib
import GateSecondLib

/-!
# Gate control: a module outside the checked library

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate as
the module `AxiomGateLib` and `GateControls/GateSecondLib.lean` as the module `GateSecondLib`,
both in a temporary folder.

The gate runs with check 5 switched on. `AxiomGateLib` is the controls' own copy of the gate,
and the library modules are not checked by the control configuration; both are exempted.
`GateSecondLib` is not.

Expected result: the gate rejects this file with exactly one problem, the line
`module GateSecondLib is not checked and comes neither from the toolchain nor from a package`.
-/

run_cmd AxiomGate.run ({ AxiomGate.controlConfig with
  foreignCheck := true, foreignExempt := fun m => m == `AxiomGateLib || (`OddPerfect).isPrefixOf m })
