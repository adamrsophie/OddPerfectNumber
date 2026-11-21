import AxiomGateLib

/-!
# Gate control: partial declaration disguised as a compiler helper

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file adds a partial (non kernel checked for termination)
declaration on purpose; files in `GateControls/` mention the words axiom and unsafe
intentionally, and scans for those words exclude this folder by path.

`disguised` is a safe non recursive definition, so the compiler adds no helper for it. Beside
it, a hand written partial definition of another type is added directly to the environment
under the helper name `disguised._unsafe_rec`. The earlier exemption (base exists and is a
safe definition) accepted this; the tightened one must not.

Expected result: the gate rejects this file with exactly one problem, the line
`GateControls.disguised._unsafe_rec: is partial (not a compiler helper: ...)`.
-/

namespace GateControls

def disguised (n : Nat) : Nat := n + 1

end GateControls

open Lean in
run_meta addDecl <| .defnDecl {
  name := `GateControls.disguised._unsafe_rec
  levelParams := []
  type := mkForall `b .default (mkConst ``Bool) (mkConst ``Bool)
  value := mkLambda `b .default (mkConst ``Bool) (.bvar 0)
  hints := .opaque
  safety := .partial }

run_cmd AxiomGate.run AxiomGate.controlConfig
