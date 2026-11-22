import AxiomGateLib

/-!
# Gate control: a declaration that the kernel never checked

A control for the axiom gate and the kernel replay, not part of the library: nothing imports
it and the library build never compiles it. Run it only through `GateControls/run.sh`, which
compiles the gate as the module `AxiomGateLib`.

With the option `debug.skipKernelTC` the theorem `GateControls.unchecked` below states `False`
with the proof term `True.intro`, and the kernel never sees it. It depends on nothing, so the
axiom gate accepts the file. The runner then compiles the file as the module `GateSkipKernel`
and replays it with `leanchecker` of the toolchain, which must reject it. The source scan
rejects the option itself in a library file.

Expected result: the gate accepts this file (exit status 0); the replay of the module
`GateSkipKernel` fails with `leanchecker found a problem in GateSkipKernel`.
-/

open Lean in
/-- A theorem of `False` with the proof term `True.intro`, which the kernel rejects. -/
def GateControls.uncheckedDecl : Declaration :=
  .thmDecl
    { name := `GateControls.unchecked, levelParams := [],
      type := .const ``False [], value := .const ``True.intro [] }

open Lean Elab Command in
set_option debug.skipKernelTC true in
run_cmd liftCoreM (addDecl GateControls.uncheckedDecl)

run_cmd AxiomGate.run AxiomGate.controlConfig
