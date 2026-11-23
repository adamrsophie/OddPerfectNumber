/-!
# Contribution gate

Checks the contributed proofs in `Contributions/`. This file is not compiled alone: the runner
`scripts/Controls/contribution_gate.sh` compiles every `Contributions/<Name>.lean` outside the
library, then puts `import OddPerfect.Steps` and one `import ContributionCheck.<Name>` for each
of them in front of this text and runs the result.

For every imported module `ContributionCheck.<Name>` the gate requires:

1. `OddPerfect.Steps.<Name>` is a definition of type `Prop` in the module `OddPerfect.Steps`;
2. `OddPerfect.Proofs.<Name>` is a theorem defined in the contributed module, without universe
   parameters, whose statement is exactly the constant `OddPerfect.Steps.<Name>`;
3. every constant of the contributed module (private and auxiliary ones included) depends only
   on the axioms `propext`, `Classical.choice`, `Quot.sound`, and is not an axiom, not
   `unsafe`, not `partial`, not `opaque`, and carries neither `@[implemented_by]` nor
   `@[extern]`.

Nothing printed while a contributed file compiles is used. The gate reads only the
environment. It is metaprogramming that runs at elaboration time and is not part of the
mathematical trust base. The format scan `scripts/Controls/contribution_scan.py` covers what a
compiled environment cannot show (options that skip the kernel, code that runs at elaboration).
-/

open Lean Elab Command

namespace ContributionGate

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def run : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let some stepsIdx := env.getModuleIdx? `OddPerfect.Steps
    | throwError "contribution gate: OddPerfect.Steps is not imported"
  let isStep (n : Name) : Bool :=
    n.getPrefix == `OddPerfect.Steps &&
      (match env.find? n with
        | some (.defnInfo v) => v.type.isProp && v.levelParams.isEmpty
        | _ => false)
  let steps := env.header.moduleData[stepsIdx.toNat]!.constNames.filter isStep
  let mut errors : Array MessageData := #[]
  let mut proved : Array Name := #[]
  for i in [0:names.size] do
    let m := names[i]!
    unless m.getPrefix == `ContributionCheck do continue
    let .str _ short := m | continue
    let step := Name.str `OddPerfect.Steps short
    let thm := Name.str `OddPerfect.Proofs short
    unless steps.contains step do
      errors := errors.push m!"{short}: OddPerfect.Steps has no step of this name"
    match env.find? thm with
    | some (.thmInfo v) =>
      unless (env.getModuleIdxFor? thm).map (·.toNat) == some i do
        errors := errors.push m!"{short}: {thm} is not defined in the contributed file"
      unless v.levelParams.isEmpty && v.type == mkConst step do
        errors := errors.push m!"{short}: the statement of {thm} is not exactly {step}"
    | _ => errors := errors.push m!"{short}: the contributed file has no theorem {thm}"
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n
        | throwError "contribution gate: {n} listed in {m} but not found"
      let mut bad : Array String := #[]
      if ci matches .axiomInfo _ then bad := bad.push "is an axiom"
      if ci.isUnsafe then bad := bad.push "is unsafe"
      if ci.isPartial then bad := bad.push "is partial"
      if ci matches .opaqueInfo _ then bad := bad.push "is opaque"
      if (Compiler.implementedByAttr.getParam? env n).isSome then
        bad := bad.push "has @[implemented_by]"
      if isExtern env n then bad := bad.push "has @[extern]"
      let axs ← collectAxioms n
      let extra := axs.toList.filter (!allowedAxioms.contains ·)
      unless extra.isEmpty do bad := bad.push s!"depends on the axioms {extra}"
      unless bad.isEmpty do
        errors := errors.push m!"{short}: {n} {", ".intercalate bad.toList}"
    proved := proved.push step
  unless errors.isEmpty do
    throwError m!"contribution gate FAILED ({errors.size} problems):\n" ++
      MessageData.joinSep errors.toList "\n"
  let stillOpen := steps.filter (!proved.contains ·)
  logInfo m!"contribution gate OK: {proved.size} proofs checked, {steps.size} steps, \
    open: {stillOpen.toList.map fun n => n.componentsRev.head!}"

end ContributionGate

run_cmd ContributionGate.run
