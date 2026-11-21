import OddPerfect

/-!
# Axiom gate

Enforces the project trust policy over the whole built library. Run after `lake build` with

    lake env lean AxiomGate.lean

The command fails (nonzero exit status) if any policy check fails.

This file is metaprogramming that runs only at elaboration time. It is not part of the
mathematical trust base: it adds no declarations that any theorem of the project uses, and
it only reads the environment produced by the kernel. All definitions here are total; the
graph traversal is a worklist loop bounded by explicit fuel, so no `partial` or `unsafe`
is used.

Checks, for every constant whose defining module is `OddPerfect` or `OddPerfect.*`
(private and auxiliary declarations included):

1. The axioms it depends on, transitively through mathlib and core, are among
   `propext`, `Classical.choice`, `Quot.sound`. This rejects `sorryAx`, the axioms that
   `native_decide` introduces (`Lean.ofReduceBool` and `Lean.trustCompiler` on older
   toolchains, an auxiliary axiom `f._native.native_decide.ax_*` on Lean 4.33), and any
   added axiom. The traversal walks
   kernel bodies directly with one shared visited set; the per-constant attribution in the
   failure report, and a consistency cross-check, use core `Lean.collectAxioms` (the
   traversal behind `#print axioms`).
2. It is not an axiom, not `unsafe`, not `partial`, not `opaque`, and carries neither
   `@[implemented_by]` nor `@[extern]`. The one exemption is the compiler auxiliary
   `f._unsafe_rec`, which is `partial` but harmless when `f` is a safe definition.
3. `OddPerfectConjecture` is a definition of type `Prop`, and no project constant has a
   statement that is syntactically `OddPerfectConjecture`, its unfolded body, or the
   negation of either, unless its name ends in `oddPerfectConjecture`; such a theorem is
   printed prominently with its axioms instead.

Not detectable from the environment: a declaration added with `debug.skipKernelTC` (the
kernel never checked it; replaying the environment with a checker such as `lean4checker`
covers that), and custom elaborators or macros in project files (they leave no trace in
`ConstantInfo` beyond the declarations they produce, which are checked).
-/

open Lean Elab Command

namespace AxiomGate

/-- The only axioms the project may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Which constants the gate checks. -/
structure Config where
  /-- Modules whose constants are checked. -/
  modulePred : Name → Bool := fun m => m == `OddPerfect || (`OddPerfect).isPrefixOf m
  /-- Also check the declarations of the file being elaborated (used by the tests). -/
  includeCurrent : Bool := false

/-- Constants referenced directly by a constant, following the cases of `Lean.collectAxioms`. -/
def directDeps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- All axioms reachable from `roots`, with one shared visited set. Also returns the number of
constants visited. Total: the loop runs at most `fuel` steps and fails if fuel runs out. -/
def reachableAxioms (env : Environment) (roots : Array Name) (fuel : Nat) :
    Except String (NameSet × Nat) := Id.run do
  let mut stack := roots
  let mut visited : NameSet := {}
  let mut axioms : NameSet := {}
  for _ in [0:fuel] do
    match stack.back? with
    | none => return .ok (axioms, visited.size)
    | some n =>
      stack := stack.pop
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        if ci matches .axiomInfo _ then axioms := axioms.insert n
        for d in directDeps ci do
          unless visited.contains d do stack := stack.push d
  return .error s!"traversal fuel {fuel} exhausted"

/-- Whether `e` is `¬ p` or `p → False`, returning `p`. -/
def negated? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .app (.const ``Not _) p => some p
  | .forallE _ p (.const ``False _) _ => if p.hasLooseBVars then none else some p
  | _ => none

/-- Run every check. Throws an error listing all offenders, or logs one summary line. -/
def run (cfg : Config := {}) : CommandElabM Unit := do
  let t0 ← IO.monoMsNow
  let env := (← getEnv).setExporting false
  let names := env.header.moduleNames
  let projModules := (List.range names.size).filter fun i => cfg.modulePred names[i]!
  -- Every constant stored in a project module's olean, private and auxiliary ones included.
  -- (`constNames` can list a name twice, hence the deduplication.)
  let mut consts : Array ConstantInfo := #[]
  let mut listed : NameSet := {}
  for i in projModules do
    for n in env.header.moduleData[i]!.constNames do
      if listed.contains n then continue
      listed := listed.insert n
      let some ci := env.find? n | throwError "axiom gate: {n} listed in {names[i]!} but not found"
      consts := consts.push ci
  if cfg.includeCurrent then
    consts := env.constants.foldStage2 (fun acc _ ci => acc.push ci) consts
  let mut errors : Array MessageData := #[]
  -- Check 2: forbidden kinds of declarations.
  for ci in consts do
    let n := ci.name
    let mut bad : Array String := #[]
    if ci matches .axiomInfo _ then bad := bad.push "is an axiom"
    if ci.isUnsafe then bad := bad.push "is unsafe"
    -- The compiler adds a `partial` auxiliary `f._unsafe_rec` for code generation even for
    -- ordinary recursive definitions. It is harmless when `f` itself is a safe kernel
    -- definition: the kernel never lets a safe constant refer to a partial one. A genuine
    -- `partial def f` is still rejected, because `f` itself is then an opaque constant.
    let compilerAux := match n with
      | .str p "_unsafe_rec" =>
        match env.find? p with
        | some (.defnInfo v) => v.safety == .safe
        | _ => false
      | _ => false
    if ci.isPartial && !compilerAux then bad := bad.push "is partial"
    if ci matches .opaqueInfo _ then bad := bad.push "is opaque"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      bad := bad.push "has @[implemented_by]"
    if isExtern env n then bad := bad.push "has @[extern]"
    unless bad.isEmpty do
      errors := errors.push m!"{n}: {", ".intercalate bad.toList}"
  -- Check 1: axioms, by one shared traversal of the whole dependency closure.
  let (seen, visitedCount) ← match reachableAxioms env (consts.map (·.name)) 100000000 with
    | .ok r => pure r
    | .error e => throwError "axiom gate: {e}"
  let t1 ← IO.monoMsNow
  let badAxioms := seen.toList.filter (!allowedAxioms.contains ·)
  -- Cross-check against core `collectAxioms` and attribute offenders per constant.
  let mut coreSeen : NameSet := {}
  for ci in consts do
    let axs ← collectAxioms ci.name
    coreSeen := axs.foldl (·.insert ·) coreSeen
    let offending := axs.toList.filter (!allowedAxioms.contains ·)
    unless offending.isEmpty do
      errors := errors.push m!"{ci.name}: depends on {offending}"
  let t2 ← IO.monoMsNow
  unless coreSeen.toList.all seen.contains && seen.toList.all coreSeen.contains do
    errors := errors.push
      m!"axiom sets disagree: traversal {seen.toList}, collectAxioms {coreSeen.toList}"
  if !badAxioms.isEmpty && errors.isEmpty then
    errors := errors.push m!"forbidden axioms reachable: {badAxioms}"
  -- Check 3: the conjecture.
  let conj := ``OddPerfectConjecture
  let mut resolutions : Array MessageData := #[]
  match env.find? conj with
  | some (.defnInfo v) =>
    unless v.type == .sort .zero do
      errors := errors.push m!"{conj} has type {v.type}, expected Prop"
    let body := v.value
    let isConj (e : Expr) : Bool := e.consumeMData == .const conj [] || e.consumeMData == body
    for ci in consts do
      unless ci matches .thmInfo _ || ci matches .defnInfo _ || ci matches .opaqueInfo _ do
        continue
      let ty := ci.type
      let kind? : Option String :=
        if isConj ty then some "OddPerfectConjecture"
        else match negated? ty with
          | some p => if isConj p then some "the negation of OddPerfectConjecture" else none
          | none => none
      if let some kind := kind? then
        if ci.name matches .str _ "oddPerfectConjecture" then
          let axs ← collectAxioms ci.name
          resolutions := resolutions.push
            m!"!!! RESOLUTION: {ci.name} proves {kind}; axioms: {axs.toList} !!!"
        else
          errors := errors.push m!"{ci.name}: states {kind} but is not named oddPerfectConjecture"
  | some _ => errors := errors.push m!"{conj} is not a definition"
  | none => errors := errors.push m!"{conj} not found"
  for r in resolutions do logInfo r
  unless errors.isEmpty do
    throwError m!"axiom gate FAILED ({errors.size} problems):\n" ++
      MessageData.joinSep errors.toList "\n"
  let thms : Nat := consts.foldl (fun (k : Nat) ci => if ci matches .thmInfo _ then k + 1 else k) 0
  let t3 ← IO.monoMsNow
  logInfo m!"axiom gate OK: {projModules.length} modules, {consts.size} constants checked, \
    {thms} theorems, axioms seen {toString seen.toList}; enumeration and traversal of \
    {visitedCount} constants {t1 - t0} ms, collectAxioms cross-check {t2 - t1} ms, total {t3 - t0} ms"

end AxiomGate

run_cmd AxiomGate.run
