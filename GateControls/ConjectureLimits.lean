import AxiomGateLib

/-!
# Gate control: reformulations that check 3 does not detect

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Each theorem below is equivalent to the conjecture or to its negation, but only by a proof,
not by definitional unfolding, so check 3 does not report it. The file records these limits:
if a later version of the gate detects one of them, the runner reports the change. The
theorems are added by the command `unchecked` without a kernel check (their proof term is
`True.intro`); the gate looks at statements only.

Expected result: the gate accepts this file (exit status 0).
-/

open Lean Elab Command in
/-- `unchecked n : t` adds a theorem `n` with statement `t` and the proof term `True.intro`,
with the kernel check switched off, so that open or false statements can be tested. -/
elab "unchecked " n:ident " : " t:term : command => do
  let ty ← liftTermElabM do
    let e ← Term.elabTermAndSynthesize t (some (.sort .zero))
    instantiateMVars e
  withScope (fun s => { s with opts := debug.skipKernelTC.set s.opts true }) do
    liftCoreM <| addDecl <| .thmDecl
      { name := (← getCurrNamespace) ++ n.getId, levelParams := [], type := ty,
        value := mkConst ``True.intro }

namespace GateControls

/-- An alias of `OddPerfect` that default transparency does not unfold. -/
@[irreducible] def HiddenOddPerfect (N : ℕ) : Prop := OddPerfect N

unchecked extraHypothesis : True → OddPerfectConjecture
unchecked positiveOnly : ∀ N : ℕ, 0 < N → ¬ OddPerfect N
unchecked viaIsEmpty : IsEmpty {N : ℕ // OddPerfect N}
unchecked viaIff : ∀ N : ℕ, OddPerfect N ↔ False
unchecked viaAnd : OddPerfectConjecture ∧ True
unchecked viaIrreducible : ∀ N : ℕ, ¬ HiddenOddPerfect N
unchecked viaSigma : ∀ N : ℕ, Odd N → ArithmeticFunction.sigma 1 N ≠ 2 * N

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
