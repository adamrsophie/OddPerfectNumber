import AxiomGateLib

/-!
# Gate control: the conjecture in other words

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`.

Check 3 compares statements with the conjecture up to definitional unfolding. Each theorem
below states the conjecture or its negation in a form that differs from
`OddPerfectConjecture` as an expression. They are added by the command `unchecked` without a
kernel check (their proof term is `True.intro`), because the conjecture cannot be proved; the
gate looks at statements only, so this does not change what check 3 sees.

Expected result: the gate rejects this file with exactly one problem per theorem, each a line
`GateControls.<name>: states ... but is not named oddPerfectConjecture`.
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

/-- An alias of `OddPerfect`. -/
def AliasOddPerfect (N : ℕ) : Prop := OddPerfect N

unchecked viaFalse : ∀ n : ℕ, OddPerfect n → False
unchecked viaNotExists : ¬ ∃ N : ℕ, OddPerfect N
unchecked viaImplicit : ∀ {n : ℕ}, ¬ OddPerfect n
unchecked viaAlias : ∀ N : ℕ, ¬ AliasOddPerfect N
unchecked viaCurried : ∀ N : ℕ, Odd N → N.Perfect → False
unchecked viaUnfolded : ∀ N : ℕ, Odd N ∧ N.Perfect → False
unchecked viaExists : ∃ N : ℕ, OddPerfect N
unchecked viaNegation : OddPerfectConjecture → False

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
