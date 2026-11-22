import AxiomGateLib

/-!
# Gate control: a headline statement about a shadowed predicate

A control for the axiom gate and the statement gate, not part of the library: nothing imports
it and the library build never compiles it. Run it only through `GateControls/run.sh`, which
compiles the gate as the module `AxiomGateLib`.

Inside the namespace `GateControls` the name `OddPerfect` means the local definition below,
which holds for no number, so the theorem `GateControls.seven_le_card_primeFactors` reads like
the headline theorem but says nothing. The axiom gate accepts it: it has no forbidden
dependency and no forbidden kind of declaration. The restatement in the style of
`StatementGate.lean`, written with `_root_.OddPerfect`, does not match it.

Expected result: the axiom gate prints its summary line `axiom gate OK: `, and then the file
fails with a type mismatch at the restatement.
-/

namespace GateControls

/-- A predicate with the name of the project's, true of no number. -/
def OddPerfect (_ : ℕ) : Prop := False

/-- Reads like the headline theorem, but `OddPerfect` here is the local definition. -/
theorem seven_le_card_primeFactors {N : ℕ} (h : OddPerfect N) : 7 ≤ N.primeFactors.card :=
  h.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig

theorem StatementGate.seven_le_card_primeFactors :
    ∀ {N : ℕ}, _root_.OddPerfect N → 7 ≤ (Nat.primeFactors N).card :=
  @GateControls.seven_le_card_primeFactors
