import AxiomGateLib

/-!
# Gate control: conjecture restated under another name

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. This file declares an axiom on purpose; files in
`GateControls/` mention the words axiom and unsafe intentionally, and scans for those words
exclude this folder by path.

The real `OddPerfectConjecture` cannot be proved, so the statements below are proved from a
locally declared axiom. The gate therefore also reports the axiom and the theorems that use
it; the runner checks for the conjecture lines specifically. A theorem of the conjecture
named `oddPerfectConjecture` is reported as a resolution, not as a misnamed statement.

Expected result: the gate rejects this file, with among its problems the lines
`GateControls.restated: states OddPerfectConjecture but is not named oddPerfectConjecture`
and `GateControls.restatedNeg: states the negation of OddPerfectConjecture but is not named
oddPerfectConjecture`.
-/

namespace GateControls

axiom ex : False

theorem restated : OddPerfectConjecture := ex.elim

theorem restatedNeg : ¬ OddPerfectConjecture := ex.elim

theorem oddPerfectConjecture : OddPerfectConjecture := ex.elim

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
