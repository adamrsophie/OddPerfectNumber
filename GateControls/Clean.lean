import AxiomGateLib

/-!
# Gate control: clean

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom and unsafe on
purpose; scans for those words exclude this folder by path.

Expected result: the gate accepts this file (exit status 0). It contains a structurally
recursive and a well founded recursive definition, whose compiler helpers `_unsafe_rec` must
be exempted, a private definition, and ordinary theorems.
-/

namespace GateControls

/-- Structural recursion: the compiler adds `sumTo._unsafe_rec`. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

/-- Well founded recursion: the compiler adds `halve._unsafe_rec`. -/
def halve (n : Nat) : Nat :=
  if h : n < 2 then 0 else 1 + halve (n - 2)
termination_by n
decreasing_by omega

private def double (n : Nat) : Nat := 2 * n

theorem sumTo_three : sumTo 3 = 6 := by decide

theorem halve_one : halve 1 = 0 := by simp [halve]

theorem double_eq (n : Nat) : double n = n + n := by unfold double; omega

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
