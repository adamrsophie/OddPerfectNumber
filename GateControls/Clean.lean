import AxiomGateLib

/-!
# Gate control: clean

A control for the axiom gate, not part of the library: nothing imports it and the library
build never compiles it. Run it only through `GateControls/run.sh`, which compiles the gate
as the module `AxiomGateLib`. Files in `GateControls/` mention the words axiom and unsafe on
purpose; scans for those words exclude this folder by path.

Expected result: the gate accepts this file (exit status 0). It contains a structurally
recursive and a well founded recursive definition, whose compiler helpers `_unsafe_rec` must
be exempted, a private definition, and ordinary theorems. It also declares an inductive type
with three constructors and an indexed family with a universe parameter, whose generated pairs
`T.ctorIdx` and `T.ctorIdx._impl` must be exempted, and a structure, for which Lean generates
`T.ctorIdx` with no `implemented_by` and no `_impl`, so it has no pair.
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

/-- Several constructors: Lean generates `Shade.ctorIdx` and `Shade.ctorIdx._impl`. -/
inductive Shade where
  | light
  | mid
  | dark

/-- An indexed family with a universe parameter: also a generated pair. -/
inductive Tagged (α : Type u) : Nat → Type u where
  | none : Tagged α 0
  | some (a : α) (n : Nat) : Tagged α (n + 1)

/-- One constructor: `Point.ctorIdx` is generated without a partner. -/
structure Point where
  x : Nat
  y : Nat

theorem shade_ne : Shade.light ≠ Shade.dark := Shade.noConfusion

theorem sumTo_three : sumTo 3 = 6 := by decide

theorem halve_one : halve 1 = 0 := by simp [halve]

theorem double_eq (n : Nat) : double n = n + n := by unfold double; omega

end GateControls

run_cmd AxiomGate.run AxiomGate.controlConfig
