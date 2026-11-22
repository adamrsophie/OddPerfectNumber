/-!
# Gate control: source scan

A control for the source scan `scripts/Controls/source_scan.py`, not part of the library and
never compiled: `GateControls/run.sh` only scans it. Each command below is one construct that
the scan must report; the runner checks the reported line of each. Mentions inside comments,
docstrings, strings, raw strings and quoted identifiers must not be reported: notation, macro,
run_cmd, debug.skipKernelTC, set_option pp.all true. The commands right after the quoted
identifier and the raw string check that the scan finds the end of each.
-/

set_option debug.skipKernelTC true in
theorem a : True := trivial

set_option pp.all true

run_cmd pure ()

run_meta pure ()

run_elab pure ()

#eval 1

initialize pure ()

syntax "gate" : term

declare_syntax_cat gate

macro "gate2" : term => `(1)

macro_rules | `(gate) => `(2)

elab "gate3" : term => pure (Lean.mkNatLit 3)

elab_rules : term | `(gate) => pure (Lean.mkNatLit 4)

notation "gate4" => 5

local infix:65 " +++ " => Nat.add

local instance : Inhabited Nat := ⟨7⟩

attribute [local instance] Nat.instInhabited

@[command_elab Lean.Parser.Command.check] def gateElab : Lean.Elab.Command.CommandElab :=
  fun _ => pure ()

example : True := by run_tac pure ()

example : Nat := by_elab pure (Lean.mkNatLit 8)

simproc gateProc (Nat.succ _) := fun _ => pure .continue

@[init gateInitDecl] def gateInit : IO Unit := pure ()

notation3 "gate5" => 6

prefix:max "gate6" => Nat.succ

postfix:max "gate7" => Nat.succ

infixl:65 " +l+ " => Nat.add

infixr:65 " +r+ " => Nat.add

dsimproc gateDProc (Nat.succ _) := fun _ => pure .continue

builtin_initialize pure ()

scoped instance : Inhabited Nat := ⟨8⟩

def «gate"quoted» : Nat := 1
run_meta pure ()

def gateRaw : String := r"\"
run_elab pure ()

example : Nat := 2⁻¹run_cmd pure ()

-- set_option debug.skipKernelTC true is ignored in this comment, and notation in this one.
def b : String := "run_cmd notation set_option debug.skipKernelTC true"

/-- A docstring that mentions macro and elab. -/
theorem c : True := trivial
