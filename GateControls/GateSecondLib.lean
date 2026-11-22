/-!
# Gate control: a second library

Compiled by `GateControls/run.sh` as the module `GateSecondLib` of a temporary folder, outside
the toolchain and outside `.lake/packages/`, and imported by `GateControls/SecondLibrary.lean`.
It stands for a second library of the package: its declarations are not checked by checks 2
and 4, which look only at modules named `OddPerfect` or `OddPerfect.*`, so check 5 must
reject the module itself. The partial definition below is one that check 2 would reject.
-/

namespace GateSecondLib

/-- A partial definition. -/
partial def spin (n : Nat) : Nat := spin (n + 1)

end GateSecondLib
