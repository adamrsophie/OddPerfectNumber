/-!
# Gate control: a second library

Compiled by `GateControls/run.sh` as the module `GateSecondLib` of a temporary folder, outside
the toolchain and outside `.lake/packages/`, and imported by `GateControls/SecondLibrary.lean`.
It stands for a second library of the package: its declarations are not checked by checks 2
and 4, which look only at modules named `OddPerfect` or `OddPerfect.*`, so check 5 must
reject the module itself. The partial definition below is one that check 2 would reject.

It also declares the inductive type `Far` without its generated `Far.ctorIdx`, for
`GateControls/CtorIdxModule.lean`, which adds a hand written pair for it in another module.
-/

namespace GateSecondLib

/-- A partial definition. -/
partial def spin (n : Nat) : Nat := spin (n + 1)

set_option genCtorIdx false in
/-- Two constructors, declared without the generated `Far.ctorIdx`. -/
inductive Far where
  | a
  | b

end GateSecondLib
