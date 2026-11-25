# Contributing a proof

The existence of an odd perfect number is an open problem, and this repository does not solve
it. It collects theorems about odd perfect numbers that the Lean kernel has checked. You can
add to it by proving one of the posted steps. A step is one exact Lean statement; a
contribution is one Lean file that proves it. People and AI agents are both welcome, and the
same rules apply to both.

No step settles the conjecture. Most steps restate a theorem from the literature that the
library does not have yet; a few are marked open. Each one says which.

## The steps

The steps are the definitions in [`OddPerfect/Steps.lean`](OddPerfect/Steps.lean). Each has
a docstring with its difficulty, its source, and what it is good for. The project site lists
them with the names of the people who proved the closed ones:
<https://adamrsophie.github.io/OddPerfectNumber/join.html>.

A step is closed when `Contributions/<Name>.lean` exists on the `main` branch. The nine steps
posted so far are all closed.

## How to contribute

1. Pick a step `<Name>` that has no file `Contributions/<Name>.lean` and no open pull request
   titled `Step <Name>`.
2. Fork the repository. Open a draft pull request titled `Step <Name>` as soon as you start;
   that is how others see the step is taken. A draft without a new commit for 14 days counts
   as released, and anyone may take the step.
3. Add exactly one file, `Contributions/<Name>.lean`, in the format below. Change no other
   file.
4. Check it on your machine (next section), mark the pull request ready, and wait for the
   checks and a maintainer.

If you find that a step is false as stated, open an issue with the counterexample instead. A
correct counterexample is credited like a proof, and the step is fixed.

If you get stuck, say so in the pull request and close it, with what you tried. A short note
on why an approach fails is useful to the next person.

## The file

```lean
import OddPerfect.Steps

namespace OddPerfect.Proofs

theorem Example : OddPerfect.Steps.Example := by
  intro N h h2
  have h1 := Nat.odd_iff.mp h.odd
  omega

end OddPerfect.Proofs
```

This is [`Contributions/Example.lean`](Contributions/Example.lean). The rules:

* The file is named after the step and contains one theorem `OddPerfect.Proofs.<Name>` whose
  statement is exactly `OddPerfect.Steps.<Name>`. Do not restate the step; a restated,
  weakened or strengthened statement is rejected.
* You may import `Mathlib`, any `Mathlib.*` module and any `OddPerfect.*` module, and you may
  add your own lemmas and definitions in the same file.
* Proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no
  new `axiom`, no `native_decide`. `by decide +kernel` is allowed.
* The file may not contain anything that runs a program while Lean elaborates it, or that
  changes how Lean reads the rest: no `#` commands, no `macro`, `syntax`, `notation`, `elab`,
  `run_cmd`, `initialize`, no `open Lean`, no string literals, no quoted identifiers, no
  attribute other than `@[simp]`, no `instance`, `structure`, `inductive` or `class`, and no
  `set_option` other than `maxHeartbeats` and `maxRecDepth`. The scan below is the exact rule.
* Lines have at most 100 characters. The file has at most 200,000 bytes.
* The file should compile in a few minutes and in less than 8 GB of memory. Say so in the
  pull request if it needs more.

## Checking your file

```sh
lake exe cache get
lake build OddPerfect.Steps          # and any OddPerfect module your file imports
python3 -I scripts/Controls/contribution_scan.py Contributions/<Name>.lean
sh scripts/Controls/contribution_gate.sh
```

The scan must print `0 findings`. The gate must print `contribution gate OK` and must not list
your step as open. The toolchain is pinned in `lean-toolchain`, and Mathlib is pinned in
`lake-manifest.json`; use those versions.

A full `lake build` of the library takes hours and is not needed for a contribution.

## What happens to a pull request

* The checks of the repository run on your pull request once a maintainer has approved the
  run. They scan the file, build it against the saved build of the library, and run the gate.
  A pull request that changes any other file fails the scan.
* A green check is necessary and not sufficient. A maintainer reads the whole file and
  repeats the checks on a separate machine.
* An accepted proof is added to `main` by the maintainers as one commit, with a message
  written by them. The pull request is then closed with a reference to that commit.
* Credit: the name or GitHub handle of the person who submitted the proof is listed next to
  the step on the project site and in the header comment of the file. Credit goes to a
  person or to a named account, not to a tool.
* The maintainers may later move an accepted proof into the library when another theorem
  needs it. The credit stays with the file and on the site.

By opening a pull request you agree that your file is your own work, or work you have the
right to submit, and that it is released under the license of this repository (see
[`LICENSE`](LICENSE)).

## Other changes

Pull requests are for step proofs only. For anything else (a mistake in a docstring, a wrong
reference, an idea for a new step, a result you think the library should have), open an
issue. New steps are welcome as issues: give the exact statement, where it is proved in the
literature, and what it would be used for.
