# Untrusted helper script for the OddPerfect Lean library.
# Emits the per round Lean lemmas from rounds_<P0>.json (written by mirror.py and checked by
# mirror2.py): lengths_eq, initial_eq, one lemma per round with its product and table, and
# iterate_eq; prints them on standard output. Optional round numbers after P0 emit only those
# rounds.
# Used by: OddPerfect/ForcingClosedBoundTwo.lean (lengths_eq, initial_eq, round1 .. round10,
# iterate_eq).
# Run: python3 mktail.py 2000 > tail.lean
# Requires: Python 3 standard library. Deterministic. Running time: about a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, math, json
P0 = int(sys.argv[1]); only = sys.argv[2:]  # optional round numbers for timing files
D = json.load(open(f"rounds_{P0}.json")); Ls = D["Ls"]; R = D["rounds"]; k = len(R) - 1
L = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
TT = lambda T: "[" + ", ".join(f"({l}, {L(rs)})" for l, rs in T) + "]"
out = [f"/-- The odd primes `l` with `2 * l + 1 ≤ {P0}`. -/",
       f"private lemma lengths_eq : lengths {P0} = {L(Ls)} := by decide +kernel", ""]
if not only:
    out += [f"/-- The starting list: every number in `[3, {P0}]` passing `smallSieveB` (the odd primes and a few composites). -/",
            f"private lemma initial_eq : initial {P0} = {L(R[0])} := by decide +kernel", ""]
for i in range(k):
    if only and str(i + 1) not in only: continue
    A, B = R[i], R[i + 1]; M = 2 * math.prod(A)
    T = [(l, [r for r in A if r % l == 1]) for l in Ls]
    out += [f"/-- Round {i + 1} of the deletion. -/",
            f"private lemma round{i + 1} : step {P0} {L(A)} = {L(B)} :=",
            f"  step_eq lengths_eq (by decide +kernel : 2 * List.prod {L(A)} = {M})",
            f"    (by decide +kernel : table {L(Ls)} {L(A)} = {TT(T)})",
            f"    (by decide +kernel)", ""]
if not only:
    simp = ", ".join(f"round{i + 1}" for i in range(k))
    out += [f"/-- The deletion from the odd primes up to `{P0}` empties in {k} rounds. -/",
            f"private lemma iterate_eq : (step {P0})^[{k}] (initial {P0}) = [] := by",
            f"  rw [" + ", ".join(["Function.iterate_succ_apply'"] * k) + ",",
            f"    Function.iterate_zero_apply, initial_eq, {simp}]"]
print("\n".join(out))
