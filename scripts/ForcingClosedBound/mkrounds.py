# Untrusted helper script for the OddPerfect Lean library.
# Deletion rounds for the bound P0: starting from the odd primes up to P0, a round keeps p
# when p = 1 (mod 4) and p + 1 | M^K, or when some odd prime length l with 2 l + 1 <= P0 has
# (p^l - 1)/(p - 1) | M^K, with M = 2 prod(A) and K the bit length of the divisor (this
# decides the same divisibility as the exponents p + 1 and p l of keepB). Prints lengths_eq,
# initial_eq, one lemma per round and iterate_eq; prints the round sizes on standard error.
# Used by: OddPerfect/ForcingClosedBound.lean (lengths_eq, initial_eq, round1 .. round9,
# iterate_eq for P0 = 1000).
# Run: python3 mkrounds.py 1000 > tail.lean
# Requires: Python 3 standard library. Deterministic. Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, math
P0 = int(sys.argv[1])
def pr(n): return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
Ls = [l for l in range(3, (P0 - 1) // 2 + 1) if pr(l)]
def sm(M, n): return pow(M, n.bit_length(), n) == 0
def keep(M, p):
    return (p % 4 == 1 and sm(M, p + 1)) or any(sm(M, (p ** l - 1) // (p - 1)) for l in Ls)
rounds = [[p for p in range(3, P0 + 1) if pr(p)]]
while rounds[-1]:
    A = rounds[-1]; M = 2 * math.prod(A)
    B = [p for p in A if keep(M, p)]
    if B == A: sys.exit("fixed point not empty")
    rounds.append(B)
k = len(rounds) - 1
L = lambda xs: "[" + ", ".join(map(str, xs)) + "]"
out = [f"/-- The odd primes `l` with `2 * l + 1 ≤ {P0}`. -/",
       f"private lemma lengths_eq : lengths {P0} = {L(Ls)} := by decide +kernel", "",
       f"/-- The odd primes up to `{P0}`. -/",
       f"private lemma initial_eq : initial {P0} = {L(rounds[0])} := by decide +kernel", ""]
for i in range(k):
    A, B = rounds[i], rounds[i + 1]; M = 2 * math.prod(A)
    out += [f"/-- Round {i + 1} of the deletion. -/",
            f"private lemma round{i + 1} : step {P0} {L(A)} = {L(B)} :=",
            f"  step_eq lengths_eq (by decide +kernel : 2 * List.prod {L(A)} = {M})",
            f"    (by decide +kernel)", ""]
simp = ", ".join(f"round{i + 1}" for i in range(k))
out += [f"/-- The deletion from the odd primes up to `{P0}` empties in {k} rounds. -/",
        f"private lemma iterate_eq : (step {P0})^[{k}] (initial {P0}) = [] := by",
        f"  simp only [Function.iterate_succ_apply', Function.iterate_zero, id, initial_eq, {simp}]"]
print("\n".join(out))
print(f"rounds {k}, sizes {[len(a) for a in rounds]}", file=sys.stderr)
