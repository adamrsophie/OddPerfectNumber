# Untrusted helper script for the OddPerfect Lean library.
# Mirror of the filtered checker of ForcingClosedBoundTwo (keepB over table): a row (p, l) is
# tested only when some r in A has r % l == 1 and p^l % r == 1; checks that the rounds in
# rounds_<P0>.json agree with those of the plain checker.
# Used by: OddPerfect/ForcingClosedBoundTwo.lean (round1 .. round10).
# Run: python3 mirror2.py 2000 (after mirror.py in the same folder)
# Requires: Python 3 standard library. Deterministic. Running time: about 4 seconds for P0 = 2000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, math, json
P0 = int(sys.argv[1])
D = json.load(open(f"rounds_{P0}.json"))
Ls = D["Ls"]
def sm(M, n, K): return pow(M, K, n) == 0
rounds = [D["rounds"][0]]; stats = []
while rounds[-1]:
    A = rounds[-1]; M = 2*math.prod(A)
    T = [(l, [r for r in A if r % l == 1]) for l in Ls]
    B = []; tests = 0; bits = 0; small = 0
    for p in A:
        ok = False
        if p % 4 == 1:
            tests += 1
            if sm(M, p+1, p+1): ok = True
        if not ok:
            for l, rs in T:
                small += len(rs)
                if any(pow(p, l, r) == 1 for r in rs):
                    n = (p**l-1)//(p-1); tests += 1; bits += n.bit_length()
                    if sm(M, n, p*l): ok = True; break
        if ok: B.append(p)
    stats.append((len(A), len(B), tests, bits, small))
    print(len(rounds), stats[-1], file=sys.stderr)
    rounds.append(B)
assert rounds == D["rounds"], "mismatch"
print("rounds agree", len(rounds)-1)
