# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of ForcingClosedBoundTwo.step: starting from the numbers in [3, P0] passing the
# small sieve, a round keeps p when p = 1 (mod 4) and (p + 1) | M^(p + 1), or when some length
# l has (p^l - 1)/(p - 1) | M^(p l), with M = 2 prod(A); repeats until the list is empty and
# writes rounds_<P0>.json.
# Used by: OddPerfect/ForcingClosedBoundTwo.lean (through mktail.py: lengths_eq, initial_eq,
# round1 .. round10, iterate_eq for P0 = 2000).
# Run: python3 mirror.py 2000
# Requires: Python 3 standard library. Deterministic. Running time: about 85 seconds for P0 = 2000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, math, json
P0 = int(sys.argv[1])
def sieve(q): return all(q <= d or q % d for d in range(2, 32))
Ls = [l for l in range(3, 3 + (P0 - 1)//2 - 2) if sieve(l)]
init = [q for q in range(3, 3 + P0 - 2) if sieve(q)]
def sm(M, n, K): return pow(M, K, n) == 0
rounds = [init]; stats = []
while rounds[-1]:
    A = rounds[-1]; M = 2*math.prod(A)
    B = []; tests = 0; bits = 0; nl_del = 0
    for p in A:
        ok = False
        if p % 4 == 1:
            tests += 1
            if sm(M, p+1, p+1): ok = True
        if not ok:
            for l in Ls:
                n = (p**l-1)//(p-1); tests += 1; bits += n.bit_length()
                if sm(M, n, p*l): ok = True; break
        if ok: B.append(p)
    if B == A: sys.exit("nonempty fixed point %s" % A)
    stats.append((len(A), len(B), tests, bits, M.bit_length()))
    print(len(rounds), stats[-1], file=sys.stderr)
    rounds.append(B)
json.dump({"Ls": Ls, "rounds": rounds, "stats": stats}, open(f"rounds_{P0}.json", "w"))
