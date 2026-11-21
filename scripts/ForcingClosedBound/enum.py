# Untrusted helper script for the OddPerfect Lean library.
# Exhaustive search for reduced forcing closed configurations inside U* (ustar_P.json).
# With the argument control it drops the parity condition and must find {3, 11}.
# Used by: OddPerfect/ForcingClosedBound.lean as an independent derivation of the deletion
# rounds: for P = 1000 the removal rounds in cert_1000.txt are those of round1 .. round9 and
# iterate_eq (nine rounds); the Lean lemmas themselves are written by mkrounds.py.
# For P = 1000 U* is empty and the search finds no configuration.
# Run: python3 enum.py 1000   or   python3 enum.py 1000 control 3
# Requires: Python 3 standard library. Running time: under a second for P = 1000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Exhaustive search for reduced forcing closed configurations inside U*.
# Rooted at the special node q: the set reachable from q along the chosen moves is itself a
# configuration (closed, one special node, smaller product), so it suffices to search those.
# usage: enum.py P [control [root]]
#   control: parity dropped; every node may use exponent 1 (row p + 1); rooted at `root`.
import sys, json, math
from fractions import Fraction

P = int(sys.argv[1]); control = len(sys.argv) > 2
tag = "_control" if control else ""
Ustar = set(json.load(open(f"ustar_{P}{tag}.json")))
LIMIT = 10 ** 7  # node budget per root; exceeding it is reported, never silently accepted

spf = list(range(P + 2))
for i in range(2, int((P + 1) ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, P + 2, i):
            if spf[j] == j: spf[j] = i
def odd_factors(n):
    s = set()
    while n > 1:
        q = spf[n]; n //= q
        if q != 2: s.add(q)
    return frozenset(s)

ordm = {}
for line in open(f"moves_{P}.txt"):
    t = line.split(); p, l = int(t[0]), int(t[1])
    fac = frozenset(int(x.split(':')[0]) for x in t[2:])
    if p in Ustar and fac <= Ustar: ordm.setdefault(p, []).append((l - 1, fac))

def lab(p, e):  # log abundancy of p^e
    return math.log((1 - p ** -(e + 1)) / (1 - 1 / p))
lb = lambda p: math.log1p(1.0 / p)  # exponent >= 1
LOG2 = math.log(2.0) + 1e-9

def options(p, special_ok):
    opts = list(ordm.get(p, []))
    if special_ok:
        f = odd_factors(p + 1)
        if f <= Ustar: opts.append((1, f))
    return opts

found = []
def search(root):
    S = {root}; choice = {}; nodes = [0]; aborted = [False]
    def rec(L):
        nodes[0] += 1
        if nodes[0] > LIMIT: aborted[0] = True; return
        pend = [p for p in S if p not in choice]
        if not pend:
            ab = Fraction(1)
            for p, e in choice.items(): ab *= Fraction(p ** (e + 1) - 1, (p - 1) * p ** e)
            if ab <= 2: found.append((root, dict(choice), ab))
            return
        best = None
        for p in pend:
            o = options(p, control)
            if best is None or (len(o), p) < (len(best[1]), best[0]): best = (p, o)
            if not o: return
        p, opts = best
        for e, fac in opts:
            new = [r for r in fac if r not in S]
            L2 = L - lb(p) + lab(p, e) + sum(lb(r) for r in new)
            if L2 > LOG2: continue
            choice[p] = e; S.update(new)
            rec(L2)
            del choice[p]; S.difference_update(new)
            if aborted[0]: return
    if control:
        rec(lb(root))
    else:
        f = odd_factors(root + 1)
        if not f <= Ustar: return nodes[0], False
        choice[root] = 1; new = [r for r in f if r != root]; S.update(new)
        rec(lab(root, 1) + sum(lb(r) for r in new))
    return nodes[0], aborted[0]

if control:
    roots = [int(sys.argv[3])]
else:
    roots = sorted(q for q in Ustar if q % 4 == 1)
tot = 0; ab_roots = []
for q in roots:
    n, a = search(q); tot += n
    if a: ab_roots.append(q)
print(f"P={P} control={control} roots={len(roots)} search nodes={tot} aborted roots={ab_roots}")
print("configurations found:", len(found))
for root, ch, ab in found[:20]:
    print(" root", root, "exponents", sorted(ch.items()), "product", ab, float(ab))
