# Untrusted helper script for the OddPerfect Lean library.
# Prunes the d = 35 table of gen.py by greedy deletion of rows and edges to the rows needed
# to reach a target set for every blocked node; argument 22 takes the first 22 robust targets
# (the table used in the library), 28 the first 28 robust targets not = 1 (mod 12) (not used
# in the library). Writes table22.json or table28.json.
# Used by: OddPerfect/CommonFamily.lean (through emit.py: nodes35, rows35, targets35, vals35).
# Run: python3 prune.py 22
# Requires: Python 3 and sympy (through gen.py, found next to this script). Deterministic.
# Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json
import os; exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gen.py')).read().split("def h(")[0])  # rebuild rows, T
import itertools
which = sys.argv[1]
if which == '22':
    tg = T[:22]
else:
    tg = [t for t in T if t % 12 != 1][:28]
edges = {s: list(rc) for s, rc in rows.items()}
def reachE(E, b):
    R = set(seeds); ch = True
    while ch:
        ch = False
        for s, rc in E.items():
            if s in R and s != b:
                for t in rc:
                    if t not in R: R.add(t); ch = True
    return R
def nodesof(E):
    S = set(seeds)
    for s, rc in E.items():
        if rc: S.add(s); S.update(rc)
    return S
def ok(E):
    ns = nodesof(E)
    for b in [None] + [x for x in ns if x % 12 == 1]:
        if not set(tg) <= reachE(E, b): return False
    return True
assert ok(edges)
# restrict to edges inside the reachable world, then greedy deletion, largest source first
for s in sorted(edges, reverse=True):
    old = edges[s]; edges[s] = []
    if not ok(edges): edges[s] = old
for s in sorted(edges, reverse=True):
    for t in sorted(edges[s], reverse=True):
        old = edges[s]; edges[s] = [x for x in old if x != t]
        if not ok(edges): edges[s] = old
E = {s: rc for s, rc in edges.items() if rc}
ns = nodesof(E)
print('sources', len(E), 'edges', sum(len(v) for v in E.values()), 'nodes', len(ns), 'max', max(ns))
print(sorted(E.items()))
json.dump({'targets': tg, 'edges': {str(k): v for k, v in E.items()}}, open('table%s.json' % which, 'w'))
