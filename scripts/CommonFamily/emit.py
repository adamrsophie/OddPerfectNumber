# Untrusted helper script for the OddPerfect Lean library.
# Reads table22.json (written by prune.py), orders the nodes breadth first from the seeds 5, 7,
# checks the rows and primality, finds the least number of passes with a mirror of the Lean
# checker tcheck, and prints the literals.
# Used by: OddPerfect/CommonFamily.lean (nodes35, rows35, targets35, vals35, and the pass
# count 1 in check35).
# Run: python3 emit.py (after python3 prune.py 22 in the same folder)
# Requires: Python 3 and sympy. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import json
from sympy import isprime
J = json.load(open('table22.json')); E = {int(k): v for k, v in J['edges'].items()}; tg = J['targets']
d = 35; seeds = [5, 7]
order = list(seeds); i = 0
while i < len(order):
    for t in E.get(order[i], []):
        if t not in order: order.append(t)
    i += 1
for t in tg: assert t in order
# drop trailing nodes with empty rows only if they are not needed; keep all (they are receivers)
idx = {x: k for k, x in enumerate(order)}
rows = [[idx[t] for t in E.get(x, [])] for x in order]
while rows and not rows[-1]: rows.pop()
targets = [idx[t] for t in tg]
def gm(p, m, n):
    a = 0
    for _ in range(n): a = (a * p + 1) % m
    return a
assert all(gm(order[s], order[j], d) == 0 for s in range(len(rows)) for j in rows[s])
assert all(isprime(x) and x != 2 for x in order) and len(set(order)) == len(order)
def iterm(b, passes):
    M = (1 << len(seeds)) - 1
    for _ in range(passes):
        for k, row in enumerate(rows):
            if (M >> k) & 1 and order[k] != b:
                for j in row: M |= 1 << j
    return M
def allok(passes):
    for b in [x for x in order if x % 12 == 1] + [0]:
        M = iterm(b, passes)
        if not all((M >> j) & 1 for j in targets): return False
    return True
P = next(p for p in range(1, 20) if allok(p))
print('passes', P, 'nodes', len(order), 'rows', len(rows), 'blocked', [x for x in order if x % 12 == 1])
print('nodes :=', order)
print('rows :=', rows)
print('targets :=', targets)
print('values :=', [order[j] for j in targets])
