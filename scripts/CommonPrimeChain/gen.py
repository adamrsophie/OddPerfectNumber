# Untrusted helper script for the OddPerfect Lean library.
# Forcing table of the common r family: breadth first search over the prime factors
# t = 1 (mod r) of Phi_r(s) = 1 + s + ... + s^(r-1), starting at s = r; the row of each source
# lists the indices of its receivers. Computes the count K with a mirror of the Lean checker
# and Pratt certificates for every node.
# Used by: OddPerfect/CommonPrimeChain.lean (pc5, nodes5, rows5 with K = 186 and pc7, nodes7,
# rows7 with K = 124, two passes).
# Run: python3 gen.py 5 2000000 220 2 t5 and python3 gen.py 7 2000000 400 2 t7
# (arguments: r, trial division limit, maximal number of nodes, passes, output name; writes
# <name>.lean.txt and prints the parameters and K on standard error).
# Requires: Python 3 and sympy. Deterministic. Running time: a few seconds each.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys
from sympy import isprime, primerange, factorint, primitive_root
r, LIM, MAXN, PASSES = map(int, sys.argv[1:5]); name = sys.argv[5]
smallp = [t for t in primerange(3, LIM) if t % r == 1]
def phi(s): return sum(s**i for i in range(r))
nodes = [r]; idx = {r: 0}; rows = []
i = 0
while i < len(nodes):
    s = nodes[i]; i += 1
    v = phi(s); ts = []
    while v % r == 0: v //= r
    for t in smallp:
        if t * t > v: break
        if v % t == 0:
            ts.append(t)
            while v % t == 0: v //= t
    if 1 < v < LIM * LIM:
        assert isprime(v); ts.append(v)
    row = []
    for t in ts:
        assert t % r == 1 and phi(s) % t == 0
        if t not in idx and len(nodes) < MAXN:
            idx[t] = len(nodes); nodes.append(t)
        if t in idx: row.append(idx[t])
    rows.append(sorted(set(row)))
n = len(nodes)
# mirror of the Lean checker
def run(b):
    M = 1
    for _ in range(PASSES):
        for k in range(min(n, len(rows))):
            if (M >> k) & 1 and nodes[k] != b:
                for j in rows[k]: M |= 1 << j
    return sum(1 for k in range(1, n) if (M >> k) & 1 and nodes[k] != b)
cands = [x for x in nodes[1:] if x % 4 == 1]
K = min([run(b) for b in cands] + [run(0)])
print("cands", len(cands), file=sys.stderr)
# Pratt certificates: (p, a, [(q, k)]) in dependency order; factors q < SMALL use trial division
SMALL = 1000
cert = []; done = set()
def certify(p):
    if p in done or p < SMALL: return
    f = factorint(p - 1)
    for q in sorted(f): certify(q)
    a = primitive_root(p)
    cert.append((p, a, sorted(f.items()))); done.add(p)
for x in nodes[1:]: certify(x)
edges = sum(len(rw) for rw in rows)
print(f"-- r={r} LIM={LIM} nodes={n} rows={len(rows)} edges={edges} K={K} cert={len(cert)} maxnode={max(nodes)}", file=sys.stderr)
def L(xs): return "[" + ", ".join(map(str, xs)) + "]"
with open(f"{name}.lean.txt", "w") as fo:
    fo.write(f"/-- Pratt certificates for the `r = {r}` table. -/\ndef pc{r} : List (ℕ × ℕ × List ℕ) :=\n  [")
    fo.write(",\n   ".join(f"({p}, {a}, [{', '.join(str(q) for q, k in fs for _ in range(k))}])" for p, a, fs in cert))
    fo.write("]\n\n")
    fo.write(f"/-- The nodes after `{r}` of the `r = {r}` table. -/\ndef nodes{r} : List ℕ :=\n  " + L(nodes[1:]) + "\n\n")
    fo.write(f"/-- The rows of the `r = {r}` table: receiver indices for each source node. -/\ndef rows{r} : List (List ℕ) :=\n  [" + ",\n   ".join(L(rw) for rw in rows) + "]\n\n")
    fo.write(f"-- K = {K}, passes = {PASSES}\n")
