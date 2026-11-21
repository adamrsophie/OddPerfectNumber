# Untrusted helper script for the OddPerfect Lean library.
# Forcing table of the common d = 35 family with seeds 5, 7: rows list the primes below 10^5
# dividing (s^35 - 1)/(s - 1); computes the targets reached from the seeds for every blocked
# node b = 1 (mod 12) and the shortest abundant prefix of the target list.
# Used by: OddPerfect/CommonFamily.lean (through prune.py and emit.py: nodes35, rows35,
# targets35, vals35).
# Run: python3 gen.py
# Requires: Python 3 and sympy. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
from sympy import primerange
d = 35; seeds = [5, 7]; TD = 10**5; MAXROWS = 400
small = list(primerange(3, TD))
def rec(s):
    n = (s**d - 1)//(s - 1)
    return [t for t in small if n % t == 0 and t != s]
import heapq
rows = {}; seen = set(seeds); heap = list(seeds); heapq.heapify(heap)
while heap and len(rows) < MAXROWS:
    s = heapq.heappop(heap); rows[s] = rec(s)
    for t in rows[s]:
        if t not in seen: seen.add(t); heapq.heappush(heap, t)
def reach(b, R0=None):
    R = set(seeds); ch = True
    while ch:
        ch = False
        for s, rc in rows.items():
            if s in R and s != b:
                for t in rc:
                    if t not in R: R.add(t); ch = True
    return R
full = reach(None)
cands = sorted(b for b in full if b % 12 == 1)
T = set(full)
for b in cands: T &= reach(b)
T = sorted(T)
print('rows', len(rows), 'reached', len(full), 'robust', len(T))
print(T[:60])
def h(t, e=4): return F(sum(t**k for k in range(e+1)), t**e)
# smallest prefix of T that is abundant in every case
for n in range(1, len(T)+1):
    S = T[:n]
    ok = True
    for qq in [None] + [t for t in S if t % 12 == 1]:
        p = F(1)
        for t in S: p *= F(t+1, t) if t == qq else h(t)
        if p <= 2: ok = False; break
    if ok: print('prefix', n, S); break
T2 = [t for t in T if t % 12 != 1]
for n in range(1, len(T2)+1):
    S = T2[:n]; p = F(1)
    for t in S: p *= h(t)
    if p > 2: print('no-1mod12 prefix', n, S, float(p)); break
