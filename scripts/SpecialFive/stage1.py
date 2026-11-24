# Untrusted helper script for the OddPerfect Lean library.
# Measuring search for scripts/SpecialFive (counts only, writes no certificate).
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
"""Stage 1 search: odd perfect N with v_5(N) = 1 and every component p^e <= B.

Usage: python3 -I stage1.py B [maxnodes] [order]
order: small (branch on the smallest undecided forced prime, default) or large.
Exit status: 0 when the search closes (no stuck node), 1 when it stops at a limit or meets a
stuck node, 2 for a usage error.
"""
import sys
import time
from functools import lru_cache
from sympy import factorint

try:
    if not 2 <= len(sys.argv) <= 4:
        raise ValueError
    B = int(sys.argv[1])
    MAXN = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    ORDER = sys.argv[3] if len(sys.argv) > 3 else "small"
    if B < 0 or MAXN < 0 or ORDER not in ("small", "large"):
        raise ValueError
except ValueError:
    print("usage: python3 -I stage1.py B [maxnodes] [small|large] (B, maxnodes natural numbers)",
          file=sys.stderr)
    sys.exit(2)
T0 = time.time()


@lru_cache(maxsize=None)
def sig_fac(p, e):
    s = (p ** (e + 1) - 1) // (p - 1)
    return tuple(sorted(factorint(s).items()))


stats = {"nodes": 0, "size": 0, "over": 0, "abund": 0, "stuck": 0, "maxp": 0}
stuck = []


def allowance(r, exps):
    return 1 if r == 2 else exps[r]


def go(exps):
    stats["nodes"] += 1
    if stats["nodes"] > MAXN or time.time() - T0 > 600:
        raise SystemExit("LIMIT")
    cnt = {}
    num, den = 1, 1
    for p, e in exps.items():
        for r, k in sig_fac(p, e):
            cnt[r] = cnt.get(r, 0) + k
            stats["maxp"] = max(stats["maxp"], r)
        num *= (p ** (e + 1) - 1) // (p - 1)
        den *= p ** e
    for r, k in cnt.items():
        if (r == 2 and k > 1) or (r in exps and k > exps[r]):
            stats["over"] += 1
            return
    if num > 2 * den:
        stats["abund"] += 1
        return
    forced = sorted(r for r in cnt if r != 2 and r not in exps)
    for r in forced:
        if r * r > B:
            stats["size"] += 1
            return
    if not forced:
        stats["stuck"] += 1
        stuck.append(dict(exps))
        return
    r = forced[0] if ORDER == "small" else forced[-1]
    e = 2
    while r ** e <= B:
        exps[r] = e
        go(exps)
        del exps[r]
        e += 2


try:
    go({5: 1})
    res = "closed" if not stats["stuck"] else "stuck"
except SystemExit as x:
    res = str(x)
print(f"B={B} order={ORDER} result={res} time={time.time()-T0:.1f}s {stats}")
for s in stuck[:10]:
    print("stuck", s)
sys.exit(0 if res == "closed" else 1)
