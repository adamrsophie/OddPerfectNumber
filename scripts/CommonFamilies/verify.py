#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Independent checker for a certificate cert_<name>.json written by search.py (shares no code
# with it): Pratt primality of every node, the row divisibilities, the reach of every target
# with every candidate special prime blocked, and the abundance of every case.
# Used by: the certificates behind OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean,
# CommonFiftyFive.lean, CommonEightyFive.lean, CommonOneFifteenData.lean,
# CommonNinetyFiveData.lean.
# Run: python3 verify.py cert.json [more.json ...]
# Requires: Python 3 and sympy. Deterministic. Running time: about ten seconds for the five
# certificates of 57, 65, 55, 85, 115; about 35 seconds for that of 95.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json
sys.set_int_max_str_digits(0)
from fractions import Fraction
from sympy import isprime, factorint

def pratt(p, memo={}):
    """Build a Pratt certificate: a witness g and the full factorization of p - 1, recursively."""
    if p in memo: return memo[p]
    if p == 2: memo[p] = True; return True
    if not isprime(p): return False
    fs = list(factorint(p - 1))
    for g in range(2, 10**4):
        if pow(g, p - 1, p) == 1 and all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            break
    else:
        return False
    ok = all(pratt(f) for f in fs)
    memo[p] = ok
    return ok

def check(path):
    c = json.load(open(path)); d = c['d']; seeds = c['seeds']; m, r = c['special_test']
    e = c.get('exponent', 4); assert e == 4
    exps = {int(k): v for k, v in c.get('exponents', {}).items()}
    excl = c.get('excluded_primes', [])
    special = lambda b: b % m == r and all(b % x != x - 1 for x in excl)
    branch = {int(b): v for b, v in c.get('branch_seeds', {}).items()}
    rows = {}
    for s, ts in c['rows']:
        assert s not in rows, f'duplicate row {s}'
        rows[s] = ts
    nodes = set(seeds) | set(rows) | {t for ts in rows.values() for t in ts}
    for v in branch.values(): nodes |= set(v)
    assert d % 2 == 1 and d >= 5
    hyp = c.get('hypothesis_seeds', [])
    for p in seeds:
        assert d % p == 0 or p in hyp, f'seed {p} neither divides d nor is a declared hypothesis'
    for p in sorted(nodes):
        assert p % 2 == 1 and pratt(p), f'node {p} not Pratt prime'
    receivers = {t for ts in rows.values() for t in ts}
    for s, ts in rows.items():
        assert s in seeds or s in receivers or any(s in v for v in branch.values()), f'source {s} unconnected'
        sig = (s**d - 1) // (s - 1)
        for t in ts:
            assert t != s and sig % t == 0, f'{t} does not divide sigma({s}^{d-1})'
    for b, v in branch.items():
        for x in v: assert ((b + 1) // 2) % x == 0, f'branch seed {x} does not divide ({b}+1)/2'
    T = c['targets']; assert len(set(T)) == len(T) and 3 not in T
    def reach(block, extra):
        R = set(seeds) | set(extra); st = list(R)
        while st:
            u = st.pop()
            if u == block: continue
            for w in rows.get(u, []):
                if w not in R: R.add(w); st.append(w)
        return R
    for x in excl: assert x not in nodes, f'excluded prime {x} used as a node'
    blocks = [None] + sorted(n for n in nodes if special(n))
    for b in blocks:
        R = reach(b, branch.get(b, []))
        miss = [t for t in T if t not in R]
        assert not miss, f'targets {miss[:5]} not reached when {b} is special'
    h = lambda t: Fraction(t**(exps.get(t, e) + 1) - 1, (t - 1) * t**exps.get(t, e))
    P = Fraction(1)
    for t in T: P *= h(t)
    want = {'none': P}
    for q in T:
        if special(q): want[q] = P / h(q) * Fraction(q + 1, q)
    got = {x['q']: Fraction(x['sigma_over_D']) for x in c['cases']}
    assert set(got) == set(want), 'case list mismatch'
    for q, V in want.items():
        assert got[q] == V, f'fraction mismatch at {q}'
        assert V > 2, f'case {q} not abundant'
    worst = min(want.values())
    print(f'{path}: OK  d={d} seeds={seeds} hyp={hyp} branch={branch} special {m},{r} excl={excl} exps={exps}  rows={len(rows)} nodes={len(nodes)} '
          f'largest={max(nodes)} targets={len(T)} cases={len(want)} blocks_checked={len(blocks)} worst={float(worst):.6f}')

for p in sys.argv[1:]: check(p)
