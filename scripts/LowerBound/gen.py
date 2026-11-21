# Untrusted helper script for the OddPerfect Lean library.
# Search for the proof trees of the lower bound: for a root prime p0 dividing N (and the
# excluded primes not dividing N) it builds a tree of case splits on exponents, forced prime
# factors of sigma(p^a) and closing contradictions, so that every leaf either contradicts
# perfectness or forces N > 10^B. The bound B is a parameter; the library uses B = 79.
# Used by: OddPerfect/LowerBound.lean through emit.py (the trees tree3, tree5, tree7).
# Run: python3 gen.py 79 3   (one root; emit.py runs all roots and writes Lean text)
# Requires: Python 3; cypari2 (version 2.2.4 was used) for the factorizations in pf.py. Without
# cypari2 the script falls back to Pollard rho and ECM, finds fewer factors and may build a
# different tree. Running time: see emit.py. Caches sigcache.json and fcache.json are
# written to the current folder.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
"""Generator of lower bound proof trees.  Usage: python3 gen.py B p [exclusions...]"""
import math, sys
from nt import factor, geom, is_prp, pratt, SMALL, TRIAL_MAX

sys.setrecursionlimit(100000)

def lcm(a, b): return a // math.gcd(a, b) * b

def primes_below(R): return [r for r in SMALL if r < R]

class St:
    __slots__ = ('lo', 'ex', 'dv', 'nd', 'sp')
    def __init__(s):
        s.lo, s.ex, s.dv, s.nd, s.sp = {}, {}, {}, set(), None
    def copy(s):
        t = St(); t.lo = dict(s.lo); t.ex = dict(s.ex); t.dv = dict(s.dv); t.nd = set(s.nd); t.sp = s.sp
        return t
    def comps(s):
        out = []
        for p in s.lo:
            if p in s.ex: out.append((p, s.ex[p]))
            elif p in s.dv: out.append((p, s.dv[p] - 1))
        return sorted(out)
    def odd(s, p):
        return (p in s.ex and s.ex[p] % 2 == 1) or (p in s.dv and s.dv[p] % 2 == 0)

def Dval(cs):
    D = 1
    for p, a in cs: D *= geom(p, a)
    return D

def Aval(st):
    A = 1
    for p, e in st.lo.items(): A = lcm(A, p ** e)
    return A

def val(st, cs):
    D = Dval(cs)
    if D % 2 == 0: D //= 2
    return lcm(Aval(st), D)

import json, os, atexit
_SC = 'sigcache.json'
_sig = {}
if os.path.exists(_SC):
    _sig = {tuple(map(int, k.split(','))): (v[0], {int(q): e for q, e in v[1].items()})
            for k, v in json.load(open(_SC)).items()}
def _save_sig():
    json.dump({'%d,%d' % k: [v[0], {str(q): e for q, e in v[1].items()}] for k, v in _sig.items()},
              open(_SC, 'w'))
atexit.register(_save_sig)
def sig_factors(p, a, secs=20):
    """known prime factorization of geom(p,a) (dict), via the cyclotomic split; cached with
    the time limit used, so a later call with a larger limit retries."""
    key = (p, a)
    if key in _sig and _sig[key][0] >= secs: return _sig[key][1]
    import nt
    fs = {}
    try:
        import pf
        for d in range(2, a + 2):
            if (a + 1) % d: continue
            c = int(pf.pari('polcyclo(%d, %d)' % (d, p)))
            f, cof = pf.pfactor(c, secs)
            for q, e in f.items(): fs[q] = fs.get(q, 0) + e
    except ImportError:
        fs, cof = factor(geom(p, a), 300000)
    _sig[key] = (secs, fs)
    return fs

STATS = {'nodes': 0, 'fail': 0}
FAILS = []
L = None

def certifiable(q):
    return q < TRIAL_MAX or pratt(q) is not None

def ordinary_known(st, p):
    if p % 4 == 3: return True
    return st.sp is not None and st.sp != p

def contradiction(st):
    for p in st.nd:
        if st.lo.get(p, 0) >= 1: return ('ndc', p)
    odds = [p for p in st.lo if st.odd(p)]
    if len(odds) >= 2: return ('par2', odds[0], odds[1])
    for p in odds:
        if p % 4 != 1: return ('parS', p)
        if p in st.ex and st.ex[p] % 4 != 1: return ('parS', p)
        if p in st.dv and st.dv[p] % 4 == 0: return ('parS', p)
    cs = st.comps()
    D = Dval(cs)
    for q, f in st.ex.items():
        if q != 2 and D % q ** (f + 1) == 0: return ('ovf', q, cs, f)
    num, den = 1, 1
    for p, e in sorted(st.lo.items()):
        num *= geom(p, e); den *= p ** e
    if 2 * den < num: return ('abund', sorted(st.lo.items()))
    return None

def solve(st, depth=0):
    STATS['nodes'] += 1
    c = contradiction(st)
    if c: return c
    cs = st.comps()
    if val(st, cs) > L: return ('big', cs)
    if depth > 60:
        STATS['fail'] += 1; FAILS.append(('depth', dict(st.lo))); return None
    # ordinary upgrade
    for p, e in sorted(st.lo.items()):
        if e % 2 == 1 and p not in st.ex and p not in st.dv and (e % 4 == 3 or ordinary_known(st, p)):
            t = st.copy(); t.lo[p] = e + 1
            sub = solve(t, depth + 1)
            return None if sub is None else ('up', p, e, sub)
    # a) unknown component: largest prime
    unk = [p for p in st.lo if p not in st.ex and p not in st.dv]
    if unk:
        p = max(unk)
        return rsplit(st, p, 1, depth)
    # b) force
    best = None
    for (p, a) in cs:
        for q, k in sig_factors(p, a).items():
            if q == 2: continue
            # multiplicity in D
            D = Dval(cs)
            kk = 0
            while D % q ** (kk + 1) == 0: kk += 1
            if q in st.ex: continue
            if st.lo.get(q, 0) >= kk: continue
            if not certifiable(q): continue
            if best is None or q > best[0]: best = (q, kk)
    if best:
        q, k = best
        t = st.copy(); t.lo[q] = max(t.lo.get(q, 0), k)
        sub = solve(t, depth + 1)
        return None if sub is None else ('force', q, k, cs, sub)
    # c) refine a dv component (largest p first)
    dvs = [p for p in st.dv if p not in st.ex]
    if dvs:
        p = max(dvs, key=lambda p: p)
        return rsplit(st, p, st.dv[p], depth)
    if not getattr(st, 'retried', False):
        before = [len(sig_factors(p, a)) for p, a in cs]
        after = [len(sig_factors(p, a, 900)) for p, a in cs]
        if after != before:
            STATS['nodes'] -= 1
            return solve(st, depth)
    STATS['fail'] += 1
    FAILS.append(('stuck', dict(st.lo), dict(st.ex), dict(st.dv), st.sp))
    return None

def rsplit(st, p, d, depth):
    # choose R: smallest prime-free bound so that fallback pw p (d*R-1) closes by big
    cs0 = [c for c in st.comps() if c[0] != p]
    base = val(st, cs0)
    R = 2
    while True:
        e = d * R - 1
        t = st.copy(); t.lo[p] = max(t.lo.get(p, 0), e)
        if lcm(base, p ** t.lo[p]) > L: break
        R += 1
    kids = []
    if d > 1:
        t = st.copy(); t.ex[p] = d - 1; t.lo[p] = max(t.lo.get(p, 0), d - 1)
        if (d - 1) % 2 == 1: t.sp = p if t.sp is None else t.sp
        if t.sp is not None and t.sp != p and (d - 1) % 2 == 1: pass
        sub = solve(t, depth + 1)
        if sub is None: return None
        kids.append(sub)
    for r in primes_below(R):
        t = st.copy(); t.dv[p] = d * r; t.lo[p] = max(t.lo.get(p, 0), d * r - 1)
        if (d * r) % 2 == 0 and t.sp is None: t.sp = p
        sub = solve(t, depth + 1)
        if sub is None: return None
        kids.append(sub)
    t = st.copy(); t.lo[p] = max(t.lo.get(p, 0), d * R - 1)
    kids.append(('big', [c for c in st.comps() if c[0] != p]))
    return ('rs', p, d, R, kids)

def size(t):
    if t[0] == 'rs': return 1 + sum(size(k) for k in t[4])
    if t[0] in ('force',): return 1 + size(t[4])
    if t[0] == 'up': return 1 + size(t[3])
    return 1

if __name__ == '__main__':
    B = int(sys.argv[1]); p0 = int(sys.argv[2]); excl = [int(x) for x in sys.argv[3:]]
    L = 10 ** B
    st = St(); st.lo[p0] = 1; st.nd = set(excl)
    t = solve(st)
    print('B', B, 'p', p0, 'ok' if t else 'FAIL', 'size', size(t) if t else None, STATS)
    for f in FAILS[:5]: print(f)
