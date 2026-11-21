# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of OmegaSevenEngine.solve (OddPerfect/OmegaSevenEngine.lean): every function
# follows the Lean definition of the same name, and run() returns the result together with
# counters (st['nodes'] is the number of search nodes the kernel run visits).
# Used by: plan.py (node counts that decide the cut plan of OddPerfect/OmegaSevenRoots*.lean);
# the node count 4415 in the docstring of OddPerfect/OmegaSevenPilot.lean.
# Run: imported by plan.py; for the pilot count, in this folder:
#   python3 -c "import sys; sys.path.insert(0, '.'); import engine as E; print(E.run(E.root(5, 13), 3, 13, E.ladder([2**i for i in range(1, 18)]), 10**4, E.primorial(10**4)))"
# Requires: Python 3 standard library. Deterministic. Running time: a few seconds per state.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import sys
from math import gcd
from collections import Counter
sys.setrecursionlimit(100000)
st = Counter()

def geomC(p, k): return (p**(k+1) - 1) // (p - 1)
def strip(g, ps):
    for y in ps:
        if y >= 2 and g != 0:
            while g % y == 0: g //= y
    return g
def noDiv(q):
    d = 2
    while d * d <= q:
        if q % d == 0: return False
        d += 1
    return True
def isPrimeQ(q): return q >= 2 and noDiv(q)
def valid(p, e): return e % 2 == 0 or (p % 4 == 1 and e % 4 == 1)
def nextValid(p, k): return k + 1 if valid(p, k + 1) else k + 2
def kmin(q): return 1 if q % 4 == 1 else 2

def nums(l):
    ln = ld = un = ud = 1
    for (p, k, ex) in l:
        g = geomC(p, k); ln *= g; ld *= p**k
        if ex: un *= g; ud *= p**k
        else: un *= p; ud *= p - 1
    return ln, ld, un, ud

def cond(un, ud, j, q): return 2*ud*(q-1)**j < un*q**j
def bsearch(un, ud, j, n, a, b):
    while n > 0 and not (b <= a + 1):
        c = (a + b) // 2
        if cond(un, ud, j, c): a = c
        else: b = c
        n -= 1
    return a
def minB(bs): return min(bs) if bs else 0

def pickAux(l, T):
    # index of the inexact entry (with p^k < T when T > 0) of largest gap; first on ties
    bi, bn, bd = 0, 0, 1
    for i, (p, k, ex) in enumerate(l):
        if not ex and (T == 0 or p**k < T) and bn*((p-1)*geomC(p, k)) < p*p**k*bd:
            bi, bn, bd = i, p*p**k, (p-1)*geomC(p, k)
    return bi

def chainList(l):
    ps = [2] + [p for (p, _, _) in l]
    return [c for c in (strip(geomC(p, k), ps) for (p, k, ex) in l if ex) if c != 1]

def lowE(ln, ld, m):
    if ln < 2*ld:
        D = 2*ld - ln
        return max(m + 1, (ln + D - 1) // D)
    return m + 1

def pickP(lad, lo):
    X, P = 0, 1
    for (x, p) in lad:
        if x < lo: X, P = x, p
        else: break
    return X, P

def forceOK(c, lo, Y, Q):
    return c < lo*lo or (c < (Y+1)*(Y+1) and gcd(c, Q) == 1)

W = 10
CFG = dict(T=3*10**6, HJ=9, ADV=20, CHP='lo', ADVP='m', PRE=1)

def advDead(l, j, lo, P, p, k):
    ps = [2] + [q for (q, _, _) in l]
    c = strip(geomC(p, k), ps)
    if c != 1 and (j == 0 or c < lo or 1 < gcd(c, P)): return True
    return k % 2 == 1 and any(ex and kk % 2 == 1 and q != p for (q, kk, ex) in l)

def adv(l, j, lo, P, p, k, n):
    while n > 0 and advDead(l, j, lo, P, p, k):
        st['adv'] += 1; k = nextValid(p, k); n -= 1
    return k

def split(lad, Y, Q, f, l, j, m, lo, P, i):
    st['split'] += 1
    p, k, ex = l[i]
    st['advcalls'] += 1
    k2 = adv(l, j, lo, P, p, k, CFG['ADV'])
    a = solve(lad, Y, Q, f, l[:i] + [(p, k2, True)] + l[i+1:], j, m)
    if not a: return False
    return solve(lad, Y, Q, f, l[:i] + [(p, nextValid(p, k2), False)] + l[i+1:], j, m)

def solve(lad, Y, Q, fuel, l, j, m):
    st['nodes'] += 1
    if fuel == 0:
        st['fuel0'] += 1; return False
    f = fuel - 1
    ln, ld, un, ud = nums(l)
    lo = lowE(ln, ld, m)
    X, P = pickP(lad, lo)
    Pm = pickP(lad, m + 1)[1]
    Pc = P if CFG['CHP'] == 'lo' else Pm
    Pa = P if CFG['ADVP'] == 'lo' else Pm
    cs = chainList(l)
    # abundancy, parity, chain
    if 2*ld < ln or (0 < j and 2*ld <= ln): st['c_abund'] += 1; return True
    if any(a[2] and b[2] and a[1] % 2 == 1 and b[1] % 2 == 1 and a[0] != b[0] for a in l for b in l):
        st['c_parity'] += 1; return True
    if any(j == 0 or c < lo or 1 < gcd(c, Pc) for c in cs): st['c_chain'] += 1; return True
    allEx = all(e[2] for e in l)
    if 0 < j:
        fc = next((c for c in cs if forceOK(c, lo, Y, Q)), 0)
        if fc != 0:
            st['force'] += 1; st['force_max'] = max(st['force_max'], fc)
            return solve(lad, Y, Q, f, ([(fc, kmin(fc), False)] + l if CFG['PRE'] else l + [(fc, kmin(fc), False)]), j - 1, m)
    if j == 0:
        if allEx:
            if ln == 2*ld: print("SOLUTION", l)
            st['c_full'] += 1; return ln != 2*ld
        if un <= 2*ud: st['c_full'] += 1; return True
        return split(lad, Y, Q, f, l, j, m, lo, Pa, pickAux(l, 0))
    bs = []
    if un < 2*ud:
        bU = bsearch(un, ud, j, 200, m, m + 2*j*un // (2*ud - un) + 2)
        if 1 <= bU and not cond(un, ud, j, bU + 1): bs.append(bU)
    bs += cs
    B = minB(bs)
    T = CFG['T']
    if bs and 2 <= j and j <= CFG['HJ'] and any(not e[2] and e[0]**e[1] < T for e in l) and not (B <= lo + W):
        st['hoist'] += 1
        return split(lad, Y, Q, f, l, j, m, lo, Pa, pickAux(l, T))
    if bs and (B <= lo + W or allEx or 2 <= j):
        st['enum'] += 1; st['range'] += max(0, B + 1 - lo)
        lset = set(e[0] for e in l)
        for q in range(lo, B + 1):
            if q not in lset and gcd(q, P) == 1 and (q < (X+1)*(X+1) or isPrimeQ(q)):
                st['child'] += 1
                if not solve(lad, Y, Q, f, ([(q, kmin(q), False)] + l if CFG['PRE'] else l + [(q, kmin(q), False)]), j - 1, q): return False
        return True
    if allEx: st['stuck'] += 1; return False
    return split(lad, Y, Q, f, l, j, m, lo, Pa, pickAux(l, 0))

def primorial(x):
    r = 1
    for d in range(2, x + 1):
        if gcd(d, r) == 1: r *= d
    return r

def ladder(xs):
    return [(x, primorial(x)) for x in xs]

def run(l, j, m, lad, Y, Q, fuel=60, **kw):
    old = dict(CFG); CFG.update(kw); st.clear()
    r = solve(lad, Y, Q, fuel, l, j, m)
    out = (r, dict(st)); CFG.clear(); CFG.update(old)
    return out

def root(*ps): return [(3, 2, False)] + [(p, kmin(p), False) for p in ps]
