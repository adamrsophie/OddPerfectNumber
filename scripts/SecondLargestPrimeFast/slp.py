# Untrusted helper script for the OddPerfect Lean library.
# Exact Python port of OddPerfect.SLP.expand and OddPerfect.SLP.run of
# OddPerfect/SecondLargestPrime.lean (Lean natural number semantics: truncated subtraction,
# division by zero is zero), with the formatting of search stacks as Lean literals.
# Used by: mkfast.py, validate.py, reach.py and knuth.py of this folder (a library, not run alone).
# Requires: Python 3.8 or later, standard library only. Deterministic.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: none.
# License: GPL 3, same as the repository.
from math import gcd, prod
import sys
sys.setrecursionlimit(10000)

def sub(a, b): return a - b if a > b else 0
def div(a, b): return a // b if b else 0
def mod(a, b): return a % b if b else a

def gs(p, e): return div(sub(p ** (e + 1), 1), sub(p, 1))

def isp(n): return n > 1 and all(n % d for d in range(2, int(n ** .5) + 1))
def primesUpTo(B): return [q for q in range(3, B + 1) if isp(q)]

def cofree(M, f, m):
    while f > 0:
        d = gcd(m, M)
        if d == 1: return m
        m = div(m, d); f -= 1
    return m

def valid(p, e): return e % 2 == 0 or (p % 4 == 1 and e % 4 == 1)
def nextValid(p, k): return k + 1 if valid(p, k + 1) else k + 2

def un1(e): q, c, k = e; return gs(q, k) if c == 3 else (1 if c == 1 else q)
def ud1(e): q, c, k = e; return q ** k if c == 3 else (1 if c == 1 else sub(q, 1))
def ln1(e): q, c, k = e; return gs(q, k) if c >= 2 else 1
def ld1(e): q, c, k = e; return q ** k if c >= 2 else 1
def uN(st): return prod(un1(e) for e in st)
def uD(st): return prod(ud1(e) for e in st)
def lN(st): return prod(ln1(e) for e in st)
def lD(st): return prod(ld1(e) for e in st)

def loEnt(B, e): q, c, k = e; return 2 * k + 3 if (c >= 2 and B < 2 * k + 3) else 0
def minz(a, b): return b if a == 0 else min(a, b)

def newLo(B, st, lo):
    m = max([loEnt(B, e) for e in st], default=0)
    ln, ld = lN(st), lD(st)
    if ln < 2 * ld:
        return max(max(lo, m), div(sub(ln + sub(2 * ld, ln), 1), sub(2 * ld, ln)))
    return max(lo, m)

def hiU(st, hi):
    n, d = uN(st), uD(st)
    if n < 2 * d: return minz(hi, div(sub(2 * d, 1), sub(2 * d, n)))
    return hi

def newHi(st, g, hi): return minz(hiU(st, hi), g) if 0 < g else hiU(st, hi)
def pun(pin, kP, xP): return gs(pin, kP) if xP else pin
def pud(pin, kP, xP): return pin ** kP if xP else sub(pin, 1)

def parityBad(st, pin, kP, xP):
    o = [q for (q, c, k) in st if c == 3 and k % 2 == 1] + ([pin] if (pin != 0 and xP and kP % 2 == 1) else [])
    return any(a != b for a in o for b in o)

def allEx(st, xP): return xP and all(c == 1 or c == 3 for (_, c, _) in st)

def closed(st, lo, hi, pin, kP, xP):
    if parityBad(st, pin, kP, xP): return True
    ln, ld, un, ud = lN(st), lD(st), uN(st), uD(st)
    if 2 * ld <= ln: return True
    if hi != 0 and hi < lo: return True
    if 0 < lo and un * lo <= 2 * sub(lo, 1) * ud: return True
    if pin != 0:
        a, b = un * pun(pin, kP, xP), 2 * (ud * pud(pin, kP, xP))
        if a < b or (a == b and not allEx(st, xP)): return True
        if 2 * (ld * pin ** kP) < ln * gs(pin, kP): return True
    return False

def hasOut(M, m):
    c = cofree(M, 200, m)
    return c != 1 and gcd(c, M) == 1

def okEx(M, st, g, lo, pin, p, k):
    s = gs(p, k)
    if not all(c != 1 or mod(s, q) != 0 for (q, c, _) in st): return False
    if pin != 0:
        return (not hasOut(M * pin, s)) and not (p == pin and hasOut(M, s))
    if not hasOut(M, s): return True
    cf = cofree(M, 200, s)
    return lo <= cf and (g == 0 or lo <= gcd(g, cf))

def adv(M, st, g, lo, pin, p, n, k):
    while n > 0:
        if okEx(M, st, g, lo, pin, p, k): return k
        k = nextValid(p, k); n -= 1
    return k

def force(st, s): return [(q, 2, nextValid(q, 0)) if (c == 0 and mod(s, q) == 0) else (q, c, k) for (q, c, k) in st]
def setE(st, p, c, k): return [(p, c, k) if q == p else (q, cc, kk) for (q, cc, kk) in st]
def gUp(M, g, pin, s): return gcd(g, cofree(M, 200, s)) if (pin == 0 and hasOut(M, s)) else g
def gapBig(p, k): return p * p ** k * 33 > sub(p, 1) * gs(p, k) * 34
def gapGt(p, k, q, l): return p * p ** k * (sub(q, 1) * gs(q, l)) > q * q ** l * (sub(p, 1) * gs(p, k))

def pickBest(l):
    y = None
    for (q, c, k) in reversed(l):
        if y is None:
            y = (q, k) if c == 2 else None
        elif c == 2 and gapGt(q, k, y[0], y[1]):
            y = (q, k)
    return y

def anyBig(st, pin, kP, xP):
    y = pickBest(st)
    return (y is not None and gapBig(*y)) or (pin != 0 and not xP and gapBig(pin, kP))

def chooseU(st, pin, kP, xP):
    if anyBig(st, pin, kP, xP): return None
    for e in st:
        if e[1] == 0: return e
    return None

def useP(st, pin, kP, xP):
    if not (pin != 0 and not xP): return False
    y = pickBest(st)
    return True if y is None else gapGt(pin, kP, y[0], y[1])

KIND = {}
def expand(B, M, W, s, stats=None):
    st, g, lo, hi, pin, kP, xP = s
    lo2, hi2 = newLo(B, st, lo), newHi(st, g, hi)
    def tag(t):
        if stats is not None: stats[t] = stats.get(t, 0) + 1
    if closed(st, lo2, hi2, pin, kP, xP): tag('closed'); return []
    if pin == 0 and 0 < g and g < lo2 * lo2: tag('gpin'); return [(st, g, g, g, g, nextValid(g, 0), False)]
    if pin == 0 and hi2 != 0 and hi2 <= lo2 + W:
        tag('window')
        return [(st, g, c, c, c, nextValid(c, 0), False) for c in range(lo2, lo2 + sub(hi2 + 1, lo2))
                if gcd(c, M) == 1 and (g == 0 or mod(g, c) == 0)]
    e = chooseU(st, pin, kP, xP)
    if e is not None:
        tag('splitU')
        return [(setE(st, e[0], 2, adv(M, st, g, lo2, pin, e[0], 40, nextValid(e[0], 0))), g, lo2, hi2, pin, kP, xP),
                (setE(st, e[0], 1, 0), g, lo2, hi2, pin, kP, xP)]
    if useP(st, pin, kP, xP):
        tag('splitP')
        r = []
        if okEx(M, st, g, lo2, pin, pin, kP):
            r.append((force(st, gs(pin, kP)), g, lo2, hi2, pin, kP, True))
        r.append((st, g, lo2, hi2, pin, adv(M, st, g, lo2, pin, pin, 40, nextValid(pin, kP)), False))
        return r
    y = pickBest(st)
    if y is None: tag('stuck'); return None
    tag('splitE')
    p, k = y
    r = []
    if okEx(M, st, g, lo2, pin, p, k):
        r.append((force(setE(st, p, 3, k), gs(p, k)), gUp(M, g, pin, gs(p, k)), lo2, hi2, pin, kP, xP))
    r.append((setE(st, p, 2, adv(M, st, g, lo2, pin, p, 40, nextValid(p, k))), g, lo2, hi2, pin, kP, xP))
    return r

def run(B, M, W, f, L, stats=None):
    L = list(L)
    # L is a stack with head at index 0; use reversed list internally
    R = L[::-1]
    while f > 0:
        if not R: return []
        s = R.pop()
        cs = expand(B, M, W, s, stats)
        if cs is None: return None
        R.extend(reversed(cs))
        f -= 1
    return R[::-1]

def init(B, LO):
    return [([(q, 0, 0) for q in primesUpTo(B)], 0, LO, 0, 0, 0, False)]

def Mof(B): return 2 * prod(primesUpTo(B))

def fmt_state(s):
    st, g, lo, hi, pin, kP, xP = s
    return '([' + ', '.join(f'({q}, {c}, {k})' for (q, c, k) in st) + f'], {g}, {lo}, {hi}, {pin}, {kP}, {"true" if xP else "false"})'

def fmt_stack(L): return '[' + ', '.join(fmt_state(s) for s in L) + ']'
