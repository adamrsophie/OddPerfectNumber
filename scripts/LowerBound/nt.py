# Untrusted helper script for the OddPerfect Lean library.
# Number theory helpers for gen.py and emit.py: probable primality, factoring (PARI through
# pf.py when available, otherwise trial division, Pollard rho and ecm.py), Pratt data.
# Used by: gen.py, emit.py.
# Run: imported, not run directly.
# Requires: Python 3 standard library; cypari2 optional (see gen.py).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
"""Number theory helpers for the generator: primality, factoring, Pratt certificates."""
import math, random, sys
sys.setrecursionlimit(100000)

SMALL = [p for p in range(2, 20000) if all(p % d for d in range(2, int(p ** 0.5) + 1))]

def is_prp(n):
    if n < 2: return False
    for p in SMALL[:40]:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in SMALL[:20]:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def rho(n, budget):
    if n % 2 == 0: return 2
    rng = random.Random(n)
    for _ in range(4):
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g, r, q = 1, 1, 1
        it = 0
        while g == 1:
            x = y
            for _ in range(r): y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n); k += m
            r *= 2
            it += r
            if it > budget: return None
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if 1 < g < n: return g
    return None

import json, os, atexit
_FC = 'fcache.json'
_split = {}   # composite -> nontrivial factor
if os.path.exists(_FC):
    _split = {int(k): int(v) for k, v in json.load(open(_FC)).items()}
_tried = set()
def _save():
    json.dump({str(k): str(v) for k, v in _split.items()}, open(_FC, 'w'))
atexit.register(_save)
ECM_LEVEL = [(2000, 25), (11000, 90)]

def split(x, budget):
    if x in _split: return _split[x]
    if (x, budget) in _tried: return None
    g = rho(x, budget)
    if g is None:
        from ecm import ecm
        for B1, cv in ECM_LEVEL:
            g = ecm(x, cv, B1)
            if g: break
    if g: _split[x] = g
    else: _tried.add((x, budget))
    return g

try:
    import pf
except ImportError:
    pf = None
PARI_SECS = 30

_fcache = {}
def factor(n, budget=200000):
    """Return (dict prime->mult, cofactor) where cofactor is unfactored composite (or 1)."""
    key = (n, budget)
    if key in _fcache: return _fcache[key]
    if pf is not None:
        r = pf.pfactor(n, PARI_SECS)
        _fcache[key] = r
        return r
    fs, rest = {}, []
    m = n
    for p in SMALL:
        if p * p > m: break
        while m % p == 0: fs[p] = fs.get(p, 0) + 1; m //= p
    stack = [m] if m > 1 else []
    cof = 1
    while stack:
        x = stack.pop()
        if x == 1: continue
        if is_prp(x): fs[x] = fs.get(x, 0) + 1; continue
        r = math.isqrt(x)
        if r * r == x: stack += [r, r]; continue
        g = split(x, budget)
        if g is None: cof *= x; continue
        stack += [g, x // g]
    _fcache[key] = (fs, cof)
    return fs, cof

def geom(p, a):
    return (p ** (a + 1) - 1) // (p - 1)

TRIAL_MAX = 10 ** 6

_pratt = {}
PRATT_TRIAL = 1000

def pratt(q, depth=0):
    """Pratt certificate entries list [(p, a, fs)] in dependency order ending with q, or None.
    Factors below PRATT_TRIAL need no entry (Lean checks them by linear trial division)."""
    if q < PRATT_TRIAL: return []
    if q in _pratt: return _pratt[q]
    if not is_prp(q): return None
    fs, cof = factor(q - 1, 2000000)
    if cof != 1: _pratt[q] = None; return None
    ents = []
    for f in fs:
        sub = pratt(f, depth + 1)
        if sub is None: _pratt[q] = None; return None
        ents += sub
    flist = []
    for f, m in sorted(fs.items()): flist += [f] * m
    for a in range(2, 1000):
        if pow(a, q - 1, q) == 1 and all(pow(a, (q - 1) // f, q) != 1 for f in fs):
            break
    else:
        _pratt[q] = None; return None
    ents = ents + [(q, a, flist)]
    _pratt[q] = ents
    return ents
