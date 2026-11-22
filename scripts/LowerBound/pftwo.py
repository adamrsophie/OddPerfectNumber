# Untrusted helper script for the OddPerfect Lean library.
# Factoring with a fixed effort and no time limit, so that the search of gentwo.py is
# deterministic: sympy (BPSW probable prime test, Pollard rho, Pollard p - 1) and the published
# ecm.py, plus optional checked hints (known prime factors of sigma(p^a), known splits).
# It stands in for pf.py (cypari2) under the module name pf; pfactor(n, secs) keeps the old
# interface, secs only selects the effort level (below 100: level 0, otherwise level 1).
# Used by: gentwo.py.
# Run: imported, not run directly.
# Requires: Python 3, sympy (1.14.0 was used for the Lean data, 1.12 gave the same trees;
# rho and p - 1 may depend on its version).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import re
from sympy import isprime, perfect_power
from sympy.ntheory.factor_ import pollard_rho, pollard_pm1
from ecm import ecm

LEVELS = {
    0: dict(rho=100000, pm1=200000, ecm=[(2000, 25), (11000, 90)]),
    1: dict(rho=1000000, pm1=3000000, ecm=[(50000, 120)]),
}
STATS = {'calls': 0, 'largest_full': 0, 'unfactored': {}}
_TD = [p for p in range(2, 100000) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
_cache = {}
HINT = {}        # composite -> nontrivial factor, filled by the caller after checking
USED_HINTS = set()


def _split(x, lv):
    c = LEVELS[lv]
    g = pollard_rho(x, retries=2, max_steps=c['rho'], seed=1234)
    if g: return g
    g = pollard_pm1(x, B=c['pm1'], retries=1, seed=1234)
    if g: return g
    for B1, cv in c['ecm']:
        g = ecm(x, cv, B1)
        if g: return g
    return None


def pfactor(n, secs):
    """(dict prime -> multiplicity, unfactored cofactor) with the effort level chosen by secs."""
    lv = 0 if secs < 100 else 1
    key = (n, lv)
    if key in _cache: return _cache[key]
    STATS['calls'] += 1
    fs, m = {}, n
    for p in _TD:
        if p * p > m: break
        while m % p == 0: fs[p] = fs.get(p, 0) + 1; m //= p
    stack, cof = ([m] if m > 1 else []), 1
    while stack:
        x = stack.pop()
        if x == 1: continue
        # every prime factor of x exceeds 10^5, so x < 10^10 is prime
        if x < 10 ** 10 or isprime(x):
            fs[x] = fs.get(x, 0) + 1; continue
        if x in HINT:
            USED_HINTS.add(x); g = HINT[x]; stack += [g, x // g]; continue
        pp = perfect_power(x)
        if pp: stack += [pp[0]] * pp[1]; continue
        g = _split(x, lv)
        if g is None: cof *= x; continue
        stack += [g, x // g]
    if cof == 1: STATS['largest_full'] = max(STATS['largest_full'], n)
    else: STATS['unfactored'][cof] = max(STATS['unfactored'].get(cof, -1), lv)
    _cache[key] = (fs, cof)
    return fs, cof


def cyclo(d, p):
    """The value of the cyclotomic polynomial Phi_d at p, by Moebius inversion."""
    num, den = 1, 1
    for k in range(1, d + 1):
        if d % k: continue
        m, mu, q, ok = d // k, 1, 2, True
        while q * q <= m:
            if m % q == 0:
                m //= q
                if m % q == 0: ok = False; break
                mu = -mu
            q += 1
        if not ok: continue
        if m > 1: mu = -mu
        if mu == 1: num *= p ** k - 1
        else: den *= p ** k - 1
    assert num % den == 0
    return num // den


def pari(s):
    """The one PARI call of gen.py: polcyclo(d, p) evaluated at an integer."""
    m = re.fullmatch(r'polcyclo\((\d+), (\d+)\)', s)
    return cyclo(int(m[1]), int(m[2]))


if __name__ == '__main__':
    import math
    assert cyclo(1, 7) == 6 and cyclo(2, 7) == 8 and cyclo(3, 7) == 57 and cyclo(6, 3) == 7
    assert cyclo(12, 2) == 13 and cyclo(5, 3) == 121 and pari('polcyclo(3, 7)') == 57
    for n in [2 ** 64 + 1, (10 ** 31 - 1) // 9, 3 ** 41 - 1, 1000003 * 1000033]:
        fs, cof = pfactor(n, 20)
        assert math.prod(q ** e for q, e in fs.items()) * cof == n and all(isprime(q) for q in fs)
    print('ok')
