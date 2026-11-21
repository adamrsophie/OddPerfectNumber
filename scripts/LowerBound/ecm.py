# Untrusted helper script for the OddPerfect Lean library.
# Lenstra ECM with Suyama curves, the fallback factoring method of nt.py without cypari2.
# Used by: nt.py.
# Run: imported, not run directly.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
"""Lenstra ECM with Suyama curves in Montgomery form (stage 1 + baby stage 2)."""
import math, random
from nt import SMALL

def _primes(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]

PR = _primes(2000000)

def xadd(P, Q, D, n):
    (xp, zp), (xq, zq), (xd, zd) = P, Q, D
    u = (xp - zp) * (xq + zq) % n
    v = (xp + zp) * (xq - zq) % n
    return (zd * (u + v) ** 2 % n, xd * (u - v) ** 2 % n)

def xdbl(P, a24, n):
    x, z = P
    s = (x + z) ** 2 % n; d = (x - z) ** 2 % n; t = s - d
    return (s * d % n, t * (d + a24 * t) % n)

def ladder(k, P, a24, n):
    R0, R1 = P, xdbl(P, a24, n)
    for b in bin(k)[3:]:
        if b == '1': R0, R1 = xadd(R1, R0, P, n), xdbl(R1, a24, n)
        else: R0, R1 = xdbl(R0, a24, n), xadd(R1, R0, P, n)
    return R0

def ecm_one(n, B1, B2, rng):
    sigma = rng.randrange(6, n - 1)
    u = (sigma * sigma - 5) % n; v = 4 * sigma % n
    x0 = pow(u, 3, n); z0 = pow(v, 3, n)
    t = pow(v - u, 3, n) * (3 * u + v) % n
    den = 16 * x0 * v % n
    g = math.gcd(den, n)
    if g != 1: return g if g != n else None
    a24 = t * pow(den, -1, n) % n
    P = (x0, z0)
    for p in PR:
        if p > B1: break
        pk = p
        while pk * p <= B1: pk *= p
        P = ladder(pk, P, a24, n)
    g = math.gcd(P[1], n)
    if 1 < g < n: return g
    if g == n: return None
    # stage 2: primes in (B1, B2], step by differences
    D = 2 * 105
    Pd = [None] * (D // 2 + 1)
    Pd[1] = P; P2 = xdbl(P, a24, n)
    if D // 2 >= 2:
        Pd[2] = P2
    for i in range(3, D // 2 + 1):
        Pd[i] = xadd(Pd[i - 1], P, Pd[i - 2], n)
    # simple: accumulate product of z of k*P for primes k, via ladder from Q = m*D*P
    acc = 1
    m = (B1 // D) * D
    Q = ladder(m, P, a24, n) if m > 0 else P
    QD = ladder(D, P, a24, n)
    Qprev = ladder(m - D, P, a24, n) if m - D > 0 else None
    idx = 0
    while m <= B2:
        # primes p in (m, m+D]: p = m + j
        for j in range(1, D, 2):
            pj = m + j
            if j > D // 2: continue
        for j in range(1, D // 2 + 1):
            if Pd[j] is None: continue
            # (Q.x*Pd.z - Q.z*Pd.x) vanishes mod q when (m±j)P = O
            acc = acc * (Q[0] * Pd[j][1] - Q[1] * Pd[j][0]) % n
        if Qprev is None:
            Qn = xdbl(Q, a24, n) if m == D else ladder(m + D, P, a24, n)
        else:
            Qn = xadd(Q, QD, Qprev, n)
        Qprev, Q = Q, Qn
        m += D
        idx += 1
        if idx % 50 == 0:
            g = math.gcd(acc, n)
            if 1 < g < n: return g
    g = math.gcd(acc, n)
    if 1 < g < n: return g
    return None

def ecm(n, curves=200, B1=50000, B2=None, seed=1):
    if B2 is None: B2 = 100 * B1
    rng = random.Random(seed ^ n)
    for c in range(curves):
        g = ecm_one(n, B1, B2, rng)
        if g: return g
    return None

if __name__ == '__main__':
    import time
    from nt import geom
    n = geom(7, 42)
    t = time.time(); g = ecm(n, 100, 20000)
    print(n, g, time.time() - t)
