"""Pratt certificates in the format of OddPerfect/Pratt.lean: entries (p, a, fs) in dependency
order, fs the prime factors of p - 1 with multiplicity; leaves below LEAF pass trial division.
check() mirrors Pratt.check exactly (exact integer arithmetic)."""
from sympy import factorint
LEAF = 1000
def trial_prime(q):
    return q >= 2 and all(q % d for d in range(2, q))
def check(cert):
    known = []
    for p, a, fs in cert:
        prod = 1
        for q in fs: prod *= q
        if prod != p - 1: return False
        if not all(q in known or (q < LEAF and trial_prime(q)) for q in fs): return False
        if pow(a, p - 1, p) != 1: return False
        if not all(pow(a, (p - 1) // q, p) != 1 for q in fs): return False
        known.append(p)
    return True
def _build(p, out, seen):
    if p < LEAF or p in seen: return
    f = factorint(p - 1)
    for q in sorted(f): _build(q, out, seen)
    fs = [q for q in sorted(f) for _ in range(f[q])]
    a = 2
    while not (pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q in f)):
        a += 1
        if a > 10000: raise ValueError('no witness %d' % p)
    seen.add(p); out.append((p, a, fs))
def cert(p):
    out = []; _build(p, out, set())
    return out
def proven_prime(p):
    """returns ('small', None) for p < 2^64 (deterministic test), ('pratt', cert) above."""
    from sympy import isprime
    if p < 2 ** 64:
        return ('small', None) if isprime(p) else None
    c = cert(p)
    assert check(c) and c[-1][0] == p
    return ('pratt', c)
