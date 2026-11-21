# Untrusted helper script for the OddPerfect Lean library.
# Helper: probable prime test, Pollard rho, odd prime factors below a bound, and a depth
# first search for forcing closed configurations. rows.py and pratt.py import it.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Search for forcing closed configurations (conjecture C1).

A configuration: dict p -> e over odd primes, one special q = 1 mod 4 with e_q = 1 mod 4,
all other exponents even, closed under odd prime factors of sigma(p^e), with
prod sigma(p^e)/p^e <= 2.  Exact arithmetic (Fraction) throughout.

Minimal configurations are the forcing closure of {q}, so DFS from the special prime.
"""
import sys, random, math
from fractions import Fraction as F
from functools import lru_cache

SMALL = [p for p in range(3, 2000) if all(p % d for d in range(2, int(p**.5) + 1))]

def is_prime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True  # deterministic below 3.3e24; beyond that a strong probable prime

def rho(n, limit):
    if n % 2 == 0: return 2
    for c in range(1, 20):
        y, m, g, r, q = random.randrange(1, n), 128, 1, 1, 1
        x = ys = y
        it = 0
        while g == 1:
            x = y
            for _ in range(r): y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n; q = q * abs(x - y) % n
                g = math.gcd(q, n); k += m
            r *= 2; it += r
            if it > limit: return None
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n; g = math.gcd(abs(x - ys), n)
        if g != n: return g
    return None

@lru_cache(maxsize=None)
def odd_factors(n, pmax, limit=None):
    """Odd prime factors of n (set), or ('BIG', set_known, cofactor) if some factor exceeds pmax
    or could not be found within the effort limit."""
    while n % 2 == 0: n //= 2
    fs = set()
    for p in SMALL:
        if n % p == 0:
            fs.add(p)
            while n % p == 0: n //= p
    stack, big = [n] if n > 1 else [], []
    while stack:
        m = stack.pop()
        if m == 1: continue
        if is_prime(m):
            (fs.add(m) if m <= pmax else big.append(m)); continue
        # composite: all its factors > 2000; if m < pmax^2 maybe splittable, else it has a factor > pmax unless smooth
        d = rho(m, limit or 8 * int(pmax ** 0.5) + 2000)
        if d is None: big.append(m); continue
        stack += [d, m // d]
    return frozenset(fs), tuple(big)

def sigma_pp(p, e): return (p ** (e + 1) - 1) // (p - 1)
def ab(p, e): return F(sigma_pp(p, e), p ** e)
def lb(p, special_ok): return F(p + 1, p) if special_ok else F(p * p + p + 1, p * p)

class Search:
    def __init__(s, pmax, evens, node_cap):
        s.pmax, s.evens, s.cap = pmax, evens, node_cap
        s.nodes = 0; s.killed_size = 0; s.killed_big = 0; s.closed = []; s.near = []
        s.big_events = []

    def run(s, q, eq):
        fs, big = odd_factors(sigma_pp(q, eq), s.pmax)
        assigned = {q: eq}
        s.dfs(assigned, ab(q, eq), set(fs) - {q}, big, depth=0)

    def dfs(s, assigned, prod, frontier, big, depth):
        s.nodes += 1
        if s.nodes > s.cap: return
        bound = prod
        for r in frontier: bound *= lb(r, False)
        for m in big: bound *= F(m + 1, m)
        if bound > 2: s.killed_size += 1; return
        if not frontier:
            if big:
                s.killed_big += 1
                s.near.append((bound, dict(assigned), big))
            else:
                s.closed.append((prod, dict(assigned)))
            return
        p = min(frontier)
        rest = frontier - {p}
        for e in s.evens:
            fs, bg = odd_factors(sigma_pp(p, e), s.pmax)
            new = set(fs) - set(assigned) - {p}
            a2 = dict(assigned); a2[p] = e
            s.dfs(a2, prod * ab(p, e), rest | new, tuple(sorted(set(big) | set(bg))), depth + 1)

def primes_1mod4(lo, hi):
    return [p for p in range(lo, hi) if p % 4 == 1 and is_prime(p)]

if __name__ == '__main__':
    # self check: the Descartes core 3^2 7^2 11^2 13^2 forces 61 (not closed)
    assert odd_factors(sigma_pp(13, 2), 10**6)[0] == {3, 61}
    assert sigma_pp(3, 4) == 121 and odd_factors(121, 100)[0] == {11}
    print('self check ok')
