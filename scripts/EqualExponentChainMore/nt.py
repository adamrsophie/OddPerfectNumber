# Untrusted helper script for the OddPerfect Lean library.
# Helper for gen2.py: probable prime test, Pollard rho (Brent), factorization and Pratt
# certificate construction. Differs from EqualExponentChain/nt.py in one place: factor caps
# the rho iterations at 10^5 and falls back to sympy ECM before giving up.
# Requires: Python 3 and sympy (for the ECM fallback). Randomized (random rho starting points).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script, and the helpers shared with
# EqualExponentChain (pm1.py, emit.py, osearch) in the sibling folder EqualExponentChain.
# License: GPL 3, same as the repository.

"""Small exact number theory helpers (sympy only for the ECM fallback)."""
import math
import random

_SMALL = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]


def is_probable_prime(n):
    if n < 2:
        return False
    for p in _SMALL:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _SMALL[:16]:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rho(n, iters=200000):
    """Pollard rho (Brent). Returns a nontrivial factor or None."""
    if n % 2 == 0:
        return 2
    for c in range(1, 8):
        y, r, q, g = random.randrange(1, n), 1, 1, 1
        m = 128
        x = ys = y
        count = 0
        while g == 1 and count < iters:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r *= 2
            count += r
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if 1 < g < n:
            return g
    return None


def factor(n, iters=200000):
    """Full factorization as a sorted list with multiplicity, or None if stuck."""
    out = []
    for p in _SMALL:
        while n % p == 0:
            out.append(p)
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if is_probable_prime(m):
            out.append(m)
            continue
        f = rho(m, min(iters, 10 ** 5))
        if f is None:
            from sympy.ntheory import ecm
            try:
                fs = [x for x in ecm(m, B1=50000, B2=5000000, max_curve=30) if 1 < x < m and m % x == 0]
            except ValueError:
                fs = []
            if not fs:
                return None
            f = fs[0]
        stack += [f, m // f]
    return sorted(out)


def phi_l(p, l):
    return sum(p ** i for i in range(l))


def partial_factors(n, l, trial_bound=200000, rho_iters=20000, max_prime=10 ** 15):
    """Prime factors of n = Phi_l(p) found by trial division over r = 2lk+1 (and r = l),
    then Pollard rho on the cofactor. Returns a set of primes (each verified to divide n)."""
    found = set()
    if n % l == 0:
        found.add(l)
        while n % l == 0:
            n //= l
    r = 2 * l + 1
    while r < trial_bound and n > 1:
        if n % r == 0:
            if is_probable_prime(r):
                found.add(r)
            while n % r == 0:
                n //= r
        r += 2 * l
    # rho on the cofactor, a few rounds
    stack = [n] if n > 1 else []
    rounds = 0
    while stack and rounds < 6:
        m = stack.pop()
        if is_probable_prime(m):
            if m <= max_prime:
                found.add(m)
            continue
        f = rho(m, rho_iters)
        rounds += 1
        if f is None:
            continue
        stack += [f, m // f]
    return found


def pratt(p, cache):
    """Pratt certificate entries (p, a, factors of p - 1) in dependency order, appended to
    cache (a dict p -> entry, insertion ordered). Primes below 1000 are left to trial division."""
    if p < 1000 or p in cache:
        return
    fs = factor(p - 1, 10 ** 7)
    assert fs is not None and math.prod(fs) == p - 1
    for f in sorted(set(fs)):
        pratt(f, cache)
    for a in range(2, p):
        if pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // f, p) != 1 for f in set(fs)):
            cache[p] = (p, a, fs)
            return
    raise ValueError(p)
