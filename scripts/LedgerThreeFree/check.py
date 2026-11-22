"""Exact checks for the numbers used in OddPerfect/LedgerThreeFree.lean.

Generator note: this script recomputes every numerical claim of the proof with exact
arithmetic (fractions and integers; sympy only for factoring and primality tests) and prints
the literals used in the Lean file: the envelope comparisons for q0 = 229, 3541 and the case
q = 109 with two primes above 660, the forcing primes for q < 229, the 15 primes p <= 660 with
p = 2 (mod 3) and p = 1 (mod 5) with the prime factor of sigma(p^4) used to exclude each, the
five attached large primes x, the cofactors of sigma(p^24) and sigma(x^4) used as certificates,
and the residues behind the Phi_125 step. Lean rechecks every literal itself.
Run with: python3 -I check.py
"""
from fractions import Fraction as Fr


def isprime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def factor(n):
    import sympy
    f = []
    for r, k in sorted(sympy.factorint(n).items()):
        f += [r] * k
    return f


def env(L):
    r = Fr(1)
    for l in L:
        r *= Fr(l, l - 1)
    return r


P2 = [p for p in range(5, 2000) if isprime(p) and p % 3 == 2]
L31 = P2[:31]
L29 = P2[:29]
print("L31 =", L31)
E31 = env(L31)
print("env31 =", float(E31), E31 < Fr(19901, 10000))


def tail(b):
    return Fr(12 * b, 12 * b - 13)


# separated product bound: a/(a-1) * T(13a) <= T(a)
for a in [5, 59, 251, 3000]:
    assert Fr(a, a - 1) * tail(13 * a) <= tail(a)

for q0, b in [(229, 3000), (3541, 251)]:
    v = Fr(q0, q0 - 1) * E31 * tail(b)
    print("q0", q0, "b", b, float(v), v < 2)

# q = 109: two ordinary primes above 660
big = [p for p in P2 if p > 660][:2]
print("first primes 2 mod 3 above 660:", big)
v = Fr(109, 108) * env(L29) * Fr(661, 660) ** 2
print("q=109 two big:", float(v), v < 2)
print("env29 exact =", env(L29))

# phi3 small cases 11 mod 12 below 59
for p in range(5, 59):
    if isprime(p) and p % 12 == 11:
        print("F(%d) =" % p, factor(p * p + p + 1))

# q < 229 with q = 1 mod 12: a prime = 1 mod 3 dividing q + 1
for q in range(13, 229):
    if isprime(q) and q % 12 == 1:
        rs = [r for r in set(factor(q + 1)) if r % 3 == 1]
        print("q", q, "q+1 primes 1 mod 3:", rs)

# F(p) mod 5 and 109^a mod 5
print("F mod 5:", sorted({(x * x + x + 1) % 5 for x in range(5)}), "109 mod 5:", 109 % 5)
# 31 divides Phi_5(109); order of 109 mod 31 is 5
print("109^5 mod 31", pow(109, 5, 31), "109 mod 31", 109 % 31)
print("v5(109^2-1):", factor(109 ** 2 - 1))

# the 15 small primes p <= 660, p = 2 mod 3, p = 1 mod 5
S15 = [p for p in range(5, 661) if isprime(p) and p % 3 == 2 and p % 5 == 1]
print(len(S15), S15)
surv = {}
for p in S15:
    s4 = sum(p ** i for i in range(5))
    f = factor(s4)
    bad1 = [r for r in f if r % 3 == 1 and r != 109]
    bigs = sorted({r for r in f if r > 660})
    status = "kill(1 mod 3: %s)" % bad1[0] if bad1 else (
        "kill(two big)" if len(bigs) >= 2 else ("survivor x=%d" % bigs[0] if bigs else "NO KILL"))
    print(p, f, status)
    if not bad1 and len(bigs) == 1:
        surv[p] = bigs[0]
print("survivors", surv)

# capacities: sigma(x^4) for the pinned x, sigma(p^24) for the survivor p
for p, x in surv.items():
    fx = factor(sum(x ** i for i in range(5)))
    print("x", x, "x%5", x % 5, "x%3", x % 3, "sigma(x^4) =", fx,
          "primes 1 mod 3:", [r for r in fx if r % 3 == 1 and r != 109],
          "big:", [r for r in fx if r > 660])
    # Phi_25(p) = sigma(p^24) / sigma(p^4); look for a small prime 1 mod 3 or a big prime != x
    n = sum(p ** i for i in range(25)) // sum(p ** i for i in range(5))
    found = []
    d = 2
    m = n
    while d < 10 ** 5 and m > 1:
        if m % d == 0:
            found.append(d)
            while m % d == 0:
                m //= d
        d += 1
    print("  Phi_25(%d) small prime factors:" % p, found, "cofactor digits", len(str(m)))
    print("  1 mod 3:", [r for r in found if r % 3 == 1], "big != x:", [r for r in found if r > 660 and r != x])

# primes r <= 660 with r = 1 mod 125
print("r = 1 mod 125 primes <= 660:", [r for r in range(2, 661) if isprime(r) and r % 125 == 1])
# Phi_5(y) mod 8 for odd y, and 5*251^a mod 8 and mod 3
print("Phi5 mod 8:", sorted({(1 + y + y * y + y ** 3 + y ** 4) % 8 for y in range(1, 8, 2)}))
print("Phi5 mod 3 for y=2 mod 3:", (1 + 2 + 4 + 8 + 16) % 3, "251 mod 8, mod 3:", 251 % 8, 251 % 3)
print("Phi5(y) mod 25 for y = 1 mod 5:", sorted({(1 + y + y * y + y ** 3 + y ** 4) % 25 for y in range(1, 25, 5)}))

# certificates used in Lean for the case q = 109
import sympy
surv = {11: 3221, 41: 579281, 251: 6586781, 431: 510101, 491: 603791}
for p, x in surv.items():
    s4 = sum(p ** i for i in range(5))
    s24 = sum(p ** i for i in range(25))
    assert sympy.isprime(x) and s4 % x == 0 and x > 660
    assert s24 % (5 * s4) == 0
    c = s24 // (5 * s4)
    assert c > 1 and all(c % d for d in range(2, 661)) and c % x
    sx = sum(x ** i for i in range(5))
    small = 1
    for r, k in sympy.factorint(sx).items():
        if r <= 660:
            small *= r ** k
    cx = sx // small
    assert cx > 1 and all(cx % d for d in range(2, 661)) and cx % x
    print("cert", p, x, "c25 =", c, "small part of sigma(x^4) =", small, "cofactor =", cx)
for r in [211, 31, 61, 1231, 17761, 1871, 13001, 4091, 751481, 170638711]:
    assert sympy.isprime(r)
print("all certificates verified")
