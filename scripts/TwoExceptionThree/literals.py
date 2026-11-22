"""Exact recomputation of every numeric literal in OddPerfect/TwoExceptionThree.lean.
Usage: python3 -I literals.py   (prints OK on success)."""
from fractions import Fraction as F


def sig(p, e):
    return sum(p ** i for i in range(e + 1))


def phi3(x):
    return x * x + x + 1


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


# Target A
assert sig(3, 4) == 121 == 11 ** 2
assert phi3(11) == 133 == 7 * 19
assert all(phi3(x) % 5 for x in range(5))
assert sig(11, 4) == 16105 == 5 * 3221 and is_prime(3221)
assert phi3(3221) == 10378063 and is_prime(10378063)
assert phi3(10378063) % 769 == 0 and is_prime(769)
assert phi3(769) % 31 == 0 and is_prime(31)
ab = F(sig(3, 4), 3 ** 4) * F(6, 5) * F(sig(11, 4), 11 ** 4) * F(sig(31, 2), 31 ** 2)
assert ab == F(2132302, 1046529) and ab > 2
d = 3 ** 4 * 5 * 11 ** 4 * 31 ** 2
assert sig(3, 4) * 6 * sig(11, 4) * sig(31, 2) > 2 * d
# 1 + 11 + ... + 11^(n-1) = n (mod 5)
assert all(sig(11, n - 1) % 5 == n % 5 for n in range(1, 60))
# Target B
assert sig(61, 4) == 14076605 == 5 * 131 * 21491
for p in (131, 21491, 17293, 421, 13, 61):
    assert is_prime(p)
assert phi3(131) == 17293 and 17293 % 3 == 1
assert phi3(21491) % 421 == 0 and 421 % 3 == 1
assert sig(13, 2) == 183 == 3 * 61 and sig(5, 1) == 6
# the table of geom_five_table and the period 20
for c in range(1, 5):
    assert sum(c ** i for i in range(20)) % 5 == 0
    for m in range(1, 20, 2):
        if sum(c ** i for i in range(m)) % 5 == 0:
            assert c == 1 and m % 5 == 0
print("OK")
