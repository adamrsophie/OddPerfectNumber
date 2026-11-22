# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of the certificates and inequalities of OddPerfect/RestrainedThree.lean (leaf
# q = 13, r = 7). It replays, with the semantics of the Lean functions (strip and sqLo with
# their fuel): kill over every x < 10000 with x = 1 (mod 3) (kill_all), rootIn on the values
# 7^a 13^b below 10^16 (box_7_13), the weight conditions of tail_le and the closing inequality,
# in exact rational arithmetic. See SPEC.md for the kill format.
# Used by: OddPerfect/RestrainedThree.lean.
# Run: python3 -I mirror13_7.py
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: reads and writes no files.
# License: GPL 3, same as the repository.
import sys
from fractions import Fraction as F

def phi3(t): return t * t + t + 1

def strip(p, f, n):
    while f > 0 and n % p == 0 and n != 0:
        n //= p
        f -= 1
    return n

def sqLo(m, f, lo, hi):
    while f > 0:
        c = (lo + hi) // 2
        if c * c <= m: lo = c
        else: hi = c
        f -= 1
    return lo

def mpart(x): return strip(13, 64, strip(7, 64, phi3(x) // 3))

def yfail(x, y): return y % 2 == 0 or y == 1 or y % 3 != 1 or strip(x, 64, mpart(y)) != 1

def killM(x, m, s):
    return (m != 1 and yfail(x, m) and s * s <= m and m < (s + 1) * (s + 1)
            and (s * s != m or yfail(x, s)))

def kill(x):
    return x % 2 == 0 or x == 1 or killM(x, mpart(x), sqLo(mpart(x), 40, 0, 2 ** 20))

def lowRoot(V, f, lo, hi):
    while f > 0:
        m = (lo + hi) // 2
        if phi3(m) <= V: lo = m
        else: hi = m
        f -= 1
    return lo

def rootIn(L, V):
    m = lowRoot(V, 64, 0, 2 ** 40)
    return (phi3(m) < V and V < phi3(m + 1)) or (phi3(m) == V and m in L)

def trial(n): return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))

def main():
    res = {}
    res["kill_all"] = all(x % 3 != 1 or kill(x) for x in range(10000))
    res["box_7_13"] = all(not 7 ** a * 13 ** b < 10 ** 16 or
                          rootIn([0, 2, 3, 9, 18], 7 ** a * 13 ** b)
                          for a in range(19) for b in range(15))
    res["box bounds"] = 10 ** 16 <= 7 ** 19 and 10 ** 16 <= 13 ** 15
    res["dummies"] = trial(10007) and trial(10009)
    a1, a2, a3, a4 = F(378, 1000), F(2774, 10000), F(1, 100), F(1, 100)
    b1, b2, beta = F(615, 1000), F(527, 1000), F(1, 10 ** 4)
    res["weights"] = (a1 ** 2 * 7 >= 1 and a2 ** 2 * 13 >= 1 and a3 ** 2 * 10000 >= 1
                      and b1 ** 4 * 7 >= 1 and b2 ** 4 * 13 >= 1 and beta ** 4 * 10 ** 16 >= 1)
    tail = F(121, 100) * (beta * (1 / (1 - b1) * (1 / (1 - b2) * (1 * 1))) +
        (a3 + a4) * (1 / (1 - a1) * (1 / (1 - a2) * (1 / (1 - a3) * (1 / (1 - a4))))))
    S = 2 * (F(121, 100) * (1 / F(10000 + 1))) + tail
    L = F(13, 9) * F(7, 6) * F(13, 12)
    print("close: %.7f < %.7f" % (L, 2 * (1 - S)))
    res["close"] = L < 2 * (1 - S)
    for k, v in res.items():
        print(k, v)
    ok = all(res.values())
    print("all checks pass" if ok else "FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
