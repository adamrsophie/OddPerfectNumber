# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of the certificates and inequalities of OddPerfect/RestrainedFour.lean (leaf
# r = 61 with 13^2 || N and q = 1 mod 3). It replays, with the semantics of the Lean functions:
# qSmall over range 157 (cert_small), qOK 8836 over 157 .. 9276 (cert_band1_0 .. cert_band1_3),
# qOK 169 over 9277 .. 9464 (cert_band2), slotOK 1000000 169 (cert_free), rootIn (box_61_13),
# the forcing facts that refute the exceptional special primes in excList, the weight
# conditions of rankin_tail and the three closing inequalities of the analytic core, in exact
# rational arithmetic. See SPEC.md for the slotOK format.
# Used by: OddPerfect/RestrainedFour.lean.
# Run: python3 -I mirror61.py
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: reads and writes no files.
# License: GPL 3, same as the repository.
import sys
from fractions import Fraction as F

def phi3(t): return t * t + t + 1

def lowRoot(V, f, lo, hi):
    while f > 0:
        m = (lo + hi) // 2
        if phi3(m) <= V: lo = m
        else: hi = m
        f -= 1
    return lo

def hasSmallFactor(m): return any(2 <= d and d < m and m % d == 0 for d in range(100))

def badSlot(q, m):
    return (m % 2 == 0 or m % 3 != 1 or m == 13 or m == 61 or m == q or m <= 1
            or hasSmallFactor(m))

def slotChk(q, V):
    W = 3 * V
    m = lowRoot(W, 64, 0, 2 ** 40)
    return (phi3(m) < W and W < phi3(m + 1)) or (phi3(m) == W and badSlot(q, m))

def loopQ(q, X, f, v):
    if f == 0: return False
    if phi3(X) <= 3 * v: return True
    return slotChk(q, v) and loopQ(q, X, f - 1, v * q)

def loop61(q, X, f, v):
    if f == 0: return False
    if phi3(X) <= 3 * v: return True
    return loopQ(q, X, 40, v) and loop61(q, X, f - 1, v * 61)

def loop13(q, X, f, v):
    if f == 0: return False
    if phi3(X) <= 3 * v: return True
    return loop61(q, X, 40, v) and loop13(q, X, f - 1, v * 13)

def slotOK(q, X): return loop13(q, X, 40, 1)

EXC = [13, 37, 61, 73, 97, 109, 181, 1801, 3169, 8269]
def qSmall(q): return q % 12 != 1 or q <= 1 or hasSmallFactor(q) or q in EXC
def qOK(X, q): return qSmall(q) or slotOK(q, X)

def rootIn(L, V):
    m = lowRoot(V, 64, 0, 2 ** 40)
    return (phi3(m) < V and V < phi3(m + 1)) or (phi3(m) == V and m in L)

def trial(n): return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))

def main():
    res = {}
    res["cert_small"] = all(qSmall(q) for q in range(157))
    for k, lo in enumerate([157, 2437, 4717, 6997]):
        res["cert_band1_%d" % k] = all(qOK(8836, lo + i) for i in range(2280))
    res["cert_band2"] = all(qOK(169, 9277 + i) for i in range(188))
    res["cert_free"] = slotOK(1000000, 169)
    res["box_61_13"] = all(not 61 ** a * 13 ** b < 10 ** 16 or rootIn([0, 3], 61 ** a * 13 ** b)
                           for a in range(9) for b in range(15))
    res["box bounds"] = 10 ** 16 <= 61 ** 9 and 10 ** 16 <= 13 ** 15
    # forcing refutations of excList: q -> chain c0, c1, ...: c0 | q + 1, c_{i+1} | phi3(c_i)
    chains = [(37, (19, 127)), (73, (37, 7)), (97, (7, 19)), (181, (7, 19)),
              (109, (5, 31, 331)), (3169, (5, 31, 331)), (8269, (5, 31, 331)),
              (1801, (17, 307, 43))]
    res["excList chains"] = all(
        (q + 1) % ch[0] == 0 and all(phi3(ch[i]) % ch[i + 1] == 0 for i in range(len(ch) - 1))
        and all(trial(c) for c in ch) for q, ch in chains)
    res["slot facts"] = phi3(168) == 28393 and trial(10007) and 10007 % 12 == 11
    # weights of rankin_tail: generators 61, 13 (alpha), floor weights (beta), B = 10^16
    a1, a2, b1, b2, beta = F(129, 1000), F(2774, 10000), F(36, 100), F(527, 1000), F(1, 10 ** 4)
    res["weights"] = (a1 ** 2 * 61 >= 1 and a2 ** 2 * 13 >= 1 and b1 ** 4 * 61 >= 1
                      and b2 ** 4 * 13 >= 1 and beta ** 4 * 10 ** 16 >= 1)
    def S(s, u, X):
        a3, a4 = F(1, s), F(1, u)
        return (F(121, 100) * (1 / F(X + 1)) +
                F(121, 100) * (beta * (1 / (1 - b1) * (1 / (1 - b2) * (1 * 1))) +
                (a3 + a4) * (1 / (1 - a1) * (1 / (1 - a2) * (1 / (1 - a3) * (1 / (1 - a4)))))))
    for Q, X, s, u in [(157, 8836, 12, 94), (9277, 169, 96, 13), (9465, 169, 97, 13)]:
        L = F(13, 9) * (F(183, 169) * (F(61, 60) * (F(Q) / (F(Q) - 1))))
        R = 2 * (1 - S(s, u, X))
        print("Q = %d, X = %d: %.7f < %.7f" % (Q, X, L, R))
        res["core %d" % Q] = (2 <= s and 2 <= u and s * s <= Q and u * u <= X
                              and 169 <= X <= 10007 and L < R)
    for k, v in res.items():
        print(k, v)
    ok = all(res.values())
    print("all checks pass" if ok else "FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
