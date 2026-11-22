# Untrusted helper script for the OddPerfect Lean library.
# Generates the data block of OddPerfect/ReciprocalSumSix.lean: for each odd prime p < B, a
# number n of series terms and the least natural number U with recipFourLogUp p n <= U/10^15
# (recipFourLogUp is the truncated series bound for log(p/(p - 1)) of
# OddPerfect/ReciprocalSumFour.lean).
# With --stats it mirrors the kernel check sixCheck exactly in integer arithmetic and prints,
# for each class of the module, the number of nodes, the largest threshold t (in units of
# 10^-15) that the check accepts, and whether the check accepts the threshold of the module.
# Used by: OddPerfect/ReciprocalSumSix.lean (sixTable: the text from the line
# "/-- The table" up to the end of the list).
# Run: python3 gen_recip6.py            (data block, printed to standard output)
#      python3 gen_recip6.py --stats
# Requires: Python 3 standard library. Deterministic.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys

sys.setrecursionlimit(100000)
M = 10 ** 15
LAM = 6931471803 * 10 ** 5
B = int(sys.argv[sys.argv.index("--B") + 1]) if "--B" in sys.argv else 10000
CLASSES = [("three_not_five", [3], [5], 604707640000000),
           ("five_not_three", [5], [3], 647649660000000)]


def odd_primes(b):
    return [p for p in range(3, b) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def log_up(p, n):
    x = F(1, p)
    return sum(x ** (i + 1) / (i + 1) for i in range(n)) + x ** (n + 1) / (1 - x)


def ceil_m(r):
    return -(-r.numerator * M // r.denominator)


def terms(p):
    n = 1
    while F(100 * M * p, (p - 1) * p ** (n + 1)) >= 1:
        n += 1
    return n


TABLE = [(p, terms(p), ceil_m(log_up(p, terms(p)))) for p in odd_primes(B)]


def early(t, m, r, u):
    return t < r or (2 * m * t + 2 * m * u + 3 * r + 4 * LAM <=
                     2 * m * r + 2 * m * LAM + 3 * t + 4 * u)


def check(t, req, exc, i, r, u, cnt):
    cnt[0] += 1
    if i == len(TABLE):
        return early(t, B, r, u)
    p, _, up = TABLE[i]
    if early(t, p, r, u):
        return True
    return ((p in req or check(t, req, exc, i + 1, r, u, cnt)) and
            (p in exc or check(t, req, exc, i + 1, r + M // p, u + up, cnt)))


if "--stats" in sys.argv:
    for name, req, exc, t0 in CLASSES:
        lo, hi = t0 - 10 ** 9, t0 + 10 ** 9
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if check(mid, req, exc, 0, 0, 0, [0]):
                lo = mid
            else:
                hi = mid - 1
        cnt = [0]
        ok = check(t0, req, exc, 0, 0, 0, cnt)
        print(name, "B", B, "primes", len(TABLE), "nodes", cnt[0], "largest accepted t:", lo,
              "module threshold %d accepted:" % t0, ok)
    sys.exit(0)

out = ["/-- The table: for each odd prime `p < %d`, a triple `(p, n, u)` with" % B,
       "`recipFourLogUp p n ≤ u / 10 ^ 15`. -/",
       "def sixTable : List (ℕ × ℕ × ℕ) :="]
items = ["(%d, %d, %d)" % e for e in TABLE]
line = "  ["
rows = []
for i, s in enumerate(items):
    piece = s + ("]" if i == len(items) - 1 else ",")
    if len(line) + len(piece) + 1 > 100:
        rows.append(line.rstrip())
        line = "   "
    line += piece + " "
rows.append(line.rstrip())
out += rows
print("\n".join(out))
