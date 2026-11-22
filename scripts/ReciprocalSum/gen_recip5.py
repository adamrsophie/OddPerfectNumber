# Untrusted helper script for the OddPerfect Lean library.
# Generates the data block of OddPerfect/ReciprocalSumFive.lean: for each odd prime p with
# 7 <= p < B, a number n of series terms and the least natural number U with
# recipFourLogUp p n <= U/10^15 (recipFourLogUp is the truncated series bound for
# log(p/(p - 1)) of OddPerfect/ReciprocalSumFour.lean).
# With --stats it mirrors the kernel check fiveCheck exactly in integer arithmetic and prints
# the number of nodes, the largest threshold t (in units of 10^-15) that the check accepts,
# and whether the check accepts the threshold used in the module.
# Used by: OddPerfect/ReciprocalSumFive.lean (fiveTable: the text from the line
# "/-- The table" up to the end of the list).
# Run: python3 gen_recip5.py            (data block, printed to standard output)
#      python3 gen_recip5.py --stats
# Requires: Python 3 standard library. Deterministic. Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys

sys.setrecursionlimit(100000)
M = 10 ** 15
LAM = 6931471803 * 10 ** 5
B = 5000
T0 = 667472880000000


def primes_from_7(b):
    return [p for p in range(7, b) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def log_up(p, n):
    x = F(1, p)
    return sum(x ** (i + 1) / (i + 1) for i in range(n)) + x ** (n + 1) / (1 - x)


def ceil_m(r):
    return -(-r.numerator * M // r.denominator)


def terms(p):
    # least n with 100 * 10^15 * p^-(n+1) * p/(p-1) < 1
    n = 1
    while F(100 * M * p, (p - 1) * p ** (n + 1)) >= 1:
        n += 1
    return n


TABLE = [(p, terms(p), ceil_m(log_up(p, terms(p)))) for p in primes_from_7(B)]


def early(t, m, r, u):
    return t < r or (2 * m - 3) * t + (2 * m - 4) * u <= (2 * m - 3) * r + (2 * m - 4) * LAM


def check(t, l, i, r, u, cnt):
    cnt[0] += 1
    if i == len(l):
        return early(t, B, r, u)
    p, _, up = l[i]
    if early(t, p, r, u):
        return True
    return check(t, l, i + 1, r, u, cnt) and check(t, l, i + 1, r + M // p, u + up, cnt)


if "--stats" in sys.argv:
    lo, hi = 667400000000000, 667500000000000
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if check(mid, TABLE, 0, 0, 0, [0]):
            lo = mid
        else:
            hi = mid - 1
    cnt = [0]
    ok = check(T0, TABLE, 0, 0, 0, cnt)
    print("B", B, "primes", len(TABLE), "nodes", cnt[0], "largest accepted t:", lo,
          "module threshold %d accepted:" % T0, ok)
    sys.exit(0)

out = ["/-- The table: for each odd prime `7 ≤ p < %d`, a triple `(p, n, u)` with" % B,
       "`recipFourLogUp p n ≤ u / 10 ^ 15`. -/",
       "def fiveTable : List (ℕ × ℕ × ℕ) :="]
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
