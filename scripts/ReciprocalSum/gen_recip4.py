# Untrusted helper script for the OddPerfect Lean library.
# Generates the data block of OddPerfect/ReciprocalSumFour.lean: for each of the thirteen head
# primes p = 3 .. 43, the least natural number U(p) with recipFourLogUp p 20 <= U(p)/10^15,
# where recipFourLogUp p n is the truncated series bound for log(p/(p - 1)) used in that module.
# With --stats it mirrors the kernel check fourCheck exactly in integer arithmetic: for each
# of the four classes (3 and 5 both divide N; only 3; only 5; neither) it prints the number of
# leaves, the largest threshold t (in units of 10^-15) that the check accepts, and whether the
# check accepts the threshold used in the module.
# Used by: OddPerfect/ReciprocalSumFour.lean (fourUTable: the text from the line
# "/-- The upper bounds" up to the end of the list).
# Run: python3 gen_recip4.py   (data block, printed to standard output)
#      python3 gen_recip4.py --stats
# Requires: Python 3 standard library. Deterministic. Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys

M = 10 ** 15
NT = 20
LAM = 6931471803 * 10 ** 5
H = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]


def log_up(p, n):
    x = F(1, p)
    return sum(x ** (i + 1) / (i + 1) for i in range(n)) + x ** (n + 1) / (1 - x)


def ceil_m(r):
    return -(-r.numerator * M // r.denominator)


U = {p: ceil_m(log_up(p, NT)) for p in H}


def leaf_ok(t, r, u):
    return t < r or ((255 * t < 255 * r + M or 91 * t + 90 * u <= 91 * r + 90 * LAM)
                     and 511 * t + 510 * u <= 511 * r + 510 * LAM)


def check(t, req, exc, l, num, den, r, u, sp, cnt):
    if not l:
        cnt[0] += 1
        return 2 * den < num or leaf_ok(t, r, u)
    p, rest = l[0], l[1:]
    if not (p in req or check(t, req, exc, rest, num, den, r, u, sp, cnt)):
        return False
    if p in exc:
        return True
    rp, up = r + M // p, u + U[p]
    if not check(t, req, exc, rest, num * (p * p + p + 1), den * p * p, rp, up, sp, cnt):
        return False
    return sp or p % 4 != 1 or check(t, req, exc, rest, num * (p + 1), den * p, rp, up, True, cnt)


CLASSES = [("three_five", [3, 5], [], 596063100000000),
           ("three_not_five", [3], [5], 604706000000000),
           ("five_not_three", [5], [3], 647648000000000),
           ("not_three_not_five", [], [3, 5], 667363000000000)]

if "--stats" in sys.argv:
    for name, req, exc, t0 in CLASSES:
        lo, hi = 0, M
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if check(mid, req, exc, H, 1, 1, 0, 0, False, [0]):
                lo = mid
            else:
                hi = mid - 1
        cnt = [0]
        ok = check(t0, req, exc, H, 1, 1, 0, 0, False, cnt)
        print(name, "leaves:", cnt[0], "largest accepted t:", lo, "= %.12f" % (lo / M),
              "module threshold %d accepted:" % t0, ok)
    sys.exit(0)

out = ["/-- The upper bounds: for each head prime `p`, a natural number `u` with",
       "`recipFourLogUp p 20 ≤ u / 10 ^ 15`. -/",
       "def fourUTable : List (ℕ × ℕ) :="]
items = ["(%d, %d)" % (p, U[p]) for p in H]
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
