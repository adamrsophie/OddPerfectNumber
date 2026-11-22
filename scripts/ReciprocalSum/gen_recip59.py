# Untrusted helper script for the OddPerfect Lean library.
# Generates the data block of OddPerfect/ReciprocalSumThree.lean: the weights W(p) of the
# odd primes p below 1009 (the least natural numbers with corrBound p <= W(p)/10^15) and the
# least bound K on the sum of W over an accepted head. A head is a subset T of the thirteen
# primes 3 .. 43; it is accepted when some role (no special prime in T, or a prime
# q = 1 (mod 4) of T as the special prime) gives a product of abundancy factors at most 2.
# With --stats it prints instead the number of accepted heads, K with a maximizing head, the
# weight R of the primes 47 .. 997, the log free threshold log2 - C and its margin over 59/100.
# Used by: OddPerfect/ReciprocalSumThree.lean (recipWeightTable and recipHeadBound: the text from the
# line "/-- The weights" up to the line of recipHeadBound).
# Run: python3 gen_recip59.py   (data block, printed to standard output)
#      python3 gen_recip59.py --stats
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys

M = 10 ** 15
B = 1009
H = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]


def u(p):
    x = F(1, p)
    return sum(x ** (i + 2) / (i + 2) for i in range(11)) + x ** 13 / (1 - x)


def ceil_m(r):
    return -(-r.numerator * M // r.denominator)


P = [p for p in range(3, B) if all(p % d for d in range(2, p))]
Wall = {p: ceil_m(u(p)) for p in P}
W = {p: Wall[p] for p in H}
rest = [p for p in P if p not in H]

acc = 0
K = 0
arg = None
for m in range(1 << len(H)):
    T = [H[i] for i in range(len(H)) if m >> i & 1]
    base = F(1)
    for p in T:
        base *= F(p * p + p + 1, p * p)
    ok = base <= 2 or any(
        base / F(q * q + q + 1, q * q) * F(q + 1, q) <= 2 for q in T if q % 4 == 1)
    if ok:
        acc += 1
        s = sum(W[p] for p in T)
        if s > K:
            K, arg = s, T

if "--stats" in sys.argv:
    R = sum(Wall[p] for p in rest)
    C = F(K + R, M) + F(1, 4 * (B - 2))
    thr = F(6931471803, 10 ** 10) - C
    print("accepted heads:", acc)
    print("K:", K, "at", arg)
    print("R (weight of the primes 47 .. 997):", R)
    print("threshold:", thr, float(thr))
    print("margin over 59/100:", float(thr - F(59, 100)))
    sys.exit(0)

out = ["/-- The weights: for each odd prime `p < 1009` (the head primes first), a natural number",
       "`w` with `corrBound p ≤ w / 10 ^ 15`. -/",
       "def recipWeightTable : List (ℕ × ℕ) :="]
items = ["(%d, %d)" % (p, Wall[p]) for p in H + rest]
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
out.append("")
out.append("/-- The bound on the weight of an accepted head. -/")
out.append("def recipHeadBound : ℕ := %d" % K)
print("\n".join(out))
