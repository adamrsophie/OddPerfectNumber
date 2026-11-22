# Untrusted helper script for the OddPerfect Lean library.
# Generates the data block of OddPerfect/ReciprocalSumUpper.lean: for each odd prime p below 71,
# a record with r = ceil(10^15/p), rational lower bounds w(a) of 10^15 log(sigma(p^a)/p^a)
# for a = 2, 4 (and a = 1, 5 when p = 1 mod 4) obtained from a truncated series with n terms,
# the odd primes below 71 dividing sigma(p^2) and p + 1, and lower bounds of the exponent
# of 3 in sigma(p^2) and in p + 1.
# With --stats it mirrors the kernel check upChk exactly in integer arithmetic: for each of the
# three classes (3 and 5 both divide N; only 3; only 5) it prints the number of nodes visited,
# the least threshold t (in units of 10^-15, rounded up to a multiple of 10^9) that the check
# accepts, and whether the check accepts the threshold used in the module.
# Used by: OddPerfect/ReciprocalSumUpper.lean (upTable: the text from the line
# "/-- The table" up to the end of the list).
# Run: python3 gen_recipupper.py   (data block, printed to standard output)
#      python3 gen_recipupper.py --stats
# Requires: Python 3 standard library. Deterministic. Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys

D = 10 ** 15
L2 = 693147180800000
B = 71
H = [p for p in range(3, B) if all(p % d for d in range(2, p))]


def geo(p, a):
    return sum(F(1, p) ** i for i in range(a + 1))


def low(p, a, n):
    x = 1 - 1 / geo(p, a)
    return sum(x ** (i + 1) / (i + 1) for i in range(n)) - x ** (n + 1) / (1 - x)


def floor_d(r):
    return r.numerator * D // r.denominator


def sig(p, a):
    return sum(p ** i for i in range(a + 1))


def v3(m):
    c = 0
    while m % 3 == 0:
        m //= 3
        c += 1
    return c


def forced(m):
    return [x for x in H if m % x == 0]


def nterms(p):
    # smallest n with every needed tail below 10^-18
    n = 1
    while True:
        ok = True
        for a in (1, 2, 4, 5):
            x = 1 - 1 / geo(p, a)
            if x ** (n + 1) / (1 - x) * 10 ** 18 >= 1:
                ok = False
        if ok:
            return n
        n += 1


def record(p):
    n = nterms(p)
    sp = p % 4 == 1
    w2 = floor_d(low(p, 2, n))
    w4 = floor_d(low(p, 4, n))
    w1 = floor_d(low(p, 1, n)) if sp else 0
    w5 = floor_d(low(p, 5, n)) if sp else 0
    return dict(p=p, n=n, r=-(-D // p), w2=w2, w4=w4, w1=w1, w5=w5,
                f2=forced(sig(p, 2)), f1=forced(p + 1) if sp else [],
                v2=v3(sig(p, 2)), v1=v3(p + 1) if sp else 0)


TAB = [record(p) for p in H]


def cost(m):
    return D // (2 * m * m) + 1


def cst(k):
    if k == len(TAB):
        return cost(B)
    p = TAB[k]['p']
    return cost(p + (5 - p % 4) % 4)


def chk(t, req, exc, stats):
    def stop(k, R, A, sp):
        return R + L2 + (0 if sp else cst(k)) <= t + A

    def rec(k, R, A, sp, ab, nd, v, b3):
        stats[0] += 1
        if stop(k, R, A, sp):
            return True
        if k == len(TAB):
            return False
        e = TAB[k]
        p = e['p']
        if not (p in req or p in nd or rec(k + 1, R, A, sp, [p] + ab, nd, v, b3)):
            return False
        if p in exc:
            return True
        b3n = b3 or p == 3
        ok2 = (any(x in ab or x in exc for x in e['f2']) or (b3n and 2 < v + e['v2'])
               or rec(k + 1, R + e['r'], A + e['w2'], sp, ab, e['f2'] + nd, v + e['v2'], b3n))
        if not ok2:
            return False
        if not rec(k + 1, R + e['r'], A + e['w4'], sp, ab, nd, v, b3):
            return False
        if sp or p % 4 != 1:
            return True
        ok1 = (any(x in ab or x in exc for x in e['f1']) or (b3 and 2 < v + e['v1'])
               or rec(k + 1, R + e['r'], A + e['w1'], True, ab, e['f1'] + nd, v + e['v1'], b3))
        if not ok1:
            return False
        return rec(k + 1, R + e['r'], A + e['w5'], True, ab, nd, v, b3)

    return rec(0, 0, 0, False, [], [], 0, False)


CLASSES = [('3 and 5 divide N', [3, 5], [7], 673634000000000),
           ('3 divides N, 5 does not', [3], [5], 657304000000000),
           ('5 divides N, 3 does not', [5], [3], 677637000000000)]


def lst(l):
    return '[' + ', '.join(str(x) for x in l) + ']'


def emit():
    out = ['/-- The table: for each odd prime `p < 71` the record',
           '`⟨p, n, r, w2, w4, w1, w5, f2, f1, v2, v1⟩` described at `URec`. -/',
           'def upTable : List URec :=']
    rows = []
    for e in TAB:
        rows.append('⟨%d, %d, %d, %d, %d, %d, %d, %s, %s, %d, %d⟩' % (
            e['p'], e['n'], e['r'], e['w2'], e['w4'], e['w1'], e['w5'], lst(e['f2']), lst(e['f1']),
            e['v2'], e['v1']))
    for i, row in enumerate(rows):
        pre = '  [' if i == 0 else '   '
        post = ']' if i == len(rows) - 1 else ','
        out.append(pre + row + post)
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    if '--stats' in sys.argv:
        step = 10 ** 9
        for name, req, exc, tmod in CLASSES:
            lo, hi = 550000, 700000
            while lo < hi:
                mid = (lo + hi) // 2
                if chk(mid * step, req, exc, [0]):
                    hi = mid
                else:
                    lo = mid + 1
            st = [0]
            ok = chk(tmod, req, exc, st)
            print(name, 'least t', lo * step, 'nodes at module t', st[0], 'accepts module t', ok)
    else:
        sys.stdout.write(emit())
