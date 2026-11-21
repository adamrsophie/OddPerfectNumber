# Untrusted helper script for the OddPerfect Lean library.
# Independent checker mirroring checkAll of OddPerfect/EqualExponentChain.lean. It imports
# nothing from the generator.
# Run: python3 checker.py cert_5.json cert_7.json ...
# Requires: Python 3 standard library. Running time: seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Independent checker mirroring OddPerfect/EqualExponentChain.lean `checkAll`.

Imports nothing from the generator. Trees are nested tuples/lists:
  ['ord', p, r, next] ['spec', m, r, next] ['branch', r, yes, no]
  ['expo', s, d, v, next] ['over', s, [[p, k], ...], m, k] ['mod4']
"""
import sys
import json
import math


def trial_prime(q):
    return q >= 2 and all(q % d != 0 for d in range(2, q))


def pratt_check(pc):
    known = []
    for p, a, fs in pc:
        ok = (math.prod(fs) == p - 1 and
              all(f in known or trial_prime(f) for f in fs) and
              pow(a, p - 1, p) == 1 and
              all(pow(a, (p - 1) // f, p) != 1 for f in fs))
        if not ok:
            return False
        known.append(p)
    return True


def gm(p, m, n):
    acc = 0
    for _ in range(n):
        acc = (acc * p + 1) % m
    return acc


def is_p(pc_primes, r):
    return r in pc_primes or trial_prime(r)


def all_ne(Q, s, n):
    return all(pow(Q, j, s) != 1 for j in range(1, n + 1))


def expo_factor(l, s, d, v):
    return s ** (l - 1) if d == 1 else d * s ** max(l - 1 - v, 0)


def run(l, pcp, st, c):
    known, ex, qs, M = st
    kind = c[0]
    if kind == 'ord':
        _, p, r, nxt = c
        neq = (r != qs) if qs is not None else (r % 4 != 1 or r in ex)
        return (p in known and is_p(pcp, r) and r != 2 and neq and gm(p, r, l) == 0 and
                run(l, pcp, ([r] + known, ex, qs, M), nxt))
    if kind == 'spec':
        _, m, r, nxt = c
        if qs is None:
            return False
        return (1 <= m and M % m == 0 and is_p(pcp, r) and r != 2 and r != qs and
                gm(qs, r, m) == 0 and run(l, pcp, ([r] + known, ex, qs, M), nxt))
    if kind == 'branch':
        _, r, y, n = c
        return run(l, pcp, (known, ex, r, M), y) and run(l, pcp, (known, [r] + ex, qs, M), n)
    if kind == 'expo':
        _, s, d, v, nxt = c
        if qs is None:
            return False
        Q = qs
        ok = (s in known and s != 2 and s != l and s % l != 1 and 1 <= d and
              pow(Q, d, s) == 1 and all_ne(Q, s, d - 1) and
              (d == 1 or pow(Q, d, s ** (v + 1)) != 1))
        if not ok:
            return False
        f = expo_factor(l, s, d, v)
        return run(l, pcp, (known, ex, qs, M * f // math.gcd(M, f)), nxt)
    if kind == 'over':
        _, s, ps, m, k = c
        if not (s in known and s != 2):
            return False
        if not all(p in known and gm(p, s ** j, l) == 0 for p, j in ps):
            return False
        firsts = [p for p, _ in ps]
        if len(set(firsts)) != len(firsts):
            return False
        if k != 0:
            if qs is None or not (1 <= m and M % m == 0 and gm(qs, s ** k, m) == 0):
                return False
        return l - 1 < k + sum(j for _, j in ps)
    if kind == 'mod4':
        return qs is not None and qs % 4 != 1
    return False


def check_all(l, pc, ordt, spect):
    if not (trial_prime(l) and l != 2 and pratt_check(pc)):
        return False
    pcp = {e[0] for e in pc}
    return run(l, pcp, ([l], [l], None, 2), ordt) and run(l, pcp, ([], [], l, 2), spect)


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    for fn in sys.argv[1:]:
        d = json.load(open(fn))
        print(fn, check_all(d['l'], d['pratt'], d['ord'], d['spec']))
