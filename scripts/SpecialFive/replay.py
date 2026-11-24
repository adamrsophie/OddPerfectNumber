# Untrusted helper script for the OddPerfect Lean library.
# Independent replay of a SpecialFive certificate (does not import gen.py).
#
# Usage: python3 -I replay.py cert.json [tree|bad]
#
# Mirrors OddPerfect.SpecialFive.check: the Pratt certificate, the fact table and the tree from
# the root state [(5, 1)], for B = 10^K. Prints ACCEPT, or REJECT with the first failing node.
# Standard library only.
# Untrusted: the Lean kernel checks the certificate again; this replay is a second reading.
# License: GPL 3, same as the repository.
import json
import sys

C = json.load(open(sys.argv[1]))
WHICH = sys.argv[2] if len(sys.argv) > 2 else "tree"
B = 10 ** C["K"]


class Reject(Exception):
    pass


def trial_prime(q):
    return q >= 2 and all(q % d for d in range(2, q))


def pratt_ok(pc):
    known = set()
    for p, a, fs in pc:
        prod = 1
        for q in fs:
            prod *= q
        if prod != p - 1:
            raise Reject("pratt %d: factors do not multiply to p - 1" % p)
        for q in fs:
            if q not in known and not trial_prime(q):
                raise Reject("pratt %d: factor %d not certified" % (p, q))
        if pow(a, p - 1, p) != 1 or any(pow(a, (p - 1) // q, p) == 1 for q in fs):
            raise Reject("pratt %d: witness %d fails" % (p, a))
        known.add(p)
    return known


KNOWN = pratt_ok(C["pratt"])


def is_pr(r):
    return (r < 200 and trial_prime(r)) or r in KNOWN


def gs(p, e):
    return sum(p ** i for i in range(e + 1))


TAB = {}
for p, e, fs in C["tab"]:
    rs = [r for r, _ in fs]
    if len(set(rs)) != len(rs):
        raise Reject("table row %d^%d: repeated prime" % (p, e))
    for r, k in fs:
        if not (is_pr(r) and r != 2 and k >= 1 and gs(p, e) % r ** k == 0):
            raise Reject("table row %d^%d: bad fact (%d, %d)" % (p, e, r, k))
    if (p, e) not in TAB:
        TAB[(p, e)] = fs


def look(p, e):
    return TAB.get((p, e), [])


def kof(fs, r):
    for y in fs:
        if y[0] == r:
            return y[1]
    return 0


def go(t, st, mode):
    tag = t[0]
    if mode is None:
        facts = [y for x in st for y in look(*x)]
        if tag == "cap":
            r = t[1]
            xs = [x for x in st if x[0] == r]
            if not xs or not xs[0][1] < sum(kof(look(*y), r) for y in st):
                raise Reject("cap %d fails at state %r" % (r, st))
            return
        if tag == "abund":
            num, den = 1, 1
            for p, e in st:
                num *= gs(p, e)
                den *= p ** e
            if not 2 * den < num:
                raise Reject("abund fails at state %r" % (st,))
            return
        if tag == "br":
            r = t[1]
            if not any(y[0] == r for y in facts) or any(x[0] == r for x in st) or r == 5:
                raise Reject("branch prime %d not allowed at state %r" % (r, st))
            return go(t[2], st, (r, 2))
        raise Reject("%s at a node, state %r" % (tag, st))
    r, e = mode
    if tag == "ord":
        go(t[1], [(r, e)] + st, None)
        return go(t[2], st, (r, e + 2))
    if tag == "stop":
        if not B < r ** e:
            raise Reject("stop at %d^%d <= B, state %r" % (r, e, st))
        return
    raise Reject("%s in a chain, state %r" % (tag, st))


sys.setrecursionlimit(100000)
try:
    go(C[WHICH], [(5, 1)], None)
    print("ACCEPT %s for B = 10^%d" % (WHICH, C["K"]))
except Reject as x:
    print("REJECT %s: %s" % (WHICH, x))
    sys.exit(1)
