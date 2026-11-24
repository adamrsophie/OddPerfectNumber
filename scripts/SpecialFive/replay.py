# Untrusted helper script for the OddPerfect Lean library.
# Independent replay of a SpecialFive certificate (does not import gen.py).
#
# Usage: python3 -I replay.py cert.json [tree|bad]
#
# Mirrors OddPerfect.SpecialFive.check: the Pratt certificate, the fact table and the tree from
# the root state [(5, 1)], for B = 10^K. Prints ACCEPT, or REJECT with the first failing node.
# Exit status: 0 on ACCEPT, 1 on REJECT, 2 for malformed input (unreadable JSON, a missing or
# surplus field, an unknown node tag or a wrong number of fields, a number that is not a
# natural number) or a usage error.
# Standard library only.
# Untrusted: the Lean kernel checks the certificate again; this replay is a second reading.
# License: GPL 3, same as the repository.
import json
import sys


def malformed(msg):
    print("malformed input: " + msg, file=sys.stderr)
    sys.exit(2)


def nat(x):
    """A natural number as Lean reads it: an integer at least 0, not a boolean or a float."""
    return type(x) is int and x >= 0


def nats(x, n=None):
    return type(x) is list and (n is None or len(x) == n) and all(nat(y) for y in x)


def tree_ok(t, node=True):
    """Exact constructors of SpecialFive.Cert: at a node cap r, abund, br r chain; in a chain
    ord node chain, stop."""
    stack = [(t, node)]
    while stack:
        t, node = stack.pop()
        if type(t) is not list or not t:
            return False
        if node and t[0] == "cap" and len(t) == 2 and nat(t[1]):
            continue
        if node and t[0] == "abund" and len(t) == 1:
            continue
        if node and t[0] == "br" and len(t) == 3 and nat(t[1]):
            stack.append((t[2], False))
            continue
        if not node and t[0] == "stop" and len(t) == 1:
            continue
        if not node and t[0] == "ord" and len(t) == 3:
            stack += [(t[1], True), (t[2], False)]
            continue
        return False
    return True


if len(sys.argv) not in (2, 3) or sys.argv[2:] not in ([], ["tree"], ["bad"]):
    print("usage: python3 -I replay.py cert.json [tree|bad]", file=sys.stderr)
    sys.exit(2)
try:
    with open(sys.argv[1]) as f:
        C = json.load(f)
except (OSError, ValueError) as e:
    malformed("%s: %s" % (sys.argv[1], e))
if type(C) is not dict or set(C) != {"K", "pratt", "tab", "tree", "bad"}:
    malformed("expected exactly the fields K, pratt, tab, tree and bad")
if not nat(C["K"]):
    malformed("K is not a natural number")
if type(C["pratt"]) is not list or not all(
        type(x) is list and len(x) == 3 and nat(x[0]) and nat(x[1]) and nats(x[2])
        for x in C["pratt"]):
    malformed("pratt is not a list of [p, a, [q, ...]] with natural numbers")
if type(C["tab"]) is not list or not all(
        type(x) is list and len(x) == 3 and nat(x[0]) and nat(x[1]) and type(x[2]) is list and
        all(nats(y, 2) for y in x[2]) for x in C["tab"]):
    malformed("tab is not a list of [p, e, [[r, k], ...]] with natural numbers")
for w in ("tree", "bad"):
    if not tree_ok(C[w]):
        malformed("%s: an unknown constructor or a wrong number of fields" % w)
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


def fail(x):
    print("REJECT %s: %s" % (WHICH, x))
    sys.exit(1)


try:
    KNOWN = pratt_ok(C["pratt"])
except Reject as x:
    fail(x)


def is_pr(r):
    return (r < 200 and trial_prime(r)) or r in KNOWN


def gs(p, e):
    return sum(p ** i for i in range(e + 1))


TAB = {}
for p, e, fs in C["tab"]:
    rs = [r for r, _ in fs]
    if len(set(rs)) != len(rs):
        fail("table row %d^%d: repeated prime" % (p, e))
    for r, k in fs:
        if not (is_pr(r) and r != 2 and k >= 1 and gs(p, e) % r ** k == 0):
            fail("table row %d^%d: bad fact (%d, %d)" % (p, e, r, k))
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
    fail(x)
