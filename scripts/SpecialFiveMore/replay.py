# Untrusted helper script for the OddPerfect Lean library.
# Independent replay of a split SpecialFiveMore certificate (does not import gen.py).
#
# Usage: python3 -I replay.py cert.json [tree|bad]
#
# Mirrors the Lean modules of OddPerfect.SpecialFiveMore:
#   * each Pratt chunk is checked with only its list of known primes (Pratt.checkAux), and
#     each such list consists of primes of earlier chunks (check_append);
#   * each table chunk is checked with tabOK against the whole Pratt certificate;
#   * the skeleton is walked from the root state [(5, 1)] as go_br, go_ord and go_stop do, and
#     each subtree is checked with go at the state the walk reaches, which must be the state
#     recorded for it;
#   * the module manifest "modules" is a partition of the pieces (each piece in exactly one
#     nonempty module, no piece that does not exist).
# With "bad" the corrupted subtree replaces its original, and the replay must reject.
# Prints ACCEPT, or REJECT with the first failing check. Standard library only.
# Exit status: 0 on ACCEPT, 1 on REJECT, 2 for malformed input (unreadable JSON, a missing or
# surplus field, an unknown node tag or a wrong number of fields, a number that is not a
# natural number) or a usage error.
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


def tree_ok(t, node=True, skeleton=False):
    """Exact constructors of SpecialFive.Cert: at a node cap r, abund, br r chain; in a chain
    ord node chain, stop. In the skeleton a node is piece i or br r chain."""
    stack = [(t, node)]
    while stack:
        t, node = stack.pop()
        if type(t) is not list or not t:
            return False
        if node and not skeleton and t[0] == "cap" and len(t) == 2 and nat(t[1]):
            continue
        if node and not skeleton and t[0] == "abund" and len(t) == 1:
            continue
        if node and skeleton and t[0] == "piece" and len(t) == 2 and nat(t[1]):
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


def pratt_entry(x):
    return type(x) is list and len(x) == 3 and nat(x[0]) and nat(x[1]) and nats(x[2])


def tab_row(x):
    return (type(x) is list and len(x) == 3 and nat(x[0]) and nat(x[1]) and type(x[2]) is list
            and all(nats(y, 2) for y in x[2]))


if len(sys.argv) not in (2, 3) or sys.argv[2:] not in ([], ["tree"], ["bad"]):
    print("usage: python3 -I replay.py cert.json [tree|bad]", file=sys.stderr)
    sys.exit(2)
try:
    with open(sys.argv[1]) as f:
        C = json.load(f)
except (OSError, ValueError) as e:
    malformed("%s: %s" % (sys.argv[1], e))
if type(C) is not dict or set(C) != {"K", "pratt_chunks", "tab_chunks", "pieces", "skeleton",
                                      "modules", "bad"}:
    malformed("expected exactly the fields K, pratt_chunks, tab_chunks, pieces, skeleton, "
              "modules and bad")
if not nat(C["K"]):
    malformed("K is not a natural number")
if type(C["pratt_chunks"]) is not list or not all(
        type(ch) is dict and set(ch) == {"entries", "known"} and nats(ch["known"]) and
        type(ch["entries"]) is list and all(pratt_entry(x) for x in ch["entries"])
        for ch in C["pratt_chunks"]):
    malformed("pratt_chunks is not a list of {entries: [[p, a, [q, ...]], ...], known: [...]}")
if type(C["tab_chunks"]) is not list or not all(
        type(ch) is list and all(tab_row(x) for x in ch) for ch in C["tab_chunks"]):
    malformed("tab_chunks is not a list of lists of [p, e, [[r, k], ...]]")
if type(C["pieces"]) is not list or not all(
        type(x) is dict and set(x) == {"state", "tree"} and type(x["state"]) is list and
        all(nats(y, 2) for y in x["state"]) and tree_ok(x["tree"]) for x in C["pieces"]):
    malformed("pieces is not a list of {state: [[p, e], ...], tree: node} with known constructors")
if not tree_ok(C["skeleton"], skeleton=True):
    malformed("skeleton: an unknown constructor or a wrong number of fields")
if type(C["modules"]) is not list or not all(nats(x) for x in C["modules"]):
    malformed("modules is not a list of lists of piece numbers")
if (type(C["bad"]) is not dict or set(C["bad"]) != {"piece", "tree"} or
        not nat(C["bad"]["piece"]) or C["bad"]["piece"] >= len(C["pieces"]) or
        not tree_ok(C["bad"]["tree"])):
    malformed("bad is not {piece: a piece number, tree: node}")
WHICH = sys.argv[2] if len(sys.argv) > 2 else "tree"
B = 10 ** C["K"]


class Reject(Exception):
    pass


def trial_prime(q):
    return q >= 2 and all(q % d for d in range(2, q))


def check_aux(known, entries):
    known = list(known)
    for p, a, fs in entries:
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
        known.append(p)


def gs(p, e):
    return sum(p ** i for i in range(e + 1))


def look(tab, p, e):
    for q, m, fs in tab:
        if q == p and m == e:
            return fs
    return []


def kof(fs, r):
    for y in fs:
        if y[0] == r:
            return y[1]
    return 0


def go(tab, t, st, mode):
    tag = t[0]
    if mode is None:
        if tag == "cap":
            r = t[1]
            xs = [x for x in st if x[0] == r]
            if not xs or not xs[0][1] < sum(kof(look(tab, *y), r) for y in st):
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
            facts = [y for x in st for y in look(tab, *x)]
            if not any(y[0] == r for y in facts) or any(x[0] == r for x in st) or r == 5:
                raise Reject("branch prime %d not allowed at state %r" % (r, st))
            return go(tab, t[2], st, (r, 2))
        raise Reject("%s at a node, state %r" % (tag, st))
    r, e = mode
    if tag == "ord":
        go(tab, t[1], [(r, e)] + st, None)
        return go(tab, t[2], st, (r, e + 2))
    if tag == "stop":
        if not B < r ** e:
            raise Reject("stop at %d^%d <= B, state %r" % (r, e, st))
        return
    raise Reject("%s in a chain, state %r" % (tag, st))


def main():
    # Pratt chunks.
    certified = []
    for i, ch in enumerate(C["pratt_chunks"]):
        for q in ch["known"]:
            if q not in certified:
                raise Reject("pratt chunk %d: known prime %d not in an earlier chunk" % (i, q))
        check_aux(ch["known"], [tuple(x) for x in ch["entries"]])
        certified += [x[0] for x in ch["entries"]]
    cset = set(certified)

    def is_pr(r):
        return (r < 200 and trial_prime(r)) or r in cset

    # Table chunks.
    tab = []
    for j, ch in enumerate(C["tab_chunks"]):
        for p, e, fs in ch:
            rs = [r for r, _ in fs]
            if len(set(rs)) != len(rs):
                raise Reject("table chunk %d row %d^%d: repeated prime" % (j, p, e))
            for r, k in fs:
                if not (is_pr(r) and r != 2 and k >= 1 and gs(p, e) % r ** k == 0):
                    raise Reject("table chunk %d row %d^%d: bad fact (%d, %d)" % (j, p, e, r, k))
        tab += ch
    pieces = [[x["state"], x["tree"]] for x in C["pieces"]]
    if WHICH == "bad":
        pieces[C["bad"]["piece"]][1] = C["bad"]["tree"]
    seen = []

    def walk_node(s, st):
        if s[0] == "piece":
            if s[1] >= len(pieces):
                raise Reject("skeleton: piece %d does not exist" % s[1])
            rec, t = pieces[s[1]]
            if [tuple(x) for x in rec] != st:
                raise Reject("piece %d: recorded state %r, reached %r" % (s[1], rec, st))
            seen.append(s[1])
            return go(tab, t, st, None)
        if s[0] != "br":
            raise Reject("skeleton: %s at a node" % s[0])
        r = s[1]
        facts = [y for x in st for y in look(tab, *x)]
        if not any(y[0] == r for y in facts) or any(x[0] == r for x in st) or r == 5:
            raise Reject("skeleton branch prime %d not allowed at state %r" % (r, st))
        return walk_chain(s[2], st, r, 2)

    def walk_chain(s, st, r, e):
        while s[0] == "ord":
            walk_node(s[1], [(r, e)] + st)
            s, e = s[2], e + 2
        if s[0] != "stop" or not B < r ** e:
            raise Reject("skeleton chain for %d ends badly at exponent %d" % (r, e))

    walk_node(C["skeleton"], [(5, 1)])
    if sorted(seen) != list(range(len(pieces))):
        raise Reject("pieces not used exactly once")
    # The module manifest must be a partition of the pieces: every piece in exactly one
    # module, no piece that does not exist, no empty module.
    listed = [i for mod in C["modules"] for i in mod]
    if sorted(listed) != list(range(len(pieces))) or not all(C["modules"]):
        raise Reject("modules %r is not a partition of the %d pieces" % (C["modules"],
                                                                       len(pieces)))


sys.setrecursionlimit(100000)
try:
    main()
    print("ACCEPT %s for B = 10^%d" % (WHICH, C["K"]))
except Reject as x:
    print("REJECT %s: %s" % (WHICH, x))
    sys.exit(1)
