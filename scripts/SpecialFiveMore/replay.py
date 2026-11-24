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
#     recorded for it.
# With "bad" the corrupted subtree replaces its original, and the replay must reject.
# Prints ACCEPT, or REJECT with the first failing check. Standard library only.
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


sys.setrecursionlimit(100000)
try:
    main()
    print("ACCEPT %s for B = 10^%d" % (WHICH, C["K"]))
except Reject as x:
    print("REJECT %s: %s" % (WHICH, x))
    sys.exit(1)
