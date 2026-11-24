# Untrusted helper script for the OddPerfect Lean library.
# Generator for the certificate of OddPerfect.SpecialFiveData.
#
# Usage: python3 -I gen.py K OUTDIR
#
# Builds, for the bound B = 10^K, the search tree that refutes an odd perfect number N with
# v_5(N) = 1 all of whose components p^v_p(N) are at most B, in the format of the checker
# OddPerfect.SpecialFive.check (module OddPerfect/SpecialFiveCode.lean). Writes
#   OUTDIR/cert.json              the certificate (B, Pratt entries, fact table, tree)
#   OUTDIR/SpecialFiveData.lean   the Lean data module with the kernel check
# The output depends only on K: factorizations are unique, every list is sorted or follows
# the deterministic search order, and Pratt witnesses are the smallest that work.
#
# Search: a node is a list of entries (p, e), newest first, starting from [(5, 1)]. Leaves are
# tried in this order: capacity at an entry (the rows send more factors of r than v_r), the
# abundance of all entries, a forced prime r that is not an entry with r^2 > B (the one with
# the fewest new Pratt entries, then the smallest; a branch whose chain stops at once). Otherwise
# the node branches on the largest forced
# prime that is not an entry, over the exponents 2, 4, ... while r^e <= B.
#
# K is a natural number at least 1 (decimal digits only). Exit status: 0 when the files are
# written, 1 when the search gets stuck or the corrupted tree cannot be built (no chain with two
# exponents; nothing is written), 2 for a usage error.
# Requires: Python 3 and sympy (factorint) for the factorizations.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import json
import os
import sys

if len(sys.argv) != 3 or not (sys.argv[1].isascii() and sys.argv[1].isdigit()) or \
        int(sys.argv[1]) < 1:
    print("usage: python3 -I gen.py K OUTDIR (K a natural number at least 1)", file=sys.stderr)
    sys.exit(2)

from sympy import factorint

K = int(sys.argv[1])
OUT = sys.argv[2]
B = 10 ** K

FAC = {}


def fac(n):
    if n not in FAC:
        FAC[n] = factorint(n)
    return FAC[n]


def gs(p, e):
    return (p ** (e + 1) - 1) // (p - 1)


def row(p, e):
    return sorted((r, k) for r, k in fac(gs(p, e)).items() if r != 2)


# Pratt certificate: every fact prime from 200 on, in dependency order.
PRATT = []
DONE = set()


def witness(p, qs):
    a = 2
    while True:
        if pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q in qs):
            return a
        a += 1


def pratt(p):
    if p < 200 or p in DONE:
        return
    f = fac(p - 1)
    for q in sorted(f):
        pratt(q)
    fs = []
    for q in sorted(f):
        fs += [q] * f[q]
    PRATT.append([p, witness(p, sorted(f)), fs])
    DONE.add(p)



def cost(r, seen=None):
    """The number of new Pratt entries that certifying r needs."""
    if seen is None:
        seen = set()
    if r < 200 or r in DONE or r in seen:
        return 0
    seen.add(r)
    return 1 + sum(cost(q, seen) for q in fac(r - 1))


USED = set()
ROWS = set()
NODES = [0]


def search(st):
    NODES[0] += 1
    for x in st:
        ROWS.add(x)
    cnt = {}
    for p, e in st:
        for r, k in row(p, e):
            cnt[r] = cnt.get(r, 0) + k
    ex = dict(st)
    for r in sorted(ex):
        if cnt.get(r, 0) > ex[r]:
            USED.add(r)
            return ["cap", r]
    num, den = 1, 1
    for p, e in st:
        num *= gs(p, e)
        den *= p ** e
    if num > 2 * den:
        return ["abund"]
    forced = sorted(r for r in cnt if r not in ex)
    big = [r for r in forced if r * r > B]
    if big:
        w = min(big, key=lambda r: (cost(r), r))
        USED.add(w)
        pratt(w)
        return ["br", w, ["stop"]]
    if not forced:
        raise SystemExit("stuck node %r" % (st,))
    r = forced[-1]
    USED.add(r)
    pratt(r)
    kids = []
    e = 2
    while r ** e <= B:
        kids.append(search([(r, e)] + st))
        e += 2
    ch = ["stop"]
    for kid in reversed(kids):
        ch = ["ord", kid, ch]
    return ["br", r, ch]


TREE = search([(5, 1)])

TAB = []
for p, e in sorted(ROWS):
    fs = [[r, k] for r, k in row(p, e) if r in USED]
    if fs:
        TAB.append([p, e, fs])

for t in TAB:
    for r, _ in t[2]:
        pratt(r)


def size(t):
    if t[0] == "br":
        return 1 + size(t[2])
    if t[0] == "ord":
        return size(t[1]) + size(t[2])
    return 1


def corrupt(t):
    """Cut the first chain with at least two exponents one step early: the stop then sits
    at an exponent e with r^e <= B and fails."""
    if t[0] == "br":
        ch = t[2]
        if ch[0] == "ord" and ch[2][0] == "ord":
            return ["br", t[1], ["ord", ch[1], ["stop"]]], True
        c, ok = corrupt(ch)
        return ["br", t[1], c], ok
    if t[0] == "ord":
        c, ok = corrupt(t[1])
        if ok:
            return ["ord", c, t[2]], True
        c, ok = corrupt(t[2])
        return ["ord", t[1], c], ok
    return t, False


BAD, ok = corrupt(TREE)
if not ok:
    print("no chain with two exponents, so no corrupted tree; nothing written", file=sys.stderr)
    sys.exit(1)

os.makedirs(OUT, exist_ok=True)
CERT = {"K": K, "pratt": PRATT, "tab": TAB, "tree": TREE, "bad": BAD}
with open(os.path.join(OUT, "cert.json"), "w") as f:
    json.dump(CERT, f, separators=(",", ":"))
    f.write("\n")


SUBS = []


def lean_tree(t, top=False):
    if t[0] == "cap":
        return "(.cap %d)" % t[1]
    if t[0] == "abund":
        return ".abund"
    if t[0] == "stop":
        return ".stop"
    if t[0] == "br":
        s = "(.br %d %s)" % (t[1], lean_tree(t[2]))
    else:
        s = "(.ord %s %s)" % (lean_tree(t[1]), lean_tree(t[2]))
    if not top and size(t) > 40:
        SUBS.append(s)
        return "t%d" % (len(SUBS) - 1)
    return s


def fold(s, ind="  ", width=100):
    out, cur = [], ind
    for tok in s.split(" "):
        if len(cur) + len(tok) + 1 > width and cur.strip():
            out.append(cur.rstrip())
            cur = ind
        cur += tok + " "
    out.append(cur.rstrip())
    return out


def lean_list(name, typ, doc, items, fmt, per=100):
    out = []
    parts = []
    for i in range(0, len(items), per):
        part = "%s_%d" % (name, i // per)
        parts.append(part)
        out.append("/-- %s, part %d. -/" % (doc, i // per))
        out.append("def %s : %s :=" % (part, typ))
        out += fold("[" + ", ".join(fmt(x) for x in items[i:i + per]) + "]")
        out.append("")
    out.append("/-- %s. -/" % doc)
    out.append("def %s : %s :=" % (name, typ))
    out += fold(" ++ ".join(parts) if parts else "[]")
    return out


def fmt_pratt(x):
    return "(%d, %d, [%s])" % (x[0], x[1], ", ".join(str(q) for q in x[2]))


def fmt_tab(x):
    return "(%d, %d, [%s])" % (x[0], x[1], ", ".join("(%d, %d)" % (r, k) for r, k in x[2]))


L = []
L.append("import OddPerfect.SpecialFiveCode")
L.append("")
L.append("/-!")
L.append("# The special component `5 ^ 1` with components at most `10 ^ %d`: data" % K)
L.append("")
L.append("Generated by `scripts/SpecialFive/gen.py %d` (see the README there). The tree has %d"
         % (K, size(TREE)))
L.append("nodes; the table has %d rows and the Pratt certificate %d entries. This module only"
         % (len(TAB), len(PRATT)))
L.append("evaluates the checker; what an accepted certificate means is the soundness theorem")
L.append("`OddPerfect.SpecialFive.check_sound`. The tree `certBad` cuts one chain short; the")
L.append("tree check rejects it.")
L.append("-/")
L.append("")
L.append("namespace OddPerfect")
L.append("")
L.append("namespace SpecialFive")
L.append("")
L.append("open DefectTree (Tab PCert)")
L.append("")
L.append("-- Check the theorems one after the other: in parallel their kernel checks raise the")
L.append("-- peak memory.")
L.append("set_option Elab.async false")
L.append("")
L += lean_list("pratt", "PCert", "The flat Pratt certificate for the fact primes from 200 on",
               PRATT, fmt_pratt)
L.append("")
L += lean_list("tab", "Tab", "The fact table: rows `(p, e)` with facts `(r, k)`, "
               "`r ^ k ∣ σ(p ^ e)`", TAB, fmt_tab)
L.append("")
TOP = lean_tree(TREE, True)
for i, sub in enumerate(SUBS):
    L.append("/-- A subtree of the search tree. -/")
    L.append("def t%d : Cert :=" % i)
    L += fold(sub)
    L.append("")
L.append("/-- The search tree. -/")
L.append("def cert : Cert :=")
L += fold(TOP)
L.append("")
NS = len(SUBS)
TOPB = lean_tree(BAD, True)
for i, sub in enumerate(SUBS[NS:]):
    L.append("/-- A subtree of the corrupted tree. -/")
    L.append("def t%d : Cert :=" % (NS + i))
    L += fold(sub)
    L.append("")
L.append("/-- The tree with one chain cut short. -/")
L.append("def certBad : Cert :=")
L += fold(TOPB)
L.append("")
L.append("/-- The Pratt certificate is accepted. -/")
L.append("theorem pratt_ok : Pratt.check pratt = true := by decide +kernel")
L.append("")
L.append("/-- The fact table is accepted. -/")
L.append("theorem tab_ok : DefectTree.tabOK pratt tab = true := by decide +kernel")
L.append("")
L.append("/-- The tree is accepted. -/")
L.append("theorem go_ok : go (10 ^ %d) tab cert [(5, 1)] .node = true := by decide +kernel" % K)
L.append("")
L.append("/-- The certificate for `B = 10 ^ %d` is accepted. -/" % K)
L.append("theorem check_cert : check (10 ^ %d) pratt tab cert = true := by" % K)
L.append("  rw [check, pratt_ok, tab_ok, go_ok]; rfl")
L.append("")
L.append("/-- The tree check rejects the corrupted tree. -/")
L.append("theorem go_certBad : go (10 ^ %d) tab certBad [(5, 1)] .node = false := by" % K)
L.append("  decide +kernel")
L.append("")
L.append("end SpecialFive")
L.append("")
L.append("end OddPerfect")
L.append("")
for n in ["pratt_ok", "tab_ok", "go_ok", "check_cert"]:
    L.append("#print axioms OddPerfect.SpecialFive.%s" % n)
L.append("#print axioms OddPerfect.SpecialFive.go_certBad")
with open(os.path.join(OUT, "SpecialFiveData.lean"), "w") as f:
    f.write("\n".join(L) + "\n")
print("K=%d nodes=%d rows=%d pratt=%d used=%d" % (K, size(TREE), len(TAB), len(PRATT), len(USED)))
