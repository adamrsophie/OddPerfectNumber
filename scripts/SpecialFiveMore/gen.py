# Untrusted helper script for the OddPerfect Lean library.
# Generator for the split certificate of OddPerfect.SpecialFiveMore.
#
# Usage: python3 -I gen.py K OUTDIR [PRATT_CHUNK TAB_CHUNK PIECE TREE_CAP]
#
# Builds, for the bound B = 10^K, the search tree that refutes an odd perfect number N with
# v_5(N) = 1 all of whose components p^v_p(N) are at most B, in the format of the checker
# OddPerfect.SpecialFive.check (module OddPerfect/SpecialFiveCode.lean), and splits it over
# several Lean data modules:
#   SpecialFiveMorePratt<i>  chunks of PRATT_CHUNK Pratt entries, each checked from a list of
#                            known primes of earlier chunks
#   SpecialFiveMorePc        the whole Pratt certificate, glued with check_append
#   SpecialFiveMoreTab<j>    chunks of TAB_CHUNK rows of the fact table
#   SpecialFiveMoreTable     the whole table, glued with tabOK_append
#   SpecialFiveMoreTree<k>   subtrees of at most PIECE constructors with their states, packed
#                            into modules of at most TREE_CAP constructors
#   SpecialFiveMore          the top of the tree glued with go_br, go_ord, go_stop, and the
#                            final theorem
# and OUTDIR/cert.json (B, Pratt chunks with their known lists, table chunks, the pieces with
# their states, the skeleton, the corrupted piece).
#
# The search is the one of scripts/SpecialFive/gen.py: a node is a list of entries (p, e),
# newest first, starting from [(5, 1)]. Leaves are tried in this order: capacity at an entry,
# the abundance of all entries, a forced prime r that is not an entry with r^2 > B (the one
# with the fewest new Pratt entries, then the smallest). Otherwise the node branches on the
# largest forced prime that is not an entry, over the exponents 2, 4, ... while r^e <= B.
#
# Standard library only: factorizations by trial division, Miller and Rabin, and Pollard's rho
# with Brent's cycle search. The output depends only on the arguments: factorizations are
# unique, every list is sorted or follows the deterministic search order, and Pratt witnesses
# are the smallest that work.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import json
import math
import os
import sys

K = int(sys.argv[1])
OUT = sys.argv[2]
PRATT_CHUNK = int(sys.argv[3]) if len(sys.argv) > 3 else 500
TAB_CHUNK = int(sys.argv[4]) if len(sys.argv) > 4 else 201
PIECE = int(sys.argv[5]) if len(sys.argv) > 5 else 150
TREE_CAP = int(sys.argv[6]) if len(sys.argv) > 6 else 600
B = 10 ** K
sys.setrecursionlimit(100000)

# Section: factorization.

SMALL = [p for p in range(2, 10000) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]


def is_prime(n):
    if n < 2:
        return False
    for p in SMALL[:30]:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def rho(n):
    """A nontrivial factor of the odd composite n (Brent's variant of Pollard's rho)."""
    c = 1
    while True:
        y, r, q, g, m = 2, 1, 1, 1, 256
        x = ys = y
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = math.gcd(q, n)
                k += m
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
        if g != n:
            return g
        c += 1


FAC = {}


def factorint(n):
    if n in FAC:
        return FAC[n]
    f = {}
    m = n
    for p in SMALL:
        if p * p > m:
            break
        while m % p == 0:
            f[p] = f.get(p, 0) + 1
            m //= p
    stack = [m] if m > 1 else []
    while stack:
        x = stack.pop()
        if is_prime(x):
            f[x] = f.get(x, 0) + 1
        else:
            d = rho(x)
            stack += [d, x // d]
    FAC[n] = f
    return f


fac = factorint


def gs(p, e):
    return (p ** (e + 1) - 1) // (p - 1)


def row(p, e):
    return sorted((r, k) for r, k in fac(gs(p, e)).items() if r != 2)


# Section: search (as SpecialFive).

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


def search(st):
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


# Section: splitting.

# Pratt chunks: each with the sorted list of the primes from 200 on that its entries use and
# that earlier chunks certify.
PCH = []
for i in range(0, len(PRATT), PRATT_CHUNK):
    ch = PRATT[i:i + PRATT_CHUNK]
    own = set()
    deps = set()
    for p, _, fs in ch:
        for q in fs:
            if q >= 200 and q not in own:
                deps.add(q)
        own.add(p)
    PCH.append({"entries": ch, "known": sorted(deps)})

TCH = [TAB[i:i + TAB_CHUNK] for i in range(0, len(TAB), TAB_CHUNK)]

# Skeleton and pieces. A piece is a subtree at a node position with at most PIECE
# constructors, together with its state. The skeleton holds the constructors above them.
PIECES = []


def split_node(t, st):
    if size(t) <= PIECE or t[0] != "br":
        PIECES.append({"state": st, "tree": t})
        return ["piece", len(PIECES) - 1]
    return ["br", t[1], split_chain(t[2], st, t[1], 2)]


def split_chain(t, st, r, e):
    if t[0] == "stop":
        return ["stop"]
    return ["ord", split_node(t[1], [(r, e)] + st), split_chain(t[2], st, r, e + 2)]


SKEL = split_node(TREE, [(5, 1)])

# Pack the pieces, in order, into tree modules of at most TREE_CAP constructors.
MODS = []
cur, cur_size = [], 0
for i, pc in enumerate(PIECES):
    s = size(pc["tree"])
    if cur and cur_size + s > TREE_CAP:
        MODS.append(cur)
        cur, cur_size = [], 0
    cur.append(i)
    cur_size += s
if cur:
    MODS.append(cur)


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


BAD = None
for i, pc in enumerate(PIECES):
    c, ok = corrupt(pc["tree"])
    if ok:
        BAD = {"piece": i, "tree": c}
        break
assert BAD is not None

os.makedirs(os.path.join(OUT, "OddPerfect"), exist_ok=True)
CERT = {"K": K, "pratt_chunks": PCH, "tab_chunks": TCH, "pieces": PIECES, "skeleton": SKEL,
        "modules": MODS, "bad": BAD}
with open(os.path.join(OUT, "cert.json"), "w") as f:
    json.dump(CERT, f, separators=(",", ":"))
    f.write("\n")

# Section: Lean output.

NS = "OddPerfect.SpecialFiveMore"
BTXT = "10 ^ %d" % K


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


def fmt_state(st):
    return "[%s]" % ", ".join("(%d, %d)" % (p, e) for p, e in st)


def header(imports, title, body):
    L = ["import " + m for m in imports]
    L += ["", "/-!", "# " + title, ""]
    L += body
    L += ["", "Generated by `scripts/SpecialFiveMore/gen.py %s` (see the README there)."
          % " ".join(sys.argv[1:2] + ["OUTDIR"] + sys.argv[3:]),
          "Ochem and Rao (Math. Comp. 81, 2012) proved that every odd perfect number has a",
          "component above `10 ^ 62`; this certificate is a machine checked special case. The",
          "odd perfect number conjecture remains open.", "-/", "",
          "namespace OddPerfect", "", "namespace SpecialFiveMore", "",
          "open DefectTree (Tab PCert tabOK)", "open SpecialFive (Cert Mode go)", "",
          "-- Check the theorems one after the other: in parallel their kernel checks raise the",
          "-- peak memory.", "set_option Elab.async false", ""]
    return L


def footer(names):
    L = ["end SpecialFiveMore", "", "end OddPerfect", ""]
    L += ["#print axioms %s.%s" % (NS, n) for n in names]
    return L


def write(mod, L):
    with open(os.path.join(OUT, "OddPerfect", mod + ".lean"), "w") as f:
        f.write("\n".join(L) + "\n")


ALLMODS = ["SpecialFiveMoreLemmas"]

# Pratt chunks.
for i, ch in enumerate(PCH):
    mod = "SpecialFiveMorePratt%d" % i
    L = header(["OddPerfect.SpecialFiveCode"],
               "Pratt certificate for `SpecialFiveMore`, chunk %d" % i,
               ["Entries %d to %d of the flat Pratt certificate (%d entries). The chunk is"
                % (i * PRATT_CHUNK, i * PRATT_CHUNK + len(ch["entries"]) - 1, len(PRATT)),
                "checked with the list `prattK%d` of primes certified by earlier chunks known;"
                % i,
                "`OddPerfect.SpecialFiveMorePc` checks that list and glues the chunks."])
    L += lean_list("prattC%d" % i, "PCert", "Pratt entries of chunk %d" % i, ch["entries"],
                   fmt_pratt)
    L += ["", "/-- The primes of earlier chunks that chunk %d uses. -/" % i,
          "def prattK%d : List ℕ :=" % i]
    L += fold("[" + ", ".join(str(q) for q in ch["known"]) + "]")
    L += ["", "/-- Chunk %d is accepted with the primes `prattK%d` known. -/" % (i, i),
          "theorem prattC%d_ok : Pratt.checkAux prattK%d prattC%d = true := by" % (i, i, i),
          "  decide +kernel", ""]
    L += footer(["prattC%d_ok" % i])
    write(mod, L)
    ALLMODS.append(mod)

# The glued Pratt certificate.
NP = len(PCH)
L = header(["OddPerfect.SpecialFiveMoreLemmas"] +
           ["OddPerfect.SpecialFiveMorePratt%d" % i for i in range(NP)],
           "Pratt certificate for `SpecialFiveMore`: the chunks glued",
           ["The flat Pratt certificate `pratt` is the concatenation of the %d chunks." % NP,
            "Each chunk was checked with a list of known primes; here each such list is",
            "checked to consist of primes of earlier chunks, and `check_append` glues."])
L += ["/-- The flat Pratt certificate. -/", "def pratt : PCert :="]
L += fold(" ++ ".join("prattC%d" % i for i in range(NP)))
L += [""]
assert PCH[0]["known"] == []
prev = "prattC0"
L += ["/-- The first chunk is accepted. -/",
      "theorem prattP0_ok : Pratt.check prattC0 = true := prattC0_ok", ""]
for i in range(1, NP):
    cur = "%s ++ prattC%d" % (prev, i)
    L += ["/-- The first %d chunks are accepted. -/" % (i + 1),
          "theorem prattP%d_ok :" % i]
    L += fold("Pratt.check (%s) = true :=" % cur, "    ")
    L += ["  check_append prattP%d_ok prattC%d_ok (by decide +kernel)" % (i - 1, i), ""]
    prev = "(%s)" % cur if i < NP - 1 else cur
L += ["/-- The flat Pratt certificate is accepted. -/",
      "theorem pratt_ok : Pratt.check pratt = true := prattP%d_ok" % (NP - 1), ""]
L += footer(["prattP%d_ok" % i for i in range(NP)] + ["pratt_ok"])
write("SpecialFiveMorePc", L)
ALLMODS.append("SpecialFiveMorePc")

# Table chunks.
NT = len(TCH)
for j, ch in enumerate(TCH):
    mod = "SpecialFiveMoreTab%d" % j
    L = header(["OddPerfect.SpecialFiveMorePc"],
               "Fact table for `SpecialFiveMore`, chunk %d" % j,
               ["Rows %d to %d of the fact table (%d rows), checked with `tabOK` against the"
                % (j * TAB_CHUNK, j * TAB_CHUNK + len(ch) - 1, len(TAB)),
                "flat Pratt certificate `pratt`."])
    L += lean_list("tabC%d" % j, "Tab", "Rows of chunk %d: `(p, e)` with facts `(r, k)`, "
                   "`r ^ k ∣ σ(p ^ e)`" % j, ch, fmt_tab)
    L += ["", "/-- Chunk %d of the table is accepted. -/" % j,
          "theorem tabC%d_ok : tabOK pratt tabC%d = true := by decide +kernel" % (j, j), ""]
    L += footer(["tabC%d_ok" % j])
    write(mod, L)
    ALLMODS.append(mod)

L = header(["OddPerfect.SpecialFiveMoreLemmas"] +
           ["OddPerfect.SpecialFiveMoreTab%d" % j for j in range(NT)],
           "Fact table for `SpecialFiveMore`: the chunks glued",
           ["The fact table `tab` is the concatenation of the %d chunks." % NT])
L += ["/-- The fact table. -/", "def tab : Tab :="]
L += fold(" ++ ".join("tabC%d" % j for j in range(NT)))
L += ["", "/-- The fact table is accepted. -/", "theorem tab_ok : tabOK pratt tab = true :="]
expr = "tabC0_ok"
for j in range(1, NT):
    expr = "tabOK_append (%s) tabC%d_ok" % (expr, j) if j > 1 else \
        "tabOK_append tabC0_ok tabC1_ok"
L += fold(expr, "  ")
L += [""]
L += footer(["tab_ok"])
write("SpecialFiveMoreTable", L)
ALLMODS.append("SpecialFiveMoreTable")


def lean_tree(t):
    if t[0] == "cap":
        return "(.cap %d)" % t[1]
    if t[0] == "abund":
        return ".abund"
    if t[0] == "stop":
        return ".stop"
    if t[0] == "br":
        return "(.br %d %s)" % (t[1], lean_tree(t[2]))
    return "(.ord %s %s)" % (lean_tree(t[1]), lean_tree(t[2]))


def tree_defs(name, t, doc):
    """Definitions for the tree t; subtrees above 40 constructors get their own names."""
    subs = []

    def rec(u, top):
        if u[0] in ("cap", "abund", "stop"):
            return lean_tree(u)
        if u[0] == "br":
            s = "(.br %d %s)" % (u[1], rec(u[2], False))
        else:
            s = "(.ord %s %s)" % (rec(u[1], False), rec(u[2], False))
        if not top and size(u) > 40:
            subs.append(s)
            return "%s_%d" % (name, len(subs) - 1)
        return s

    top = rec(t, True)
    L = []
    for i, s in enumerate(subs):
        L += ["/-- A subtree of `%s`. -/" % name, "def %s_%d : Cert :=" % (name, i)]
        L += fold(s)
        L += [""]
    L += ["/-- %s -/" % doc, "def %s : Cert :=" % name]
    L += fold(top)
    L += [""]
    return L


TREEMODS = []
for k, idx in enumerate(MODS):
    mod = "SpecialFiveMoreTree%d" % k
    TREEMODS.append(mod)
    body = ["Subtrees %d to %d of the search tree for `B = 10 ^ %d`, each checked by"
            % (idx[0], idx[-1], K),
            "`OddPerfect.SpecialFive.go` at its state. `OddPerfect.SpecialFiveMore` glues them."]
    names = []
    if BAD["piece"] in idx:
        body += ["The tree `pieceBad` cuts one chain of the subtree `piece%d` short; the tree"
                 % BAD["piece"], "check rejects it."]
    L = header(["OddPerfect.SpecialFiveMoreTable"], "Search tree for `SpecialFiveMore`, "
               "part %d" % k, body)
    for i in idx:
        pc = PIECES[i]
        L += tree_defs("piece%d" % i, pc["tree"], "Subtree %d of the search tree." % i)
        L += ["/-- Subtree %d is accepted at its state. -/" % i,
              "theorem piece%d_ok :" % i]
        L += fold("go (%s) tab piece%d %s .node = true := by" % (BTXT, i,
                                                               fmt_state(pc["state"])), "    ")
        L += ["  decide +kernel", ""]
        names.append("piece%d_ok" % i)
        if BAD["piece"] == i:
            L += tree_defs("pieceBad", BAD["tree"],
                           "Subtree %d with one chain cut short." % i)
            L += ["/-- The tree check rejects the corrupted subtree. -/",
                  "theorem pieceBad_rejected :"]
            L += fold("go (%s) tab pieceBad %s .node = false := by" % (
                BTXT, fmt_state(pc["state"])), "    ")
            L += ["  decide +kernel", ""]
            names.append("pieceBad_rejected")
    L += footer(names)
    write(mod, L)
    ALLMODS.append(mod)

# The final module: skeleton glue and the theorem.
SK = []
COUNT = [0]


def fresh():
    COUNT[0] += 1
    return "skel%d" % (COUNT[0] - 1)


def glue_node(s, st):
    """Returns (cert term, proof term) for the skeleton node s at the state st."""
    if s[0] == "piece":
        return "piece%d" % s[1], "piece%d_ok" % s[1]
    r = s[1]
    ct, pt = glue_chain(s[2], st, r, 2)
    name = fresh()
    SK.append(("/-- Skeleton node: the branch on %d. -/" % r, name, "(.br %d %s)" % (r, ct),
               "go (%s) tab %s %s .node = true" % (BTXT, name, fmt_state(st)),
               "go_br (by decide +kernel) %s" % pt))
    return name, name + "_ok"


def glue_chain(s, st, r, e):
    if s[0] == "stop":
        return ".stop", "(go_stop (by decide +kernel))"
    kc, kp = glue_node(s[1], [(r, e)] + st)
    rc, rp = glue_chain(s[2], st, r, e + 2)
    name = fresh()
    SK.append(("/-- Skeleton chain step: %d with exponent %d. -/" % (r, e), name,
               "(.ord %s %s)" % (kc, rc),
               "go (%s) tab %s %s (.chain %d %d) = true" % (BTXT, name, fmt_state(st), r, e),
               "go_ord %s %s" % (kp, rp)))
    return name, name + "_ok"


ROOT, ROOTPF = glue_node(SKEL, [(5, 1)])

WORDS = {24: "twenty_four", 27: "twenty_seven", 30: "thirty", 33: "thirty_three",
         36: "thirty_six"}
THM = "exists_component_gt_ten_pow_%s_of_factorization_five_eq_one" % WORDS.get(K, str(K))
L = ["import OddPerfect.SpecialFiveCheck", "import OddPerfect.SpecialFiveMoreLemmas"]
L += ["import OddPerfect.%s" % m for m in TREEMODS]
L += ["", "/-!",
      "# Odd perfect numbers with special component `5 ^ 1` have a component above `10 ^ %d`"
      % K, "",
      "If `N` is an odd perfect number with `v_5(N) = 1`, then some prime power component",
      "`p ^ v_p(N)` of `N` exceeds `10 ^ %d`. The proof is the certificate checker" % K,
      "`OddPerfect.SpecialFive.check` with its soundness theorem",
      "`OddPerfect.SpecialFive.check_sound`, both unchanged. The certificate is split: the",
      "Pratt certificate over `SpecialFiveMorePratt<i>` (glued in `SpecialFiveMorePc`), the",
      "fact table over `SpecialFiveMoreTab<j>` (glued in `SpecialFiveMoreTable`) and the",
      "search tree over `SpecialFiveMoreTree<k>`, whose subtrees this module glues with the",
      "lemmas `go_br`, `go_ord` and `go_stop` of `SpecialFiveMoreLemmas`.", "",
      "Generated by `scripts/SpecialFiveMore/gen.py %s` (see the README there)."
      % " ".join(sys.argv[1:2] + ["OUTDIR"] + sys.argv[3:]), "",
      "Ochem and Rao (Math. Comp. 81, 2012) proved that every odd perfect number has a",
      "component above `10 ^ 62`, so this statement is a special case of a published theorem;",
      "its interest is the machine checked proof. The odd perfect number conjecture remains",
      "open.", "-/", "",
      "namespace OddPerfect", "", "namespace SpecialFiveMore", "",
      "open SpecialFive (Cert Mode go)", "",
      "set_option Elab.async false", ""]
for doc, name, ct, stmt, pf in SK:
    L += [doc, "def %s : Cert :=" % name]
    L += fold(ct)
    L += ["", "/-- The skeleton node `%s` is accepted at its state. -/" % name,
          "theorem %s_ok :" % name]
    L += fold(stmt + " :=", "    ")
    L += fold(pf)
    L += [""]
L += ["/-- The search tree for `B = 10 ^ %d`. -/" % K, "def cert : Cert := %s" % ROOT, "",
      "/-- The tree is accepted. -/",
      "theorem go_ok : go (%s) tab cert [(5, 1)] .node = true := %s" % (BTXT, ROOTPF), "",
      "/-- The certificate for `B = 10 ^ %d` is accepted. -/" % K,
      "theorem check_cert : SpecialFive.check (%s) pratt tab cert = true := by" % BTXT,
      "  rw [SpecialFive.check, pratt_ok, tab_ok, go_ok]; rfl", "",
      "end SpecialFiveMore", "",
      "/-- An odd perfect number `N` with `v_5(N) = 1` has a prime factor `p` with",
      "`10 ^ %d < p ^ v_p(N)`. A special case of the theorem of Ochem and Rao (2012). -/" % K,
      "theorem %s {N : ℕ}" % THM,
      "    (h : OddPerfect N) (h5 : N.factorization 5 = 1) :",
      "    ∃ p ∈ N.primeFactors, %s < p ^ N.factorization p :=" % BTXT,
      "  SpecialFive.check_sound SpecialFiveMore.check_cert h h5", "",
      "end OddPerfect", ""]
L += ["#print axioms %s.%s_ok" % (NS, n) for _, n, _, _, _ in SK]
L += ["#print axioms %s.go_ok" % NS, "#print axioms %s.check_cert" % NS,
      "#print axioms OddPerfect.%s" % THM]
write("SpecialFiveMore", L)
ALLMODS.append("SpecialFiveMore")

with open(os.path.join(OUT, "modules.txt"), "w") as f:
    f.write(" ".join(ALLMODS) + "\n")

print("K=%d nodes=%d rows=%d pratt=%d used=%d pratt_chunks=%d tab_chunks=%d pieces=%d "
      "tree_modules=%d skeleton=%d" % (K, size(TREE), len(TAB), len(PRATT), len(USED), NP, NT,
                                       len(PIECES), len(MODS), len(SK)))
