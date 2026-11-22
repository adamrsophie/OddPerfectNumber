# Untrusted helper script for the OddPerfect Lean library.
# Successor of gen5.py for the checker LPF3.exists_primeFactor_gt_of_cert3 of
# OddPerfect/LargestPrimeFactorThree.lean. The search and its table are those of gen5.py
# (imported from the same folder). The row certificates (p, R, X, EXS, EX) avoid the large
# numbers sigma(p^(r-1)): for every prime r with a prime q <= B, q = 1 mod 2r, the global list
# DR holds (r, M_r), M_r the product of these q, and a row only computes sigma(p^(r-1)) modulo
# M_r and modulo S M_r. The script checks everything with a Python mirror of LPF3.drOK,
# LPF3.rowOK3 and LPF2.listOK, and writes the generated modules of the bound. The search is cut
# into subtrees of at most C nodes, packed into S modules, and joined in the final module.
# Used by: OddPerfect/LargestPrimeFactorThreeData.lean, LargestPrimeFactorThreeRows1.lean ..
# LargestPrimeFactorThreeRows<k>.lean, LargestPrimeFactorThreeSearch1.lean ..
# LargestPrimeFactorThreeSearch<S>.lean and LargestPrimeFactorThreeFinal.lean.
# Run:
#   python3 -I gen6.py B mirror [J]        certificates and the mirror check (J processes)
#   python3 -I gen6.py B lean OUT K S:C [J]  the same, then the modules in folder OUT, with K row
#                                            modules and S search modules of subtrees of at
#                                            most C nodes
# Requires: Python 3 standard library and gen5.py in the same folder.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: output files are written to the folder OUT given on the command line.
# License: GPL 3, same as the repository.
import sys, os, math, time
from math import gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen5
from gen5 import gs, parity_ok, factor, xpow, kill_ok, list_ok, lst, pairs
sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(0)

# ---------------------------------------------------------------- global data

def global_data(B, R):
    P = R.primes[1:]
    K = math.isqrt(B)
    Q = 2
    for q in P:
        if q <= K: Q *= q
    isp = set(P)
    DR = []; QS = {}
    for r in P:
        qs = [q for q in range(2 * r + 1, B + 1, 2 * r) if q in isp]
        if qs:
            m = 1
            for q in qs: m *= q
            DR.append((r, m)); QS[r] = qs
    return P, K, Q, DR, QS

# ---------------------------------------------------------------- mirror of the checks

def phi_mod(p, r, m):
    return (pow(p, r, (p - 1) * m) - 1) // (p - 1) if m else gs(p, r - 1)

def kill_s(p, r, Mr, S):
    if S == 0: return False
    x = phi_mod(p, r, S * Mr)
    return x % S == 0 and gcd(x // S, Mr) == 1 and r * S < 2 ** ((r - 1) * (p.bit_length() - 1))

def kill_g(p, r, Mr):
    S = gcd(phi_mod(p, r, Mr), Mr)
    if S == 1: return True
    return kill_s(p, r, Mr, S)

def look_s(r, EXS):
    for a, b in EXS:
        if a == r: return b
    return 0

def step_ok(p, X, EXS, x):
    r, Mr = x
    return kill_g(p, r, Mr) or r in X or kill_s(p, r, Mr, look_s(r, EXS))

def row_ok3(args):
    M, XU, DR, L, c = args
    p, row, X, EXS, EX = c
    if not all(step_ok(p, X, EXS, x) for x in DR): return False
    if XU % xpow(X) != 0: return False
    if not all(kill_ok(M, p, d, S) for d, S in EX): return False
    return all(not parity_ok(p, e) or e in row or xpow(X) % (e + 1) != 0
               or any((e + 1) % d == 0 for d, _ in EX) for e in L)

def prime_g(Q, K, n):
    if K < n: return gcd(Q % n, n) == 1
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))

def cprod_p(Q, K, r, k):
    m = 1
    for j in range(1, k + 1):
        c = 2 * j * r + 1
        if prime_g(Q, K, c): m *= c
    return m

def dr_ok(B, Q, K, P, DR):
    rest = list(DR)
    for r in P:
        cp = cprod_p(Q, K, r, (B - 1) // (2 * r))
        if rest and rest[0][0] == r:
            if cp != rest.pop(0)[1]: return False
        elif cp != 1: return False
    return not rest

# ---------------------------------------------------------------- certificates

def smooth_part(p, r, qs, S0):
    S = 1
    for q in qs:
        if S0 % q: continue
        k = 1
        while phi_mod(p, r, q ** (k + 1)) % q ** (k + 1) == 0: k += 1
        S *= q ** k
    return S

def make_cert3(B, R, DR, QS, p, row):
    E = (B - 3) // 2
    X = []; EXS = []
    for r, Mr in DR:
        if kill_g(p, r, Mr): continue
        S0 = gcd(phi_mod(p, r, Mr), Mr)
        S = smooth_part(p, r, QS[r], S0)
        if kill_s(p, r, Mr, S): EXS.append((r, S))
        else: X.append(r)
    Xs = set(X); EX = []
    for e in range(1, E + 1):
        if not parity_ok(p, e) or e in row: continue
        n = e + 1
        if not all(q == 2 or q in Xs for q in factor(n, R.spf)): continue
        if any(n % d == 0 for d, _ in EX): continue
        S, sm = R.smooth(p, e)
        assert not sm, (p, e)
        EX.append((n, S))
    return (p, row, X, EXS, EX)

def make_certs3(B, R, T, DR, QS):
    certs = [make_cert3(B, R, DR, QS, p, row) for p, row in T]
    XU = 2
    for x in sorted({x for c in certs for x in c[2]}): XU *= x
    XU = XU ** 20
    L = [e for e in range((B - 3) // 2, 0, -1) if XU % (e + 1) == 0]
    return certs, XU, L

def mirror3(B, P, M, K, Q, DR, XU, L, certs, jobs):
    okP = [q for q in range(B + 1) if q != 2 and prime_g(Q, K, q)] == P
    okD = dr_ok(B, Q, K, P, DR)
    okL = list_ok(XU, (B - 3) // 2, L)
    args = [(M, XU, DR, L, c) for c in certs]
    if jobs > 1:
        from multiprocessing import Pool
        with Pool(jobs) as pool: res = pool.map(row_ok3, args, chunksize=1)
    else:
        res = [row_ok3(a) for a in args]
    bad = [c[0] for c, r in zip(certs, res) if not r]
    return okP and okD and okL and not bad, (okP, okD, okL), bad

# ---------------------------------------------------------------- Lean text

def cert_lit(c):
    p, row, X, EXS, EX = c
    return f"({p}, {lst(row)}, {lst(X)}, {pairs(EXS)}, {pairs(EX)})"

def split_even(certs, parts):
    n = len(certs); out = []; s = 0
    for k in range(parts):
        e = s + (n - s) // (parts - k)
        out.append(certs[s:e]); s = e
    return out

# ---------------------------------------------------------------- the search, split

def search_tree(B, T, P, M, D):
    """Mirror of LPF.search that records each node as (kind, state, count, children, extra)."""
    rows = dict(T)
    def prod(l):
        r = 1
        for x in l: r *= x
        return r
    def term(ex, nd):
        if 2 * prod(q ** e for q, e in ex) < prod(gs(q, e) for q, e in ex): return True
        num = M * prod(gs(q, e) * (q - 1) for q, e in ex) * prod(q - 1 for q in nd)
        return num < 4 * D * prod(q ** e * q for q, e in ex) * prod(nd)
    def go(fuel, ex, dv, nd):
        st = (fuel, ex, dv, nd)
        assert fuel > 0
        if term(ex, nd): return ('stop', st, 1, [], None)
        if dv:
            p, rest = dv[0], dv[1:]
            if any(x == p for x, _ in ex):
                c = go(fuel - 1, ex, rest, nd)
                return ('old', st, 1 + c[2], [c], None)
            kids = []; es = []
            for e in rows[p]:
                g = gs(p, e)
                if not all(g % q for q in nd): continue
                es.append(e)
                if e % 2 == 1 and any(f % 2 == 1 for _, f in ex):
                    kids.append(None); continue
                new = [q for q in P if g % q == 0]
                kids.append(go(fuel - 1, [(p, e)] + ex, new + rest, nd))
            return ('cons', st, 1 + sum(k[2] for k in kids if k), kids, es)
        exs = {x for x, _ in ex}; nds = set(nd)
        q = [q for q in P if q not in exs and q not in nds][0]
        a = go(fuel - 1, ex, [q], nd); b = go(fuel - 1, ex, [], [q] + nd)
        return ('nil', st, 1 + a[2] + b[2], [a, b], q)
    return go(1000, [], [], [])

def cut_tree(node, cap):
    """Internal nodes (expanded in the final module) and leaves (checked whole), in order."""
    internal, leaves = [], []
    def walk(n):
        if n[2] <= cap or n[0] == 'stop':
            leaves.append(n); return
        internal.append(n)
        for k in n[3]:
            if k: walk(k)
    walk(node)
    return internal, leaves

def pack(leaves, k):
    bins = [[] for _ in range(k)]; load = [0] * k
    for n in sorted(leaves, key=lambda n: -n[2]):
        i = load.index(min(load)); bins[i].append(n); load[i] += n[2]
    return bins, load

CT = "ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)"
LIT = ("Much larger bounds are published (Hagis and Cohen `10 ^ 6`, Jenkins `10 ^ 7`, Goto and "
       "Ohno `10 ^ 8`);\nthey are not proved here.")

def lean_files(B, P, M, D, K, Q, DR, XU, L, certs, parts, width, tree, sparts):
    t = f"{B}"; E = (B - 3) // 2
    files = {}
    chunks = []; s = 0
    while s <= B:
        n = min(width, B + 1 - s); chunks.append((s, n)); s += n
    xs = sorted({x for c in certs for x in c[2]})
    xu_txt = "(" + " · ".join(str(x) for x in [2] + xs) + ") ^ 20"
    body = [f"""import OddPerfect.LargestPrimeFactorThree

/-!
# Data for the largest prime factor bound `{B}`

The list of the odd primes up to `{B}`, the products `M = 2 ∏ P` and `D = ∏ (q - 1)`, the
number `Q = 2 ∏ primesUpTo {K}`, the global list `DR` of the pairs `(r, M_r)`, the number
`XU = {xu_txt}` and the list `L` of the `e ≤ {E}` with `e + 1 ∣ XU`, for
`LPF3.exists_primeFactor_gt_of_cert3`. The data were computed outside Lean
(`scripts/LargestPrimeFactor/gen6.py`) and every fact used is checked here by the kernel.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

/-- The odd primes up to `{B}`. -/
def primes{t} : List ℕ := {lst(P)}

/-- `2` times the product of the odd primes up to `{B}`. -/
def bigM{t} : ℕ := {M}

/-- The product of `q - 1` over the odd primes `q` up to `{B}`. -/
def bigD{t} : ℕ := {D}

/-- `2` times the product of the odd primes up to `{K}`. -/
def bigQ{t} : ℕ := {Q}

/-- The pairs `(r, M_r)`: `r` an odd prime and `M_r ≠ 1` the product of the primes
`q ≤ {B}` with `q ≡ 1 (mod 2 r)`. -/
def listDR{t} : List (ℕ × ℕ) := {pairs(DR)}

/-- `{xu_txt}`, a multiple of `xpow X` for every list `X` of the certificates of the bound
`{B}`. -/
def bigXU{t} : ℕ := {XU}

/-- The `e` with `1 ≤ e ≤ {E}` and `e + 1 ∣ bigXU{t}`, in decreasing order. -/
def listL{t} : List ℕ := {lst(L)}

/-- The defining property of `bigM{t}`. -/
theorem bigM{t}_eq : 2 * primes{t}.prod = bigM{t} := by decide +kernel

/-- The defining property of `bigD{t}`. -/
theorem bigD{t}_eq : (primes{t}.map (· - 1)).prod = bigD{t} := by decide +kernel

/-- The defining property of `bigQ{t}`. -/
theorem bigQ{t}_eq : 2 * (LPF.primesUpTo {K}).prod = bigQ{t} := by decide +kernel

/-- `listL{t}` contains every `e ≤ {E}` with `e + 1 ∣ bigXU{t}`. -/
theorem listL{t}_ok : LPF2.listOK bigXU{t} (({B} - 3) / 2) listL{t} = true := by
  decide +kernel

/-- The global list `listDR{t}` passes `drOK`. -/
theorem listDR{t}_ok : drOK {B} bigQ{t} {K} primes{t} listDR{t} = true := by decide +kernel

private def oddPrimeTest (n : ℕ) : Bool := !Nat.beq n 2 && primeG bigQ{t} {K} n

private theorem split_filter (s m n : ℕ) : (List.range' s (m + n)).filter oddPrimeTest =
    (List.range' s m).filter oddPrimeTest ++ (List.range' (s + m) n).filter oddPrimeTest := by
  rw [← List.range'_append, List.filter_append, Nat.one_mul]
"""]
    for i, (s, n) in enumerate(chunks):
        lit = [q for q in P if s <= q < s + n]
        body.append(f"private theorem chunk{i} : (List.range' {s} {n}).filter oddPrimeTest =\n"
                    f"    {lst(lit)} := by\n  decide +kernel\n")
    haves = []; rws = []
    for i in range(len(chunks) - 1):
        s, n = chunks[i]; rest = B + 1 - s - n
        haves.append(f"  have h{i} : (List.range' {s} {n + rest}).filter oddPrimeTest =\n"
                     f"      (List.range' {s} {n}).filter oddPrimeTest ++\n"
                     f"        (List.range' {s + n} {rest}).filter oddPrimeTest :=\n"
                     f"    split_filter {s} {n} {rest}")
        rws.append(f"h{i}")
    rws += [f"chunk{i}" for i in range(len(chunks))]
    nl = "\n"
    body.append(f"""/-- The odd primes up to `{B}`, checked in chunks of `{width}` with `primeG`. -/
theorem primesUpTo{t}_eq : LPF.primesUpTo {B} = primes{t} := by
  have e : LPF.primesUpTo {B} = (List.range' 0 {B + 1}).filter oddPrimeTest := by
    rw [primesUpTo_eq_filterG (K := {K}) (by decide) (by decide) bigQ{t}_eq, List.range_eq_range']
    rfl
{nl.join(haves)}
  rw [e, {', '.join(rws)}]
  decide +kernel

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.bigM{t}_eq
#print axioms OddPerfect.LPF3.bigD{t}_eq
#print axioms OddPerfect.LPF3.bigQ{t}_eq
#print axioms OddPerfect.LPF3.listL{t}_ok
#print axioms OddPerfect.LPF3.listDR{t}_ok
#print axioms OddPerfect.LPF3.primesUpTo{t}_eq
""")
    files["LargestPrimeFactorThreeData.lean"] = "\n".join(body)
    groups = split_even(certs, parts)
    args = f"bigM{t} bigXU{t} listDR{t} listL{t}"
    for k, g in enumerate(groups, 1):
        out = [f"""import OddPerfect.LargestPrimeFactorThreeData

/-!
# Row certificates for the largest prime factor bound `{B}`, part {k} of {len(groups)}

Certificates `(p, R, X, EXS, EX)` of the rows of {len(g)} primes of the search table, found
outside Lean (`scripts/LargestPrimeFactor/gen6.py`) and checked here by the kernel with
`LPF3.rowOK3`, one prime at a time.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3
"""]
        for c in g:
            p = c[0]
            out.append(f"private def c{p} : {CT} :=\n  {cert_lit(c)}\n\n"
                       f"private theorem ok{p} : rowOK3 {args} c{p} = true := by decide +kernel\n")
        names = ", ".join(f"c{c[0]}" for c in g)
        oks = ", ".join(f"ok{c[0]}" for c in g)
        out.append(f"""/-- The row certificates of part {k} for the bound `{B}`. -/
def certs{t}_{k} : List ({CT}) :=
  [{names}]

/-- The row certificates of part {k} pass `rowOK3`. -/
theorem certs{t}_{k}_ok : certs{t}_{k}.all (rowOK3 {args}) = true := by
  simp only [certs{t}_{k}, List.all_cons, List.all_nil, {oks}, Bool.true_and]

end LPF3

end OddPerfect

#print axioms OddPerfect.LPF3.certs{t}_{k}_ok
""")
        files[f"LargestPrimeFactorThreeRows{k}.lean"] = "\n".join(out)
    Kp = len(groups)
    imports = "\n".join(f"import OddPerfect.LargestPrimeFactorThreeRows{k}" for k in range(1, Kp + 1))
    allc = " ++ ".join(f"certs{t}_{k}" for k in range(1, Kp + 1))
    allok = ", ".join(f"LPF3.certs{t}_{k}_ok" for k in range(1, Kp + 1))
    internal, leaves = tree
    bins, load = pack(leaves, sparts)
    lname = {}
    for k, bn in enumerate(bins, 1):
        for n in bn: lname[id(n)] = f"sub{t}_{len(lname) + 1}"
    def stmt(n, tbl):
        fuel, ex, dv, nd = n[1]
        return (f"LPF.search {B} primes{t} bigM{t} bigD{t}\n    ({tbl}.map fun c => (c.1, c.2.1)) "
                f"{fuel} {pairs(ex)} {lst(dv)} {lst(nd)} = true")
    for k, bn in enumerate(bins, 1):
        out = [f"""{imports}

/-!
# Part {k} of {len(bins)} of the search for the largest prime factor bound `{B}`

Subtrees of the search `LPF.search` for the bound `{B}`, each run whole by the kernel; the module
`LargestPrimeFactorThreeFinal` joins them with the steps above them. The cut was chosen outside
Lean (`scripts/LargestPrimeFactor/gen6.py`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3
"""]
        for n in bn:
            out.append(f"/-- A subtree of the search for the bound `{B}` ({n[2]} nodes). -/\n"
                       f"theorem {lname[id(n)]} : {stmt(n, '(' + allc + ')')} := by\n  decide +kernel\n")
        out.append("end LPF3\n\nend OddPerfect\n")
        out += [f"#print axioms OddPerfect.LPF3.{lname[id(n)]}" for n in bn]
        files[f"LargestPrimeFactorThreeSearch{k}.lean"] = "\n".join(out) + "\n"
    iname = {id(n): (f"search{t}" if i == 0 else f"node{t}_{i}") for i, n in enumerate(internal)}
    def ref(n): return iname.get(id(n)) or lname[id(n)]
    def cons_child(p, rest, n):
        lit = lst(n[1][2])
        return (f"Or.inr (by rw [show LPF.newPrimes primes{t} (LPF.gs {p} {n[1][1][0][1]}) ++ {lst(rest)} = "
                f"{lit} by decide +kernel]; exact {ref(n)})")
    thms = []
    for i, n in reversed(list(enumerate(internal))):
        kind, st, cnt, kids, extra = n
        if kind == 'nil':
            pf = f"search_nil (by decide +kernel) {ref(kids[0])} {ref(kids[1])}"
        elif kind == 'old':
            pf = f"search_cons_old (by decide +kernel) {ref(kids[0])}"
        else:
            p, rest = st[2][0], st[2][1:]
            alts = " | ".join("rfl" for _ in extra)
            cases = "\n".join(f"    · exact {cons_child(p, rest, c) if c else 'Or.inl (by decide +kernel)'}"
                              for c in kids)
            pf = (f"search_cons_all (es := {lst(extra)}) (by decide +kernel) (by decide +kernel)\n"
                  f"    fun e he => by\n"
                  f"    simp only [List.mem_cons, List.not_mem_nil, or_false] at he\n"
                  f"    rcases he with {alts}\n{cases}")
        if i == 0:
            thms.append(f"/-- The search for the bound `{B}` with the table of `certs{t}` succeeds. -/\n"
                        f"theorem search{t} : LPF.search {B} primes{t} bigM{t} bigD{t}\n"
                        f"    (certs{t}.map fun c => (c.1, c.2.1)) 1000 [] [] [] = true :=\n  {pf}\n")
        else:
            thms.append(f"private theorem {ref(n)} : {stmt(n, 'certs' + t)} :=\n  {pf}\n")
    simports = "\n".join(f"import OddPerfect.LargestPrimeFactorThreeSearch{k}" for k in range(1, len(bins) + 1))
    nl = "\n"
    files["LargestPrimeFactorThreeFinal.lean"] = f"""{simports}

/-!
# The largest prime factor of an odd perfect number exceeds `{B}`

The search `LPF.search` of `OddPerfect.LargestPrimeFactor` for the bound `{B}`, with the table
read off the certificates of the modules `LargestPrimeFactorThreeRows1` ..
`LargestPrimeFactorThreeRows{Kp}`, is assembled here from its top steps (`LPF3.search_nil`,
`LPF3.search_cons_old`, `LPF3.search_cons_all`) and the subtrees run by the kernel in the modules
`LargestPrimeFactorThreeSearch1` .. `LargestPrimeFactorThreeSearch{len(bins)}`.
`LPF3.exists_primeFactor_gt_of_cert3` turns the accepted search into the theorem. The search
table, the certificates and the cut were found outside Lean and are checked by the kernel.
{LIT}
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

namespace OddPerfect

namespace LPF3

/-- All row certificates for the bound `{B}`. -/
def certs{t} : List ({CT}) := {allc}

{nl.join(thms)}
end LPF3

/-- The largest prime factor of an odd perfect number exceeds `{B}`. The search table and its
row certificates were found outside Lean and are checked by the kernel. {LIT} -/
theorem exists_primeFactor_gt_{t} {{N : ℕ}} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, {B} < p :=
  LPF3.exists_primeFactor_gt_of_cert3 LPF3.primesUpTo{t}_eq LPF3.bigM{t}_eq LPF3.bigD{t}_eq
    (by decide) (K := {K}) (by decide) (by decide) LPF3.bigQ{t}_eq LPF3.listDR{t}_ok rfl
    LPF3.listL{t}_ok
    (by simp only [LPF3.certs{t}, List.all_append, {allok}, Bool.and_true]) LPF3.search{t} h

end OddPerfect

#print axioms OddPerfect.LPF3.search{t}
#print axioms OddPerfect.exists_primeFactor_gt_{t}
"""
    sys.stderr.write(f"search: {len(internal)} internal nodes, {len(leaves)} leaves, module loads {load}\n")
    return files

# ---------------------------------------------------------------- main

if __name__ == '__main__':
    B = int(sys.argv[1]); mode = sys.argv[2]
    t0 = time.process_time()
    R = gen5.Rows(B)
    ok, nodes, T, P, M, D = gen5.run_search(B, R)
    sys.stderr.write(f"B={B} ok={ok} nodes={nodes} rows={len(T)} "
                     f"rowentries={sum(len(r) for _, r in T)} cpu={time.process_time() - t0:.1f}\n")
    if not ok: sys.exit("search failed")
    P2, K, Q, DR, QS = global_data(B, R)
    assert P2 == P
    certs, XU, L = make_certs3(B, R, T, DR, QS)
    sys.stderr.write(f"DR entries {len(DR)}, K = {K}, X union {sorted({x for c in certs for x in c[2]})}, "
                     f"|L| = {len(L)}, exceptions {sum(len(c[3]) for c in certs)}, "
                     f"extra {sum(len(c[4]) for c in certs)}, cpu={time.process_time() - t0:.1f}\n")
    jobs_at = 3 if mode == 'mirror' else 7
    jobs = int(sys.argv[jobs_at]) if len(sys.argv) > jobs_at and sys.argv[jobs_at].isdigit() else 1
    if '--nomirror' not in sys.argv:
        allok, parts, bad = mirror3(B, P, M, K, Q, DR, XU, L, certs, jobs)
        sys.stderr.write(f"mirror: primes, drOK, listOK {parts}, failing rows {bad}\n")
        if not allok: sys.exit("mirror check failed")
    if mode == 'lean':
        out = sys.argv[3]; parts = int(sys.argv[4]); sparts, cap = map(int, sys.argv[5].split(':'))
        tree = cut_tree(search_tree(B, T, P, M, D), cap)
        for name, text in lean_files(B, P, M, D, K, Q, DR, XU, L, certs, parts, 20000, tree,
                                     sparts).items():
            with open(os.path.join(out, name), "w") as fh: fh.write(text)
        sys.stderr.write(f"wrote the modules to {out}\n")
