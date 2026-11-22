# Untrusted helper script for the OddPerfect Lean library.
# Successor of gen4.py. It runs the same search (a mirror of LPF.search in
# OddPerfect/LargestPrimeFactor.lean), but computes the rows LPF.row from multiplicative orders
# and lifting the exponent instead of gcds of large numbers, so B = 10000 takes about a second
# instead of 3.5 minutes. For the checker LPF2.exists_primeFactor_gt_of_cert of
# OddPerfect/LargestPrimeFactorTwo.lean it also writes the row certificates (p, R, X, SP, EX),
# the number XU and the list L, checks them with a Python mirror of LPF2.rowOK and LPF2.listOK,
# and writes the generated modules of the bound.
# Used by: OddPerfect/LargestPrimeFactorTwoData.lean, LargestPrimeFactorTwoRows1.lean ..
# LargestPrimeFactorTwoRows<k>.lean and LargestPrimeFactorTwoFinal.lean (B = 100000).
# Run:
#   python3 -I gen5.py B search        counts of the search only
#   python3 -I gen5.py B thm           the theorem text of gen4.py (same output as gen4.py)
#   python3 -I gen5.py B mirror [J]    certificates and the mirror check (J processes)
#   python3 -I gen5.py B lean OUT [J]  certificates, mirror check, and the modules in folder OUT
# Requires: Python 3 standard library. Running time for B = 100000: search about 20 seconds,
# certificates about 15 seconds, mirror check tens of CPU minutes (split over J processes).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: output files are written to the folder OUT given on the command line.
# The theorem text (mode thm) checks the row table T in chunks of RK rows, one kernel check
# per chunk (private theorems rows1, rows2, ...), which keeps the peak memory of the check low.
# License: GPL 3, same as the repository.
import sys, os, math, time
from math import gcd
sys.setrecursionlimit(100000)
sys.set_int_max_str_digits(0)

# ---------------------------------------------------------------- arithmetic helpers

def sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n ** .5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j: spf[j] = i
    return spf

def factor(n, spf):
    f = {}
    while n > 1:
        q = spf[n]; f[q] = f.get(q, 0) + 1; n //= q
    return f

def vq(n, q):
    v = 0
    while n % q == 0: n //= q; v += 1
    return v

def gs(p, e): return (p ** (e + 1) - 1) // (p - 1)

def parity_ok(p, e): return e % 2 == 0 or (p % 4 == 1 and e % 4 == 1)

class Rows:
    """Prime factorizations of gs(p, e) over the primes up to B, from orders."""
    def __init__(self, B):
        self.B = B
        self.spf = sieve(max(B, 10) + 2)
        self.primes = [q for q in range(2, B + 1) if self.spf[q] == q]
        self.cache = {}

    def order(self, p, q):
        k = q - 1
        for r in factor(q - 1, self.spf):
            while k % r == 0 and pow(p, k // r, q) == 1: k //= r
        return k

    def data(self, p):
        # groups[k]: (q, v_q(p^k - 1)) for odd primes q <= B, q != p, ord_q(p) = k > 1;
        # one: odd primes q <= B dividing p - 1.
        if p in self.cache: return self.cache[p]
        groups = {}; one = []
        for q in self.primes:
            if q == 2 or q == p: continue
            if (p - 1) % q == 0: one.append(q); continue
            k = self.order(p, q)
            v = 1; m = q * q
            while pow(p, k, m) == 1: v += 1; m *= q
            groups.setdefault(k, []).append((q, v))
        self.cache = {p: (groups, one)}
        return groups, one

    def divisors(self, n):
        ds = [1]
        for r, a in factor(n, self.spf).items():
            ds = [d * r ** i for d in ds for i in range(a + 1)]
        return ds

    def vals(self, p, e):
        """dict q -> v_q(gs(p, e)) > 0 over the primes q <= B."""
        groups, one = self.data(p)
        n = e + 1; out = {}
        if n % 2 == 0: out[2] = vq(p + 1, 2) + vq(n, 2) - 1
        for q in one:
            if n % q == 0: out[q] = vq(n, q)
        for d in self.divisors(n):
            if d > 1 and d in groups:
                for q, v in groups[d]: out[q] = v + vq(n // d, q)
        return out

    def smooth(self, p, e):
        """(S, smooth): S the B-smooth part of gs(p, e), smooth iff S = gs(p, e)."""
        vs = self.vals(p, e); S = 1
        for q, v in vs.items(): S *= q ** v
        ls = sum(v * math.log(q) for q, v in vs.items())
        lg = (e + 1) * math.log(p) - math.log(p - 1)
        if lg - ls > 1.0: return S, False
        return S, S == gs(p, e)

    def row(self, p):
        """LPF.row B M p: bigF M m is false iff m is B-smooth or a prime exponent exceeds 100."""
        r = []
        for e in range(1, (self.B - 3) // 2 + 1):
            if not parity_ok(p, e): continue
            vs = self.vals(p, e)
            if vs and max(vs.values()) > 100: r.append(e); continue
            if self.smooth(p, e)[1]: r.append(e)
        return r

# ---------------------------------------------------------------- the search (LPF.search)

def run_search(B, R):
    P = R.primes[1:]
    M = 2
    for p in P: M *= p
    D = 1
    for p in P: D *= p - 1
    rowc = {}; cnt = [0]
    def row(p):
        if p not in rowc: rowc[p] = R.row(p)
        return rowc[p]
    def prod(l):
        r = 1
        for x in l: r *= x
        return r
    def lower(ex):
        return 2 * prod(q ** e for q, e in ex) < prod(gs(q, e) for q, e in ex)
    def upper(ex, nd):
        num = M * prod(gs(q, e) * (q - 1) for q, e in ex) * prod(q - 1 for q in nd)
        den = 4 * D * prod(q ** e * q for q, e in ex) * prod(nd)
        return num < den
    def search(fuel, ex, dv, nd):
        cnt[0] += 1
        if fuel == 0: return False
        if lower(ex) or upper(ex, nd): return True
        if dv:
            p, rest = dv[0], dv[1:]
            if any(x == p for x, _ in ex): return search(fuel - 1, ex, rest, nd)
            for e in row(p):
                g = gs(p, e)
                if not all(g % q for q in nd): continue
                if e % 2 == 1 and any(f % 2 == 1 for _, f in ex): continue
                new = [q for q in P if g % q == 0]
                if not search(fuel - 1, [(p, e)] + ex, new + rest, nd): return False
            return True
        exs = {x for x, _ in ex}; nds = set(nd)
        und = [q for q in P if q not in exs and q not in nds]
        if not und: return False
        q = und[0]
        return search(fuel - 1, ex, [q], nd) and search(fuel - 1, ex, [], [q] + nd)
    ok = search(1000, [], [], [])
    return ok, cnt[0], [(p, rowc[p]) for p in rowc], P, M, D

# ---------------------------------------------------------------- row certificates

def xpow(X):
    r = 2
    for x in X: r *= x
    return r ** 20

def make_cert(B, R, p, row):
    E = (B - 3) // 2
    X = []; SP = []
    for r in R.primes[1:]:
        if r > E + 1: break
        S, sm = R.smooth(p, r - 1)
        if sm: X.append(r)
        elif S != 1: SP.append((r, S))
    Xs = set(X); EX = []
    for e in range(1, E + 1):
        if not parity_ok(p, e) or e in row: continue
        n = e + 1
        if not all(q == 2 or q in Xs for q in factor(n, R.spf)): continue
        if any(n % d == 0 for d, _ in EX): continue
        S, sm = R.smooth(p, e)
        assert not sm, (p, e)
        EX.append((n, S))
    return (p, row, X, SP, EX)

def make_certs(B, R, T):
    certs = [make_cert(B, R, p, row) for p, row in T]
    XU = 2
    for x in sorted({x for c in certs for x in c[2]}): XU *= x
    XU = XU ** 20
    L = [e for e in range((B - 3) // 2, 0, -1) if XU % (e + 1) == 0]
    return certs, XU, L

# ---------------------------------------------------------------- mirror of LPF2.rowOK

def kill_p(B, p, r, S):
    m = gs(p, r - 1)
    if m % S != 0: return False
    u = m // S
    if not (1 < u) or u % r == 0: return False
    return all(u % (2 * k * r + 1) != 0 for k in range(1, (B - 1) // (2 * r) + 1))

def kill_ok(M, p, d, S):
    m = gs(p, d - 1)
    return m % S == 0 and 1 < m // S and gcd(m // S, M) == 1

def row_ok(args):
    B, P, M, XU, L, c = args
    p, row, X, SP, EX = c
    cut = (B - 3) // 2 + 1; sp = list(SP)
    for r in P:
        if cut < r or r in X: continue
        if sp and sp[0][0] == r: S = sp.pop(0)[1]
        else: S = 1
        if not kill_p(B, p, r, S): return False
    if XU % xpow(X) != 0: return False
    if not all(kill_ok(M, p, d, S) for d, S in EX): return False
    return all(not parity_ok(p, e) or e in row or xpow(X) % (e + 1) != 0
               or any((e + 1) % d == 0 for d, _ in EX) for e in L)

def list_ok(XU, f, L):
    rest = list(L)
    for e in range(f, 0, -1):
        if rest and rest[0] == e: rest.pop(0); continue
        if XU % (e + 1) == 0: return False
    return True

def mirror(B, P, M, XU, L, certs, jobs):
    ok = list_ok(XU, (B - 3) // 2, L)
    args = [(B, P, M, XU, L, c) for c in certs]
    if jobs > 1:
        from multiprocessing import Pool
        with Pool(jobs) as pool: res = pool.map(row_ok, args, chunksize=1)
    else:
        res = [row_ok(a) for a in args]
    bad = [c[0] for c, r in zip(certs, res) if not r]
    return ok and not bad, ok, bad

# ---------------------------------------------------------------- Lean text

def lst(l): return "[" + ", ".join(str(x) for x in l) + "]"
def pairs(l): return "[" + ", ".join(f"({a}, {b})" for a, b in l) + "]"
def cert_lit(c):
    p, row, X, SP, EX = c
    return f"({p}, {lst(row)}, {lst(X)}, {pairs(SP)}, {pairs(EX)})"

def cost(p): return 8 + 0.8 * math.log(p)

def split_rows(certs, parts):
    total = sum(cost(c[0]) for c in certs); groups = [[]]; acc = 0.0
    for c in certs:
        if acc >= total * len(groups) / parts and len(groups) < parts: groups.append([])
        groups[-1].append(c); acc += cost(c[0])
    return groups

CT = "ℕ × List ℕ × List ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)"

def lean_files(B, P, M, D, XU, L, certs, parts, width):
    tag = f"{B}"
    KQ = math.isqrt(B)
    assert B < (KQ + 1) ** 2
    xu_txt = "(" + " · ".join(str(x) for x in [2] + sorted({x for c in certs for x in c[2]})) + ") ^ 20"
    files = {}
    # data module
    chunks = []; s = 0
    while s <= B:
        n = min(width, B + 1 - s); chunks.append((s, n)); s += n
    body = []
    body.append(f"""import OddPerfect.LargestPrimeFactorTwo

/-!
# Data for the largest prime factor bound `{B}`

The list of the odd primes up to `{B}`, the products `M = 2 ∏ P` and `D = ∏ (q - 1)`, the
number `XU = {xu_txt}` and the list `L` of the `e ≤ {(B - 3) // 2}` with
`e + 1 ∣ XU`, for `LPF2.exists_primeFactor_gt_of_cert`. The data were computed outside Lean
(`scripts/LargestPrimeFactor/gen5.py`) and every fact used is checked here by the kernel.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace OddPerfect

namespace LPF2

/-- The odd primes up to `{B}`. -/
def primes{tag} : List ℕ := {lst(P)}

/-- `2` times the product of the odd primes up to `{B}`. -/
def bigM{tag} : ℕ := {M}

/-- The product of `q - 1` over the odd primes `q` up to `{B}`. -/
def bigD{tag} : ℕ := {D}

/-- `{xu_txt}`, a multiple of `xpow X` for every list `X` of the
certificates of the bound `{B}`. -/
def bigXU{tag} : ℕ := {XU}

/-- The `e` with `1 ≤ e ≤ {(B - 3) // 2}` and `e + 1 ∣ bigXU{tag}`, in decreasing order. -/
def listL{tag} : List ℕ := {lst(L)}

/-- The defining property of `bigM{tag}`. -/
theorem bigM{tag}_eq : 2 * primes{tag}.prod = bigM{tag} := by decide +kernel

/-- The defining property of `bigD{tag}`. -/
theorem bigD{tag}_eq : (primes{tag}.map (· - 1)).prod = bigD{tag} := by decide +kernel

/-- `listL{tag}` contains every `e ≤ {(B - 3) // 2}` with `e + 1 ∣ bigXU{tag}`. -/
theorem listL{tag}_ok : listOK bigXU{tag} (({B} - 3) / 2) listL{tag} = true := by decide +kernel

private def oddPrimeTest (n : ℕ) : Bool := !Nat.beq n 2 && primeBy (2 :: LPF.primesUpTo {KQ}) n

private theorem split_filter (s m n : ℕ) : (List.range' s (m + n)).filter oddPrimeTest =
    (List.range' s m).filter oddPrimeTest ++ (List.range' (s + m) n).filter oddPrimeTest := by
  rw [← List.range'_append, List.filter_append, Nat.one_mul]
""")
    for i, (s, n) in enumerate(chunks):
        lit = [q for q in P if s <= q < s + n]
        body.append(f"private theorem chunk{i} : (List.range' {s} {n}).filter oddPrimeTest =\n"
                    f"    {lst(lit)} := by\n  decide +kernel\n")
    haves = []; rewrites = []
    for i in range(len(chunks) - 1):
        s, n = chunks[i]; rest = B + 1 - s - n
        haves.append(f"  have h{i} : (List.range' {s} {n + rest}).filter oddPrimeTest =\n"
                     f"      (List.range' {s} {n}).filter oddPrimeTest ++\n"
                     f"        (List.range' {s + n} {rest}).filter oddPrimeTest :=\n"
                     f"    split_filter {s} {n} {rest}")
        rewrites.append(f"h{i}")
    rewrites += [f"chunk{i}" for i in range(len(chunks))]
    body.append(f"""/-- The odd primes up to `{B}`, checked in chunks of `{width}` by trial division by `2` and the
odd primes up to `{KQ}`. -/
theorem primesUpTo{tag}_eq : LPF.primesUpTo {B} = primes{tag} := by
  have e : LPF.primesUpTo {B} = (List.range' 0 {B + 1}).filter oddPrimeTest := by
    rw [primesUpTo_eq_filter (K := {KQ}) (by decide), List.range_eq_range']
    rfl
{chr(10).join(haves)}
  rw [e, {', '.join(rewrites)}]
  decide +kernel

end LPF2

end OddPerfect

#print axioms OddPerfect.LPF2.bigM{tag}_eq
#print axioms OddPerfect.LPF2.bigD{tag}_eq
#print axioms OddPerfect.LPF2.listL{tag}_ok
#print axioms OddPerfect.LPF2.primesUpTo{tag}_eq
""")
    files["LargestPrimeFactorTwoData.lean"] = "\n".join(body)
    groups = split_rows(certs, parts)
    args = f"{B} bigM{tag} bigXU{tag} primes{tag} listL{tag}"
    for k, g in enumerate(groups, 1):
        out = [f"""import OddPerfect.LargestPrimeFactorTwoData

/-!
# Row certificates for the largest prime factor bound `{B}`, part {k} of {len(groups)}

Certificates `(p, R, X, SP, EX)` of the rows of {len(g)} primes of the search table, found
outside Lean (`scripts/LargestPrimeFactor/gen5.py`) and checked here by the kernel with
`LPF2.rowOK`, one prime at a time.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace OddPerfect

namespace LPF2
"""]
        for c in g:
            p = c[0]
            out.append(f"private def c{p} : {CT} :=\n  {cert_lit(c)}\n\n"
                       f"private theorem ok{p} : rowOK {args} c{p} = true := by decide +kernel\n")
        names = ", ".join(f"c{c[0]}" for c in g)
        oks = ", ".join(f"ok{c[0]}" for c in g)
        out.append(f"""/-- The row certificates of part {k} for the bound `{B}`. -/
def certs{tag}_{k} : List ({CT}) :=
  [{names}]

/-- The row certificates of part {k} pass `rowOK`. -/
theorem certs{tag}_{k}_ok : certs{tag}_{k}.all (rowOK {args}) = true := by
  simp only [certs{tag}_{k}, List.all_cons, List.all_nil, {oks}, Bool.true_and]

end LPF2

end OddPerfect

#print axioms OddPerfect.LPF2.certs{tag}_{k}_ok
""")
        files[f"LargestPrimeFactorTwoRows{k}.lean"] = "\n".join(out)
    K = len(groups)
    imports = "\n".join(f"import OddPerfect.LargestPrimeFactorTwoRows{k}" for k in range(1, K + 1))
    allc = " ++ ".join(f"certs{tag}_{k}" for k in range(1, K + 1))
    allok = ", ".join(f"certs{tag}_{k}_ok" for k in range(1, K + 1))
    files["LargestPrimeFactorTwoFinal.lean"] = f"""{imports}

/-!
# The largest prime factor of an odd perfect number exceeds `{B}`

The search `LPF.search` of `OddPerfect.LargestPrimeFactor` is run by the kernel for the bound
`{B}` with the table read off the certificates of the modules
`LargestPrimeFactorTwoRows1` .. `LargestPrimeFactorTwoRows{K}`, and
`LPF2.exists_primeFactor_gt_of_cert` turns the accepted search into the theorem. Much larger
bounds are published (Hagis and Cohen `10 ^ 6`, Jenkins `10 ^ 7`, Goto and Ohno `10 ^ 8`);
they are not proved here.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace OddPerfect

namespace LPF2

/-- All row certificates for the bound `{B}`. -/
def certs{tag} : List ({CT}) := {allc}

/-- The search for the bound `{B}` with the table of `certs{tag}` succeeds. -/
theorem search{tag} : LPF.search {B} primes{tag} bigM{tag} bigD{tag}
    (certs{tag}.map fun c => (c.1, c.2.1)) 1000 [] [] [] = true := by decide +kernel

end LPF2

/-- The largest prime factor of an odd perfect number exceeds `{B}`. The search table and its
row certificates were found outside Lean and are checked by the kernel. Much larger bounds
are published (Goto and Ohno: `10 ^ 8`); they are not proved here. -/
theorem exists_primeFactor_gt_{tag} {{N : ℕ}} (h : OddPerfect N) :
    ∃ p ∈ N.primeFactors, {B} < p :=
  LPF2.exists_primeFactor_gt_of_cert LPF2.primesUpTo{tag}_eq LPF2.bigM{tag}_eq LPF2.bigD{tag}_eq
    (by decide) rfl LPF2.listL{tag}_ok
    (by simp only [LPF2.certs{tag}, List.all_append, {', '.join('LPF2.' + n for n in allok.split(', '))},
      Bool.and_true]) LPF2.search{tag} h

end OddPerfect

#print axioms OddPerfect.LPF2.search{tag}
#print axioms OddPerfect.exists_primeFactor_gt_{tag}
"""
    return files

def thm_text(B, P, M, D, T, RK=8):
    Ts = "[" + ", ".join(f"({p}, {r})" for p, r in T) + "]"
    ch = [T[i:i + RK] for i in range(0, len(T), RK)]
    lit = lambda c: "[" + ", ".join(f"({p}, {r})" for p, r in c) + "]"
    out = [f"""/-- The number `M = 2 ∏ P` of `exists_primeFactor_gt`, named so that the row checks below
do not repeat it. -/
private def bigM : ℕ := {M}
"""]
    for k, c in enumerate(ch, 1):
        out.append(f"""set_option maxHeartbeats 0 in
/-- Rows {RK * (k - 1) + 1} to {RK * (k - 1) + len(c)} of the row table of `exists_primeFactor_gt`. -/
private theorem rows{k} : ({lit(c)} : List (ℕ × List ℕ)).all
    (fun x => x.2 == LPF.row {B} bigM x.1) = true := by decide +kernel
""")
    app = " ++ (\n      ".join(lit(c) for c in ch) + ")" * (len(ch) - 1)
    names = ", ".join(f"rows{k}" for k in range(1, len(ch) + 1))
    out.append(f"""set_option maxRecDepth 10000 in
/-- The row table of `exists_primeFactor_gt`, checked in chunks of {RK} rows (one kernel check
each, which keeps the peak memory of the check low). -/
private theorem rows : ({Ts} : List (ℕ × List ℕ)).all
    (fun x => x.2 == LPF.row {B} bigM x.1) = true := by
  rw [show ({Ts} : List (ℕ × List ℕ)) =
      {app} from rfl]
  simp only [List.all_append, {names}, Bool.and_self]

set_option maxHeartbeats 0 in
/-- The largest prime factor of an odd perfect number exceeds `{B}`. -/
theorem exists_primeFactor_gt {{N : ℕ}} (h : OddPerfect N) : ∃ p ∈ N.primeFactors, {B} < p :=
  LPF.exists_primeFactor_gt_of_search (P := {P})
    (M := {M})
    (D := {D})
    (T := {Ts})
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rows
    (by decide +kernel) h""")
    return "\n".join(out)

# ---------------------------------------------------------------- main

if __name__ == '__main__':
    B = int(sys.argv[1]); mode = sys.argv[2]
    t0 = time.process_time()
    R = Rows(B)
    ok, nodes, T, P, M, D = run_search(B, R)
    sys.stderr.write(f"B={B} ok={ok} nodes={nodes} rows={len(T)} "
                     f"rowentries={sum(len(r) for _, r in T)} cpu={time.process_time() - t0:.1f}\n")
    if mode == 'thm':
        print(thm_text(B, P, M, D, T))
    elif mode in ('mirror', 'lean'):
        if not ok: sys.exit("search failed")
        certs, XU, L = make_certs(B, R, T)
        sys.stderr.write(f"certificates: X union {sorted({x for c in certs for x in c[2]})}, "
                         f"|L| = {len(L)}, sparse {sum(len(c[3]) for c in certs)}, "
                         f"extra {sum(len(c[4]) for c in certs)}, "
                         f"cpu={time.process_time() - t0:.1f}\n")
        jobs = int(sys.argv[4 if mode == 'lean' else 3]) if len(sys.argv) > (4 if mode == 'lean' else 3) else 1
        if '--nomirror' not in sys.argv:
            allok, lok, bad = mirror(B, P, M, XU, L, certs, jobs)
            sys.stderr.write(f"mirror: listOK {lok}, failing rows {bad}\n")
            if not allok: sys.exit("mirror check failed")
        if mode == 'lean':
            out = sys.argv[3]
            for name, text in lean_files(B, P, M, D, XU, L, certs, 9, 10000).items():
                with open(os.path.join(out, name), "w") as fh: fh.write(text)
            sys.stderr.write(f"wrote the modules to {out}\n")
