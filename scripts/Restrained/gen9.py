# Untrusted helper script for the OddPerfect Lean library.
# Writes OddPerfect/RestrainedNineData.lean: for every prime 3 <= d < P0 a branch closing the
# source sigma(3^(d-1)) = (3^d - 1)/2 for the checker `chk mask2 0` of
# OddPerfect/RestrainedSevenCheck.lean, and the coverage check of the primes below P0.
# Run: python3 -I gen9.py OUTDIR   (writes OUTDIR/RestrainedNineData.lean, a few minutes)
# Requires: Python 3 and sympy (checked with sympy 1.14.0). Deterministic: the witness primes
# are fixed in the table WIT below (found by exploratory factoring, not published); every tree is found by the same
# bounded deterministic search as scripts/Restrained/gen7.py (fixed seeds, step bounds).
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import sys, os, math
from sympy import primerange
from functools import lru_cache
from sympy import factorint, isprime
from sympy.ntheory import pollard_rho, ecm

B = 132257
BIG = 10 ** 6
SMALL = 200
RHO = 20000
ECM = 30


@lru_cache(maxsize=None)
def bfactor(n):
    """Bounded deterministic factoring (as in scripts/Restrained/gen7.py)."""
    f = factorint(n, limit=10 ** 6, use_rho=False, use_pm1=False, use_ecm=False)
    ps, stack, full = set(), [int(x) for x in f], True
    while stack:
        c = stack.pop()
        if c < 10 ** 12 or isprime(c):
            ps.add(c)
            continue
        d = pollard_rho(c, retries=2, max_steps=RHO, seed=1234)
        if d is not None:
            stack += [int(d), c // int(d)]
            continue
        try:
            fs = sorted(int(x) for x in ecm(c, B1=10000, B2=1000000, max_curve=ECM, seed=1234))
        except ValueError:
            fs = []
        if len(fs) > 1 or (fs and fs[0] != c):
            stack += fs
            m = c
            for x in fs:
                while m % x == 0:
                    m //= x
            if m > 1:
                stack.append(m)
        else:
            full = False
    return sorted(ps), full


@lru_cache(maxsize=None)
def pratt(p):
    """A Pratt certificate for p (dependency order), or None when bounded factoring fails."""
    out, done = [], set()

    def go(n):
        if n < SMALL or n in done:
            return
        fl, full = bfactor(n - 1)
        if not full:
            raise ValueError
        f = {}
        for x in fl:
            m, e = n - 1, 0
            while m % x == 0:
                m //= x
                e += 1
            f[x] = e
        for x in sorted(f):
            go(x)
        a = 2
        while not (pow(a, n - 1, n) == 1 and all(pow(a, (n - 1) // x, n) != 1 for x in f)):
            a += 1
        done.add(n)
        out.append((n, a, sorted(x for x, e in f.items() for _ in range(e))))

    try:
        go(p)
    except ValueError:
        return None
    return out


def usable(t):
    return t not in (2, 3) and isprime(t) and (t < BIG or pratt(t) is not None)


def odd_primes(n):
    return tuple(sorted(t for t in bfactor(n)[0] if usable(t)))


def closed(t, extra):
    return 5 <= t < B and isprime(t)


def size(b):
    if b[0] == "k":
        return 1
    return 1 + (size(b[2]) if b[2] is not None else 0) + size(b[3])


def branch(src, qv, depth, memo, extra):
    kills = [t for t in bfactor(src)[0] if closed(t, extra)]
    if kills:
        return ("k", kills[0])
    if depth == 0:
        return None
    ps = odd_primes(src)
    best = None
    for t in ps:
        if t == qv:
            continue
        tr = tree(t, qv, depth - 1, memo, extra)
        if tr is not None:
            cand = ("n", t, tr[0], tr[1])
            if best is None or size(cand) < size(best):
                best = cand
    return best


def tree(d, qv, depth, memo, extra):
    key = (d, qv, depth)
    if key in memo:
        return memo[key]
    memo[key] = None
    qb, res = None, None
    if qv == 0 and d % 12 == 1:
        qb = branch(d + 1, d, depth, memo, extra)
        if qb is None:
            return None
    ob = branch(d * d + d + 1, qv, depth, memo, extra)
    if ob is not None:
        res = (qb, ob)
    memo[key] = res
    return res



DEPTH = 4
# d -> the prime factor s of (3^d - 1)/2 whose branch is used (from explore.py).
WIT = {3: 13, 5: 11, 7: 1093, 11: 23, 13: 797161, 17: 1871, 19: 1597, 23: 47, 29: 59, 31: 683,
       37: 13097927, 41: 83, 43: 431, 47: 1223, 53: 107, 59: 14425532687, 61: 603901, 67: 221101,
       71: 3754733257489862401973357979128773, 73: 11243, 79: 392038110671, 83: 167, 89: 179,
       97: 76631, 101: 50316775668019759306202964023,
       103: 6957596529882152968992225251835887181478451547013, 107: 50077, 109: 1091, 113: 227,
       127: 5843, 131: 263, 137: 4933, 139: 1669, 149: 7451, 151: 1511, 157: 9421,
       163: 5227348213873, 167: 58451, 173: 347, 179: 359, 181: 90863, 191: 383, 193: 6563,
       197: 9851}


def lcert(t):
    if t < BIG:
        return "[]"
    return "[%s]" % ", ".join("(%d, %d, [%s])" % (n, a, ", ".join(map(str, fs)))
                              for n, a, fs in pratt(t))


def lean(b):
    if b is None:
        return ".skip"
    if b[0] == "k":
        return "(.kill %d)" % b[1]
    return "(.node %d %s %s %s)" % (b[1], lcert(b[1]), lean(b[2]), lean(b[3]))


def wrap(s, ind):
    """Split a long literal at spaces into lines of at most 100 characters."""
    out, cur = [], ind
    for w in s.split(" "):
        if len(cur) + len(w) + 1 > 100 and cur.strip():
            out.append(cur.rstrip())
            cur = ind + "  "
        cur += w + " "
    out.append(cur.rstrip())
    return "\n".join(out)


def main():
    outdir = sys.argv[1]
    ds = sorted(WIT)
    P0 = next(p for p in primerange(3, 10 ** 6) if p not in WIT)
    assert ds == list(primerange(3, P0))
    rows = []
    for d in ds:
        s = WIT[d]
        assert isprime(s) and ((3 ** d - 1) // 2) % s == 0
        if 5 <= s < B:
            br = ("k", s)
        else:
            res = None
            for dep in range(0, DEPTH):
                res = tree(s, 0, dep, {}, None)
                if res is not None:
                    break
            assert res is not None, d
            assert usable(s)
            br = ("n", s, res[0], res[1])
        rows.append((d, br))
    BLK = 16
    blocks = [rows[i:i + BLK] for i in range(0, len(rows), BLK)]
    D = list(primerange(2, math.isqrt(P0) + 1))
    o = ["import OddPerfect.RestrainedSevenData2", "", "/-!",
         "# Restrained odd perfect numbers: branches for `σ(3 ^ (d - 1))`", "",
         "Generated by `python3 -I scripts/gen9.py` (deterministic). For every prime `3 ≤ d < %d`" % P0,
         "the list `dRows` holds a branch `b` with `chk mask2 0 ((3 ^ d - 1) / 2) b = true`, checked",
         "by the kernel in blocks; `dCover_ok` checks that every prime `3 ≤ p < %d` is in `dList`." % P0,
         "-/", "", "namespace OddPerfect", "", "namespace RestrainedNine", "",
         "open RestrainedSeven", "",
         "/-- Every `m` with `lo ≤ m < lo + n` is in `L` or has a divisor `d ∈ D` with",
         "`2 ≤ d < m`. -/",
         "def dCover (L D : List ℕ) (lo n : ℕ) : Bool :=",
         "  (List.range' lo n).all fun m =>",
         "    L.contains m || D.any (fun d => decide (2 ≤ d) && decide (d < m) && m % d == 0)", ""]
    for i, blk in enumerate(blocks):
        o += ["/-- Branches for `(3 ^ d - 1) / 2`, block %d (`d` from %d to %d). -/"
              % (i, blk[0][0], blk[-1][0]),
              "def dRows_%d : List (ℕ × Br) := [" % i,
              ",\n".join(wrap("(%d, %s)" % (d, lean(b)), "  ") for d, b in blk), "]", "",
              "/-- Block %d is accepted. -/" % i,
              "theorem dRows_%d_ok :" % i,
              "    dRows_%d.all (fun r => chk mask2 0 ((3 ^ r.1 - 1) / 2) r.2) = true := by" % i,
              "  decide +kernel", ""]
    nb = len(blocks)
    o += ["/-- The branches for every prime `3 ≤ d < %d`. -/" % P0,
          "def dRows : List (ℕ × Br) := " + " ++ ".join("dRows_%d" % i for i in range(nb)), "",
          "/-- All branches are accepted. -/",
          "theorem dRows_ok : dRows.all (fun r => chk mask2 0 ((3 ^ r.1 - 1) / 2) r.2) = true := by",
          "  simp only [dRows, List.all_append, %s, Bool.and_self]"
          % ", ".join("dRows_%d_ok" % i for i in range(nb)), "",
          "/-- The excluded values of `d`. -/",
          "def dList : List ℕ := dRows.map Prod.fst", "",
          "/-- Every prime `3 ≤ p < %d` is in `dList`. -/" % P0,
          "theorem dCover_ok : dCover dList [%s] 3 %d = true := by decide +kernel"
          % (", ".join(map(str, D)), P0 - 3), "",
          "end RestrainedNine", "", "end OddPerfect", ""]
    o += ["#print axioms OddPerfect.RestrainedNine.dRows_%d_ok" % i for i in range(nb)]
    o += ["#print axioms OddPerfect.RestrainedNine.dRows_ok",
          "#print axioms OddPerfect.RestrainedNine.dCover_ok"]
    with open(os.path.join(outdir, "RestrainedNineData.lean"), "w") as f:
        f.write("\n".join(o) + "\n")
    print("P0", P0, "rows", len(rows), "nodes",
          sum(1 for _, b in rows if b[0] == "n"), file=sys.stderr)


if __name__ == "__main__":
    main()
