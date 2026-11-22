# Untrusted helper script for the OddPerfect Lean library.
# Exclusion rows for the restrained family (r = 3): writes the data modules
# OddPerfect/RestrainedSevenData1.lean ... RestrainedSevenData<K>.lean checked by
# OddPerfect/RestrainedSevenCheck.lean and used by OddPerfect/RestrainedSeven.lean.
# Run: python3 -I gen7.py B DEPTH K OUTDIR   (the landed modules: B = 132257, DEPTH = 10, K = 2;
# RestrainedSeven.lean imports part 2, so K = 2 is fixed)
# Requires: Python 3 and sympy (output checked with sympy 1.14.0). Running time: about 3 CPU
# minutes, one process, under 2 GB, for the landed arguments.
# Deterministic: the output depends only on the arguments.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
#
# Setting: N odd perfect, special prime q (q = 1 mod 12, odd exponent), every prime other than q
# and 3 has exponent exactly 2, and 5, 7 do not divide N. A tree for a prime d dividing N, with
# qv = 0 (q unknown) or qv = q:
#   q branch (only when qv = 0 and d = 1 mod 12): the source d + 1 divides 2N;
#   o branch (always; d != qv): the source d^2 + d + 1 divides 2N.
# A branch closes its source by an odd divisor already excluded ("kill t") or continues at an odd
# prime divisor t != 3, t != qv ("node t"), with qv = d below a q branch.
# Factoring is bounded and deterministic (trial division below 10^6, then Pollard rho with a fixed
# seed and a step bound, then ECM with a fixed seed and a curve bound); a node
# at or above 10^6 must have a Pratt certificate found the same way.
# Search: primes p in increasing order, the smallest tree (fewest nodes) of depth at most DEPTH;
# primes without one are retried after the others, to a fixpoint. Rows are split into K modules
# of nearly equal kernel cost; each module starts from the bit mask of the excluded numbers left by the
# previous one (5 and 7 at the start).
import sys, math, os
from functools import lru_cache
from sympy import primerange, factorint, isprime
from sympy.ntheory import pollard_rho, ecm

sys.set_int_max_str_digits(0)
B, DEPTH, K, OUTDIR = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
BIG = 10 ** 6      # nodes at or above BIG carry a Pratt certificate
SMALL = 200        # Pratt factors below SMALL are left to trial division
RHO = 20000        # step bound of each Pollard rho attempt
ECM = 30           # curve bound of the ECM attempt after rho fails
BLOCK = 400        # rows per list literal and per kernel check
CB = 10000         # numbers per coverage check
Eset = {5, 7}


@lru_cache(maxsize=None)
def bfactor(n):
    """Bounded deterministic factoring: trial division below 10^6, then Pollard rho with a fixed
    seed and at most RHO steps per attempt on each composite cofactor, then ECM with a fixed seed
    and at most ECM curves. Returns the prime factors
    found (without multiplicity) and whether the factorization is complete."""
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
def odd_primes(n):
    return tuple(sorted(t for t in bfactor(n)[0] if t not in (2, 3) and (t < BIG or pratt(t) is not None)))


def size(b):
    if b[0] == "k":
        return 1
    return 1 + (size(b[2]) if b[2] is not None else 0) + size(b[3])


def branch(src, qv, depth, memo):
    ps = odd_primes(src)
    kills = [t for t in ps if t in Eset]
    if kills:
        return ("k", kills[0])
    if depth == 0:
        return None
    best = None
    for t in ps:
        if t == qv:
            continue
        tr = tree(t, qv, depth - 1, memo)
        if tr is not None:
            cand = ("n", t, tr[0], tr[1])
            if best is None or size(cand) < size(best):
                best = cand
    return best


def tree(d, qv, depth, memo):
    key = (d, qv, depth)
    if key in memo:
        return memo[key]
    memo[key] = None
    qb, res = None, None
    if qv == 0 and d % 12 == 1:
        qb = branch(d + 1, d, depth, memo)
        if qb is None:
            return None
    ob = branch(d * d + d + 1, qv, depth, memo)
    if ob is not None:
        res = (qb, ob)
    memo[key] = res
    return res


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


def lcert(t):
    if t < BIG:
        return "[]"
    return "[%s]" % ", ".join("(%d, %d, [%s])" % (n, a, ", ".join(map(str, fs))) for n, a, fs in pratt(t))


def lean(b):
    if b is None:
        return ".skip"
    if b[0] == "k":
        return "(.kill %d)" % b[1]
    return "(.node %d %s %s %s)" % (b[1], lcert(b[1]), lean(b[2]), lean(b[3]))


rows = []
todo = [p for p in primerange(5, B) if p not in Eset]
changed = True
while todo and changed:
    changed = False
    left = []
    for p in todo:
        res = None
        for dep in range(1, DEPTH + 1):
            res = tree(p, 0, dep, {})
            if res is not None:
                break
        if res is None:
            left.append(p)
            continue
        rows.append((p, res[0], res[1]))
        Eset.add(p)
        changed = True
    todo = left
if todo:
    sys.exit("no tree for %s" % todo)

# Kernel cost per row grows with the row index i (about 1 + i / n with n rows), so the parts
# hold equal total weight rather than equal numbers of rows.
n = len(rows)
cuts = [0]
for j in range(1, K):
    x = math.sqrt(1 + 3 * j / K) - 1     # x + x^2 / 2 = (3 / 2) j / K
    cuts.append(round(n * x))
cuts.append(n)
masks = [(1 << 5) | (1 << 7)]
chunks = []
for j in range(K):
    part = rows[cuts[j]:cuts[j + 1]]
    chunks.append(part)
    m = masks[-1]
    for p, _, _ in part:
        m |= 1 << p
    masks.append(m)
D = list(primerange(2, math.isqrt(B) + 1))

for j, part in enumerate(chunks, 1):
    lo, hi = part[0][0], part[-1][0]
    o = ["import OddPerfect.RestrainedSevenCheck", ""]
    if j > 1:
        o[0:1] = ["import OddPerfect.RestrainedSevenData%d" % (j - 1)]
    o += ["/-!",
          "# Restrained odd perfect numbers: exclusion rows, part %d of %d" % (j, K),
          "",
          "Generated by `scripts/Restrained/gen7.py %d %d %d` (deterministic). The %d rows of this" % (B, DEPTH, K, len(part)),
          "part run from `%d` to `%d` in the order in which the primes join the excluded set;" % (lo, hi),
          "`rowsOK` starts from the bit mask of the numbers excluded before this part (bits 5 and 7",
          "for part 1) and ends at `mask%d`." % j]
    if j == K:
        o += ["`cover_ok` checks that every prime `5 ≤ p < %d` has its bit set in `mask%d`." % (B, K)]
    o += ["-/", "", "namespace OddPerfect", "", "namespace RestrainedSeven", "",
          "/-- The excluded numbers after part %d, as a bit mask. -/" % j,
          "def mask%d : ℕ := %d" % (j, masks[j]), "",
          ]
    blocks = [part[i:i + BLOCK] for i in range(0, len(part), BLOCK)]
    nb = len(blocks)
    start = str(masks[0]) if j == 1 else "mask%d" % (j - 1)
    for i, blk in enumerate(blocks):
        o += ["/-- Rows of part %d, block %d. -/" % (j, i),
              "def rows%d_%d : List (ℕ × Br × Br) := [" % (j, i),
              ",\n".join("  (%d, %s, %s)" % (p, lean(qb), lean(ob)) for p, qb, ob in blk),
              "]", ""]
        if i == 0:
            o += ["/-- The mask before block 0 of part %d. -/" % j,
                  "def mask%d_0 : ℕ := %s" % (j, start), ""]
        if i + 1 < nb:
            o += ["/-- The mask after block %d of part %d. -/" % (i, j),
                  "def mask%d_%d : ℕ := maskAfter mask%d_%d rows%d_%d" % (j, i + 1, j, i, j, i), ""]
        end = "mask%d_%d" % (j, i + 1) if i + 1 < nb else "mask%d" % j
        o += ["/-- Block %d of part %d is accepted. -/" % (i, j),
              "theorem rows%d_%d_ok : rowsOK mask%d_%d rows%d_%d %s = true := by decide +kernel" % (j, i, j, i, j, i, end), ""]
    o += ["/-- The exclusion rows `(p, q branch, exponent 2 branch)` of part %d. -/" % j,
          "def rows%d : List (ℕ × Br × Br) :=" % j,
          "  " + " ++ (".join("rows%d_%d" % (j, i) for i in range(nb)) + ")" * (nb - 1), "",
          "/-- The rows of part %d are accepted. -/" % j,
          "theorem rows%d_ok : rowsOK %s rows%d mask%d = true :=" % (j, start, j, j),
          "  " + "".join("rowsOK_append rows%d_%d_ok (" % (j, i) for i in range(nb - 1)) + "rows%d_%d_ok" % (j, nb - 1) + ")" * (nb - 1)]
    if j == K:
        Ds = "[%s]" % ", ".join(map(str, D))
        o += ["", "/-- The trial divisors of `cover`: the primes up to the square root of %d. -/" % B,
              "def coverD : List ℕ := %s" % Ds]
        segs = [(lo_, min(CB, B - lo_)) for lo_ in range(5, B, CB)]
        for i, (lo_, n_) in enumerate(segs):
            o += ["", "/-- Coverage of `%d ≤ m < %d`. -/" % (lo_, lo_ + n_),
                  "theorem cover_%d : cover mask%d coverD %d %d = true := by decide +kernel" % (i, K, lo_, n_)]
        o += ["", "/-- Every prime `5 ≤ p < %d` has its bit set in `mask%d`. -/" % (B, K),
              "theorem cover_ok : cover mask%d coverD 5 %d = true := by" % (K, B - 5),
              "  have c0 : cover mask%d coverD 5 %d = true := cover_0" % (K, segs[0][1])]
        tot = segs[0][1]
        for i in range(1, len(segs)):
            tot += segs[i][1]
            o += ["  have c%d : cover mask%d coverD 5 %d = true := cover_append' c%d cover_%d rfl rfl" % (i, K, tot, i - 1, i)]
        o += ["  exact c%d" % (len(segs) - 1)]
    o += ["", "end RestrainedSeven", "", "end OddPerfect", "",
          "#print axioms OddPerfect.RestrainedSeven.rows%d_ok" % j]
    if j == K:
        o += ["#print axioms OddPerfect.RestrainedSeven.cover_ok"]
    with open(os.path.join(OUTDIR, "RestrainedSevenData%d.lean" % j), "w") as f:
        f.write("\n".join(o) + "\n")

print("B", B, "rows", len(rows), "part sizes", [len(c) for c in chunks], file=sys.stderr)
