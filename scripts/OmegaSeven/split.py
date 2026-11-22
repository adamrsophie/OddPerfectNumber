# Untrusted helper script for the OddPerfect Lean library.
# Cuts the kernel checks of the children in OddPerfect/OmegaSeven.lean (the theorems closed_3_7_11,
# closed_3_7_13, closed_3_7, closed_no_five and closed_three_five_big) into separate lemmas, one per
# child; a child of more than CAP = 1200 search nodes of the mirror ../OmegaSix/mirror.py is cut
# further, along its prime window (solve_of_window) or its exponent split (solve_of_split).
# Used by: OddPerfect/OmegaSeven.lean (the private theorems between solve_of_split and closed_3_7_11).
# Run: python3 split.py > split.lean (in scripts/OmegaSeven, with ../OmegaSix/mirror.py present)
# Requires: Python 3 standard library. Deterministic. Running time: under one second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: ../OmegaSix/mirror.py is read relative to this script; output goes to standard output.
# License: GPL 3, same as the repository.
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.argv = ['mirror.py', '10', '4', '30']
src = open(os.path.join(here, '..', 'OmegaSix', 'mirror.py')).read()
exec(src[:src.rindex('print(solve(FUEL')])
CAP = 1200

def cnt(known, j, m, fuel):
    st['nodes'] = 0; r = solve(fuel, known, j, m); assert r; return st['nodes']

def lit(l): return '[' + ', '.join('⟨%d, %d, %s⟩' % (p, k, 'true' if ex else 'false') for p, k, ex in l) + ']'

def branch(known, j, m):
    """The branch solve takes at a live state with j > 0: ('window', lo, n) or ('split', l1, l2)."""
    Ln = Ld = Un = Ud = 1
    for (p, k, ex) in known:
        g = geom(p, k); Ln *= g; Ld *= p ** k
        if ex: Un *= g; Ud *= p ** k
        else: Un *= p; Ud *= p - 1
    assert j > 0 and not (2 * Ld < Ln or 2 * Ld <= Ln)
    ps = [2] + [p for (p, _, _) in known]
    cs = [c for c in [strip(geom(p, k), ps) for (p, k, ex) in known if ex] if c != 1]
    assert not any(c <= m for c in cs)
    assert not any(a[2] and b[2] and a[1] % 2 == 1 and b[1] % 2 == 1 and a[0] != b[0] for a in known for b in known)
    allex = all(e[2] for e in known)
    bounds = []
    if Un < 2 * Ud:
        bU = bsearch(Un, Ud, j, m, bhi(Un, Ud, j, m), 200)
        if not cond(Un, Ud, j, bU + 1): bounds.append(bU)
    bounds += cs
    lo = m + 1
    if j == 1 and Ln < 2 * Ld:
        D = 2 * Ld - Ln; lo = max(lo, (Ln + D - 1) // D)
    if bounds and (minB(bounds) <= lo + W or allex or j >= 2):
        return ('window', lo, minB(bounds) + 1 - lo)
    assert not allex
    i = pick(known); p, k, ex = known[i]
    return ('split', known[:i] + [(p, k, True)] + known[i + 1:], known[:i] + [(p, nextvalid(p, k), False)] + known[i + 1:])

out = []
def P(f, l, j):
    return 'isPrimeQ q = true → solve %d (%s ++ [⟨q, kmin q, false⟩]) (%d - 1) q = true' % (f, lit(l), j)

def leaf(name, known, j, m, fuel, c, what):
    out.append('set_option maxRecDepth 100000 in')
    out.append('/-- %s (mirror nodes: %d). -/' % (what, c))
    out.append('private theorem %s : solve %d %s %d %d = true := by decide +kernel' % (name, fuel, lit(known), j, m))
    out.append('')

def node(name, known, j, m, fuel, what):
    """Lemma `name : solve fuel known j m = true`."""
    c = cnt(known, j, m, fuel)
    if c <= CAP:
        leaf(name, known, j, m, fuel, c, what); return
    b = branch(known, j, m)
    if b[0] == 'split':
        node(name + 'x', b[1], j, m, fuel - 1, 'The exact case of the split')
        node(name + 'y', b[2], j, m, fuel - 1, 'The next exponent of the split')
        out.append('/-- %s, through its exponent split (mirror nodes: %d). -/' % (what, c))
        out.append('private theorem %s : solve %d %s %d %d = true :=' % (name, fuel, lit(known), j, m))
        out.append('  solve_of_split (by decide) (by decide +kernel) (by decide +kernel) rfl rfl %sx %sy' % (name, name))
        out.append('')
        return
    a, n = b[1], b[2]
    segs = []; cur = None
    for q in range(a, a + n):
        cc = cnt(known + [(q, kmin(q), False)], j - 1, q, fuel - 1) if isPrimeQ(q) else 0
        if cc > CAP:
            if cur: segs.append(cur); cur = None
            segs.append([q, 1, 'sub', cc]); continue
        if cur and cur[3] + cc > CAP: segs.append(cur); cur = None
        if not cur: cur = [q, 0, 'chk', 0]
        cur[1] += 1; cur[3] += cc
    if cur: segs.append(cur)
    hyps = []
    for s, k, kind, cc in segs:
        if kind == 'sub':
            node('%s_%d' % (name, s), known + [(s, kmin(s), False)], j - 1, s, fuel - 1, 'The child `%d`' % s)
            hyps.append('(win_one (b := %d) %s_%d)' % (s, name, s))
        else:
            cn = '%s_w%d' % (name, s)
            out.append('set_option maxRecDepth 100000 in')
            out.append('/-- Window `[%d, %d)` (mirror nodes: %d). -/' % (s, s + k, cc))
            out.append("private theorem %s : ∀ q ∈ List.range' %d %d,\n    %s := by" % (cn, s, k, P(fuel - 1, known, j)))
            out.append('  decide +kernel')
            out.append('')
            hyps.append(cn)
    def comb(i):
        if i == len(segs) - 1: return hyps[i]
        return '(win_split %s\n      %s rfl rfl)' % (hyps[i], comb(i + 1))
    out.append('/-- %s, through its window (mirror nodes: %d). -/' % (what, c))
    out.append('private theorem %s : solve %d %s %d %d = true :=' % (name, fuel, lit(known), j, m))
    out.append('  solve_of_window (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)')
    out.append('    %s' % comb(0))
    out.append('')

specs = [('c3_7_11', [(3, 2, False), (7, 2, False), (11, 2, False)], 3,
          [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]),
         ('c3_7_13', [(3, 2, False), (7, 2, False), (13, 1, False)], 3, [17, 19, 23, 29, 31, 37, 41, 43, 47, 53]),
         ('c3_7', [(3, 2, False), (7, 2, False)], 4, [17, 19, 23, 29]),
         ('cno5', [(3, 2, False)], 5, [11, 13, 17]),
         ('c35big', [(3, 2, False), (5, 1, False)], 4, [37, 41, 43, 47, 53, 59, 61])]
for base, known, j, qs in specs:
    for q in qs:
        node('%s_%d' % (base, q), known + [(q, kmin(q), False)], j - 1, q, 30, 'The child `%d`' % q)
print('\n'.join(out))
