#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Forced prime closure search for a common d family: grows rows (s, [t, ...]) with t an odd
# prime dividing sigma(s^(d-1)) and Pratt provable, keeps the targets reached from the seeds
# whatever node b = r (mod m) is blocked, and writes cert_<name>.json with targets chosen so
# that every case is abundant. Rows are cached in rows_<name>.json so runs extend the table.
# Used by: OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean, CommonFiftyFive.lean,
# CommonEightyFive.lean, CommonOneFifteenData.lean, CommonNinetyFiveData.lean (through
# gen2.py: the certificates).
# Run: python3 search.py name d seeds minutes [options]. The certificates record their seeds
# and branch (d = 5 with seeds 5,7 and hypothesis seed 7; d = 65 with seeds 5,13 and branch
# 13:7; d = 55, 85, 115, 95 with seeds 5,11, 5,17, 5,23 and 5,19); the minutes and the
# other options of the original runs were not recorded (see the README).
# Requires: Python 3 and sympy. Not deterministic: the search stops at a wall clock deadline
# and factoring steps have time budgets. Running time: the minutes argument, plus the final
# pruning step.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Usage: search.py name d seeds minutes [--special 12,1] [--branch 13:7] [--tdb 1e6] [--budget 2]
#        [--nodemax 1e25] [--maxnodes N] [--prune] [--goal 2]
import sys, json, time, signal, heapq, math, os, argparse
sys.set_int_max_str_digits(0)
from fractions import Fraction
from sympy import isprime, primerange, divisors, factorint, cyclotomic_poly, Poly, symbols, perfect_power
from sympy.ntheory.factor_ import pollard_rho, pollard_pm1
import sympy.ntheory.ecm
ECM = sys.modules['sympy.ntheory.ecm']._ecm_one_factor

ap = argparse.ArgumentParser()
ap.add_argument('name'); ap.add_argument('d', type=int); ap.add_argument('seeds'); ap.add_argument('minutes', type=float)
ap.add_argument('--special', default='12,1'); ap.add_argument('--branch', default='')
ap.add_argument('--tdb', type=float, default=1e6); ap.add_argument('--budget', type=float, default=2.0)
ap.add_argument('--nodemax', type=float, default=1e25); ap.add_argument('--maxnodes', type=int, default=10**9)
ap.add_argument('--prune', action='store_true'); ap.add_argument('--hyp', default='', help='seeds assumed as a case hypothesis'); ap.add_argument('--goal', type=float, default=2.0); ap.add_argument('--sizepen', type=float, default=0.0)
ap.add_argument('--excl', default='', help='primes proved not to divide N: q special needs q %% r != r - 1')
ap.add_argument('--exp', default='', help='proved exponents, e.g. 5:186')
ap.add_argument('--bounds', default='', help='report closure restricted to nodes <= each bound, then exit')
ap.add_argument('--reexpand', type=float, default=0, help='re-factor cached rows with leftovers, given budget')
A = ap.parse_args()
D = A.d; SEEDS = [int(x) for x in A.seeds.split(',')]
SM, SR = map(int, A.special.split(','))
EXCL = [int(x) for x in A.excl.split(',') if x]
EXP = {int(a): int(b) for a, b in (x.split(':') for x in A.exp.split(',') if x)}
BRANCH = {}  # b -> extra seeds valid only when b is special
for item in filter(None, A.branch.split(';')):
    b, xs = item.split(':'); BRANCH[int(b)] = [int(x) for x in xs.split(',')]
NODEMAX = int(A.nodemax); T0 = time.time(); DEADLINE = T0 + 60 * A.minutes
HERE = os.getcwd()
CACHE = os.path.join(HERE, f'rows_{A.name}.json')

class TO(Exception): pass
def _alarm(*a): raise TO()
signal.signal(signal.SIGALRM, _alarm)
def timed(fn, sec, *a, **k):
    signal.setitimer(signal.ITIMER_REAL, max(sec, 0.01))
    try: return fn(*a, **k)
    except TO: return None
    finally: signal.setitimer(signal.ITIMER_REAL, 0)

# cyclotomic factors Phi_k, k | d, k > 1, and trial division lists (p = 1 mod 2k, or p | k)
x = symbols('x')
KS = [k for k in divisors(D) if k > 1]
COEF = {k: [int(c) for c in Poly(cyclotomic_poly(k, x), x).all_coeffs()] for k in KS}
def phi(k, s):
    v = 0
    for c in COEF[k]: v = v * s + c
    return v
BASE = list(primerange(3, int(A.tdb)))
BLOCKS = {}
for k in KS:
    ps = [p for p in BASE if p % (2 * k) == 1 or k % p == 0]
    BLOCKS[k] = [(ps[i:i + 300], math.prod(ps[i:i + 300])) for i in range(0, len(ps), 300)]

def split(m):
    pp = perfect_power(m)
    if pp: return pp[0]
    f = pollard_pm1(m, B=20000)
    if f: return f
    f = pollard_rho(m, max_steps=50000)
    if f: return f
    B1 = 2000
    while True:
        f = ECM(m, B1=B1, B2=50 * B1, max_curve=8)
        if f: return f
        B1 = min(B1 * 2, 10**6)

def factor_phi(n, k, budget):
    found = set()
    for block, P in BLOCKS[k]:
        g = math.gcd(n, P)
        if g > 1:
            for p in block:
                if g % p == 0:
                    found.add(p)
                    while n % p == 0: n //= p
    left = []; stack = [n] if n > 1 else []; dl = time.time() + budget
    while stack:
        m = stack.pop()
        if isprime(m): found.add(m); continue
        f = timed(split, dl - time.time(), m) if dl > time.time() else None
        if not f or f in (1, m): left.append(m); continue
        stack += [f, m // f]
    return found, left

PR = {}
def pratt_ok(t, sec=8):
    if t < 10**12: return True
    if t in PR: return PR[t]
    f = timed(factorint, sec, t - 1)
    PR[t] = ok = f is not None and all(pratt_ok(p, sec) for p in f if p > 2)
    return ok

def make_row(s, budget):
    recv = set(); left = []
    for k in KS:
        f, l = factor_phi(phi(k, s), k, budget); recv |= f; left += l
    recv = sorted(t for t in recv if t % 2 and t != s and t <= NODEMAX and pratt_ok(t))
    return recv, [str(m) for m in left]

rows = {}
if os.path.exists(CACHE):
    for s, v in json.load(open(CACHE)).items(): rows[int(s)] = v
def save():
    json.dump({str(s): v for s, v in rows.items()}, open(CACHE + '.tmp', 'w')); os.replace(CACHE + '.tmp', CACHE)

def cand(b): return b % SM == SR and all(b % r != r - 1 for r in EXCL)

def analyze(rows, targets_only=None):
    """robust set via dominators of the graph root -> seeds, s -> t."""
    adj = {s: v['r'] for s, v in rows.items()}
    ROOT = 0
    succ = lambda u: SEEDS if u == ROOT else adj.get(u, [])
    # iterative DFS postorder
    order = []; seen = {ROOT}; st = [(ROOT, iter(succ(ROOT)))]
    while st:
        u, it = st[-1]
        for w in it:
            if w not in seen: seen.add(w); st.append((w, iter(succ(w)))); break
        else: order.append(u); st.pop()
    rpo = order[::-1]; num = {u: i for i, u in enumerate(rpo)}
    preds = {u: [] for u in rpo}
    for u in rpo:
        for w in succ(u): preds[w].append(u)
    idom = {ROOT: ROOT}
    def inter(a, b):
        while a != b:
            while num[a] > num[b]: a = idom[a]
            while num[b] > num[a]: b = idom[b]
        return a
    ch = True
    while ch:
        ch = False
        for u in rpo[1:]:
            ps = [p for p in preds[u] if p in idom]
            nd = ps[0]
            for p in ps[1:]: nd = inter(p, nd)
            if idom.get(u) != nd: idom[u] = nd; ch = True
    # explicit reach for branches with extra seeds
    def reach(block, extra):
        R = set(SEEDS) | set(extra); q = list(R)
        while q:
            u = q.pop()
            if u == block: continue
            for w in adj.get(u, []):
                if w not in R: R.add(w); q.append(w)
        return R
    br = {b: reach(b, ex) for b, ex in BRANCH.items() if b in idom}
    robust = set()
    for t in rpo[1:]:
        u = idom[t]; ok = True
        while u != ROOT:
            if cand(u) and (u not in br or t not in br[u]): ok = False; break
            u = idom[u]
        if ok: robust.add(t)
    return set(rpo[1:]), robust

def hfac(t):
    e = EXP.get(t, 4)
    return Fraction(t**(e + 1) - 1, (t - 1) * t**e)
def worst(T):
    P = math.prod(float(hfac(t)) for t in T)
    qs = [t for t in T if cand(t)]
    return min([P] + [P / float(hfac(q)) * (q + 1) / q for q in qs])

def report(full, robust):
    w = worst(robust)
    small = [p for p in primerange(3, 3000) if any(p % (2 * k) == 1 for k in KS) or D % p == 0]
    miss_un = [p for p in small if p not in full]; miss_nr = [p for p in small if p in full and p not in robust]
    print(f'[{time.time()-T0:7.0f}s] rows {len(rows)} reached {len(full)} robust {len(robust)} worst {w:.5f}', flush=True)
    print('   unreached<3000', miss_un[:40], len(miss_un)); print('   not robust<3000', miss_nr[:40], flush=True)
    return w

if A.bounds:
    for X in [int(float(b)) for b in A.bounds.split(',')]:
        sub = {s: {'r': [t for t in v['r'] if t <= X]} for s, v in rows.items() if s <= X}
        full, robust = analyze(sub)
        print(f'bound {X:.0e}: rows {len(sub)} reached {len(full)} robust {len(robust)} worst {worst(robust):.5f}', flush=True)
    sys.exit(0)
# expansion: smallest unexpanded reached node first
if not A.prune:
    if A.reexpand:
        for s in sorted(rows):
            if rows[s]['left'] and time.time() < DEADLINE:
                r, l = make_row(s, A.reexpand); rows[s] = {'r': sorted(set(r) | set(rows[s]['r'])), 'left': l}
        save()
    full, robust = analyze(rows)
    heap = [t for t in full | set(SEEDS) if t not in rows]; heapq.heapify(heap); queued = set(heap)
    last = time.time(); w = report(full, robust)
    while heap and time.time() < DEADLINE and len(rows) < A.maxnodes and w <= A.goal:
        s = heapq.heappop(heap)
        r, l = make_row(s, A.budget); rows[s] = {'r': r, 'left': l}
        for t in r:
            if t not in rows and t not in queued: queued.add(t); heapq.heappush(heap, t)
        if time.time() - last > 60:
            save(); full, robust = analyze(rows); w = report(full, robust); last = time.time()
    save(); full, robust = analyze(rows); w = report(full, robust)
    print('next unexpanded', heap[0] if heap else None)
    sys.exit(0)

# prune: choose targets T and a small sub table, then write the certificate
full, robust = analyze(rows); print('full worst', worst(robust))
assert worst(robust) > 2, 'closure not abundant'
srt = sorted(robust); T = []
for t in srt:
    T.append(t)
    if worst(T) > 2: break
# drop targets that are not needed (largest first), keeping the bound
for t in sorted(T, reverse=True):
    if t in SEEDS: continue
    U = [u for u in T if u != t]
    if worst(U) > 2: T = U
print('targets', len(T), 'max', max(T), 'worst', worst(T))

def fast_ok(sel):
    full_s, rob_s = analyze({s: {'r': r} for s, r in sel.items()})
    return all(t in rob_s for t in T)

def sub_check(sel):
    """fast pass/fail via dominators; on failure fall back to the explicit (t, b) list."""
    return [] if fast_ok(sel) else sub_check_slow(sel)

def sub_check_slow(sel):
    """sel: dict s -> receivers. returns list of (t, b) failures."""
    sub = {s: {'r': r} for s, r in sel.items()}
    nodes = set(SEEDS) | set(sel) | {t for r in sel.values() for t in r}
    def reach(block, extra=()):
        R = set(SEEDS) | set(extra); q = list(R)
        while q:
            u = q.pop()
            if u == block: continue
            for w in sel.get(u, []):
                if w not in R: R.add(w); q.append(w)
        return R
    fails = []
    for b in [None] + sorted(n for n in nodes if cand(n)):
        R = reach(b, BRANCH.get(b, ()))
        fails += [(t, b) for t in T if t not in R]
    return fails

def path(t, block, extra, sel):
    """cheapest path in the full table to t avoiding block's row; rows already in sel are free."""
    src = set(SEEDS) | set(extra); dist = {u: 0.0 for u in src}; par = {}
    pq = [(0.0, u) for u in src]
    while pq:
        dd, u = heapq.heappop(pq)
        if dd > dist.get(u, 1e18): continue
        if u == t: break
        if u == block or u not in rows: continue
        c = 0.0 if u in sel else 1.0 + math.log10(u) / 5 + A.sizepen * max(0.0, math.log10(u) - 6)
        for w in rows[u]['r']:
            nd = dd + c + (0 if w in sel or w == t else 0.01 * (1 + cand(w) * 5))
            if nd < dist.get(w, 1e18): dist[w] = nd; par[w] = u; heapq.heappush(pq, (nd, w))
    assert t in dist, (t, block)
    edges = []; u = t
    while u not in src: edges.append((par[u], u)); u = par[u]
    return edges

sel = {}
it = 0
while True:
    fails = sub_check(sel); it += 1
    if not fails: break
    for t, b in fails[:200]:
        for s, w in path(t, b, BRANCH.get(b, ()), sel):
            sel.setdefault(s, [])
            if w not in sel[s]: sel[s].append(w)
print('greedy rows', len(sel), 'iterations', it)
# reverse deletion of receivers then rows, largest source first
for s in sorted(sel, reverse=True):
    for w in list(sel[s]):
        trial = {k: [x for x in v if not (k == s and x == w)] for k, v in sel.items()}
        trial = {k: v for k, v in trial.items() if v}
        if fast_ok(trial): sel = trial
print('pruned rows', len(sel))
nodes = sorted(set(SEEDS) | set(sel) | {t for r in sel.values() for t in r})
cases = []
P = math.prod(hfac(t) for t in T)
cases.append({'q': 'none', 'sigma_over_D': f'{P.numerator}/{P.denominator}', 'float': float(P)})
for q in sorted(t for t in T if cand(t)):
    V = P / hfac(q) * Fraction(q + 1, q)
    cases.append({'q': q, 'sigma_over_D': f'{V.numerator}/{V.denominator}', 'float': float(V)})
cert = {'d': D, 'seeds': SEEDS, 'hypothesis_seeds': [int(x) for x in A.hyp.split(',') if x], 'special_test': [SM, SR], 'branch_seeds': {str(b): v for b, v in BRANCH.items()},
        'exponent': 4, 'exponents': {str(k): v for k, v in EXP.items()}, 'excluded_primes': EXCL, 'rows': [[s, sorted(sel[s])] for s in sorted(sel)], 'targets': sorted(T), 'cases': cases,
        'stats': {'rows': len(sel), 'nodes': len(nodes), 'largest_node': max(nodes), 'targets': len(T),
                  'worst': min(c['float'] for c in cases)}}
json.dump(cert, open(os.path.join(HERE, f'cert_{A.name}.json'), 'w'), indent=1)
print(json.dumps(cert['stats']))
