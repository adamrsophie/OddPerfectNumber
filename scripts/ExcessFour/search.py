# Untrusted helper script for the OddPerfect Lean library.
# Exact search for the three families of total excess below 4: writes the certificates that
# gen_excess.py turns into OddPerfect/ExcessFourS1.lean, ExcessFourS2a.lean and
# ExcessFourS2b.lean, checked by TwoExcEngine.checkV (OddPerfect/TwoExcEngineCheck.lean,
# TwoExcEngineTail.lean) and behind excessS1, excessS2a, excessS2b and so four_le_excess and
# four_le_cardFactors_sub (OddPerfect/ExcessFour.lean).
#
# Setting: N odd perfect with special prime q (q = 1 mod 4, odd exponent) and
#   S1:  exponent 6 at 3 and at most one further prime of exponent 4,
#   S2a: exponent 4 at 3 and at most two further primes of exponent 4,
#   S2b: exponent 2 at 3 and at most three primes of exponent 4,
# every other prime factor except q of exponent exactly 2 (EMAX below is the number of primes of
# exponent 4 other than 3). The search is the one of ../TwoExceptionTwo/search.py with these
# changes: the root value is sigma(3^V3) (source ["sig", 3, V3]) and the budget of 3 is V3; an
# exception has the single class e4 (exponent exactly 4, value Phi_5(f), budget 4); no facts on q
# are used (q = 5 and q = 8 mod 9 are allowed, the class q of a prime 2 mod 3 is not no3); rule L
# is used only for S2b; in a deficient leaf each undecided exception counts as four slots of type
# (d), and with q undecided and K empty the rows of type (e) are powers of q (field `pureq`, bound
# of FORMAT.md). The format of the certificates is ../TwoExceptionTwo/FORMAT.md with the changes
# in FORMAT.md of this folder.
#
# Run: python3 -I search.py FAM LIMIT [cert] [nojump] [pade]
#   the three certificates of the library:
#     python3 -I search.py S1 100000 cert nojump    writes cert_ex_S1_100000_nojump_nolanded.jsonl
#     python3 -I search.py S2a 100000 cert nojump   writes cert_ex_S2a_100000_nojump_nolanded.jsonl
#     python3 -I search.py S2b 100000 cert          writes cert_ex_S2b_100000_nolanded_ruleL.jsonl
#   and result_<tag>.json, in the current folder, and prints the summary. The header records the
#   flags: those given, `nolanded` always and `ruleL` for S2b. The flag `nojump` changes nothing
#   in this script but the header and the file name: it switched off a step that skipped a range
#   of primes, which no certificate of the library uses, which the checker does not read, and
#   which is not part of this script. The flag `pade` (off by default; no certificate of the
#   library uses it) lets a deficient leaf close by the second path of the Lean tail test: when
#   S < 1 and U < 2 with the tail factor 1/(1 - S) fail, S < 3 and U < 2 with the factor
#   (S^2 + 4 S + 6)/(6 - 2 S); the pure q bound (field `pureq`) keeps 1/(1 - S). Like every
#   flag it is recorded in the header and the file name. A branch whose scan passes LIMIT is
#   left open (exit status 1); none is for these arguments.
# Requires: Python 3 and sympy (factorint, isprime, nextprime, n_order, divisors, mobius,
#   primerange; checked with sympy 1.14.0). Factoring is by sympy factorint for values below 2^64
#   and for the cofactor left after trial division by the odd primes below 20000 when a value is
#   at least 2^64; a larger cofactor is not factored and its factor list is marked incomplete.
# Running time: under a second for each family, one process, under 100 MB.
# Deterministic: the output depends only on the arguments and the sympy version.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import sys, time, json
from fractions import Fraction as F
from math import isqrt, gcd
from sympy import factorint, isprime, nextprime, n_order, divisors, mobius, primerange

USAGE = 'usage: python3 -I search.py FAM LIMIT [cert] [nojump] [pade]   (FAM is S1, S2a or S2b)'
if (len(sys.argv) < 3 or sys.argv[1] not in ('S1', 'S2a', 'S2b')
        or any(f not in ('cert', 'nojump', 'pade') for f in sys.argv[3:])):
    print(USAGE); sys.exit(2)
FAM = sys.argv[1]; LIMIT = int(sys.argv[2])
V3, EMAX = {'S1': (6, 1), 'S2a': (4, 2), 'S2b': (2, 3)}[FAM]
# the flags recorded in the header: those given, nolanded always, ruleL for S2b
FLAGS = set(sys.argv[3:]) | {'nolanded'}
if FAM == 'S2b': FLAGS.add('ruleL')
RULEL = 'ruleL' in FLAGS   # rule L (false_of_three_sq_of_index_three) for S2b only
CERT = 'cert' in FLAGS
PADE = 'pade' in FLAGS     # the Pade path of the tail test (off by default)
TAG = 'ex_%s_%d%s' % (FAM, LIMIT, ''.join('_' + f.replace('=', '') for f in sorted(FLAGS) if f != 'cert'))
L8 = (7, 13, 19, 31, 61, 97, 127, 331)
B64 = 2**64
MHIT = 10**30     # bound of the enumerated products of the tail bound
DMAX = 300        # largest index d of a computed value Phi_d(p)
KCAP = 64         # cap of the exponents of the ratio bounds and of the abundant divisors
LOAD = {'cyc_values': 0, 'cyc_distinct': set(), 'generated': 0, 'max_generated': 0, 'square_4n3': 0}
sys.setrecursionlimit(1000000)

FC = {}
SMALLP = list(primerange(3, 20000))
NOTE = {'partial': 0, 'uncomputed': 0, 'splits': 0}
PRIMES_USED = set()      # primes whose primality the run relies on
FACTORED = set()         # values factored completely (cofactor below 2^64)

def fstr(x): return '%d/%d' % (x.numerator, x.denominator)

def factor_value(V, present):
    """returns (factors, complete): certified odd prime factors with exact multiplicity.
    complete means the listed primes (with 2 removed) multiply to V."""
    out = []
    for p in present:
        if V % p == 0:
            e = 0
            while V % p == 0: V //= p; e += 1
            out.append([p, e])
    while V % 2 == 0: V //= 2
    if V == 1: return out, True
    if V >= B64:
        NOTE['partial'] += 1
        for p in SMALLP:
            if V % p == 0:
                e = 0
                while V % p == 0: V //= p; e += 1
                out.append([p, e])
        if not (1 < V < B64): return out, V == 1
    f = FC.get(V)
    if f is None:
        f = factorint(V); m = 1
        for p, e in f.items():
            if not (p < B64 and isprime(p)): raise SystemExit('factoring failed for %d' % V)
            m *= p**e
        if m != V: raise SystemExit('factoring failed for %d' % V)
        FC[V] = f
    FACTORED.add(V)
    return out + [[p, e] for p, e in f.items()], True

def phi3(p): return p*p + p + 1
def sig(p, k): return (p**(k + 1) - 1) // (p - 1)
SR = {}
def sratio(p, k):
    k = min(k, KCAP)
    if (p, k) not in SR: SR[(p, k)] = F(sig(p, k), p**k)
    return SR[(p, k)]
CYC = {}
def cyc(d, p):
    if (d, p) not in CYC:
        num = den = 1
        for k in divisors(d):
            m = mobius(d // k)
            if m == 1: num *= p**k - 1
            elif m == -1: den *= p**k - 1
        CYC[(d, p)] = num // den
    return CYC[(d, p)]
def dprime(p, g): return p if g % p == 1 else n_order(g, p)
def allowed(n, kind, D, no3):
    if n % D: return False
    if no3 and n % 3 == 0: return False
    return n % 4 == 2 if kind == 'q' else (n % 2 == 1 and n >= 5)
def nextn(kind, D, no3, start):
    n = -(-start // D) * D
    for _ in range(64):
        if allowed(n, kind, D, no3): return n
        n += D
    return None

# ---------- state: S, R map a prime to its list of contributions [source, weight] ----------
class St:
    __slots__ = ('x', 'q', 'Fr', 'R', 'S', 'sq', 'exq')
    def copy(s):
        t = St.__new__(St)
        t.x, t.q, t.exq = s.x, s.q, s.exq
        t.Fr = {k: list(v) for k, v in s.Fr.items()}
        t.R = {k: list(v) for k, v in s.R.items()}
        t.S = {k: list(v) for k, v in s.S.items()}
        t.sq = s.sq
        return t
def wt(lst): return sum(w for _, w in lst)
def present(s, f): return f in s.S or f in s.Fr
def nexc(s): return len(s.Fr) - (0 if s.q is None else 1)
def excs(s): return [p for p in s.Fr if p != s.q]
def plist(s): return list(s.S) + list(s.Fr)
def lohi(s):
    lo = hi = s.sq
    for p, (D, no3, kmin, ex) in s.Fr.items():
        r = sratio(p, kmin); lo = lo * r
        hi = hi * (r if ex and kmin <= KCAP else F(p, p - 1))
    return lo, hi
def sjson(s):
    return {'x': s.x, 'q': s.q, 'exq': sorted(s.exq),
            'F': {str(p): list(v) for p, v in sorted(s.Fr.items())},
            'R': {str(p): [list(c) for c in v] for p, v in sorted(s.R.items())},
            'S': {str(p): [list(c) for c in v] for p, v in sorted(s.S.items())}}

STATS = {'nodes': 0, 'leaves': 0, 'maxprime': 0, 'maxx': 0, 'decide': 0}
REASONS = {}
MINM = [None, None]
OPEN = []
QS = set(); PAIRS = set(); TAILS = set()
OUT = None
NID = [0]
def newid():
    NID[0] += 1; return NID[0]
def emit(rec):
    if OUT is not None: OUT.write(json.dumps(rec, separators=(',', ':')) + '\n')
def leafrec(nid, s, reason, proof, margin=None, rec=None):
    STATS['leaves'] += 1
    REASONS[reason] = REASONS.get(reason, 0) + 1
    if margin is not None and (MINM[0] is None or margin < MINM[0]):
        MINM[0] = margin; MINM[1] = reason
    if s is not None:
        if s.q is not None: QS.add(s.q)
        PAIRS.add(tuple(sorted(excs(s))))
    if rec is None: rec = {'id': nid, 'kind': 'leaf'}
    rec['outcome'] = 'leaf'; rec['reason'] = reason; rec['proof'] = proof
    emit(rec)

# ---------- values and items ----------
def value_rec(s, src):
    """src = ['row', p] (p^2+p+1), ['sig', p, k] (sigma(p^k)) or ['cyc', d, p] (Phi_d(p));
    returns record and items"""
    V = phi3(src[1]) if src[0] == 'row' else sig(src[1], src[2]) if src[0] == 'sig' else cyc(src[1], src[2])
    fac, complete = factor_value(V, plist(s))
    for p, e in fac: PRIMES_USED.add(p)
    rec = {'src': src, 'factors': fac, 'complete': complete}
    if V < 10**40: rec['value'] = str(V)
    return rec, [(p, e, src) for p, e in fac]

def cyc_values(s, p, dnew, dold):
    recs, its = [], []
    for d in divisors(dnew):
        if d == 1 or dold % d == 0: continue
        if d > DMAX: NOTE['uncomputed'] += 1; continue
        LOAD['cyc_values'] += 1; LOAD['cyc_distinct'].add((d, p))
        r, i = value_rec(s, ['cyc', d, p]); recs.append(r); its += i
    return recs, its

def setD(s, p, d, exact=False):
    D, no3, kmin, ex = s.Fr[p]
    kind = 'q' if p == s.q else 'e'
    Dn = D * d // gcd(D, d)
    if ex:
        if (kmin + 1) % Dn: return None, 'exact exponent %d: %d does not divide %d' % (kmin, Dn, kmin + 1)
        return (s.copy(), [], []), None
    if kind == 'q' and Dn % 4 == 0: return None, 'q: 4 | %d but alpha+1 = 2 mod 4' % Dn
    if kind == 'e' and Dn % 2 == 0: return None, 'exception: %d even but b+1 odd' % Dn
    if no3 and Dn % 3 == 0: return None, 'class no3 but 3 | %d' % Dn
    n = nextn(kind, Dn, no3, kmin + 1)
    if n is None: return None, 'no allowed exponent'
    t = s.copy()
    if exact:
        t.Fr[p] = [n, no3, n - 1, True]
        recs, its = cyc_values(t, p, n, D)
    else:
        t.Fr[p] = [Dn, no3, n - 1, False]
        recs, its = cyc_values(t, p, Dn, D)
    return (t, recs, its), None

# ---------- roles ----------
def make_square(s, f, w, src):
    t = s.copy(); t.S[f] = [[src, w]] if w else []; t.sq = t.sq * F(phi3(f), f*f)
    rec, its = value_rec(t, ['row', f])
    return {'role': 'square', 'prime': f}, t, [rec], its

def new_free(s, f, w, src, D, no3, kind, lab):
    t = s.copy()
    if kind == 'q': t.q = f
    n = nextn(kind, D, no3, 1)
    t.Fr[f] = [D, no3, n - 1, False]; t.R[f] = [[src, w]] if w else []
    recs, its = cyc_values(t, f, D, 1)
    return {'role': lab, 'prime': f, 'D': D, 'no3': no3, 'kmin': n - 1}, t, recs, its

def make_q(s, f, w, src):
    # q = 1 mod 4; no facts on q are used in these families
    if s.q is not None or f % 4 != 1 or f in s.exq: return []
    if f % 3 == 1:
        return [new_free(s, f, w, src, 2, True, 'q', 'q0'),
                new_free(s, f, w, src, 6, False, 'q', 'q3')]
    return [new_free(s, f, w, src, 2, False, 'q', 'q')]

def make_exc(s, f, w, src):
    if nexc(s) >= EMAX: return []
    # exponent exactly 4: full component sigma(f^4) = Phi_5(f) at once, budget 4
    t = s.copy(); t.Fr[f] = [5, True, 4, True]; t.R[f] = [[src, w]] if w else []
    recs, its = cyc_values(t, f, 5, 1)
    return [({'role': 'e4', 'prime': f, 'D': 5, 'no3': True, 'kmin': 4}, t, recs, its)]

def roles(s, f, w, src):
    return [make_square(s, f, w, src)] + make_q(s, f, w, src) + make_exc(s, f, w, src)

def roles_note(s, f):
    """the role classes a checker must find among the children"""
    return {'square': True,
            'q_allowed': s.q is None and f % 4 == 1 and f not in s.exq,
            'exc_allowed': nexc(s) < EMAX}

def landed_ok(s):
    if not RULEL: return True
    if any(e in L8 and s.Fr[e][1] for e in excs(s)): return True
    if nexc(s) >= EMAX: return False
    return any(p >= s.x and not present(s, p) for p in L8)

def receivers(s):
    out = [p for p, c in s.S.items() if p % 3 == 2 and wt(c) == 0]
    out += [p for p in s.Fr if p % 3 == 2 and wt(s.R[p]) == 0]
    return sorted(out)

# ---------- closure node ----------
def apply_node(nid, s, values, items, nextx, action):
    """s: state with the action applied; items: forced (prime, weight, source)."""
    STATS['nodes'] += 1
    before = sjson(s)
    for f, w, src in items:
        if f > STATS['maxprime']: STATS['maxprime'] = f
    bad = None; pend = []
    for f, w, src in items:
        if f in s.S:
            s.S[f].append([src, w])
            cap = V3 if f == 3 else 2
            if wt(s.S[f]) > cap:
                bad = ('cap3' if f == 3 else 'cap', {'prime': f, 'budget': cap, 'contributions': s.S[f]}); break
        elif f in s.Fr:
            s.R[f].append([src, w])
            if s.Fr[f][3] and wt(s.R[f]) > s.Fr[f][2]:
                bad = ('capexact', {'prime': f, 'budget': s.Fr[f][2], 'contributions': s.R[f]}); break
        elif f < s.x:
            bad = ('absentforced', {'prime': f, 'source': src, 'x': s.x}); break
        else: pend.append((f, w, src))
    head = {'id': nid, 'kind': 'apply', 'action': action, 'state': before, 'values': values,
            'items': [[f, w, src] for f, w, src in items]}
    if bad:
        leafrec(nid, s, bad[0], bad[1], rec=head); return
    lo, hi = lohi(s)
    if lo > 2:
        div = [[3, V3]] + [[p, 2] for p in s.S if p != 3] + [[p, min(v[2], KCAP)] for p, v in s.Fr.items()]
        leafrec(nid, s, 'abundant', {'divisor': sorted(div), 'ratio': fstr(lo)}, lo - 2, rec=head); return
    if not landed_ok(s):
        leafrec(nid, s, 'landedL', {'exceptions': excs(s), 'x': s.x}, rec=head); return
    if pend:
        f = min(pend)[0]
        w = sum(v for g, v, _ in pend if g == f)
        srcs = [sr for g, v, sr in pend if g == f]
        rest = [(g, v, sr) for g, v, sr in pend if g != f]
        kids = []
        for act, t, recs, its in roles(s, f, w, srcs[0] if len(srcs) == 1 else ['multi', srcs]):
            # the weight w is split over its sources in the role; record the full list
            if f in t.S: t.S[f] = [[sr, v] for g, v, sr in pend if g == f]
            else: t.R[f] = [[sr, v] for g, v, sr in pend if g == f]
            kids.append((newid(), act, t, recs, its))
        head['forced'] = f; head['roles'] = roles_note(s, f)
        if not kids: leafrec(nid, s, 'noroles', {'prime': f}, rec=head); return
        head['outcome'] = 'force'; head['children'] = [k[0] for k in kids]; emit(head)
        for cid, act, t, recs, its in kids:
            apply_node(cid, t, recs, rest + its, nextx, act)
        return
    if s.q is not None and nexc(s) == EMAX:
        rc = receivers(s)
        if rc:
            p = rc[0]; kids = []; why = {}
            for g in sorted(s.Fr):
                if g == p: continue
                d = dprime(p, g)
                r, reason = setD(s, g, d)
                if r is None: why[str(g)] = {'d': d, 'infeasible': reason}; continue
                t, recs, its = r
                if not any(h == p for h, v, sr in its):
                    its = its + [(p, 1, ['receipt', p, d, g])]
                kids.append((newid(), {'role': 'sender', 'receiver': p, 'sender': g, 'd': d}, t, recs, its))
            head['receiver'] = p; head['senders_infeasible'] = why
            if not kids: leafrec(nid, s, 'receipt', {'receiver': p, 'senders': why}, rec=head); return
            head['outcome'] = 'receipt'; head['children'] = [k[0] for k in kids]
            emit(head)
            for cid, act, t, recs, its in kids:
                apply_node(cid, t, recs, its, nextx, act)
            return
    cid = newid()
    head['outcome'] = 'closed'; head['next_x'] = nextx; head['children'] = [cid]; emit(head)
    s.x = nextx
    dfs(cid, s, None)

# ---------- tail bound ----------
def iroot(n, k):
    if n < 2: return n
    x = int(round(n ** (1.0 / k))) if n.bit_length() < 1000 else 1 << ((n.bit_length() + k - 1) // k)
    while x**k > n: x -= 1
    while (x + 1)**k <= n: x += 1
    return x
ALPHA = {}
def alpha(g, k):
    if (g, k) not in ALPHA:
        D = 10**6
        ALPHA[(g, k)] = (F(D, iroot(g * D**k, k)), iroot(g * D**k, k))
    return ALPHA[(g, k)][0]
HITS = {}
def hits_for(K):
    if K in HITS: return HITS[K]
    vals = [1]
    for g in K:
        nv = []
        for v in vals:
            while v < MHIT: nv.append(v); v *= g
        vals = nv
    hs = []; nh = []
    for n in vals:
        d = 4 * n - 3; r = isqrt(d)
        if r * r == d:
            t = (r - 1) // 2
            if t % 2 == 0: nh.append([n, t, 'even'])
            elif t % 3 != 2: nh.append([n, t, 'mod3'])
            elif not isprime(t): nh.append([n, t, 'composite', min(factorint(t))])
            else: hs.append((t, n))
    hs.sort(); nh.sort()
    HITS[K] = (hs, nh, len(vals))
    return HITS[K]
KS = [3, 4, 5, 6, 8, 10, 12, 16, 24]
def mth(Lb, k): return F(iroot(Lb, k) + 1, isqrt(Lb))
def rankin(K, u, x, want=False):
    L = x*x + x + 1; best = None
    for k in KS:
        G = F(1)
        for g in K: G *= 1 / (1 - alpha(g, k))
        ax = alpha(x, k)
        if ax >= 1: continue
        term = mth(L, k) * G * ((1 / (1 - ax))**u - 1) + mth(max(L, MHIT), k) * G
        if best is None or term < best[0]: best = (term, k, G, ax)
    if best is None: return None, None
    pr = None
    if want:
        term, k, G, ax = best
        pr = {'mode': 'theta', 'k': k, 'theta': '1/2-1/%d' % k,
              'alpha': {str(g): [fstr(alpha(g, k)), ALPHA[(g, k)][1], 10**6] for g in K},
              'alpha_x': [fstr(ax), ALPHA[(x, k)][1], 10**6], 'G': fstr(G),
              'mL': fstr(mth(L, k)), 'mM': fstr(mth(max(L, MHIT), k)),
              'L': L, 'M': max(L, MHIT), 'R': fstr(term)}
    return best[0], pr

def tail_factor(U0, S):
    """U0 times the bound of the tail product as the Lean checker tests it (tailOK): the old path
    1/(1 - S) when S < 1 and it gives U < 2; otherwise, with the flag pade and S < 3, the Pade
    path (S^2 + 4 S + 6)/(6 - 2 S); None when no path applies (S >= 1 without the flag)."""
    if S < 1 and U0 / (1 - S) < 2: return U0 / (1 - S)
    if PADE and S < 3: return U0 * (S * S + 4 * S + 6) / (6 - 2 * S)
    if S < 1: return U0 / (1 - S)
    return None

def upper(s, x, hi, want=False):
    a = 1 if s.q is None else 0
    b = EMAX - nexc(s)
    rem3 = V3 - wt(s.S[3])
    capAl = {p: 2 - wt(c) for p, c in s.S.items() if p % 3 == 1}
    capA = sum(capAl.values())
    capXl = {}; K = []
    for p, (D, no3, kmin, ex) in s.Fr.items():
        if p % 3 != 1: continue
        if ex: capXl[p] = max(0, kmin - wt(s.R[p]))
        else: K.append(p)
    capX = sum(capXl.values())
    c = rem3; d = capA + 2 * rem3 + capX + 4 * b   # undecided exceptions: budget 4 each
    eab = a + b; ecd = c + d
    K = tuple(sorted(K)); u = a
    if K and u: raise SystemExit('a generator set K with q undecided is not handled')
    pq = bool(u)      # q undecided: rows of type (e) are pure powers of q
    if pq: ecd += 1   # the row Phi_3(t) = q
    if not want and float(hi) * (x / (x - 1))**eab * ((x*x + x + 1) / (x*x))**ecd > 2.000001:
        return None, None
    U = hi * F(x, x - 1)**eab * F(x*x + x + 1, x*x)**ecd
    pr = None
    if want:
        pr = {'x': x, 'H': fstr(hi), 'a': a, 'b': b, 'c': c, 'd': d,
              'd_items': {'A_capacity': {str(p): v for p, v in capAl.items()}, 'future_A': 2 * rem3,
                          'exact_receivers': {str(p): v for p, v in capXl.items()}},
              'extra_ab': 0, 'extra_cd': 0, 'K': list(K), 'u': u, 'hits': []}
    if not K:
        S = F(0)
        if pq:   # rows q^i, i >= 3 (q^2 is not a row): sum y <= ((x+1)/x)^2 s^-3/(1 - 1/s), s = isqrt(x)
            sx = isqrt(x); S = F((x + 1)**2, x*x) * F(1, sx**3) / (1 - F(1, sx))
            if S >= 1: return None, None
            U = U / (1 - S)
        if want: pr['S'] = fstr(S); pr['U'] = fstr(U); pr['pureq'] = pq
        return U, pr
    hs, nh, nv = hits_for(K)
    if want:
        LOAD['generated'] += nv; LOAD['max_generated'] = max(LOAD['max_generated'], nv)
        nonhits = [list(e) for e in nh]
    for t, n in hs:
        if t >= x and not present(s, t):
            U *= F(n, t * t)
            if want: pr['hits'].append([t, n])
        elif want: nonhits.append([n, t, 'below_x' if t < x else 'listed'])
    if want:
        nonhits.sort()
        LOAD['square_4n3'] += len(nonhits) + len(pr['hits'])
        pr['generated'] = nv; pr['nonhits'] = nonhits
    R, rp = rankin(K, u, x, want)
    if R is None: return None, None
    S = R * F((x + 1)**2, x*x)
    U = tail_factor(U, S)
    if U is None: return None, None
    if want: pr['rankin'] = rp; pr['S'] = fstr(S); pr['U'] = fstr(U)
    return U, pr

# ---------- dfs ----------
def split(s):
    best = None
    for p, (D, no3, kmin, ex) in s.Fr.items():
        if ex or kmin >= KCAP: continue
        g = F(p, p - 1) / sratio(p, kmin)
        if best is None or g > best[0]: best = (g, p)
    if best is None: return None
    p = best[1]; D, no3, kmin, ex = s.Fr[p]
    kind = 'q' if p == s.q else 'e'
    NOTE['splits'] += 1
    out = []
    r, _ = setD(s, p, 1, exact=True)
    if r: out.append(({'role': 'exact', 'prime': p, 'k': kmin},) + r)
    n = nextn(kind, D, no3, kmin + 2)
    if n is not None:
        t = s.copy(); t.Fr[p][2] = n - 1
        out.append(({'role': 'atleast', 'prime': p, 'k': n - 1}, t, [], []))
    return p, kmin, out

def dfs(nid, s, prev):
    lo, hi = lohi(s)
    if hi > 2:
        r = split(s)
        if r is not None:
            p, kmin, kids = r
            STATS['nodes'] += 1
            ids = [newid() for _ in kids]
            emit({'id': nid, 'kind': 'split', 'state': sjson(s), 'prime': p, 'kmin': kmin,
                  'children': ids})
            for cid, (act, t, recs, its) in zip(ids, kids):
                apply_node(cid, t, recs, its, s.x, act)
            return
    st = sjson(s); first = True
    while True:
        STATS['nodes'] += 1; STATS['decide'] += 1
        if STATS['decide'] % 20000 == 0:
            print('decide', STATS['decide'], 'leaves', STATS['leaves'], 'x', s.x, 'q', s.q,
                  'F', sorted(s.Fr), 'maxx', STATS['maxx'], REASONS, round(time.time() - T0), flush=True)
        x = s.x
        while present(s, x): x = nextprime(x)
        s.x = x
        PRIMES_USED.add(x)
        if not landed_ok(s):
            leafrec(nid, s, 'landedL', {'exceptions': excs(s), 'x': x}, rec={'id': nid, 'kind': 'check', 'state': st if first else None, 'prev': prev, 'x': x}); return
        U, _ = upper(s, x, hi)
        if U is not None and U < 2:
            U, pr = upper(s, x, hi, want=True)
            if not U < 2: raise SystemExit('tail bound changed between the two evaluations')
            if x > STATS['maxx']: STATS['maxx'] = x
            TAILS.add((s.q, tuple(sorted(s.Fr)), x))
            leafrec(nid, s, 'deficient', pr, 2 - U, rec={'id': nid, 'kind': 'check', 'state': st if first else None, 'prev': prev, 'x': x}); return
        if x > LIMIT:
            OPEN.append(sjson(s))
            leafrec(nid, s, 'OPEN', {}, rec={'id': nid, 'kind': 'check', 'state': st if first else None, 'prev': prev, 'x': x}); return
        nx = nextprime(x)
        kids = [(newid(),) + r for r in roles(s, x, 0, ['decided', x])]
        aid = newid()
        emit({'id': nid, 'kind': 'decide', 'x': x, 'state': st if first else None, 'prev': prev,
              'roles': roles_note(s, x), 'children': [k[0] for k in kids], 'absent': aid})
        for cid, act, t, recs, its in kids:
            apply_node(cid, t, recs, its, nx, act)
        s.x = nx
        prev = nid; nid = aid; first = False

def root():
    s = St.__new__(St)
    s.x = 5; s.q = None; s.Fr = {}; s.R = {}; s.S = {3: []}; s.exq = set()
    s.sq = F(sig(3, V3), 3**V3)
    return s

T0 = time.time()
if __name__ == '__main__':
    OUT = open('cert_%s.jsonl' % TAG, 'w') if CERT else None
    rid = newid()
    emit({'id': 0, 'kind': 'header', 'root': rid, 'FAM': FAM, 'V3': V3, 'EMAX': EMAX, 'flags': sorted(FLAGS),
          'MHIT': MHIT, 'DMAX': DMAX, 'KCAP': KCAP})
    r = root()
    rec, its = value_rec(r, ['sig', 3, V3])
    apply_node(rid, r, [rec], its, 5, {'role': 'root'})
    if OUT: OUT.close()
    def dist(xs):
        bins = [10**6, 10**9, 10**12, B64, 10**40]
        out = {}
        for v in xs:
            for bnd in bins:
                if v < bnd: out[str(bnd)] = out.get(str(bnd), 0) + 1; break
            else: out['larger'] = out.get('larger', 0) + 1
        return out
    res = {'tag': TAG, 'stats': STATS, 'reasons': REASONS, 'open': len(OPEN), 'notes': NOTE,
           'minmargin': None if MINM[0] is None else [float(MINM[0]), MINM[1]],
           'distinct_q': len(QS), 'distinct_exception_sets': len(PAIRS),
           'distinct_tail_bounds': len(TAILS),
           'primes_used': len(PRIMES_USED), 'primes_dist': dist(PRIMES_USED),
           'max_prime_used': max(PRIMES_USED),
           'factored': len(FACTORED), 'factored_dist': dist(FACTORED),
           'max_factored': max(FACTORED) if FACTORED else None,
           'load': {'cyc_values': LOAD['cyc_values'], 'cyc_distinct': len(LOAD['cyc_distinct']),
                    'generated_total': LOAD['generated'], 'generated_max_leaf': LOAD['max_generated'],
                    'square_4n3_total': LOAD['square_4n3']},
           'secs': round(time.time() - T0, 1)}
    print(json.dumps(res))
    with open('result_%s.json' % TAG, 'w') as fh:
        json.dump(res, fh); fh.write('\n')
        for o in OPEN: fh.write(json.dumps(o) + '\n')
    sys.exit(0 if not OPEN else 1)
