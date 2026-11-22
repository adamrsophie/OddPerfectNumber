# Untrusted helper script for the OddPerfect Lean library.
# Search for the case analysis certificate of the three exception theorem: for each of the
# 102 sorted class triples it splits the constraints on (q, r1, r2, r3) until every leaf
# closes (bound at most 1999/1000), as described in SPEC.md, and writes the certificate.
# Used by: OddPerfect.three_dvd_of_three_exceptions in OddPerfect/ThreeFreeThree.lean, through
# the certificate cert3_final.json, which gen_lean.py turns into the data modules
# OddPerfect/ThreeFreeThreeData01.lean .. ThreeFreeThreeData11.lean.
# Run: python3 -I cert3f.py cert3_final.json   (without an argument it only prints the totals)
# Rule switches in the environment variable RULES (comma separated list). When RULES is not
# set, all four switches are on; these are the rules of the certificate used in the library.
#   noub      ordering only raises the lower bound of later slots (no upper bound on earlier ones)
#   noinj     C: every prime factor accepted by some slot, each factor tested on its own
#   noprimex  exact part: hit when 4n - 3 = (2s + 1)^2 with s >= CAP (no primality, no s mod 3)
#   noprimem  least value: least integer with the class residue (no primality test)
# Requires: Python 3 standard library. Deterministic: with the default rules the output is
# byte for byte the file whose SHA-256 is in cert3_final.sha256. Running time: about five
# seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.
import sys, os, json, time
from fractions import Fraction as F
from itertools import combinations_with_replacement, product, permutations
from math import isqrt

CAP, M, D = 300, 5, 1000
THRESH = F(1999, 1000)
RULES = set(x for x in os.environ.get('RULES', 'noub,noinj,noprimex,noprimem').split(',') if x)
OUT = sys.argv[1] if len(sys.argv) > 1 else None
NODE_BUDGET = 20000


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def factorization(n):
    out, d = [], 2
    while d * d <= n:
        e = 0
        while n % d == 0:
            n //= d
            e += 1
        if e:
            out.append([d, e])
        d += 1
    if n > 1:
        out.append([n, 1])
    return out


TABLE = {s: factorization(s * s + s + 1) for s in range(5, CAP) if s % 3 == 2 and is_prime(s)}
CLASSES = ['5', '7', '13', '19', '31', '37', '43', 'n2', 'big']
NAMES = ['q', 'r1', 'r2', 'r3']
K = F(CAP + 1, CAP) ** 2

_W = {}
def weight(m):
    """Least n/d with d <= D and n^2 m >= d^2."""
    if m not in _W:
        best = None
        for d in range(1, D + 1):
            n = isqrt(d * d // m)
            while n * n * m < d * d:
                n += 1
            if best is None or F(n, d) < best:
                best = F(n, d)
        _W[m] = best
    return _W[m]


def res_ok(kind, f):
    return {'q': f % 12 == 1, 'n2': f % 3 == 2, 'big': f % 3 == 1}[kind]


def mk_root(t):
    slots = [dict(kind='q', val=None, lb=13, ub=None, excl=(), grp='q')]
    for c in t:
        if c in ('n2', 'big'):
            slots.append(dict(kind=c, val=None, lb=11 if c == 'n2' else 61, ub=None, excl=(), grp=c))
        else:
            slots.append(dict(kind='fix', val=int(c), lb=None, ub=None, excl=(), grp=c))
    return slots


def pinned_vals(slots):
    return {s['val'] for s in slots if s['val'] is not None}


def least_values(slots):
    """(mins, scans) or None if empty. scans[i] = length of the scanned interval."""
    pv = pinned_vals(slots)
    mins, scans, last = [], [], {}
    for sl in slots:
        prev = last.get(sl['grp'])
        if sl['val'] is not None:
            if prev is not None and sl['val'] <= prev:
                return None
            mins.append(sl['val'])
            scans.append(0)
        else:
            start = max(sl['lb'], prev + 1 if prev is not None else 0)
            p = start
            while not ((('noprimem' in RULES) or is_prime(p)) and res_ok(sl['kind'], p)
                       and p not in sl['excl'] and p not in pv):
                p += 1
                if sl['ub'] is not None and p > sl['ub']:
                    return None
            if sl['ub'] is not None and p > sl['ub']:
                return None
            mins.append(p)
            scans.append(p - start)
        last[sl['grp']] = mins[-1]
    return mins, scans


def accepts(sl, f, pv, m):
    """f is a prime (a factor from the table)."""
    if sl['val'] is not None:
        return f == sl['val']
    return (res_ok(sl['kind'], f) and f >= m and (sl['ub'] is None or f <= sl['ub'])
            and f not in sl['excl'] and f not in pv)


def leaf_C(slots, mins):
    pv = pinned_vals(slots)
    C = {}
    for s, fac in TABLE.items():
        if s in pv:
            continue
        fs = [p for p, e in fac]
        if 'noinj' in RULES:
            asg = {}
            for f in fs:
                js = [j for j in range(4) if accepts(slots[j], f, pv, mins[j])]
                if not js:
                    break
                asg[str(f)] = [NAMES[j] for j in js]
            else:
                C[s] = asg
            continue
        if len(fs) > 4:
            continue
        for perm in permutations(range(4), len(fs)):
            if all(accepts(slots[j], f, pv, mins[j]) for f, j in zip(fs, perm)):
                C[s] = {str(f): NAMES[j] for f, j in zip(fs, perm)}
                break
    return C


def is_target(sl, m):
    return sl['kind'] in ('q', 'big') or (sl['kind'] == 'fix' and m % 3 == 1)


def evaluate(slots):
    lv = least_values(slots)
    if lv is None:
        return dict(status='vacuous')
    mins, scans = lv
    C = leaf_C(slots, mins)
    tg = [is_target(sl, m) for sl, m in zip(slots, mins)]
    ws = [weight(m) if t else F(0) for t, m in zip(tg, mins)]
    exact = [t and sl['val'] is not None for t, sl in zip(tg, slots)]
    floor = F(mins[0], mins[0] - 1)
    for m in mins[1:]:
        floor *= F(m, m - 1)
    for s in C:
        floor *= F(s * s + s + 1, s * s)
    c = F(1, CAP)
    E, R, wit = F(0), F(0), []
    for v in product(*[range(M) if t else range(1) for t in tg]):
        if all(a % 2 == 0 for a in v):
            continue
        w = F(1)
        for x, a in zip(ws, v):
            if a:
                w *= x ** a
        if not all(a == 0 or e for a, e in zip(v, exact)):
            R += min(c, w)
            continue
        n = 1
        for sl, a in zip(slots, v):
            if a:
                n *= sl['val'] ** a
        d = 4 * n - 3
        r = isqrt(d)
        if r * r == d:
            s = (r - 1) // 2
            hit = s >= CAP and ('noprimex' in RULES or (s % 3 == 2 and is_prime(s)))
            if hit:
                E += F(s + 1, s * s)
                wit.append(dict(v=list(v), kind='hit', s=s))
            else:
                wit.append(dict(v=list(v), kind='small' if s < CAP else 'nonprime', s=s))
        else:
            wit.append(dict(v=list(v), kind='nonsquare', r=r))
    num = sum((w ** M for w in ws), F(0))
    den = F(1)
    for w in ws:
        den *= (1 - w)
    Tl = num / den
    X = E + K * (R + Tl)
    bound = None if X >= 1 else floor / (1 - X)
    st = 'closed' if bound is not None and bound <= THRESH else 'open'
    return dict(status=st, mins=mins, scans=scans, C=C, tg=tg, ws=ws, exact=exact, floor=floor,
                E=E, R=R, Tl=Tl, X=X, bound=bound, wit=wit)


def split_choice(slots, rec):
    pv = pinned_vals(slots)
    mins = rec['mins']
    facs = {s: [p for p, e in TABLE[s]] for s in rec['C']}
    opts = []
    for i, sl in enumerate(slots):
        if sl['val'] is not None or sl['kind'] == 'n2':
            continue
        cands = sorted({f for fs in facs.values() for f in fs if accepts(sl, f, pv, mins[i])})
        if not cands:
            continue
        mass = F(1)
        for s, fs in facs.items():
            if any(f in cands for f in fs):
                mass *= F(s * s + s + 1, s * s)
        opts.append((i, cands, mass))
    if opts:
        i, c, _ = max(opts, key=lambda x: (x[2], -x[0]))
        return i, c, 'relevant'
    for i, sl in enumerate(slots):
        if sl['val'] is None and sl['kind'] in ('q', 'big'):
            return i, [mins[i]], 'peel'
    return None, None, None


def pin(slots, i, f):
    ch = [dict(s) for s in slots]
    ch[i]['val'] = f
    for j in range(4):
        if j != i and ch[j]['grp'] == ch[i]['grp'] and ch[j]['val'] is None:
            if j > i:
                ch[j]['lb'] = max(ch[j]['lb'], f + 1)
            elif 'noub' not in RULES:
                ch[j]['ub'] = f - 1 if ch[j]['ub'] is None else min(ch[j]['ub'], f - 1)
    return ch


def P(x):
    return [x.numerator, x.denominator]


def slot_json(sl, m=None):
    d = dict(name=None, kind=sl['kind'], cls=sl['grp'])
    if sl['val'] is not None:
        d['pinned'] = sl['val']
    else:
        d.update(lb=sl['lb'], ub=sl['ub'], excluded=sorted(sl['excl']))
        if m is not None:
            d['least'] = m
    return d


def leaf_json(slots, rec, nid):
    out = dict(id=nid, status=rec['status'])
    out['slots'] = [dict(slot_json(sl, rec.get('mins', [None] * 4)[i] if rec['status'] != 'vacuous' else None), name=NAMES[i])
                    for i, sl in enumerate(slots)]
    if rec['status'] == 'vacuous':
        return out
    out['C'] = [dict(s=s, n=s * s + s + 1, factorization=TABLE[s], assignment=a) for s, a in sorted(rec['C'].items())]
    out['target'] = rec['tg']
    out['weights'] = [P(w) for w in rec['ws']]
    out['exact_coords'] = rec['exact']
    out['witnesses'] = rec['wit']
    for k in ('floor', 'E', 'R', 'Tl', 'X', 'bound'):
        out[k] = P(rec[k])
    return out


def solve(slots, ctx):
    ctx['nodes'] += 1
    nid = ctx['nodes']
    if nid > NODE_BUDGET:
        raise RuntimeError('budget')
    rec = evaluate(slots)
    if rec['status'] in ('closed', 'vacuous'):
        ctx['leaves'] += 1
        if rec['status'] == 'closed':
            ctx['scan'] = max(ctx['scan'], max(rec['scans']))
            ub_used = any(sl['ub'] is not None for sl in slots)
            ctx['ub_leaves'] += ub_used
            key = (rec['bound'], nid)
            if key > ctx['worst']:
                ctx['worst'] = key
            ctx['stats'].append(dict(id=nid, nopin=not any(rec['exact']), Epos=rec['E'] > 0,
                                     ub=ub_used, bound=rec['bound']))
        else:
            ctx['vac'] += 1
        return dict(id=nid, leaf=leaf_json(slots, rec, nid)) if ctx['json'] else dict(id=nid)
    i, cands, how = split_choice(slots, rec)
    if i is None:
        ctx['fails'].append((nid, slots, rec))
        ctx['leaves'] += 1
        return dict(id=nid, leaf=leaf_json(slots, rec, nid)) if ctx['json'] else dict(id=nid)
    node = dict(id=nid, split=dict(slot=NAMES[i], pins=cands, rule=how))
    kids = [solve(pin(slots, i, f), ctx) for f in cands]
    g = [dict(s) for s in slots]
    g[i]['excl'] = tuple(sorted(set(g[i]['excl']) | set(cands)))
    kids.append(solve(g, ctx))
    node['children'] = kids
    ctx['splits'] += 1
    return node


def main():
    t0 = time.time()
    triples = [t for t in combinations_with_replacement(CLASSES, 3)
               if not any(t.count(c) > 1 for c in CLASSES[:7])]
    ctx = dict(nodes=0, leaves=0, vac=0, splits=0, fails=[], worst=(F(0), 0), scan=0,
               ub_leaves=0, stats=[], json=OUT is not None)
    trees = []
    for t in triples:
        try:
            tree = solve(mk_root(t), ctx)
        except RuntimeError:
            print(f"rules={sorted(RULES)} BUDGET exhausted at {t}")
            return
        trees.append(dict(triple=list(t), root=[dict(slot_json(s), name=NAMES[i]) for i, s in enumerate(mk_root(t))], tree=tree))
    w, wid = ctx['worst']
    print(f"rules={sorted(RULES)} leaves={ctx['leaves']} vacuous={ctx['vac']} splits={ctx['splits']} "
          f"fails={len(ctx['fails'])} worst={float(w):.6f} (leaf {wid}) longest_scan={ctx['scan']} "
          f"ub_leaves={ctx['ub_leaves']} time={time.time() - t0:.0f}s")
    for nid, slots, rec in ctx['fails'][:5]:
        print('  FAIL', nid, [slot_json(s) for s in slots], rec.get('bound') and float(rec['bound']))
    if OUT:
        st = ctx['stats']
        pilot = dict(
            no_pinned_target=next(x['id'] for x in st if x['nopin']),
            E_positive=next(x['id'] for x in st if x['Epos']),
            thinnest=wid,
            uses_ub=next((x['id'] for x in st if x['ub']), None))
        doc = dict(format='cert3_final v1', rules=sorted(RULES), cap=CAP, box=M,
                   k=P(K), threshold=P(THRESH), weight_denominator_max=D,
                   classes=CLASSES, table={str(s): v for s, v in TABLE.items()},
                   leaf_count=ctx['leaves'], split_count=ctx['splits'], worst_bound=P(w), worst_leaf=wid,
                   pilot_leaves=pilot, triples=trees)
        with open(OUT, 'w') as fh:
            json.dump(doc, fh, separators=(',', ':'))
        print('  pilot', pilot)
        print('  worst exact', w)


if __name__ == '__main__':
    main()
