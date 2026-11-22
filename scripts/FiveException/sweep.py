"""Five slot one sided search (q, r1..r4), exact rationals, mod version: small ordinary primes
enter with s/(s - 1) and large ones with fv(s) times the tail factor 1/(1 - 1/(2 (CAP - 1)^2)).
Env: CAP (300), BOX (5), TAIL (parity|union), BUDGET (nodes per quadruple), THRESH (num/den, default 2 strict),
     STRONG=1 (injective C, prime-aware least values and exact part), N2PEEL=1 (allow peeling n2 slots).
Usage: python3 -I sweep.py OUT.jsonl QUAD [QUAD ...]   (QUAD like 5_7_13_19 or 'all' or 'shard:i/n')"""
import sys, os, json, time
from fractions import Fraction as F
from itertools import combinations_with_replacement, product, permutations
from math import isqrt

CAP = int(os.environ.get('CAP', 300))
M = int(os.environ.get('BOX', 5))
BOXPIN = int(os.environ.get('BOXPIN', M))  # box size used at leaves whose target slots are all pinned
TAIL = os.environ.get('TAIL', 'parity')
BUDGET = int(os.environ.get('BUDGET', 3000))
STRONG = os.environ.get('STRONG', '1') == '1'
N2PEEL = os.environ.get('N2PEEL', '1') == '1'
th = os.environ.get('THRESH', '2/1').split('/')
THRESH = F(int(th[0]), int(th[1]))
D = 1000
NS = 5
NAMES = ['q', 'r1', 'r2', 'r3', 'r4']
CLASSES = ['5', '7', '13', '19', '31', '37', '43', 'n2', 'big']
K = F(CAP + 1, CAP) ** 2
TAILF = 1 / (1 - F(1, 2 * (CAP - 1) ** 2))  # product of s^3/(s^3 - 1) over s >= CAP, mod version


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
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

_W = {}
def weight(m):
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
    slots = [dict(kind='q', val=None, lb=13, excl=(), grp='q')]
    for c in t:
        if c in ('n2', 'big'):
            slots.append(dict(kind=c, val=None, lb=11 if c == 'n2' else 61, excl=(), grp=c))
        else:
            slots.append(dict(kind='fix', val=int(c), lb=None, excl=(), grp=c))
    return slots


def pinned_vals(slots):
    return {s['val'] for s in slots if s['val'] is not None}


def least_values(slots):
    pv = pinned_vals(slots)
    mins, last = [], {}
    for sl in slots:
        prev = last.get(sl['grp'])
        if sl['val'] is not None:
            if prev is not None and sl['val'] <= prev:
                return None
            mins.append(sl['val'])
        else:
            p = max(sl['lb'], prev + 1 if prev is not None else 0)
            while not ((not STRONG or is_prime(p)) and res_ok(sl['kind'], p)
                       and p not in sl['excl'] and p not in pv):
                p += 1
            mins.append(p)
        last[sl['grp']] = mins[-1]
    return mins


def accepts(sl, f, pv, m):
    if sl['val'] is not None:
        return f == sl['val']
    return res_ok(sl['kind'], f) and f >= m and f not in sl['excl'] and f not in pv


def leaf_C(slots, mins):
    pv = pinned_vals(slots)
    C = []
    for s, fac in TABLE.items():
        if s in pv:
            continue
        fs = [p for p, e in fac]
        if STRONG:
            if len(fs) > NS:
                continue
            if any(all(accepts(slots[j], f, pv, mins[j]) for f, j in zip(fs, pm))
                   for pm in permutations(range(NS), len(fs))):
                C.append(s)
        elif all(any(accepts(slots[j], f, pv, mins[j]) for j in range(NS)) for f in fs):
            C.append(s)
    return C


def is_target(sl, m):
    return sl['kind'] in ('q', 'big') or (sl['kind'] == 'fix' and m % 3 == 1)


def evaluate(slots):
    mins = least_values(slots)
    if mins is None:
        return dict(status='vacuous')
    C = leaf_C(slots, mins)
    tg = [is_target(sl, m) for sl, m in zip(slots, mins)]
    ws = [weight(m) if t else F(0) for t, m in zip(tg, mins)]
    exact = [t and sl['val'] is not None for t, sl in zip(tg, slots)]
    rho = F(1)
    for m in mins:
        rho *= F(m, m - 1)
    cprod = F(1)
    for s in C:
        cprod *= F(s, s - 1)
    floor = rho * cprod * TAILF
    if floor >= THRESH:
        return dict(status='open', mins=mins, C=C, floor=floor, rho=rho, cprod=cprod,
                    E=None, kR=None, kTl=None, bound=None, tg=tg)
    c = F(1, CAP)
    E, R, sw = F(0), F(0), F(0)
    Mloc = BOXPIN if all(e for e, t in zip(exact, tg) if t) else M
    for v in product(*[range(Mloc) if t else range(1) for t in tg]):
        if all(a % 2 == 0 for a in v):
            continue
        w = F(1)
        for x, a in zip(ws, v):
            if a:
                w *= x ** a
        sw += w
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
            if s >= CAP and (not STRONG or (s % 3 == 2 and is_prime(s))):
                E += F(s + 1, s * s)
    if TAIL == 'parity':
        a = b = F(1)
        for w in ws:
            a /= 1 - w
            b /= 1 - w * w
        Tl = a - b - sw
    else:
        Tl = sum((w ** Mloc for w in ws), F(0))
        for w in ws:
            Tl /= 1 - w
    X = E + K * (R + Tl)
    bound = None if X >= 1 else floor / (1 - X)
    st = 'closed' if bound is not None and bound < THRESH else 'open'
    return dict(status=st, mins=mins, C=C, floor=floor, rho=rho, cprod=cprod, E=E, kR=K * R,
                kTl=K * Tl, bound=bound, tg=tg)


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
        return i, c
    kinds = ('q', 'big', 'n2') if N2PEEL else ('q', 'big')
    # peel the free slot with the largest factor m/(m-1)
    best = None
    for i, sl in enumerate(slots):
        if sl['val'] is None and sl['kind'] in kinds:
            if best is None or mins[i] < mins[best]:
                best = i
    if best is None:
        return None, None
    return best, [mins[best]]


def pin(slots, i, f):
    ch = [dict(s) for s in slots]
    ch[i]['val'] = f
    for j in range(i + 1, NS):
        if ch[j]['grp'] == ch[i]['grp'] and ch[j]['val'] is None:
            ch[j]['lb'] = max(ch[j]['lb'], f + 1)
    return ch


def desc(slots, mins):
    out = []
    for sl, m in zip(slots, mins or [None] * NS):
        if sl['val'] is not None:
            out.append(str(sl['val']) if sl['kind'] == 'fix' else f"{sl['kind']}={sl['val']}")
        else:
            out.append(f"{sl['kind']}>={m}")
    return ' '.join(out)


def fl(x):
    return None if x is None else float(x)


class Budget(Exception):
    pass


def solve(slots, ctx, depth):
    ctx['nodes'] += 1
    if ctx['nodes'] > BUDGET:
        raise Budget
    rec = evaluate(slots)
    if rec['status'] in ('closed', 'vacuous'):
        ctx['leaves'] += 1
        ctx['depth'] = max(ctx['depth'], depth)
        if rec['status'] == 'closed' and rec['bound'] > ctx['worst']:
            ctx['worst'] = rec['bound']
            ctx['worst_leaf'] = desc(slots, rec['mins'])
        return
    i, cands = split_choice(slots, rec)
    if i is None:
        ctx['fails'].append(dict(leaf=desc(slots, rec['mins']), floor=float(rec['floor']),
                                 rho=float(rec['rho']), cprod=float(rec['cprod']),
                                 C=rec['C'], E=fl(rec['E']), kR=fl(rec['kR']), kTl=fl(rec['kTl']),
                                 bound=fl(rec['bound'])))
        ctx['leaves'] += 1
        return
    for f in cands:
        solve(pin(slots, i, f), ctx, depth + 1)
    g = [dict(s) for s in slots]
    g[i]['excl'] = tuple(sorted(set(g[i]['excl']) | set(cands)))
    solve(g, ctx, depth + 1)


def quads():
    return [t for t in combinations_with_replacement(CLASSES, 4)
            if not any(t.count(c) > 1 for c in CLASSES[:7])]


def main():
    out = sys.argv[1]
    sel = sys.argv[2:]
    Q = quads()
    if sel == ['count']:
        print(len(Q))
        return
    if sel == ['all']:
        todo = Q
    elif sel and sel[0].startswith('shard:'):
        i, n = map(int, sel[0][6:].split('/'))
        todo = Q[i::n]
    else:
        todo = [tuple(s.split('_')) for s in sel]
    for t in todo:
        t0 = time.time()
        root = evaluate(mk_root(t))
        ctx = dict(nodes=0, leaves=0, depth=0, worst=F(0), worst_leaf=None, fails=[])
        status = 'closed'
        try:
            solve(mk_root(t), ctx, 0)
        except Budget:
            status = 'budget'
        if ctx['fails']:
            status = 'FAILS' if status == 'closed' else status
        rec = dict(quad='_'.join(t), status=status, leaves=ctx['leaves'], nodes=ctx['nodes'],
                   depth=ctx['depth'], worst=float(ctx['worst']), worst_exact=str(ctx['worst']),
                   worst_leaf=ctx['worst_leaf'],
                   root_bound=fl(root.get('bound')), root_floor=float(root['floor']),
                   nfails=len(ctx['fails']), fails=ctx['fails'], secs=round(time.time() - t0, 1),
                   cap=CAP, box=M, boxpin=BOXPIN, tail=TAIL, strong=STRONG)
        with open(out, 'a') as fh:
            fh.write(json.dumps(rec) + '\n')
        print(rec['quad'], status, 'leaves', rec['leaves'], 'nodes', rec['nodes'], 'depth', rec['depth'],
              'worst', round(rec['worst'], 6), 'fails', rec['nfails'], f"{rec['secs']}s", flush=True)


if __name__ == '__main__':
    import threading
    sys.setrecursionlimit(200000)
    threading.stack_size(1 << 30)
    th = threading.Thread(target=main)
    th.start()
    th.join()
