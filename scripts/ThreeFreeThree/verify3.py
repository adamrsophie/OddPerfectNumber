# Untrusted helper script for the OddPerfect Lean library.
# Second checker for the certificate cert3_final.json, written from SPEC.md alone (it shares
# no code with cert3f.py or check3.py). It performs every check listed in Section 6 of
# SPEC.md, including the corrected bound of Section 4, with exact arithmetic throughout (int
# and Fraction; floats only for display), and stops at the first failed check, naming it.
# With --tamper it applies 13 corruptions to the certificate, one at a time, and reports
# whether each is rejected.
# Used by: the certificate behind OddPerfect/ThreeFreeThreeData01.lean .. Data11.lean and
# OddPerfect/ThreeFreeThree.lean.
# Run: python3 -I verify3.py cert3_final.json [--tamper]   (or cert3_final.json.xz)
# Requires: Python 3 standard library. Deterministic. Running time: about two seconds; with
# --tamper about four seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.
import json
import sys
from fractions import Fraction
from itertools import product, combinations_with_replacement
from math import isqrt

CAP = 300
BOX = 5
K = Fraction(301, 300) ** 2
THRESH = Fraction(1999, 1000)
# Corrected bound (exponents only known to be 2 modulo 3): each s in C contributes
# s/(s - 1) instead of fv(s), and the ordinary primes s >= CAP contribute at most the tail
# factor TAIL = 1/(1 - 1/(2*299^2)) (from sum_{s >= 300} s^-3 <= 1/(2*299^2)). The corrected
# bound must be < 2; the Lean checker tests <= 2.
TAIL = Fraction(2 * 299 ** 2, 2 * 299 ** 2 - 1)
WDEN = 1000
CLASSES = ['5', '7', '13', '19', '31', '37', '43', 'n2', 'big']
FIXED = CLASSES[:7]
NAMES = ['q', 'r1', 'r2', 'r3']


class VerifyError(Exception):
    pass


def need(cond, check, msg=''):
    if not cond:
        raise VerifyError('[%s] %s' % (check, msg))


def isint(x):
    return type(x) is int


def frac(x, check):
    need(isinstance(x, list) and len(x) == 2 and isint(x[0]) and isint(x[1]) and x[1] > 0,
         check, 'bad fraction %r' % (x,))
    return Fraction(x[0], x[1])


def read_cert(path):
    """Bytes of the certificate, plain or compressed with xz (file name ending in .xz)."""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as fh:
            return fh.read()
    with open(path, 'rb') as fh:
        return fh.read()


# Arithmetic.

def factor(n):
    """Full factorization by trial division: list of [p, e], p increasing."""
    out = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out.append([d, e])
        d += 1
    if n > 1:
        out.append([n, 1])
    return out


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


TABLE_PRIMES = [s for s in range(5, CAP) if s % 3 == 2 and is_prime(s)]
TABLE = {s: factor(1 + s + s * s) for s in TABLE_PRIMES}


def fv(s):
    return Fraction(s * s + s + 1, s * s)


# Constraint model.
# slot: dict name, kind, cls, pinned (int or None), lb, excluded (frozenset)

def root_slots(triple):
    slots = [dict(name='q', kind='q', cls='q', pinned=None, lb=13, excluded=frozenset())]
    for name, c in zip(NAMES[1:], triple):
        if c in FIXED:
            slots.append(dict(name=name, kind='fix', cls=c, pinned=int(c), lb=None, excluded=None))
        elif c == 'n2':
            slots.append(dict(name=name, kind='n2', cls='n2', pinned=None, lb=11, excluded=frozenset()))
        elif c == 'big':
            slots.append(dict(name=name, kind='big', cls='big', pinned=None, lb=61, excluded=frozenset()))
        else:
            raise VerifyError('[triples] unknown class %r' % c)
    return slots


def residue_ok(kind, x):
    if kind == 'q':
        return x % 12 == 1
    if kind == 'n2':
        return x % 3 == 2
    if kind == 'big':
        return x % 3 == 1
    raise VerifyError('[slots] free slot of kind %r has no residue test' % kind)


def pinned_values(slots):
    return {s['pinned'] for s in slots if s['pinned'] is not None}


def least_values(slots):
    """Returns (list of m, vacuous flag)."""
    pv = pinned_values(slots)
    last = {}
    ms = []
    vac = False
    for s in slots:
        prev = last.get(s['cls'])
        if s['pinned'] is not None:
            m = s['pinned']
            if prev is not None and m <= prev:
                vac = True
        else:
            x = s['lb'] if prev is None else max(s['lb'], prev + 1)
            while not (residue_ok(s['kind'], x) and x not in s['excluded'] and x not in pv):
                x += 1
            m = x
        last[s['cls']] = m
        ms.append(m)
    return ms, vac


def accepts(slot, m, f, pv):
    if slot['pinned'] is not None:
        return f == slot['pinned']
    return residue_ok(slot['kind'], f) and f >= m and f not in slot['excluded'] and f not in pv


def compute_C(slots, ms):
    pv = pinned_values(slots)
    C = {}
    for s in TABLE_PRIMES:
        if s in pv:
            continue
        assign = {}
        ok = True
        for p, _ in TABLE[s]:
            acc = [sl['name'] for sl, m in zip(slots, ms) if accepts(sl, m, p, pv)]
            if not acc:
                ok = False
                break
            assign[p] = acc
        if ok:
            C[s] = assign
    return C


def apply_split(slots, idx, pins):
    """Children constraint lists: one per pin, then generic."""
    kids = []
    cls = slots[idx]['cls']
    for p in pins:
        ch = [dict(s) for s in slots]
        ch[idx]['pinned'] = p
        ch[idx]['lb'] = None
        ch[idx]['excluded'] = None
        for j in range(idx + 1, 4):
            if ch[j]['pinned'] is None and ch[j]['cls'] == cls:
                ch[j]['lb'] = max(ch[j]['lb'], p + 1)
        kids.append(ch)
    g = [dict(s) for s in slots]
    g[idx]['excluded'] = g[idx]['excluded'] | frozenset(pins)
    kids.append(g)
    return kids


# Leaf computation.

def leaf_quantities(slots):
    """Everything a leaf needs, from the constraints only."""
    ms, vac = least_values(slots)
    C = compute_C(slots, ms)
    target = [sl['kind'] in ('q', 'big') or (sl['pinned'] is not None and m % 3 == 1)
              for sl, m in zip(slots, ms)]
    exact = [t and sl['pinned'] is not None for t, sl in zip(target, slots)]
    floor = Fraction(1)
    for m in ms:
        floor *= Fraction(m, m - 1)
    cfloor = floor
    for s in C:
        floor *= fv(s)
        cfloor *= Fraction(s, s - 1)
    return dict(ms=ms, vac=vac, C=C, target=target, exact=exact, floor=floor, cfloor=cfloor)


def box_vectors(target):
    rngs = [range(BOX) if t else (0,) for t in target]
    for v in product(*rngs):
        if all(x % 2 == 0 for x in v):
            continue
        yield v


def check_witness(w, v, n, check):
    D = 4 * n - 3
    need(isinstance(w, dict) and w.get('v') == list(v), check, 'witness vector %r != expected %r' % (w.get('v') if isinstance(w, dict) else w, list(v)))
    kind = w.get('kind')
    if kind in ('hit', 'small'):
        need(set(w) == {'v', 'kind', 's'}, check, 'bad witness keys %r' % sorted(w))
        s = w['s']
        need(isint(s) and s >= 0, check, 'bad s')
        need((2 * s + 1) ** 2 == D, check, '%s witness at %r: (2s+1)^2 != 4n-3' % (kind, v))
        if kind == 'hit':
            need(s >= CAP, check, 'hit witness at %r has s=%d < %d' % (v, s, CAP))
            return Fraction(s + 1, s * s)
        need(s < CAP, check, 'small witness at %r has s=%d >= %d' % (v, s, CAP))
        return Fraction(0)
    if kind == 'nonsquare':
        need(set(w) == {'v', 'kind', 'r'}, check, 'bad witness keys %r' % sorted(w))
        r = w['r']
        need(isint(r) and r >= 0, check, 'bad r')
        need(r * r < D < (r + 1) * (r + 1), check, 'nonsquare witness at %r: not r^2 < 4n-3 < (r+1)^2 (r=%d)' % (v, r))
        return Fraction(0)
    raise VerifyError('[%s] unknown witness kind %r' % (check, kind))


def check_leaf(node, slots, stats):
    lid = node['id']
    L = node['leaf']
    ck = lambda name: 'leaf %d: %s' % (lid, name)
    need(isinstance(L, dict), ck('format'))
    need(L.get('id') == lid, ck('id'), 'leaf id %r != node id %r' % (L.get('id'), lid))
    need(L.get('status') == 'closed', ck('status'), repr(L.get('status')))
    Q = leaf_quantities(slots)
    ms = Q['ms']
    if Q['vac']:
        stats['vacuous'] += 1
    # slots
    fs = L['slots']
    need(isinstance(fs, list) and len(fs) == 4, ck('slots'), 'need four slots')
    for sl, m, f in zip(slots, ms, fs):
        if sl['pinned'] is not None:
            exp = dict(name=sl['name'], kind=sl['kind'], cls=sl['cls'], pinned=sl['pinned'])
            need(f == exp, ck('slots'), 'stored %r != rebuilt %r' % (f, exp))
        else:
            need(isinstance(f, dict) and set(f) == {'name', 'kind', 'cls', 'lb', 'ub', 'excluded', 'least'},
                 ck('slots'), 'free slot keys %r' % (sorted(f) if isinstance(f, dict) else f))
            need(f['name'] == sl['name'] and f['kind'] == sl['kind'] and f['cls'] == sl['cls'],
                 ck('slots'), 'name/kind/cls mismatch %r' % f)
            need(f['lb'] == sl['lb'], ck('slots lb'), 'slot %s stored lb %r != rebuilt %r' % (sl['name'], f['lb'], sl['lb']))
            need(f['ub'] is None, ck('slots ub'), 'ub must be null')
            ex = f['excluded']
            need(isinstance(ex, list) and all(isint(x) for x in ex) and len(set(ex)) == len(ex),
                 ck('slots excluded'), 'bad excluded list')
            need(set(ex) == sl['excluded'], ck('slots excluded'),
                 'slot %s stored excluded %r != rebuilt %r' % (sl['name'], sorted(ex), sorted(sl['excluded'])))
            need(f['least'] == m, ck('least value'), 'slot %s stored least %r != recomputed %r' % (sl['name'], f['least'], m))
    # C
    Cf = L['C']
    need(isinstance(Cf, list), ck('C'))
    seen = set()
    for rec in Cf:
        need(isinstance(rec, dict) and set(rec) == {'s', 'n', 'factorization', 'assignment'}, ck('C'), 'bad record keys')
        s = rec['s']
        need(isint(s) and s not in seen, ck('C'), 'bad or duplicate s %r' % (s,))
        seen.add(s)
        need(s in Q['C'], ck('C'), 's=%r stored in C but not in recomputed C' % s)
        need(rec['n'] == 1 + s + s * s, ck('C'), 'n mismatch for s=%d' % s)
        need(rec['factorization'] == TABLE[s], ck('C'), 'factorization mismatch for s=%d' % s)
        a = rec['assignment']
        exp = Q['C'][s]
        need(isinstance(a, dict) and set(a) == {str(p) for p in exp}, ck('C assignment'), 'keys for s=%d' % s)
        for p, names in exp.items():
            got = a[str(p)]
            need(isinstance(got, list) and sorted(got) == sorted(names) and len(set(got)) == len(got),
                 ck('C assignment'), 's=%d factor %d: stored %r != recomputed %r' % (s, p, got, names))
    need(seen == set(Q['C']), ck('C'), 'stored C %r != recomputed C %r' % (sorted(seen), sorted(Q['C'])))
    # targets, exact
    need(L['target'] == Q['target'], ck('target'), 'stored %r != recomputed %r' % (L['target'], Q['target']))
    need(L['exact_coords'] == Q['exact'], ck('exact_coords'), 'stored %r != recomputed %r' % (L['exact_coords'], Q['exact']))
    # weights
    ws = L['weights']
    need(isinstance(ws, list) and len(ws) == 4, ck('weights'))
    W = [frac(x, ck('weights')) for x in ws]
    for i in range(4):
        if Q['target'][i]:
            need(0 < W[i] < 1, ck('weight admissibility'), 'slot %s weight %s not in (0,1)' % (NAMES[i], W[i]))
            need(W[i] * W[i] * ms[i] >= 1, ck('weight admissibility'),
                 'slot %s: w^2 * m = %s < 1 (w=%s, m=%d)' % (NAMES[i], W[i] * W[i] * ms[i], W[i], ms[i]))
            need(W[i].denominator <= WDEN, ck('weight denominator'), 'slot %s denominator %d' % (NAMES[i], W[i].denominator))
        else:
            need(W[i] == 0, ck('weight admissibility'), 'non-target slot %s has weight %s' % (NAMES[i], W[i]))
    # box, exact part, witnesses, E, R
    tgt, exa = Q['target'], Q['exact']
    pins = [sl['pinned'] for sl in slots]
    nums = [w.numerator for w in W]
    dens = [w.denominator for w in W]
    Lden = 1
    for i in range(4):
        if tgt[i]:
            Lden *= dens[i] ** (BOX - 1)
    Rint = 0
    Rcap = 0
    E = Fraction(0)
    wit = L['witnesses']
    need(isinstance(wit, list), ck('witnesses'))
    wi = 0
    nbox = 0
    for v in box_vectors(tgt):
        nbox += 1
        if all(v[i] == 0 for i in range(4) if tgt[i] and not exa[i]):
            n = 1
            for i in range(4):
                if exa[i]:
                    n *= pins[i] ** v[i]
            need(wi < len(wit), ck('witnesses'), 'missing witness for exact vector %r' % (v,))
            e = check_witness(wit[wi], v, n, ck('witnesses'))
            if e:
                stats['hits'] += 1
            E += e
            wi += 1
        else:
            num = 1
            den = 1
            for i in range(4):
                if v[i]:
                    num *= nums[i] ** v[i]
                    den *= dens[i] ** v[i]
            if CAP * num >= den:
                Rcap += 1
            else:
                Rint += num * (Lden // den)
    need(wi == len(wit), ck('witnesses'), '%d extra witnesses' % (len(wit) - wi))
    stats['maxbox'] = max(stats['maxbox'], nbox)
    R = Fraction(Rint, Lden) + Fraction(Rcap, CAP)
    num = sum(w ** BOX for w in W)
    den = Fraction(1)
    for w in W:
        den *= (1 - w)
    Tl = num / den
    X = E + K * (R + Tl)
    floor = Q['floor']
    for key, val in (('E', E), ('R', R), ('Tl', Tl), ('X', X), ('floor', floor)):
        need(frac(L[key], ck(key)) == val, ck(key), 'stored %s != recomputed %s' % (L[key], val))
    need(X < 1, ck('X < 1'), 'X = %s' % float(X))
    bound = floor / (1 - X)
    need(frac(L['bound'], ck('bound')) == bound, ck('bound'), 'stored != recomputed')
    need(bound <= THRESH, ck('bound <= threshold'), 'bound = %.6f' % float(bound))
    cbound = Q['cfloor'] * TAIL / (1 - X)
    need(cbound < 2, ck('corrected bound < 2'), 'corrected bound = %.6f' % float(cbound))
    if stats['cworst'] is None or cbound > stats['cworst'][0]:
        stats['cworst'] = (cbound, lid)
    stats['leaves'] += 1
    if E > 0:
        stats['Epos'] += 1
    if stats['worst'] is None or bound > stats['worst'][0]:
        stats['worst'] = (bound, lid)


def walk(node, slots, counter, stats):
    need(isinstance(node, dict), 'tree', 'node not a dict')
    counter[0] += 1
    need(node.get('id') == counter[0], 'node ids', 'expected preorder id %d, got %r' % (counter[0], node.get('id')))
    if 'leaf' in node:
        need(set(node) == {'id', 'leaf'}, 'tree', 'leaf node %d keys %r' % (counter[0], sorted(node)))
        check_leaf(node, slots, stats)
        return
    nid = counter[0]
    need(set(node) == {'id', 'split', 'children'}, 'tree', 'node %d keys %r' % (nid, sorted(node)))
    sp = node['split']
    need(isinstance(sp, dict) and set(sp) == {'slot', 'pins', 'rule'}, 'split', 'node %d split keys' % nid)
    need(sp['slot'] in NAMES, 'split', 'node %d bad slot %r' % (nid, sp['slot']))
    idx = NAMES.index(sp['slot'])
    sl = slots[idx]
    need(sl['pinned'] is None and sl['kind'] in ('q', 'big'), 'split',
         'node %d splits slot %s which is not a free q/big slot' % (nid, sp['slot']))
    pins = sp['pins']
    need(isinstance(pins, list) and len(pins) > 0 and all(isint(p) for p in pins), 'split pins',
         'node %d pins must be a nonempty list of integers' % nid)
    need(len(set(pins)) == len(pins), 'split pins', 'node %d pins not distinct' % nid)
    ch = node['children']
    need(isinstance(ch, list) and len(ch) == len(pins) + 1, 'split exhaustiveness',
         'node %d has %d children for %d pins (need pins + generic)' % (nid, len(ch) if isinstance(ch, list) else -1, len(pins)))
    stats['splits'] += 1
    stats['rules'][sp['rule']] = stats['rules'].get(sp['rule'], 0) + 1
    ms, _ = least_values(slots)
    if sp['rule'] == 'peel' and pins != [ms[idx]]:
        stats['peel_mismatch'] += 1
    for p in pins:
        if not is_prime(p):
            stats['composite_pins'].add((sp['slot'], p))
        if not residue_ok(sl['kind'], p) or p < ms[idx] or p in sl['excluded'] or p in pinned_values(slots):
            stats['vacuous_pins'] += 1
    for c, cs in zip(ch, apply_split(slots, idx, pins)):
        walk(c, cs, counter, stats)


def expected_triples():
    out = []
    for t in combinations_with_replacement(CLASSES, 3):
        if any(t.count(c) > 1 for c in FIXED):
            continue
        out.append(list(t))
    return out


def root_record(slots):
    out = []
    for s in slots:
        if s['pinned'] is not None:
            out.append(dict(name=s['name'], kind=s['kind'], cls=s['cls'], pinned=s['pinned']))
        else:
            out.append(dict(name=s['name'], kind=s['kind'], cls=s['cls'], lb=s['lb'], ub=None, excluded=[]))
    return out


def verify(cert):
    need(cert.get('format') == 'cert3_final v1', 'header', 'format')
    need(cert.get('cap') == CAP and cert.get('box') == BOX, 'header', 'cap/box')
    need(frac(cert.get('k'), 'header') == K and cert['k'] == [90601, 90000], 'header', 'k')
    need(frac(cert.get('threshold'), 'header') == THRESH, 'header', 'threshold')
    need(cert.get('weight_denominator_max') == WDEN, 'header', 'weight_denominator_max')
    need(cert.get('classes') == CLASSES, 'header', 'classes')
    # table
    tab = cert['table']
    need(isinstance(tab, dict) and set(tab) == {str(s) for s in TABLE_PRIMES}, 'table',
         'keys are not exactly the %d primes' % len(TABLE_PRIMES))
    for s in TABLE_PRIMES:
        got = tab[str(s)]
        need(sorted(map(tuple, got)) == [tuple(x) for x in TABLE[s]], 'table',
             's=%d: stored %r != recomputed %r' % (s, got, TABLE[s]))
    # triples
    exp = expected_triples()
    tr = cert['triples']
    need(isinstance(tr, list) and len(tr) == len(exp), 'triples', 'count %d != %d' % (len(tr), len(exp)))
    stats = dict(leaves=0, splits=0, Epos=0, hits=0, vacuous=0, worst=None, cworst=None, maxbox=0, rules={},
                 peel_mismatch=0, composite_pins=set(), vacuous_pins=0)
    counter = [0]
    for rec, t in zip(tr, exp):
        need(isinstance(rec, dict) and set(rec) == {'triple', 'root', 'tree'}, 'triples', 'record keys')
        need(rec['triple'] == t, 'triples', 'triple %r != expected %r (order or content)' % (rec['triple'], t))
        rs = root_slots(t)
        need(rec['root'] == root_record(rs), 'root', 'triple %r root mismatch' % (t,))
        walk(rec['tree'], rs, counter, stats)
    need(cert['leaf_count'] == stats['leaves'], 'totals', 'leaf_count %r != %d' % (cert['leaf_count'], stats['leaves']))
    need(cert['split_count'] == stats['splits'], 'totals', 'split_count %r != %d' % (cert['split_count'], stats['splits']))
    need(frac(cert['worst_bound'], 'totals') == stats['worst'][0], 'totals', 'worst_bound')
    need(cert['worst_leaf'] == stats['worst'][1], 'totals', 'worst_leaf')
    return stats


def report(stats):
    wb, wl = stats['worst']
    print('table: %d primes, recomputed and matching' % len(TABLE_PRIMES))
    print('triples: %d, all rebuilt from roots' % len(expected_triples()))
    print('leaves: %d  split nodes: %d  leaves with E > 0: %d  hit witnesses: %d  vacuous leaves: %d'
          % (stats['leaves'], stats['splits'], stats['Epos'], stats['hits'], stats['vacuous']))
    print('max box size: %d' % stats['maxbox'])
    print('split rules: %r  peel splits whose pin != least value: %d' % (stats['rules'], stats['peel_mismatch']))
    print('composite pins: %r' % sorted(stats['composite_pins']))
    print('pins that make a child trivially vacuous (residue/least/excluded/pinned): %d' % stats['vacuous_pins'])
    print('worst bound: %d/%d' % (wb.numerator, wb.denominator))
    print('worst bound ~ %.9f at leaf %d' % (float(wb), wl))
    cb, cl = stats['cworst']
    print('tail factor: %d/%d' % (TAIL.numerator, TAIL.denominator))
    print('worst corrected bound: %d/%d' % (cb.numerator, cb.denominator))
    print('worst corrected bound ~ %.9f at leaf %d (all %d leaves < 2)' % (float(cb), cl, stats['leaves']))


# Tamper tests.

def iter_nodes(node):
    yield node
    for c in node.get('children', []):
        yield from iter_nodes(c)


def tamper_tests(path):
    import copy
    raw = read_cert(path)

    def fresh():
        return json.loads(raw)

    def leaves(c):
        for rec in c['triples']:
            for n in iter_nodes(rec['tree']):
                if 'leaf' in n:
                    yield n['leaf']

    def first_leaf(c, pred):
        for L in leaves(c):
            if pred(L):
                return L
        raise RuntimeError('no leaf for tamper')

    tests = []

    def t1(c):  # weight just below admissibility
        L = first_leaf(c, lambda L: L['slots'][0].get('pinned') is None)
        m = L['slots'][0]['least']
        best = None
        for d in range(1, WDEN + 1):
            n = isqrt(d * d // m)  # n/d <= 1/sqrt(m)
            while n * n * m >= d * d:
                n -= 1
            f = Fraction(n, d)
            if f > 0 and (best is None or f > best):
                best = f
        L['weights'][0] = [best.numerator, best.denominator]
        return 'q weight set to %s, largest fraction with den <= 1000 below 1/sqrt(%d), leaf %d' % (best, m, L['id'])
    tests.append(t1)

    def t2(c):  # removed witness
        L = first_leaf(c, lambda L: len(L['witnesses']) > 3)
        del L['witnesses'][2]
        return 'third witness removed, leaf %d' % L['id']
    tests.append(t2)

    def t3(c):  # nonsquare with wrong r
        L = first_leaf(c, lambda L: any(w['kind'] == 'nonsquare' for w in L['witnesses']))
        w = next(w for w in L['witnesses'] if w['kind'] == 'nonsquare')
        w['r'] += 1
        return 'nonsquare r incremented at v=%r, leaf %d' % (w['v'], L['id'])
    tests.append(t3)

    def t4(c):  # hit relabeled as small
        L = first_leaf(c, lambda L: any(w['kind'] == 'hit' for w in L['witnesses']))
        w = next(w for w in L['witnesses'] if w['kind'] == 'hit')
        w['kind'] = 'small'
        return 'hit s=%d relabeled small, leaf %d' % (w['s'], L['id'])
    tests.append(t4)

    def t5(c):  # entry removed from C
        L = first_leaf(c, lambda L: len(L['C']) > 0)
        s = L['C'].pop()['s']
        return 'C entry s=%d removed, leaf %d' % (s, L['id'])
    tests.append(t5)

    def t6(c):  # pin removed from split
        for rec in c['triples']:
            for n in iter_nodes(rec['tree']):
                if 'split' in n and len(n['split']['pins']) > 1:
                    p = n['split']['pins'].pop(0)
                    return 'pin %d removed from split node %d' % (p, n['id'])
    tests.append(t6)

    def t7(c):  # excluded value dropped from a generic child
        for rec in c['triples']:
            for n in iter_nodes(rec['tree']):
                if 'split' in n:
                    g = n['children'][-1]
                    if 'leaf' in g:
                        sl = next(s for s in g['leaf']['slots'] if s['name'] == n['split']['slot'])
                        p = sl['excluded'].pop()
                        return 'excluded %d dropped from generic leaf %d' % (p, g['id'])
    tests.append(t7)

    def t8(c):  # least value lowered
        L = first_leaf(c, lambda L: L['slots'][0].get('pinned') is None)
        L['slots'][0]['least'] -= 12
        return 'q least lowered by 12, leaf %d' % L['id']
    tests.append(t8)

    def t9(c):  # least value raised
        L = first_leaf(c, lambda L: any(s.get('pinned') is None and s['kind'] == 'big' for s in L['slots']))
        s = next(s for s in L['slots'] if s.get('pinned') is None and s['kind'] == 'big')
        s['least'] += 3
        return 'big slot %s least raised by 3, leaf %d' % (s['name'], L['id'])
    tests.append(t9)

    def t10(c):  # table factor changed
        c['table']['5'] = [[29, 1]]
        return 'table entry for 5 changed'
    tests.append(t10)

    def t11(c):  # bound below true value (consistent claim forging)
        L = first_leaf(c, lambda L: True)
        b = L['bound']
        L['bound'] = [b[0] - 1, b[1]]
        return 'bound numerator decremented, leaf %d' % L['id']
    tests.append(t11)

    def t12(c):  # a triple dropped
        t = c['triples'].pop(50)['triple']
        return 'triple %r removed' % (t,)
    tests.append(t12)

    def t13(c):  # stored leaf constraint tightened (lb raised) consistently
        L = first_leaf(c, lambda L: L['slots'][0].get('pinned') is None)
        L['slots'][0]['lb'] += 12
        L['slots'][0]['least'] += 12
        return 'q lb and least both raised by 12, leaf %d' % L['id']
    tests.append(t13)

    ok = True
    for t in tests:
        c = fresh()
        desc = t(c)
        try:
            verify(c)
            print('NOT REJECTED: %s' % desc)
            ok = False
        except VerifyError as e:
            print('rejected: %s\n    -> %s' % (desc, e))
    print('all tampers rejected' if ok else 'SOME TAMPERS ACCEPTED')


def main():
    path = sys.argv[1]
    if '--tamper' in sys.argv:
        tamper_tests(path)
        return
    cert = json.loads(read_cert(path))
    try:
        stats = verify(cert)
    except VerifyError as e:
        print('REJECTED:', e)
        sys.exit(1)
    report(stats)
    print('ACCEPTED')


if __name__ == '__main__':
    main()
