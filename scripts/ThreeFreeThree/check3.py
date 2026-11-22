# Untrusted helper script for the OddPerfect Lean library.
# Checker for the certificate cert3_final.json written by cert3f.py, written from SPEC.md
# (it imports nothing from the generator): it rebuilds the constraints of every node from the
# roots and the splits and recomputes every leaf from them.
# Used by: the certificate behind OddPerfect/ThreeFreeThreeData01.lean .. Data11.lean and
# OddPerfect/ThreeFreeThree.lean.
# Run: python3 -I check3.py cert3_final.json   (or cert3_final.json.xz)
# Requires: Python 3 standard library. Deterministic. Running time: about four seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.
import sys, json
from fractions import Fraction as F
from itertools import product, combinations_with_replacement
from math import isqrt

def read_cert(path):
    """Bytes of the certificate, plain or compressed with xz (file name ending in .xz)."""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as fh:
            return fh.read()
    with open(path, 'rb') as fh:
        return fh.read()


CLASSES = ['5', '7', '13', '19', '31', '37', '43', 'n2', 'big']
NAMES = ['q', 'r1', 'r2', 'r3']


def fail(msg):
    raise SystemExit('REJECT: ' + msg)


def need(c, msg):
    if not c:
        fail(msg)


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def fr(p):
    need(isinstance(p, list) and len(p) == 2 and p[1] > 0, f'bad fraction {p}')
    return F(p[0], p[1])


def res_ok(kind, f):
    return {'q': f % 12 == 1, 'n2': f % 3 == 2, 'big': f % 3 == 1}[kind]


def root(t):
    sl = [dict(kind='q', cls='q', val=None, lb=13, ex=set())]
    for c in t:
        if c in ('n2', 'big'):
            sl.append(dict(kind=c, cls=c, val=None, lb=11 if c == 'n2' else 61, ex=set()))
        else:
            sl.append(dict(kind='fix', cls=c, val=int(c), lb=None, ex=set()))
    return sl


def least(sl):
    pv = {s['val'] for s in sl if s['val'] is not None}
    out, last = [], {}
    for s in sl:
        prev = last.get(s['cls'])
        if s['val'] is not None:
            if prev is not None and s['val'] <= prev:
                return None
            out.append(s['val'])
        else:
            m = max(s['lb'], prev + 1 if prev is not None else 0)
            while not (res_ok(s['kind'], m) and m not in s['ex'] and m not in pv):
                m += 1
            out.append(m)
        last[s['cls']] = out[-1]
    return out


def accepts(s, f, pv, m):
    if s['val'] is not None:
        return f == s['val']
    return res_ok(s['kind'], f) and f >= m and f not in s['ex'] and f not in pv


def check_leaf(sl, lf, nid, doc, st):
    cap, M, k, thr = doc['cap'], doc['box'], fr(doc['k']), fr(doc['threshold'])
    need(lf['id'] == nid, f'leaf id {lf["id"]} != {nid}')
    mins = least(sl)
    if lf['status'] == 'vacuous':
        need(mins is None, f'leaf {nid} marked vacuous but is not')
        st['vacuous'] += 1
        return
    need(lf['status'] == 'closed' and mins is not None, f'leaf {nid} status')
    pv = {s['val'] for s in sl if s['val'] is not None}
    for i, (s, j) in enumerate(zip(sl, lf['slots'])):
        need(j['name'] == NAMES[i] and j['kind'] == s['kind'], f'leaf {nid} slot names')
        if s['val'] is not None:
            need(j.get('pinned') == s['val'], f'leaf {nid} pinned')
        else:
            need(j['lb'] == s['lb'] and set(j['excluded']) == s['ex'] and j['least'] == mins[i]
                 and j.get('ub') is None, f'leaf {nid} constraints')
    # C
    myC = set()
    for s_, fac in doc['_table'].items():
        if s_ in pv:
            continue
        if all(any(accepts(sl[j], p, pv, mins[j]) for j in range(4)) for p, e in fac):
            myC.add(s_)
    need({c['s'] for c in lf['C']} == myC, f'leaf {nid} C')
    tg = [s['kind'] in ('q', 'big') or (s['kind'] == 'fix' and m % 3 == 1) for s, m in zip(sl, mins)]
    need(lf['target'] == tg, f'leaf {nid} target')
    ws = [fr(w) for w in lf['weights']]
    for t, w, m in zip(tg, ws, mins):
        if t:
            need(0 < w < 1 and w * w * m >= 1 and w.denominator <= 1000, f'leaf {nid} weight')
        else:
            need(w == 0, f'leaf {nid} zero weight')
    ex = [t and s['val'] is not None for t, s in zip(tg, sl)]
    need(lf['exact_coords'] == ex, f'leaf {nid} exact coords')
    floor = F(1)
    for m in mins:
        floor *= F(m, m - 1)
    for s_ in myC:
        floor *= F(s_ * s_ + s_ + 1, s_ * s_)
    need(fr(lf['floor']) == floor, f'leaf {nid} floor')
    c = F(1, cap)
    E, R = F(0), F(0)
    wit = iter(lf['witnesses'])
    for v in product(*[range(M) if t else range(1) for t in tg]):
        if all(a % 2 == 0 for a in v):
            continue
        w = F(1)
        for x, a in zip(ws, v):
            w *= x ** a
        if not all(a == 0 or e for a, e in zip(v, ex)):
            R += min(c, w)
            continue
        n = 1
        for s, a in zip(sl, v):
            if a:
                n *= s['val'] ** a
        d = 4 * n - 3
        x = next(wit, None)
        need(x is not None and x['v'] == list(v), f'leaf {nid} witness order')
        if x['kind'] == 'nonsquare':
            r = x['r']
            need(r * r < d < (r + 1) * (r + 1), f'leaf {nid} nonsquare witness')
        else:
            s_ = x['s']
            need(d == (2 * s_ + 1) ** 2, f'leaf {nid} square witness')
            if x['kind'] == 'hit':
                need(s_ >= cap, f'leaf {nid} hit')
                E += F(s_ + 1, s_ * s_)
            else:
                need(x['kind'] == 'small' and s_ < cap, f'leaf {nid} small')
    need(next(wit, None) is None, f'leaf {nid} extra witnesses')
    Tl = sum((w ** M for w in ws), F(0))
    for w in ws:
        Tl /= 1 - w
    X = E + k * (R + Tl)
    need(fr(lf['E']) == E and fr(lf['R']) == R and fr(lf['Tl']) == Tl and fr(lf['X']) == X,
         f'leaf {nid} E R Tl X')
    need(X < 1, f'leaf {nid} X >= 1')
    b = floor / (1 - X)
    need(fr(lf['bound']) == b and b <= thr, f'leaf {nid} bound')
    st['closed'] += 1
    st['E>0'] += E > 0
    if b > st['worst'][0]:
        st['worst'] = (b, nid)


def walk(sl, node, doc, st):
    st['id'] += 1
    nid = st['id']
    need(node['id'] == nid, f'node id {node["id"]} != {nid}')
    if 'leaf' in node:
        check_leaf(sl, node['leaf'], nid, doc, st)
        return
    sp = node['split']
    i = NAMES.index(sp['slot'])
    need(sl[i]['val'] is None and sl[i]['kind'] in ('q', 'big'), f'node {nid} split slot')
    pins = sp['pins']
    need(len(pins) >= 1 and len(set(pins)) == len(pins), f'node {nid} pins')
    kids = node['children']
    need(len(kids) == len(pins) + 1, f'node {nid} children')
    for p, kid in zip(pins, kids):
        ch = [dict(s, ex=set(s['ex'])) for s in sl]
        ch[i]['val'] = p
        for j in range(i + 1, 4):
            if ch[j]['cls'] == ch[i]['cls'] and ch[j]['val'] is None:
                ch[j]['lb'] = max(ch[j]['lb'], p + 1)
        walk(ch, kid, doc, st)
    ch = [dict(s, ex=set(s['ex'])) for s in sl]
    ch[i]['ex'] |= set(pins)
    walk(ch, kids[-1], doc, st)


def main():
    doc = json.loads(read_cert(sys.argv[1]))
    need(doc['cap'] == 300 and doc['box'] == 5, 'cap/box')
    need(fr(doc['k']) == F(301, 300) ** 2 and fr(doc['threshold']) < 2, 'k/threshold')
    tab = {int(s): v for s, v in doc['table'].items()}
    need(set(tab) == {s for s in range(5, 300) if s % 3 == 2 and is_prime(s)}, 'table keys')
    for s, fac in tab.items():
        n = 1
        for p, e in fac:
            need(is_prime(p) and e >= 1, f'table {s}')
            n *= p ** e
        need(n == s * s + s + 1, f'table {s} product')
    doc['_table'] = tab
    want = [list(t) for t in combinations_with_replacement(CLASSES, 3)
            if not any(t.count(c) > 1 for c in CLASSES[:7])]
    need([t['triple'] for t in doc['triples']] == want and len(want) == 102, 'triples')
    st = dict(id=0, closed=0, vacuous=0, worst=(F(0), 0), **{'E>0': 0})
    for t in doc['triples']:
        walk(root(t['triple']), t['tree'], doc, st)
    need(st['closed'] + st['vacuous'] == doc['leaf_count'], 'leaf count')
    need(fr(doc['worst_bound']) == st['worst'][0], 'worst bound')
    print(f"ACCEPT: 102 triples, {st['closed']} closed leaves, {st['vacuous']} vacuous, "
          f"{st['E>0']} leaves with E > 0, worst bound {float(st['worst'][0]):.6f} at leaf {st['worst'][1]}")
    print('worst bound exact:', st['worst'][0])


if __name__ == '__main__':
    main()
