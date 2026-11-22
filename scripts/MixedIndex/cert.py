"""Build the closed tree as a certificate (cert.json) from the search rules, with pruning:
a forced prime is kept only if the subtree uses it (branches on it or needs it in an
abundant divisor). Abundant closures list a small sufficient set of components.
Usage: python3 -I cert.py   (reads the factor caches cache_*.json made by search.py)"""
import json, sys
from fractions import Fraction
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import search as S

S.load_cache()
BASE = [(3, 2), (5, 1)]


def comps(st):
    c = [(p, k - 1) for p, k in st['idx'].items()]
    c += [(p, 2) for p in st['pend'] if p < S.BIG]
    return c


def ab(p, e):
    return Fraction(S.phi(e + 1, p), p ** e)


def abund_set(st):
    a = Fraction(13, 9) * Fraction(6, 5)
    chosen = []
    for p, e in sorted(comps(st), key=lambda x: -ab(*x)):
        a *= ab(p, e); chosen.append((p, e))
        if a > 2:
            return chosen
    return None


def build(st):
    """Return (tree, used primes). tree: {'p', 'br': {k: child}}; child: closure or force."""
    s = abund_set(st)
    if s is not None:
        return {'close': 'abund', 'set': s}, {p for p, _ in s}
    assert st['pend'], 'open leaf'
    p = min(st['pend'])
    br, used = {}, {p}
    for k in (3, 5, 7):
        F = S.phi(k, p)
        v = {}
        for r in (3, 5, 7):
            v[r] = 0
            while F % r ** (v[r] + 1) == 0:
                v[r] += 1
        child = {'idx': dict(st['idx']), 'pend': [x for x in st['pend'] if x != p],
                 's3': st['s3'] + v[3], 's5': st['s5'] + v[5], 'path': st['path'] + [(p, k)],
                 'chain3': st['chain3'] + ([(p, k, v[3])] if v[3] else []),
                 'chain5': st['chain5'] + ([(p, k, v[5])] if v[5] else [])}
        child['idx'][p] = k
        if v[7]:
            br[k] = {'close': 'seven'}; continue
        if child['s3'] > 2:
            br[k] = {'close': 'cap3', 'senders': child['chain3']}; continue
        if child['s5'] > 1:
            br[k] = {'close': 'cap5', 'senders': child['chain5']}; continue
        fs, bad = S.phifac(k, p)
        assert not bad
        new = []
        for r in sorted(fs):
            if r in (3, 5, 7):
                continue
            if r not in child['idx'] and r not in child['pend']:
                child['pend'].append(r); new.append(r)
        sub, u = build(child)
        keep = [r for r in new if r in u]
        br[k] = {'force': keep, 'next': sub}
        used |= u - set(new)
    for k, c in br.items():
        pass
    return {'p': p, 'br': br}, used


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    root = {'idx': {}, 'pend': [13], 's3': 1, 's5': 0, 'path': [], 'chain3': [], 'chain5': []}
    tree, used = build(root)
    json.dump(tree, open('cert.json', 'w'))
    print('built; primes used at root level', sorted(used))
