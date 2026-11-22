"""Build a pruned certificate tree for one root configuration of search2.py.
A forced prime is kept only if the subtree branches on it or uses it in an abundant divisor.
Usage: python3 -I cert2.py CONFIG.json OUT.json"""
import json, sys, os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'MixedIndex'))
import search as S


def ab(p, e):
    return Fraction(S.phi(e + 1, p), p ** e)


def main(cfg):
    base = Fraction(1)
    for p, e in cfg['base']:
        base *= ab(p, e)
    cap3, cap5 = cfg['cap3'], cfg['cap5']

    def abund_set(st):
        comps = [(p, k - 1) for p, k in st['idx'].items()]
        comps += [(p, 2) for p in st['pend'] if p < S.BIG]
        a, chosen = base, []
        for p, e in sorted(comps, key=lambda x: -ab(*x)):
            a *= ab(p, e); chosen.append((p, e))
            if a > 2:
                return chosen
        return None

    def build(st):
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
                     's3': st['s3'] + v[3], 's5': st['s5'] + v[5]}
            child['idx'][p] = k
            if v[7]:
                br[k] = {'close': 'seven'}; continue
            if cap3 is not None and child['s3'] > cap3:
                br[k] = {'close': 'cap3'}; continue
            if cap5 is not None and child['s5'] > cap5:
                br[k] = {'close': 'cap5'}; continue
            fs, bad = S.phifac(k, p)
            new = []
            for r in sorted(fs):
                if r not in (3, 5, 7) and r not in child['idx'] and r not in child['pend']:
                    child['pend'].append(r); new.append(r)
            sub, u = build(child)
            br[k] = {'force': [r for r in new if r in u], 'next': sub}
            used |= u - set(new)
        return {'p': p, 'br': br}, used

    root = {'idx': {}, 'pend': list(cfg['pend']), 's3': cfg['s3'], 's5': cfg['s5']}
    return build(root)[0]


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    S.load_cache()
    tree = main(json.load(open(sys.argv[1])))
    json.dump(tree, open(sys.argv[2], 'w'))
    print('built', sys.argv[2])
