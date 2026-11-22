"""Build a pruned certificate tree (format of ../MixedIndexTwo/cert2.py) with a choice of the
branching order, for the rules of `MixedIndexThree.chk3` (cap at 3 counts distinct senders).

Orders: 'min' branches on the least pending prime (as cert2.py); 'ff' branches on the pending
prime with the fewest branches left open by the rules seven, cap3, cap5 (ties: least prime).
Usage: python3 -I cert3.py CONFIG.json ORDER OUT.json [NODE_LIMIT]"""
import json, sys, os
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'MixedIndex'))
import search as S


def ab(p, e):
    return Fraction(S.phi(e + 1, p), p ** e)


class Limit(Exception):
    pass


def main(cfg, order, limit):
    base = Fraction(1)
    for p, e in cfg['base']:
        base *= ab(p, e)
    cap3, cap5 = cfg['cap3'], cfg['cap5']
    count = [0]

    def abund_set(st):
        comps = [(p, k - 1) for p, k in st['idx'].items()]
        comps += [(p, 2) for p in st['pend'] if p < S.BIG]
        a, chosen = base, []
        for p, e in sorted(comps, key=lambda x: -ab(*x)):
            a *= ab(p, e); chosen.append((p, e))
            if a > 2:
                return chosen
        return None

    def vals(p, k):
        F = S.phi(k, p)
        v = {}
        for r in (3, 5, 7):
            v[r] = 0
            while F % r ** (v[r] + 1) == 0:
                v[r] += 1
        return v

    def shut(st, p, k):
        v = vals(p, k)
        if v[7]:
            return 'seven'
        if cap3 is not None and st['s3'] + v[3] > cap3:
            return 'cap3'
        if cap5 is not None and st['s5'] + v[5] > cap5:
            return 'cap5'
        return None

    def pick(st):
        cand = [p for p in st['pend'] if p < S.BIG]  # primality is certified only below 2^64
        assert cand, 'open leaf: only probable primes pending'
        if order == 'min':
            return min(cand)
        return min(cand, key=lambda p: (sum(shut(st, p, k) is None for k in (3, 5, 7)), p))

    def build(st):
        s = abund_set(st)
        if s is not None:
            return {'close': 'abund', 'set': s}, {p for p, _ in s}
        count[0] += 1
        if count[0] > limit:
            raise Limit
        p = pick(st)
        br, used = {}, {p}
        for k in (3, 5, 7):
            rule = shut(st, p, k)
            if rule:
                br[k] = {'close': rule}; continue
            v = vals(p, k)
            child = {'idx': dict(st['idx']), 'pend': [x for x in st['pend'] if x != p],
                     's3': st['s3'] + v[3], 's5': st['s5'] + v[5]}
            child['idx'][p] = k
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
    try:
        tree = build(root)[0]
    except Limit:
        tree = None
    return tree, count[0]


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    def usage():
        print('usage: cert3.py CONFIG.json {min,ff} OUT.json [NODE_LIMIT] with '
              'NODE_LIMIT >= 0 and a nonempty OUT', file=sys.stderr)
        sys.exit(2)

    if len(sys.argv) not in (4, 5): usage()
    order, out = sys.argv[2], sys.argv[3]
    try:
        limit = int(sys.argv[4]) if len(sys.argv) == 5 else 10 ** 9
    except ValueError:
        usage()
    if order not in ('min', 'ff') or limit < 0 or not out: usage()
    cfg = json.load(open(sys.argv[1]))
    S.load_cache()
    try:
        tree, n = main(cfg, order, limit)
    finally:
        S.save_cache(os.path.basename(out).replace('.json', ''))
    if tree is not None:
        json.dump(tree, open(out, 'w'))
    print(json.dumps({'out': out, 'order': order, 'nodes': n, 'closed': tree is not None}))

    # An incomplete search must not look successful to a caller or allow stale output reuse.
    sys.exit(0 if tree is not None else 1)
