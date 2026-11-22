"""Generalized branch search for the mixed index family 3, 5, 7 (special prime 5).

Same branching and factoring as ../MixedIndex/search.py (imported, unchanged); the root is a
configuration (JSON file) instead of the fixed case v_3(N) = 2, v_5(N) = 1:
  base   : list of [p, e]: p^e | N is known (3 and 5), giving the abundancy factor sigma(p^e)/p^e;
  cap3   : exact v_3(N) if known (rule cap3 active), else null;
  cap5   : exact v_5(N) if known (rule cap5 active), else null;
  s3, s5 : factors 3 and 5 already received from the base components (lower bounds);
  pend   : primes forced at the root.
Closing rules: seven (3 and 5 divide N, so 7 does not), cap3 / cap5 when active, abund.
Usage: python3 -I search2.py CONFIG.json DEPTH BUDGET TAG [MAX7]
"""
import sys, os, json, time
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'MixedIndex'))
import search as S


def run(cfg, depth, budget, out, max7):
    base = Fraction(1)
    for p, e in cfg['base']:
        base *= S.abund(p, e + 1)
    cap3, cap5 = cfg['cap3'], cfg['cap5']
    stats, nodes = {}, [0]

    def lower(st):
        a = base
        for p, k in st['idx'].items():
            a *= S.abund(p, k)
        for p in st['pend']:
            if p < S.BIG:
                a *= S.abund(p, 3)
        return a

    def leaf(st, rule, info):
        d = len(st['path'])
        stats.setdefault(d, {'nodes': 0})
        stats[d][rule] = stats[d].get(rule, 0) + 1
        out.write(json.dumps({'rule': rule, 'info': info, 'path': st['path'],
                              'pend': sorted(st['pend']), 's3': st['s3'], 's5': st['s5'],
                              'partial': st['partial'], 'prp': st['prp'],
                              'abund': float(lower(st))}) + '\n')

    def rec(st):
        nodes[0] += 1
        d = len(st['path'])
        stats.setdefault(d, {'nodes': 0})
        stats[d]['nodes'] += 1
        if lower(st) > 2:
            return leaf(st, 'abund', '')
        if not st['pend']:
            return leaf(st, 'open_nopending', '')
        if d >= depth:
            return leaf(st, 'open_depth', '')
        if nodes[0] > budget:
            return leaf(st, 'open_budget', '')
        p = min(st['pend'])
        for k in (3, 5, 7):
            if k == 7 and st['n7'] >= max7:
                leaf(dict(st, path=st['path'] + [(p, 7)]), 'excluded7', ''); continue
            F = S.phi(k, p)
            v = {}
            for r in (3, 5, 7):
                v[r] = 0
                while F % r ** (v[r] + 1) == 0:
                    v[r] += 1
            child = {'idx': dict(st['idx']), 'pend': [x for x in st['pend'] if x != p],
                     's3': st['s3'] + v[3], 's5': st['s5'] + v[5], 'path': st['path'] + [(p, k)],
                     'partial': st['partial'], 'prp': st['prp'] or p >= S.BIG,
                     'n7': st['n7'] + (k == 7)}
            child['idx'][p] = k
            if v[7]:
                leaf(child, 'seven', ''); continue
            if cap3 is not None and child['s3'] > cap3:
                leaf(child, 'cap3', ''); continue
            if cap5 is not None and child['s5'] > cap5:
                leaf(child, 'cap5', ''); continue
            fs, bad = S.phifac(k, p)
            if bad:
                child['partial'] = True
            for r in fs:
                if r not in (3, 5, 7) and r not in child['idx'] and r not in child['pend']:
                    child['pend'].append(r)
            rec(child)

    root = {'idx': {}, 'pend': list(cfg['pend']), 's3': cfg['s3'], 's5': cfg['s5'], 'path': [],
            'partial': False, 'prp': False, 'n7': 0}
    rec(root)
    return stats, nodes[0]


if __name__ == '__main__':
    sys.setrecursionlimit(20000)
    cfg = json.load(open(sys.argv[1]))
    depth, budget, tag = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    max7 = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9
    S.load_cache()
    t = time.time()
    with open('leaves_%s.jsonl' % tag, 'w') as out:
        try:
            stats, n = run(cfg, depth, budget, out, max7)
        finally:
            S.save_cache(tag)
    json.dump({'cfg': cfg, 'depth': depth, 'budget': budget, 'max7': max7, 'nodes': n,
               'seconds': round(time.time() - t, 1), 'stats': stats},
              open('stats_%s.json' % tag, 'w'), indent=1)
    print(json.dumps({'tag': tag, 'nodes': n, 'seconds': round(time.time() - t, 1)}))
