"""Bounded branch search for the mixed index family 3, 5, 7 with special prime 5.

Hypothetical N: odd perfect, special prime 5 with exponent 1, exponent of 3 equal to 2,
every ordinary prime p has index m_p = e_p + 1 divisible by 3, 5 or 7.

Facts used (all elementary, exact):
  * v_3(N) = 2 and v_5(N) = 1; sigma(5) = 2*3 already sends one factor 3.
    So the factors 3 sent by ordinary primes total exactly 1, and the factors 5 total exactly 1.
  * 7 does not divide N (105 | N is impossible, landed), so no sigma(p^e) is divisible by 7.
  * For a prime k in {3,5,7} with k | m_p, Phi_k(p) = F_k(p) divides sigma(p^e), hence 2N.
  * Every ordinary index is at least 3, so each ordinary prime contributes at least
    1 + 1/p + 1/p^2 to the abundancy; the abundancy of p^e is increasing in e.
Search: a node holds the known primes and a branch choice k for some of them; the least
pending prime is branched on k = 3, 5, 7. Closing rules:
  cap3  : factors 3 received exceed 2,
  cap5  : factors 5 received exceed 1,
  seven : 7 divides Phi_k(p) (then 3 * 5 * 7 | N),
  abund : lower bound of the abundancy of the known part exceeds 2.
Open leaves: depth bound or node budget reached. A cofactor that the bounded factoring cannot
split is dropped (the factors found are still forced) and the node is flagged 'partial'.
Primality: sympy isprime is a proof below 2^64; a probable prime above 2^64 is left out of the
abundancy bound, and a node that branches on one is flagged 'prp'.
Optional fifth argument max7: at most that many 7 choices on a path (leaf 'excluded7').
Usage: python3 -I search.py DEPTH BUDGET PREFIX TAG [MAX7]
"""
import sys, json, time
from fractions import Fraction
from math import gcd
from sympy import isprime
from sympy.ntheory import pollard_rho, pollard_pm1, ecm

BIG = 2 ** 64
SMALL = [p for p in range(2, 100000) if isprime(p)]


def phi(k, p):
    return sum(p ** i for i in range(k))  # k prime, so Phi_k = F_k


def split(n):
    """Return a nontrivial factor of composite n or None (bounded, deterministic)."""
    d = pollard_rho(n, retries=3, max_steps=200000, seed=1234)
    if d:
        return d
    d = pollard_pm1(n, B=200000, seed=1234)
    if d:
        return d
    if n < 10 ** 70:
        try:
            fs = ecm(n, B1=50000, B2=5000000, max_curve=60, seed=1234)
        except Exception:
            fs = None
        if fs:
            for f in sorted(fs):
                if 1 < f < n:
                    return f
    return None


def factor(n):
    """Return (dict prime -> exponent, list of unfactored composite cofactors)."""
    res, bad = {}, []
    for p in SMALL:
        if p * p > n:
            break
        while n % p == 0:
            res[p] = res.get(p, 0) + 1
            n //= p
    stack = [n] if n > 1 else []
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if isprime(m):
            res[m] = res.get(m, 0) + 1
            continue
        d = split(m)
        if d is None:
            bad.append(m)
            continue
        g = gcd(d, m)
        stack += [g, m // g]
    return res, bad


FCACHE = {}
NEW = {}


def load_cache():
    import glob
    for fn in glob.glob('cache_*.json'):
        try:
            for key, (fs, bad) in json.load(open(fn)).items():
                k, p = map(int, key.split(','))
                FCACHE[(k, p)] = ({int(r): e for r, e in fs}, [int(b) for b in bad])
        except Exception:
            pass


def save_cache(tag):
    old = {}
    try:
        old = json.load(open('cache_%s.json' % tag))
    except Exception:
        pass
    for (k, p), (fs, bad) in NEW.items():
        old['%d,%d' % (k, p)] = [[str(r), e] for r, e in fs.items()], [str(b) for b in bad]
    json.dump(old, open('cache_%s.json' % tag, 'w'))


def phifac(k, p):
    key = (k, p)
    if key not in FCACHE:
        FCACHE[key] = NEW[key] = factor(phi(k, p))
    return FCACHE[key]


def abund(p, m):
    return Fraction(phi(m, p), p ** (m - 1)) if m > 1 else Fraction(1)


def lower_abund(state):
    a = Fraction(13, 9) * Fraction(6, 5)
    for p, k in state['idx'].items():
        a *= abund(p, k)
    for p in state['pend']:
        if p < BIG:  # a probable prime above 2^64 is left out (lower bound stays valid)
            a *= abund(p, 3)
    return a


def run(depth, budget, prefix, out, max7):
    root = {'idx': {}, 'pend': [13], 's3': 1, 's5': 0, 'path': [], 'partial': False, 'prp': False, 'n7': 0}
    stats = {}
    leaves = []
    nodes = [0]

    def rec(st, prefix):
        nodes[0] += 1
        d = len(st['path'])
        stats.setdefault(d, {'nodes': 0})
        stats[d]['nodes'] += 1
        if lower_abund(st) > 2:
            return leaf(st, 'abund', str(float(lower_abund(st))))
        if not st['pend']:
            return leaf(st, 'open_nopending', '')
        if d >= depth:
            return leaf(st, 'open_depth', 'pending=%s' % sorted(st['pend'])[:3])
        if nodes[0] > budget:
            return leaf(st, 'open_budget', 'pending=%s' % sorted(st['pend'])[:3])
        p = min(st['pend'])
        choices = [prefix[0]] if prefix else [3, 5, 7]
        for k in choices:
            if k == 7 and st['n7'] >= max7:
                leaf(dict(st, path=st['path'] + [(p, 7)]), 'excluded7', 'p=%d' % p); continue
            path = st['path'] + [(p, k)]
            F = phi(k, p)
            v = {r: 0 for r in (3, 5, 7)}
            for r in v:
                while F % r ** (v[r] + 1) == 0:
                    v[r] += 1
            child = {'idx': dict(st['idx']), 'pend': [x for x in st['pend'] if x != p],
                     's3': st['s3'] + v[3], 's5': st['s5'] + v[5], 'path': path,
                     'partial': st['partial'], 'prp': st['prp'] or p >= BIG,
                     'n7': st['n7'] + (k == 7)}
            child['idx'][p] = k
            if v[7]:
                leaf(child, 'seven', 'p=%d k=%d' % (p, k)); continue
            if child['s3'] > 2:
                leaf(child, 'cap3', 'p=%d k=%d' % (p, k)); continue
            if child['s5'] > 1:
                leaf(child, 'cap5', 'p=%d k=%d' % (p, k)); continue
            fs, bad = phifac(k, p)
            if bad:  # the factors found are still forced; the cofactor is never used
                child['partial'] = True
            for r in fs:
                if r in (3, 5, 7):
                    continue
                if r not in child['idx'] and r not in child['pend']:
                    child['pend'].append(r)
            rec(child, prefix[1:])

    def leaf(st, rule, info):
        d = len(st['path'])
        stats.setdefault(d, {'nodes': 0})
        stats[d][rule] = stats[d].get(rule, 0) + 1
        rec_ = {'rule': rule, 'info': info, 'path': st['path'], 'pend': st['pend'],
                's3': st['s3'], 's5': st['s5'], 'prp': st['prp'], 'partial': st['partial'],
                'abund': float(lower_abund(st))}
        out.write(json.dumps(rec_) + '\n'); out.flush()
        leaves.append(rule)

    rec(root, prefix)
    return stats, nodes[0]


if __name__ == '__main__':
    depth = int(sys.argv[1]); budget = int(sys.argv[2])
    prefix = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 and sys.argv[3] else []
    tag = sys.argv[4] if len(sys.argv) > 4 else 'run'
    max7 = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9
    load_cache()
    t = time.time()
    with open('leaves_%s.jsonl' % tag, 'w') as out:
        try:
            stats, n = run(depth, budget, prefix, out, max7)
        finally:
            save_cache(tag)
    with open('stats_%s.json' % tag, 'w') as f:
        json.dump({'depth': depth, 'budget': budget, 'prefix': prefix, 'max7': max7, 'nodes': n,
                   'seconds': round(time.time() - t, 1), 'stats': stats}, f, indent=1)
    print(json.dumps({'nodes': n, 'seconds': round(time.time() - t, 1)}))
