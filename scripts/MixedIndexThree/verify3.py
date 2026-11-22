"""Independent check of a MixedIndexThree certificate (imports no other script).

Root facts for a configuration cfg_<tag>.json: N odd perfect, 5 has odd exponent, every prime
p != 5 dividing N has 3 | m_p or 5 | m_p or 7 | m_p (m_p = v_p(N) + 1), the powers in `base`
divide N, the primes in `pend` divide N; `cap3` (if not null) is the exact v_3(N), `cap5` (if not
null) is the exact v_5(N) = 1. The special component sends at least one factor 3.
Every step is checked with exact integers; primality by sympy isprime (a proof below 2^64);
larger primes are rejected.
Usage: python3 -I verify3.py TAG   (reads cfg_TAG.json and cert_TAG.json or cert_TAG.json.xz)"""
import json, sys, os, lzma
from collections import Counter
from sympy import isprime

BIG = 2 ** 64
stats = Counter()


def F(k, p):
    return sum(p ** i for i in range(k))


def val(n, r):
    v = 0
    while n % r == 0:
        n //= r; v += 1
    return v


def load(tag):
    fn = 'cert_%s.json' % tag
    if os.path.exists(fn):
        return json.load(open(fn))
    return json.load(lzma.open(fn + '.xz', 'rt'))


def main(tag):
    cfg = json.load(open('cfg_%s.json' % tag))
    base = [tuple(x) for x in cfg['base']]
    cap3, cap5 = cfg['cap3'], cfg['cap5']

    def check_abund(S, K, idx):
        num, den = 1, 1
        for p, e in base:
            num *= F(e + 1, p); den *= p ** e
        seen = set()
        for p, e in S:
            assert p in K and p not in seen and p not in (3, 5, 7)
            seen.add(p)
            assert e <= (idx[p] - 1 if p in idx else 2)
            num *= F(e + 1, p); den *= p ** e
        assert num > 2 * den, 'not abundant'

    def node(t, K, idx, s3, s5):
        if 'close' in t:
            assert t['close'] == 'abund'
            stats['abund'] += 1
            return check_abund(t['set'], K, idx)
        p = t['p']
        assert p in K and p not in (3, 5, 7) and p not in idx
        assert sorted(t['br']) == ['3', '5', '7']
        stats['node'] += 1
        for ks, c in t['br'].items():
            k = int(ks)
            f = F(k, p)
            n3, n5 = s3 + val(f, 3), s5 + val(f, 5)
            rule = c.get('close')
            if rule == 'seven':
                assert f % 7 == 0; stats['seven'] += 1; continue
            if rule == 'cap3':
                assert cap3 is not None and n3 > cap3; stats['cap3'] += 1; continue
            if rule == 'cap5':
                assert cap5 is not None and n5 > cap5; stats['cap5'] += 1; continue
            assert rule is None
            K2 = set(K)
            for r in c['force']:
                assert f % r == 0 and r not in (2, 3, 5, 7) and r < BIG and isprime(r)
                K2.add(r)
            stats['force'] += len(c['force'])
            idx2 = dict(idx); idx2[p] = k
            node(c['next'], K2, idx2, n3, n5)

    for r in cfg['pend']:
        assert r < BIG and isprime(r)
    node(load(tag), set(cfg['pend']), {}, cfg['s3'], cfg['s5'])
    print(tag, 'ACCEPTED', dict(stats))


if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    main(sys.argv[1])
