"""Independent check of cert.json (does not import search.py).
Root facts: N odd perfect, 5 special with exponent 1, v_3(N) = 2, every ordinary prime p has
3 | m_p or 5 | m_p or 7 | m_p (m_p = v_p(N) + 1). Then sigma(9) = 13 gives 13 | N, and
sigma(5) = 6 sends one factor 3.
Checks every step with exact integers; primality by sympy isprime, which is a proof below 2^64;
larger primes are rejected (none should occur).
Usage: python3 -I verify.py cert.json"""
import json, sys
from collections import Counter
from sympy import isprime

BIG = 2 ** 64
stats = Counter()
primes = set()
maxF = [0]
depth = Counter()


def F(k, p):
    return sum(p ** i for i in range(k))


def val(n, r):
    v = 0
    while n % r == 0:
        n //= r; v += 1
    return v


def prime_ok(r):
    assert r < BIG and isprime(r), r
    primes.add(r)


def check_abund(S, K, idx):
    num, den = 13 * 6, 9 * 5          # sigma(3^2) / 3^2 and sigma(5) / 5
    seen = set()
    for p, e in S:
        assert p in K and p not in seen and p not in (3, 5, 7)
        seen.add(p)
        assert e <= (idx[p] - 1 if p in idx else 2)   # p^e | N
        num *= F(e + 1, p); den *= p ** e
    assert num > 2 * den, 'not abundant'


def node(t, K, idx, s3, s5, d):
    depth[d] += 1
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
        maxF[0] = max(maxF[0], f)
        n3, n5 = s3 + val(f, 3), s5 + val(f, 5)
        rule = c.get('close')
        if rule == 'seven':
            assert f % 7 == 0; stats['seven'] += 1; continue
        if rule == 'cap3':
            assert n3 > 2; stats['cap3'] += 1; continue
        if rule == 'cap5':
            assert n5 > 1; stats['cap5'] += 1; continue
        assert rule is None and 'force' in c
        K2 = set(K)
        for r in c['force']:
            assert f % r == 0 and r not in (2, 3, 5, 7)
            prime_ok(r); K2.add(r)
        stats['force'] += len(c['force'])
        idx2 = dict(idx); idx2[p] = k
        node(c['next'], K2, idx2, n3, n5, d + 1)


if __name__ == '__main__':
    sys.setrecursionlimit(10000)
    t = json.load(open(sys.argv[1]))
    prime_ok(13)
    node(t, {13}, {}, 1, 0, 0)
    print('ACCEPTED', dict(stats))
    print('distinct primes', len(primes), 'max prime', max(primes),
          'primes >= 10^6:', sum(1 for x in primes if x >= 10 ** 6),
          'max Phi value digits', len(str(maxF[0])))
    print('max depth', max(depth))
    json.dump(sorted(primes), open('cert_primes.json', 'w'))
