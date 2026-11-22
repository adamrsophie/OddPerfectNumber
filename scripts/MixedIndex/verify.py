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


class InvalidCertificate(Exception):
    pass


def require(condition, message="certificate condition failed"):
    # Certificate conditions must remain active under python -O.
    if not condition:
        raise InvalidCertificate(message)


def natural(value):
    return type(value) is int and value >= 0


def cli_error(error, status):
    print("REJECTED:" if status == 1 else "ERROR:", error, file=sys.stderr)
    sys.exit(status)


BIG = 2 ** 64
stats = Counter()
primes = set()
maxF = [0]
depth = Counter()


def F(k, p):
    return sum(p ** i for i in range(k))


def val(n, r):
    require(natural(n) and n > 0 and natural(r) and r >= 2, "invalid valuation input")
    v = 0
    while n % r == 0:
        n //= r; v += 1
    return v


def prime_ok(r):
    require(natural(r) and 2 <= r < BIG and isprime(r), r)
    primes.add(r)


def check_abund(S, K, idx):
    num, den = 13 * 6, 9 * 5          # sigma(3^2) / 3^2 and sigma(5) / 5
    seen = set()
    for p, e in S:
        require(natural(p) and natural(e), "abundance components must be natural numbers")
        require(p in K and p not in seen and p not in (3, 5, 7), 'certificate condition at original line 39')
        seen.add(p)
        require(e <= (idx[p] - 1 if p in idx else 2), 'certificate condition at original line 41')   # p^e | N
        num *= F(e + 1, p); den *= p ** e
    require(num > 2 * den, 'not abundant')


def node(t, K, idx, s3, s5, d):
    depth[d] += 1
    if 'close' in t:
        require(t['close'] == 'abund', 'certificate condition at original line 49')
        stats['abund'] += 1
        return check_abund(t['set'], K, idx)
    p = t['p']
    require(p in K and p not in (3, 5, 7) and p not in idx, 'certificate condition at original line 53')
    require(sorted(t['br']) == ['3', '5', '7'], 'certificate condition at original line 54')
    stats['node'] += 1
    for ks, c in t['br'].items():
        k = int(ks)
        f = F(k, p)
        maxF[0] = max(maxF[0], f)
        n3, n5 = s3 + val(f, 3), s5 + val(f, 5)
        rule = c.get('close')
        if rule == 'seven':
            require(f % 7 == 0, 'certificate condition at original line 63'); stats['seven'] += 1; continue
        if rule == 'cap3':
            require(n3 > 2, 'certificate condition at original line 65'); stats['cap3'] += 1; continue
        if rule == 'cap5':
            require(n5 > 1, 'certificate condition at original line 67'); stats['cap5'] += 1; continue
        require(rule is None and 'force' in c, 'certificate condition at original line 68')
        K2 = set(K)
        for r in c['force']:
            require(f % r == 0 and r not in (2, 3, 5, 7), 'certificate condition at original line 71')
            prime_ok(r); K2.add(r)
        stats['force'] += len(c['force'])
        idx2 = dict(idx); idx2[p] = k
        node(c['next'], K2, idx2, n3, n5, d + 1)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        cli_error('usage: verify.py CERTIFICATE.json', 2)
    try:
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
    except InvalidCertificate as error:
        cli_error(error, 1)
    except (OSError, ValueError, KeyError, TypeError, IndexError, AttributeError,
            RecursionError, ZeroDivisionError, OverflowError) as error:
        cli_error(error, 2)
