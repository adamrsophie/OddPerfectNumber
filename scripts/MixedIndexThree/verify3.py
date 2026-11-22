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


def F(k, p):
    return sum(p ** i for i in range(k))


def val(n, r):
    require(natural(n) and n > 0 and natural(r) and r >= 2, "invalid valuation input")
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
    # The root lists powers known to divide N. Multiplying their abundance
    # factors is justified only for distinct prime bases.
    require(all(len(x) == 2 for x in base), "invalid base component")
    require(all(natural(p) and 2 <= p < BIG and isprime(p) and natural(e)
                for p, e in base), "invalid base prime or exponent")
    base_primes = {p for p, _ in base}
    require(len(base_primes) == len(base), "duplicate base prime")
    require(cap3 is None or (natural(cap3) and cap3 >= 2 and cap3 % 2 == 0),
            "cap3 must be a positive even exact exponent or null")
    require(cap5 is None or (type(cap5) is int and cap5 == 1),
            "the supported cap5 is exactly one or null")
    require(all(p != 3 or cap3 is None or e <= cap3 for p, e in base),
            "base power exceeds the exact cap3")
    require(all(p != 5 or cap5 is None or e <= cap5 for p, e in base),
            "base power exceeds the exact cap5")
    # No ordinary source has yet been processed. The only initial receipt
    # supported here is one factor 3 from the special component at 5.
    require(natural(cfg['s3']) and cfg['s3'] <= 1 and cfg['s5'] == 0
            and type(cfg['s5']) is int, "unsupported initial valuation receipts")

    def check_abund(S, K, idx):
        num, den = 1, 1
        for p, e in base:
            num *= F(e + 1, p); den *= p ** e
        seen = set()
        for p, e in S:
            require(natural(p) and natural(e), "abundance components must be natural numbers")
            require(p not in base_primes, "abundance component repeats a base prime")
            require(p in K and p not in seen and p not in (3, 5, 7), 'certificate condition at original line 47')
            seen.add(p)
            require(e <= (idx[p] - 1 if p in idx else 2), 'certificate condition at original line 49')
            num *= F(e + 1, p); den *= p ** e
        require(num > 2 * den, 'not abundant')

    def node(t, K, idx, s3, s5):
        if 'close' in t:
            require(t['close'] == 'abund', 'certificate condition at original line 55')
            stats['abund'] += 1
            return check_abund(t['set'], K, idx)
        p = t['p']
        require(p in K and p not in (3, 5, 7) and p not in idx, 'certificate condition at original line 59')
        require(sorted(t['br']) == ['3', '5', '7'], 'certificate condition at original line 60')
        stats['node'] += 1
        for ks, c in t['br'].items():
            k = int(ks)
            f = F(k, p)
            n3, n5 = s3 + val(f, 3), s5 + val(f, 5)
            rule = c.get('close')
            if rule == 'seven':
                require(f % 7 == 0, 'certificate condition at original line 68'); stats['seven'] += 1; continue
            if rule == 'cap3':
                require(cap3 is not None and n3 > cap3, 'certificate condition at original line 70'); stats['cap3'] += 1; continue
            if rule == 'cap5':
                require(cap5 is not None and n5 > cap5, 'certificate condition at original line 72'); stats['cap5'] += 1; continue
            require(rule is None, 'certificate condition at original line 73')
            K2 = set(K)
            for r in c['force']:
                require(natural(r) and 2 <= r < BIG and isprime(r) and r not in (2, 3, 5, 7) and f % r == 0, 'certificate condition at original line 76')
                K2.add(r)
            stats['force'] += len(c['force'])
            idx2 = dict(idx); idx2[p] = k
            node(c['next'], K2, idx2, n3, n5)

    for r in cfg['pend']:
        require(natural(r) and 2 <= r < BIG and isprime(r), 'certificate condition at original line 83')
    node(load(tag), set(cfg['pend']), {}, cfg['s3'], cfg['s5'])
    print(tag, 'ACCEPTED', dict(stats))


if __name__ == '__main__':
    if len(sys.argv) != 2:
        cli_error('usage: verify3.py TAG', 2)
    try:
        sys.setrecursionlimit(50000)
        main(sys.argv[1])
    except InvalidCertificate as error:
        cli_error(error, 1)
    except (OSError, ValueError, KeyError, TypeError, IndexError, AttributeError,
            RecursionError, ZeroDivisionError, OverflowError) as error:
        cli_error(error, 2)
