# Untrusted helper script for the OddPerfect Lean library.
# The strict input loader shared by search.py, check.py and gen.py: the row table (rows.json)
# and the certificate (written by search.py). Exact types (an integer is `type(x) is int`, so no
# boolean and no float), natural numbers at least 0, a closed set of fields and of node tags,
# no repeated JSON key, no repeated row. Any violation ends the calling script with exit
# status 2 and a one line message `malformed input: ...`.
# Also the checks of a factorization of p - 1 (pm1_problem), the trial division used for
# primes below 200 (trial_prime), as the Lean checker OddPerfect/DefectTreeCode.lean reads them,
# and the certified route of a prime (certify) with which search.py validates its facts.
# Optional field witness of the row table: {p: a} with a stored Pratt witness a for an entry p
# of pm1 (written by search.py for each factorization of p - 1 it adds); a table without it is
# a legacy table, whose witnesses are found by a scan bounded by LEGACY_SCAN.
# Requires: Python 3 standard library only.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.

import json
import sys

# Fields of each node kind, as in the Lean types Leaf and Cert (open: a leaf left open by
# search.py, well formed but never accepted).
NODE = {'cap': {'r'}, 'small': {'r'}, 'budget': set(), 'ledger': {'ks'}, 'abund': {'ws'},
        'open': set(), 'br': {'r', 'sp', 'ch'}}
CHAIN = ('ord', 'high')
PARAMS = ('K', 'w', 'u', 'root', 'cap')


def malformed(msg):
    print('malformed input: ' + msg, file=sys.stderr)
    sys.exit(2)


def nat(x):
    """A natural number as Lean reads it: an integer at least 0, not a boolean or a float."""
    return type(x) is int and x >= 0


def nats(x, n=None):
    return type(x) is list and (n is None or len(x) == n) and all(nat(y) for y in x)


def _no_dup_keys(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            raise ValueError('repeated key %r' % k)
        d[k] = v
    return d


def load_json(path):
    try:
        with open(path) as f:
            return json.load(f, object_pairs_hook=_no_dup_keys)
    except (OSError, ValueError, RecursionError) as e:
        malformed('%s: %s' % (path, e))


def decimal(p):
    """The natural number written by the string p (decimal digits, no leading zero), or None.
    A string beyond the integer string conversion limit of Python is None, not a traceback."""
    try:
        return int(p) if p.isascii() and p.isdigit() and str(int(p)) == p else None
    except ValueError:
        return None


def load_rows(path):
    """The row table: (rows, pm1, partset, wit) with rows {(p, m): [(r, k), ...]}, pm1
    {p: [q, ...]}, partset the set of rows marked partial and wit {p: a} the stored Pratt
    witnesses (empty for a legacy table)."""
    d = load_json(path)
    if type(d) is not dict or not {'rows', 'pm1'} <= set(d) <= {'rows', 'pm1', 'partial',
                                                                'witness'} or \
            type(d['rows']) is not list or type(d['pm1']) is not dict or \
            type(d.get('partial', [])) is not list or type(d.get('witness', {})) is not dict:
        malformed('%s: expected the fields rows (a list), pm1 (an object) and optionally '
                  'partial (a list) and witness (an object)' % path)
    rows = {}
    for row in d['rows']:
        if not (type(row) is list and len(row) == 3 and nat(row[0]) and nat(row[1]) and
                type(row[2]) is list and all(nats(f, 2) for f in row[2])):
            malformed('%s: row %r is not [p, m, [[r, k], ...]] with natural numbers'
                      % (path, row))
        if (row[0], row[1]) in rows:
            malformed('%s: repeated row (%d, %d)' % (path, row[0], row[1]))
        rows[(row[0], row[1])] = [tuple(f) for f in row[2]]
    pm1 = {}
    for p, fs in d['pm1'].items():
        if decimal(p) is None or not nats(fs):
            malformed('%s: pm1 entry %r is not a decimal number (no leading zero, at most 4300 '
                      'digits) with a list of natural numbers' % (path, p[:50]))
        pm1[int(p)] = list(fs)
    partset = set()
    for key in d.get('partial', []):
        if not (nats(key, 2) and tuple(key) in rows):
            malformed('%s: partial entry %r is not a row of the table' % (path, key))
        partset.add(tuple(key))
    wit = {}
    for p, a in d.get('witness', {}).items():
        if decimal(p) not in pm1 or not nat(a):
            malformed('%s: witness entry %r is not an entry of pm1 with a natural number'
                      % (path, p[:50]))
        wit[int(p)] = a
    return rows, pm1, partset, wit


def shape(t, where='cert'):
    """Exact tags and fields of a certificate node, recursively; None or a description."""
    if type(t) is not dict or type(t.get('t')) is not str or t['t'] not in NODE:
        return '%s: not a node with a known tag' % where
    if set(t) != NODE[t['t']] | {'t'}:
        return '%s: node %s with fields %s' % (where, t['t'], sorted(t))
    if 'r' in t and not nat(t['r']):
        return '%s: %s prime is not a natural number' % (where, t['t'])
    if 'ks' in t and not nats(t['ks']):
        return '%s: ledger primes are not natural numbers' % where
    if 'ws' in t and not (type(t['ws']) is list and all(nats(w, 2) for w in t['ws'])):
        return '%s: abund pairs are not pairs of natural numbers' % where
    if t['t'] == 'br':
        if t['sp'] is not None:
            bad = shape(t['sp'], where + '.sp')
            if bad:
                return bad
        if type(t['ch']) is not list:
            return '%s: chain is not a list' % where
        for i, it in enumerate(t['ch']):
            if type(it) is not dict or set(it) != {'t', 'kid'} or type(it['t']) is not str or \
                    it['t'] not in CHAIN:
                return '%s.ch[%d]: not a chain item ord or high with field kid' % (where, i)
            bad = shape(it['kid'], '%s.ch[%d]' % (where, i))
            if bad:
                return bad
    return None


def load_cert(path):
    """The certificate: exactly the fields params (K, w, u, root natural numbers, cap null or a
    natural number), rows (pairs of natural numbers) and cert (a tree of known nodes)."""
    c = load_json(path)
    if type(c) is not dict or set(c) != {'params', 'rows', 'cert'}:
        malformed('%s: expected exactly the fields params, rows and cert' % path)
    P = c['params']
    if type(P) is not dict or set(P) != set(PARAMS) or \
            not all(nat(P[k]) for k in PARAMS[:4]) or not (P['cap'] is None or nat(P['cap'])):
        malformed('%s: params must be exactly K, w, u, root (natural numbers) and cap (null or a '
                  'natural number)' % path)
    if type(c['rows']) is not list or not all(nats(r, 2) for r in c['rows']):
        malformed('%s: rows must be a list of pairs of natural numbers' % path)
    try:
        bad = shape(c['cert'])
    except RecursionError:
        bad = 'the tree is nested too deeply'
    if bad:
        malformed('%s: %s' % (path, bad))
    return c


def trial_prime(n):
    return n >= 2 and all(n % k for k in range(2, n))


def composite(n):
    """True when a Miller and Rabin base proves n >= 200 composite, so that the Pratt witness
    scan below n is never started for a composite (it would not end in practice)."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(b, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return True
    return False


# Bound of the witness scan for a prime without a stored witness (legacy tables). The least
# witness of every entry of the landed rows.json is at most 74.
LEGACY_SCAN = 10000


def witness_ok(p, fs, a):
    """a ^ (p - 1) = 1 and a ^ ((p - 1) / r) != 1 mod p for every r of fs, with 1 < a < p."""
    return 1 < a < p and pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // r, p) != 1
                                                       for r in set(fs))


def least_witness(p, fs, bound=None):
    """(a, None) with the least witness a below p (and below bound, if given); (None,
    'composite') when a Miller and Rabin base proves p composite or no a < p is a witness;
    (None, 'unknown') when the scan stops at the bound, which decides nothing."""
    if composite(p):
        return None, 'composite'
    top = p if bound is None else min(p, bound)
    a = next((a for a in range(2, top) if witness_ok(p, fs, a)), None)
    if a is not None:
        return a, None
    return None, 'composite' if top == p else 'unknown'


def pratt_witness(p, fs):
    """The least a < p with a ^ (p - 1) = 1 and a ^ ((p - 1) / r) != 1 mod p for every r of fs,
    or None (also at once when p is proven composite)."""
    return least_witness(p, fs)[0]


def certify(p, pm1, wit, done, skip=()):
    """None when p is certified prime by the route of check.py and gen.py: trial division
    below 200; from 200 on a factorization of p - 1 in pm1 (integers above 1, product p - 1,
    each factor certified recursively) and a Pratt witness (the stored one, verified, or for a
    legacy entry the least one, scanned up to LEGACY_SCAN). 'partial' when the route reaches a
    prime of skip (a p - 1 whose factorization timed out); otherwise a description. Certified
    primes are added to done."""
    if p < 200:
        return None if trial_prime(p) else '%d is below 200 and not prime by trial division' % p
    if p in done:
        return None
    if p in skip:
        return 'partial'
    if p not in pm1:
        return 'no factorization of %d - 1 for the Pratt certificate' % p
    fs = pm1[p]
    bad = pm1_problem(p, fs)
    if bad:
        return bad
    for r in sorted(set(fs)):
        bad = certify(r, pm1, wit, done, skip)
        if bad:
            return bad
    if p in wit:
        if not witness_ok(p, fs, wit[p]):
            return 'the stored Pratt witness %d of %d fails' % (wit[p], p)
    else:
        a, why = least_witness(p, fs, LEGACY_SCAN)
        if a is None:
            return ('no Pratt witness below %d for %d (undecided)' % (LEGACY_SCAN, p)
                    if why == 'unknown' else '%d is not certified prime' % p)
    done.add(p)
    return None


def pm1_problem(p, fs):
    """None when fs lists integers greater than 1 (not booleans) whose product is p - 1, else
    a description. Primality of the factors is checked by the caller (recursively)."""
    if type(fs) is not list or not all(type(r) is int and r > 1 for r in fs):
        return 'the factorization of %d - 1 lists a factor that is not an integer above 1' % p
    prod = 1
    for r in fs:
        prod *= r
    if prod != p - 1:
        return 'the factorization of %d - 1 does not multiply back' % p
    return None
