#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Independent checker for a certificate cert_<name>.json written by search.py (shares no code
# with it): Pratt primality of every node, the row divisibilities, the reach of every target
# with every candidate special prime blocked, and the abundance of every case.
# Used by: the certificates behind OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean,
# CommonFiftyFive.lean, CommonEightyFive.lean, CommonOneFifteenData.lean,
# CommonNinetyFiveData.lean.
# Run: python3 verify.py cert.json [more.json ...]
#      python3 verify.py --expect '{"d": 5, "seeds": [5, 7], "special_test": [12, 1],
#          "excluded_primes": [], "exponents": {}}' cert.json
# Without --expect, OK means only that the certificate proves the statement it declares itself
# (its d, seeds, special prime test (m, r), excluded primes and exponent overrides). With
# --expect, which takes exactly one certificate, these five items must also equal the stated
# claim: d, special_test and excluded_primes as given, seeds and excluded primes compared as
# sets, exponents as a map from prime to exponent ({} when the certificate has none). The keys
# hypothesis_seeds and branch_seeds are not compared: every seed of the claim is in the compared
# seed list, and each branch seed is checked as a consequence of its source.
# Exit status: 0 when every certificate passes, 1 when a well formed certificate fails a
# mathematical check or differs from --expect, 2 for malformed data or usage (unreadable JSON,
# duplicate keys, wrong types, duplicate rows, targets or cases, a residue r outside 0 <= r < m,
# an excluded prime that is not an odd prime, an exponent other than 4).
# Requires: Python 3 and sympy. Deterministic. Running time: about ten seconds for the five
# certificates of 57, 65, 55, 85, 115; about 35 seconds for that of 95.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json
sys.set_int_max_str_digits(0)
from fractions import Fraction
from sympy import isprime, factorint

def pratt(p, memo={}):
    """Build a Pratt certificate: a witness g and the full factorization of p - 1, recursively."""
    if p in memo: return memo[p]
    if p == 2: memo[p] = True; return True
    if not isprime(p): return False
    fs = list(factorint(p - 1))
    for g in range(2, 10**4):
        if pow(g, p - 1, p) == 1 and all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            break
    else:
        return False
    ok = all(pratt(f) for f in fs)
    memo[p] = ok
    return ok

class Malformed(Exception):
    """The data does not have the certificate format: exit status 2."""


class Failed(Exception):
    """A well formed certificate fails a mathematical check: exit status 1."""


def need(cond, msg):
    if not cond: raise Failed(msg)


def form(cond, msg):
    if not cond: raise Malformed(msg)


def is_nat(x): return type(x) is int and x >= 0


def nats(v, what):
    form(type(v) is list and all(is_nat(x) for x in v), f'{what}: expected a list of natural numbers')
    return v


def nat_keys(dct, what):
    """A JSON object with decimal keys, as a dict with int keys; rejects keys that collide."""
    form(type(dct) is dict, f'{what}: expected an object')
    out = {}
    for k, v in dct.items():
        form(type(k) is str and k.isdigit(), f'{what}: key {k!r} is not a natural number')
        form(int(k) not in out, f'{what}: key {k!r} repeats an earlier key')
        out[int(k)] = v
    return out


def no_dup_keys(pairs):
    keys = [k for k, _ in pairs]
    form(len(set(keys)) == len(keys), 'duplicate key in a JSON object')
    return dict(pairs)


def profile(d, seeds, mr, excl, exps):
    """The claim of a certificate, in a form that compares equal for equal claims."""
    return {'d': d, 'seeds': sorted(set(seeds)), 'special_test': list(mr),
            'excluded_primes': sorted(set(excl)), 'exponents': exps}


def parse_expect(text):
    try:
        x = json.loads(text, object_pairs_hook=no_dup_keys)
    except ValueError as e:
        raise Malformed(f'--expect: {e}')
    form(type(x) is dict and set(x) == {'d', 'seeds', 'special_test', 'excluded_primes', 'exponents'},
         '--expect: give exactly the keys d, seeds, special_test, excluded_primes, exponents')
    form(is_nat(x['d']), '--expect: d')
    mr = nats(x['special_test'], '--expect: special_test'); form(len(mr) == 2, '--expect: special_test')
    exps = nat_keys(x['exponents'], '--expect: exponents')
    for v in exps.values(): form(is_nat(v), '--expect: exponents')
    return profile(x['d'], nats(x['seeds'], '--expect: seeds'), mr,
                   nats(x['excluded_primes'], '--expect: excluded_primes'), exps)


def check(path, expect=None):
    with open(path) as f:
        c = json.load(f, object_pairs_hook=no_dup_keys)
    form(type(c) is dict, 'top level is not an object')
    for k in ('d', 'seeds', 'special_test', 'rows', 'targets', 'cases'):
        form(k in c, f'missing key {k}')
    d = c['d']; form(is_nat(d), 'd is not a natural number')
    seeds = nats(c['seeds'], 'seeds')
    mr = nats(c['special_test'], 'special_test')
    form(len(mr) == 2, 'special_test is not a pair [m, r]')
    m, r = mr
    form(m >= 1 and 0 <= r < m, f'special_test ({m}, {r}) outside 1 <= m, 0 <= r < m')
    e = c.get('exponent', 4); form(e == 4, f'exponent {e!r} is not supported (only 4)')
    exps = nat_keys(c.get('exponents', {}), 'exponents')
    for t, v in exps.items(): form(is_nat(v), f'exponent of {t} is not a natural number')
    excl = nats(c.get('excluded_primes', []), 'excluded_primes')
    for x in excl: form(x % 2 == 1 and isprime(x), f'excluded prime {x} is not an odd prime')
    special = lambda b: b % m == r and all(b % x != x - 1 for x in excl)
    branch = nat_keys(c.get('branch_seeds', {}), 'branch_seeds')
    for b, v in branch.items(): nats(v, f'branch_seeds of {b}')
    form(type(c['rows']) is list, 'rows is not a list')
    rows = {}
    for row in c['rows']:
        form(type(row) is list and len(row) == 2 and is_nat(row[0]), f'row {row!r:.60} is not [source, [receivers]]')
        s, ts = row
        nats(ts, f'row {s}')
        form(s not in rows, f'duplicate row {s}')
        rows[s] = ts
    nodes = set(seeds) | set(rows) | {t for ts in rows.values() for t in ts}
    for v in branch.values(): nodes |= set(v)
    hyp = nats(c.get('hypothesis_seeds', []), 'hypothesis_seeds')
    T = nats(c['targets'], 'targets')
    form(len(set(T)) == len(T), 'duplicate target')
    form(type(c['cases']) is list, 'cases is not a list')
    got = {}
    for x in c['cases']:
        form(type(x) is dict and 'q' in x and 'sigma_over_D' in x, f'case {x!r:.60} lacks q or sigma_over_D')
        q = x['q']
        form(q == 'none' or is_nat(q), f'case key {q!r:.60} is neither "none" nor a natural number')
        form(q not in got, f'duplicate case {q}')
        form(type(x['sigma_over_D']) is str, f'case {q}: sigma_over_D is not a string')
        try:
            got[q] = Fraction(x['sigma_over_D'])
        except (ValueError, ZeroDivisionError):
            raise Malformed(f'case {q}: sigma_over_D is not a fraction')
    # The data is well formed from here on; what follows are the mathematical checks.
    if expect is not None:
        mine = profile(d, seeds, mr, excl, exps)
        for k in expect:
            need(mine[k] == expect[k], f'claim mismatch: {k} is {mine[k]} in the certificate, {expect[k]} expected')
    need(d % 2 == 1 and d >= 5, f'd = {d} is not an odd number at least 5')
    for p in seeds:
        need(d % p == 0 or p in hyp, f'seed {p} neither divides d nor is a declared hypothesis')
    for p in sorted(nodes):
        need(p % 2 == 1 and pratt(p), f'node {p} not Pratt prime')
    receivers = {t for ts in rows.values() for t in ts}
    for s, ts in rows.items():
        need(s in seeds or s in receivers or any(s in v for v in branch.values()), f'source {s} unconnected')
        sig = (s**d - 1) // (s - 1)
        for t in ts:
            need(t != s and sig % t == 0, f'{t} does not divide sigma({s}^{d-1})')
    for b, v in branch.items():
        for x in v: need(((b + 1) // 2) % x == 0, f'branch seed {x} does not divide ({b}+1)/2')
    need(3 not in T, 'the prime 3 is listed as a target')
    def reach(block, extra):
        R = set(seeds) | set(extra); st = list(R)
        while st:
            u = st.pop()
            if u == block: continue
            for w in rows.get(u, []):
                if w not in R: R.add(w); st.append(w)
        return R
    for x in excl: need(x not in nodes, f'excluded prime {x} used as a node')
    blocks = [None] + sorted(n for n in nodes if special(n))
    for b in blocks:
        R = reach(b, branch.get(b, []))
        miss = [t for t in T if t not in R]
        need(not miss, f'targets {miss[:5]} not reached when {b} is special')
    h = lambda t: Fraction(t**(exps.get(t, e) + 1) - 1, (t - 1) * t**exps.get(t, e))
    P = Fraction(1)
    for t in T: P *= h(t)
    want = {'none': P}
    for q in T:
        if special(q): want[q] = P / h(q) * Fraction(q + 1, q)
    missing = [q for q in want if q not in got]
    extra = [q for q in got if q not in want]
    need(not missing, f'cases missing: {missing[:5]}')
    need(not extra, f'cases not implied by the profile: {extra[:5]}')
    for q, V in want.items():
        need(got[q] == V, f'fraction mismatch at {q}')
        if not V > 2:  # the message is built only on failure: V can have thousands of digits
            raise Failed(f'case {q} not abundant (sigma/D = {V} <= 2)')
    worst = min(want.values())
    print(f'{path}: OK  d={d} seeds={seeds} hyp={hyp} branch={branch} special {m},{r} excl={excl} exps={exps}  rows={len(rows)} nodes={len(nodes)} '
          f'largest={max(nodes)} targets={len(T)} cases={len(want)} blocks_checked={len(blocks)} worst={float(worst):.6f}')


def main(argv):
    args = argv[1:]
    expect = None
    try:
        if args[:1] == ['--expect']:
            if len(args) != 3:
                print('usage: python3 verify.py --expect CLAIM_JSON cert.json  (exactly one certificate)', file=sys.stderr)
                return 2
            expect = parse_expect(args[1]); args = args[2:]
    except Malformed as x:
        print(f'MALFORMED: {x}', file=sys.stderr)
        return 2
    if not args or any(a.startswith('--') for a in args):
        print('usage: python3 verify.py [--expect CLAIM_JSON] cert.json [more.json ...]\n'
              'Without --expect, OK means that the certificate proves the statement it declares;\n'
              'CLAIM_JSON gives d, seeds, special_test, excluded_primes and exponents of the\n'
              'expected claim (see the header of this file).', file=sys.stderr)
        return 2
    status = 0
    for p in args:
        try:
            check(p, expect)
        except Failed as x:
            print(f'{p}: FAILED  {x}')
            status = max(status, 1)
        except (Malformed, OSError, ValueError, TypeError, KeyError, ZeroDivisionError, RecursionError) as x:
            print(f'{p}: MALFORMED  {x}')
            status = 2
    return status


sys.exit(main(sys.argv))
