# Untrusted helper script for the OddPerfect Lean library.
# Exact search for a factor chain tree with the defect ledger: writes the certificate that
# gen.py turns into the data module checked by OddPerfect/DefectTreeCode.lean (soundness in
# OddPerfect/DefectTreeCheck.lean). The format and the rules are those of DefectTreeCode.lean;
# check.py replays a certificate with the same rules.
#
# Setting: N odd perfect, q its special prime, D = supportDefect N q, T the total excess.
# Hypotheses: w * omega(N) + D <= K, every prime factor of N is at least u, the root prime
# divides N, and optionally T <= cap. A state assigns to primes either the special role or an
# ordinary exponent (exact, or "at least e" with e >= 4). Rows: sigma(p ^ e) for an exact
# ordinary prime, p + 1 for the special prime; their odd prime factors (facts) are forced
# primes of N. Leaves: cap (capacity at an exact prime), small (forced prime below u), budget
# (T over cap), ledger (lower bound of w * omega + D above K for every candidate of q), abund
# (an abundant divisor). Branch: a forced prime; children special (when allowed), exponents
# 2, 4, ... exactly, and a last child "at least e".
#
# Run: python3 search.py K W U ROOT CAP ROWS OUT [noledger] [maxnodes=M]
#   statement A, K = 2: python3 search.py 2 0 3 3 none rows.json cert2.json
#   Flags: noledger, maxnodes=M, maxexp=E (a chain above exponent E is left open),
#   factor_seconds=S. CAP is an integer or none. ROWS is the frozen row table (read if
#   present, missing rows are factored with sympy and the file is rewritten).
#   OUT gets the certificate.
# Requires: Python 3, sympy (only for rows not yet in ROWS).
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.

import sys, json, os, signal

args = [a for a in sys.argv[1:] if '=' not in a and a != 'noledger']
opts = dict(a.split('=') for a in sys.argv[1:] if '=' in a)
NOLEDGER = 'noledger' in sys.argv[1:]
K, W, U, ROOT = map(int, args[:4])
CAP = None if args[4] == 'none' else int(args[4])
ROWS, OUT = args[5], args[6]
MAXNODES = int(opts.get('maxnodes', 10 ** 7))
MAXEXP = int(opts.get('maxexp', 400))
FACTOR_SECONDS = int(opts.get('factor_seconds', 600))

rows = {}
pm1 = {}
if os.path.exists(ROWS):
    d = json.load(open(ROWS))
    rows = {(p, m): [tuple(f) for f in fs] for p, m, fs in d['rows']}
    pm1 = {int(p): fs for p, fs in d['pm1'].items()}
dirty = False
used = set()

class Slow(Exception):
    pass

def _alarm(*a):
    raise Slow()

def gs(p, m):
    return sum(p ** i for i in range(m + 1))

def factor_row(n):
    """Odd prime factors with exponents. On a timeout, only proven prime factors found by
    trial division and the sympy factorization with a limit are kept (a lower bound)."""
    from sympy import factorint, isprime
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(FACTOR_SECONDS)
    try:
        f = factorint(n)
    except Slow:
        f = {r: v for r, v in factorint(n, limit=10 ** 6).items() if isprime(r)}
    finally:
        signal.alarm(0)
    for r in f:
        assert isprime(r)
    return sorted((r, v) for r, v in f.items() if r != 2)

def facts_row(p, m):
    global dirty
    key = (p, m)
    used.add(key)
    if key not in rows:
        rows[key] = factor_row(gs(p, m))
        dirty = True
    return rows[key]

# A state: os is a list of entries (p, e, exact), newest first; sp is the special prime or 0.

def facts_e(x):
    return facts_row(x[0], x[1]) if x[2] else []

def sp_facts(os_, sp):
    return [] if sp == 0 else facts_row(sp, 1)

def all_facts(os_, sp):
    out = list(sp_facts(os_, sp))
    for x in os_:
        out += facts_e(x)
    return out

def k_of(fs, r):
    for y in fs:
        if y[0] == r:
            return y[1]
    return 0

def forced(os_, sp, r):
    return any(y[0] == r for y in all_facts(os_, sp))

def fresh(os_, sp, r):
    return all(x[0] != r for x in os_) and r != sp

def find_entry(os_, p):
    for x in os_:
        if x[0] == p:
            return x
    return None

def recv_l(fs, c):
    return sum(k for r, k in fs if r % 3 == 1 and r != c)

def ent_b(x, c):
    p, e, _ = x
    fs = facts_e(x)
    if e == 2:
        return max(recv_l(fs, c) - 1, 0)
    if e >= 4:
        return ((0 if p == 3 else 3 * (e // 2 - 2)) + (e if p % 3 == 2 else 0)
                + 2 * k_of(fs, 3) + recv_l(fs, c))
    return 0

def three_t(os_):
    x = find_entry(os_, 3)
    return 0 if x is None else max(x[1] // 2 - 2, 0)

def bound(os_, sp, c):
    b = three_t(os_) + (4 if 3 < U else 0)
    if sp != 0:
        b += recv_l(sp_facts(os_, sp), c)
    return b + sum(ent_b(x, c) for x in os_)

def cands(os_, sp):
    if sp != 0:
        return [sp]
    return [0] + [y[0] for y in all_facts(os_, sp) if y[0] % 4 == 1]

def known_primes(os_, sp):
    s = set(x[0] for x in os_) | set(y[0] for y in all_facts(os_, sp))
    if sp != 0:
        s.add(sp)
    return sorted(s)

def allowed(os_, sp, p):
    """The largest admissible exponent f for p in an abundant divisor, or None."""
    x = find_entry(os_, p)
    if x is not None:
        return x[1]
    if p == sp and p != 0:
        return 1
    if not forced(os_, sp, p):
        return None
    return 2 if (sp != 0 or p % 4 != 1) else 1

def leaf(os_, sp):
    """A closing leaf for the state, or None. Mirrors the leaf checks of DefectTreeCode."""
    for x in sorted(os_):
        if x[2]:
            r, e = x[0], x[1]
            wsum = k_of(sp_facts(os_, sp), r) + sum(k_of(facts_e(y), r) for y in os_)
            if e < wsum:
                return {'t': 'cap', 'r': r}
    for r in sorted(set(y[0] for y in all_facts(os_, sp))):
        if r < U:
            return {'t': 'small', 'r': r}
    if CAP is not None and CAP < sum(x[1] // 2 - 1 for x in os_):
        return {'t': 'budget'}
    if not NOLEDGER:
        ks = known_primes(os_, sp) if W > 0 else []
        if all(K < bound(os_, sp, c) + W * len(ks) for c in cands(os_, sp)):
            return {'t': 'ledger', 'ks': ks}
    ws = [(p, allowed(os_, sp, p)) for p in known_primes(os_, sp)]
    num, den = 1, 1
    for p, f in ws:
        num *= gs(p, f)
        den *= p ** f
    if 2 * den < num:
        return {'t': 'abund', 'ws': ws}
    return None

NODES = [0]
OPEN = []
STATS = {}

def count(kind):
    STATS[kind] = STATS.get(kind, 0) + 1

def chain(os_, sp, r):
    """The chain of exponent children of the branch prime r."""
    items = []
    e = 2
    while True:
        if e >= 4:
            hl = leaf([(r, e, False)] + os_, sp)
            if hl is not None:
                count('high')
                count(hl['t'])
                NODES[0] += 1
                items.append({'t': 'high', 'kid': hl})
                return items
        if e > MAXEXP:
            OPEN.append(('exponent', os_, sp, r))
            items.append({'t': 'high', 'kid': {'t': 'open'}})
            return items
        items.append({'t': 'ord', 'kid': node([(r, e, True)] + os_, sp)})
        e += 2

def branch(os_, sp, r):
    count('br')
    spk = None
    if sp == 0 and r % 4 == 1:
        spk = node(os_, r)
    return {'t': 'br', 'r': r, 'sp': spk, 'ch': chain(os_, sp, r)}

def node(os_, sp):
    NODES[0] += 1
    if NODES[0] > MAXNODES:
        OPEN.append(('nodes', os_, sp))
        return {'t': 'open'}
    lf = leaf(os_, sp)
    if lf is not None:
        count(lf['t'])
        return lf
    fr = sorted(set(y[0] for y in all_facts(os_, sp) if fresh(os_, sp, y[0])))
    if not fr:
        OPEN.append(('noforced', os_, sp))
        return {'t': 'open'}
    return branch(os_, sp, fr[0])

NODES[0] += 1
cert = branch([], 0, ROOT)

def pm1_of(p):
    global dirty
    if p not in pm1:
        from sympy import factorint
        f = factorint(p - 1)
        pm1[p] = sorted(r for r, v in f.items() for _ in range(v))
        dirty = True
    for r in set(pm1[p]):
        if r >= 200:
            pm1_of(r)

tab_rows = sorted(used)
for key in tab_rows:
    for r, k in rows[key]:
        if r >= 200:
            pm1_of(r)
if dirty or not os.path.exists(ROWS):
    json.dump({'rows': [[p, m, [list(f) for f in rows[(p, m)]]] for p, m in sorted(rows)],
               'pm1': {str(p): pm1[p] for p in sorted(pm1)}}, open(ROWS, 'w'), indent=0,
              sort_keys=True)
json.dump({'params': {'K': K, 'w': W, 'u': U, 'root': ROOT, 'cap': CAP},
           'rows': [[p, m] for p, m in tab_rows], 'cert': cert},
          open(OUT, 'w'), sort_keys=True)
maxrow = max((r for key in tab_rows for r, _ in rows[key]), default=0)
print('K', K, 'w', W, 'u', U, 'root', ROOT, 'cap', CAP, 'noledger' if NOLEDGER else '')
print('nodes', NODES[0], 'stats', dict(sorted(STATS.items())), 'open', len(OPEN))
print('rows', len(tab_rows), 'largest prime in a row', maxrow)
for o in OPEN[:10]:
    print('  OPEN', o)
