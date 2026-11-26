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
# Run: python3 search.py K W U ROOT CAP ROWS OUT [noledger] [maxnodes=M] [maxexp=E]
#   [factor_seconds=S]
#   statement A, K = 2: python3 search.py 2 0 3 3 none rows.json cert2.json
#   K and W are natural numbers, U is at least 3, ROOT is a prime at least 3, CAP is a natural
#   number or none, M and S are at least 1 and E at least 2 (decimal digits only). ROWS is the
#   frozen row table (read if present, missing rows are factored with sympy and the file is
#   rewritten). OUT gets the certificate. ROWS and OUT must be different files (also through a
#   symbolic or a hard link), otherwise exit status 2 before the search.
#   Flags: noledger, maxnodes=M (at most M nodes are expanded, leaves and high leaves included;
#   every node beyond them is an open leaf, not counted), maxexp=E (a chain above exponent E is
#   left open), factor_seconds=S (a deadline for each factoring step, also for the
#   factorizations of p - 1).
# Partial rows: a row whose factorization did not finish keeps the odd prime factors proven
# before the deadline and is listed in the field "partial" of ROWS (absent when there is none).
# A marked row is factored again when the search uses it; the new facts are merged with the
# stored ones (for each prime the larger valuation, no stored factor dropped) and the merged
# facts must divide the row. A p - 1 whose factorization did not finish is not stored. Every
# unmarked row must multiply back to its value up to a power of 2 (except the nine landed rows
# of LANDED_PARTIAL, pinned to their recorded facts), and every stored factorization of p - 1
# must list integers above 1 that multiply back to p - 1. ROWS is read by the strict loader
# certio.py. Pratt data is stored for every fact prime from 200 on and for the root prime, with
# the least Pratt witness of each new factorization of p - 1 (field witness of ROWS), searched
# below certio.LEGACY_SCAN only; when none is found there the factorization is kept, no witness
# is stored, and validation leaves the prime undecided (exit 3).
# Validation: before anything is written, every row the certificate uses must list each prime
# once, multiply back (unless partial), and each of its facts and the root prime must be
# certified prime by the route of check.py and gen.py (certio.certify). A tree that closed on
# facts that fail this is only raw closed: nothing is written and the exit status is 3.
# Exit status: 0 when the tree closes (no open leaf), every factorization finished and the
# validation passed (the last line says closed and validated), 1 when a leaf stays open or a
# row or a p - 1 stayed partial (check.py and gen.py reject such a certificate), 2 for a usage
# error or an unreadable or rejected row table, 3 when the validation fails (nothing written).
# Output: both files are written under temporary names and renamed into place afterwards.
# Requires: Python 3, sympy (only for rows not yet in ROWS).
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.

import sys, json, os, signal, math


def usage(why):
    print('usage: python3 search.py K W U ROOT CAP ROWS OUT [noledger] [maxnodes=M] [maxexp=E] '
          '[factor_seconds=S]: %s' % why, file=sys.stderr)
    sys.exit(2)


def nat_arg(s, name, low):
    """A command line number: decimal digits only (at most 4300), at least low."""
    try:
        n = int(s) if s.isascii() and s.isdigit() else -1
    except ValueError:
        n = -1
    if n < low:
        usage('%s must be a natural number at least %d, got %r' % (name, low, s[:50]))
    return n


def is_prime_small(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


args = [a for a in sys.argv[1:] if '=' not in a and a != 'noledger']
NOLEDGER = 'noledger' in sys.argv[1:]
opts = {}
for a in sys.argv[1:]:
    if '=' in a:
        key, _, val = a.partition('=')
        if key not in ('maxnodes', 'maxexp', 'factor_seconds') or key in opts:
            usage('unknown or repeated option %r' % a)
        opts[key] = val
if len(args) != 7:
    usage('expected 7 arguments, got %d' % len(args))
K = nat_arg(args[0], 'K', 0)
W = nat_arg(args[1], 'W', 0)
U = nat_arg(args[2], 'U', 3)
ROOT = nat_arg(args[3], 'ROOT', 3)
if not is_prime_small(ROOT):
    usage('ROOT must be a prime, got %d' % ROOT)
CAP = None if args[4] == 'none' else nat_arg(args[4], 'CAP', 0)
ROWS, OUT = args[5], args[6]
MAXNODES = nat_arg(opts.get('maxnodes', str(10 ** 7)), 'maxnodes', 1)
MAXEXP = nat_arg(opts.get('maxexp', '400'), 'maxexp', 2)
FACTOR_SECONDS = nat_arg(opts.get('factor_seconds', '600'), 'factor_seconds', 1)
# (factor_seconds at least 1: signal.alarm(0) would switch the deadline off.)


def same_file(a, b):
    """True when the paths a and b name one file: equal after resolving symbolic links, or
    one file through a hard link."""
    if os.path.realpath(a) == os.path.realpath(b):
        return True
    try:
        return os.path.samefile(a, b)
    except OSError:
        return False


if same_file(ROWS, OUT):
    usage('ROWS and OUT name the same file %r' % OUT)

def gs(p, m):
    return sum(p ** i for i in range(m + 1))


# Landed rows whose factorization did not finish (factor_seconds=60), written before partial
# rows were marked; each is pinned to its recorded facts, a lower bound that every rule of the
# checker allows. Any other unmarked row must multiply back.
LANDED_PARTIAL = {
    (88741, 10): [(89, 1)],
    (6619231, 10): [(2311, 1), (732491, 1), (3436841, 1), (1255056807467, 1)],
    (262209281, 10): [(23, 1), (67, 1), (947, 1)],
    (52379047267, 10): [(23, 1), (67, 1), (24509, 1), (2898485987, 1)],
    (297134095231, 4): [(5, 1), (2311, 1)],
    (1957650063931, 6): [(43, 1), (583171, 1), (8460677, 1), (16222061143, 1)],
    (1957650063931, 8): [(3, 2), (7, 1), (13, 1), (37, 2), (73, 1), (271, 1), (895091017, 1),
                         (14098470301, 1), (15683402202973, 1)],
    (31747594185191, 8): [(19, 1), (37, 1), (181, 1), (199, 1), (397, 1), (2671, 1),
                          (548749, 1), (82339759, 1)],
    (241562563680036301, 6): [(29, 1), (700220696536117, 1)],
}


def odd_cofactor(n, fs):
    """n divided by every r ^ k of fs and by its powers of 2, or None when a fact (r, k) is not
    an odd r > 2 with k >= 1 and r ^ k dividing what is left."""
    for r, k in fs:
        if not (r > 2 and 1 <= k <= n.bit_length() and n % r ** k == 0):
            return None
        n //= r ** k
    while n > 1 and n % 2 == 0:
        n //= 2
    return n


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certio     # the strict loader shared with check.py and gen.py (exit 2 on violation)

rows = {}
pm1 = {}
PARTSET = set()       # marked rows: factored again when used
WIT = {}              # stored Pratt witnesses (field witness)
if os.path.exists(ROWS):
    rows, pm1, PARTSET, WIT = certio.load_rows(ROWS)
    for (p, m), fs in sorted(rows.items()):
        if (p, m) in PARTSET or LANDED_PARTIAL.get((p, m)) == fs:
            continue
        if odd_cofactor(gs(p, m), fs) != 1:
            print('rejected row table %s: the facts of the row (%d, %d) do not multiply back to '
                  'its value and the row is not marked partial' % (ROWS, p, m), file=sys.stderr)
            sys.exit(2)
    for p, fs in sorted(pm1.items()):
        bad = certio.pm1_problem(p, fs)
        if bad:
            print('rejected row table %s: %s' % (ROWS, bad), file=sys.stderr)
            sys.exit(2)
dirty = False
used = set()

class Slow(Exception):
    pass

def _alarm(*a):
    raise Slow()

def under_deadline(work):
    """Runs work() with an alarm of FACTOR_SECONDS; True when it finished in time."""
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(FACTOR_SECONDS)
    try:
        work()
        return True
    except Slow:
        return False
    finally:
        signal.alarm(0)

def factor_row(n):
    """Odd prime factors with exponents, and whether the factorization is complete. The full
    factorization and its primality checks run under one deadline; after a timeout, the sympy
    factorization with a limit and the primality checks of its factors run under a second
    deadline, and only the factors proven prime before it expires are kept (a lower bound).
    Complete means that the kept facts multiply back to n up to a power of 2."""
    from sympy import factorint, isprime
    f = {}

    def full():
        g = factorint(n)
        for r in g:
            if not isprime(r):
                raise SystemExit('factorint returned the composite factor %d' % r)
        f.update(g)

    def limited():
        for r, v in factorint(n, limit=10 ** 6).items():
            if isprime(r):
                f[r] = v

    timed_out = not under_deadline(full)
    if timed_out:
        f.clear()
        under_deadline(limited)
    fs = sorted((r, v) for r, v in f.items() if r != 2)
    return fs, odd_cofactor(n, fs) == 1, timed_out

PARTIAL = []
TRIED = set()      # rows factored in this run

def facts_row(p, m):
    global dirty
    key = (p, m)
    used.add(key)
    if key not in rows or (key in PARTSET and key not in TRIED):
        TRIED.add(key)
        new, complete, timed_out = factor_row(gs(p, m))
        if key in rows:
            # Resuming a marked row: merge, never drop an established factor. For each prime
            # the larger valuation of the stored and the new facts is kept, and the merged
            # facts must divide the row.
            merged = dict(rows[key])
            for r, k in new:
                merged[r] = max(merged.get(r, 0), k)
            new = sorted(merged.items())
            if odd_cofactor(gs(p, m), new) is None:
                print('rejected row table %s: the facts %r of the marked row (%d, %d) do not '
                      'divide its value' % (ROWS, new, p, m), file=sys.stderr)
                sys.exit(2)
            complete = odd_cofactor(gs(p, m), new) == 1
        rows[key] = new
        if complete:
            PARTSET.discard(key)
            if timed_out:
                print('row', p, m, ': the full factorization timed out, the factorization '
                      'with a limit is complete', flush=True)
        else:
            PARTSET.add(key)
            PARTIAL.append(key)
            print('PARTIAL row', p, m, 'factor_seconds', FACTOR_SECONDS, 'kept', rows[key],
                  flush=True)
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
        if NODES[0] >= MAXNODES:      # the budget is spent: the rest of the chain stays open
            OPEN.append(('nodes', os_, sp, r))
            items.append({'t': 'high', 'kid': {'t': 'open'}})
            return items
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
    if NODES[0] >= MAXNODES:
        OPEN.append(('nodes', os_, sp))
        return {'t': 'open'}
    NODES[0] += 1
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

PARTIAL_PM1 = []      # primes whose p - 1 timed out in this run (not tried again)

def pm1_of(p):
    """Stores the factorization of p - 1 (and recursively of r - 1 for its prime factors r from
    200 on). The factorization and its primality checks run under the deadline; after a timeout
    nothing is stored (a partial factorization of p - 1 is no Pratt data), and p is reported."""
    global dirty
    if p in PARTIAL_PM1:
        return
    if p not in pm1:
        from sympy import factorint, isprime
        f = {}

        def full():
            g = factorint(p - 1)
            for r in g:
                if not isprime(r):
                    raise SystemExit('factorint returned the composite factor %d' % r)
            f.update(g)

        if not under_deadline(full):
            PARTIAL_PM1.append(p)
            print('PARTIAL pm1', p, 'factor_seconds', FACTOR_SECONDS, 'nothing stored',
                  flush=True)
            return
        pm1[p] = sorted(r for r, v in f.items() for _ in range(v))
        a = certio.pratt_witness(p, pm1[p])
        if a is not None:
            WIT[p] = a
        dirty = True
    for r in set(pm1[p]):
        if r >= 200:
            pm1_of(r)

tab_rows = sorted(used)
# Pratt data for every prime the Lean checker tests with isPr (DefectTreeCode.lean): each fact
# prime of the table rows (tabOK) and the root prime (brHead at the root). A branch at a node
# needs nothing more: its prime is forced, so it is a fact prime of a row.
for key in tab_rows:
    for r, k in rows[key]:
        if r >= 200:
            pm1_of(r)
if ROOT >= 200:
    pm1_of(ROOT)


def validation_problem():
    """None when every fact the certificate uses is valid: one entry per prime in each used
    row, the facts multiply back (unless the row is partial or one of LANDED_PARTIAL), each
    fact prime and the root prime certified by certio.certify. Primes whose route meets a
    p - 1 that timed out are left to the partial status."""
    done = set()
    for key in tab_rows:
        fs = rows[key]
        if len(set(r for r, _ in fs)) != len(fs):
            return 'the row (%d, %d) lists a prime in two entries' % key
        if key not in PARTSET and LANDED_PARTIAL.get(key) != fs and \
                odd_cofactor(gs(*key), fs) != 1:
            return 'the facts of the row (%d, %d) do not multiply back to its value' % key
        for r, _ in fs:
            bad = certio.certify(r, pm1, WIT, done, PARTIAL_PM1)
            if bad and bad != 'partial':
                return 'the row (%d, %d): %s' % (key[0], key[1], bad)
    bad = certio.certify(ROOT, pm1, WIT, done, PARTIAL_PM1)
    if bad and bad != 'partial':
        return 'the root prime: %s' % bad
    return None


bad = validation_problem()
if bad:
    print('%s, not validated: %s; nothing written' % ('open' if OPEN else 'raw closed', bad),
          file=sys.stderr)
    sys.exit(3)


def write_files(pending):
    """Writes each (path, object) under a temporary name next to the file the path resolves
    to, then renames each into place, so that a failure never leaves a truncated file."""
    made = []
    for path, obj, kw in pending:
        real = os.path.realpath(path)
        tmp = os.path.join(os.path.dirname(real), '.%s.%d.tmp' % (os.path.basename(real),
                                                                   os.getpid()))
        with open(tmp, 'w') as f:
            json.dump(obj, f, **kw)
        made.append((tmp, real))
    for tmp, real in made:
        os.replace(tmp, real)


pending = []
if dirty or not os.path.exists(ROWS):
    table = {'rows': [[p, m, [list(f) for f in rows[(p, m)]]] for p, m in sorted(rows)],
             'pm1': {str(p): pm1[p] for p in sorted(pm1)}}
    if PARTSET:       # written only when there is a mark, so complete tables keep their bytes
        table['partial'] = [[p, m] for p, m in sorted(PARTSET)]
    if WIT:           # likewise: a legacy table without witnesses keeps its bytes
        table['witness'] = {str(p): WIT[p] for p in sorted(WIT)}
    pending.append((ROWS, table, {'indent': 0, 'sort_keys': True}))
pending.append((OUT, {'params': {'K': K, 'w': W, 'u': U, 'root': ROOT, 'cap': CAP},
                      'rows': [[p, m] for p, m in tab_rows], 'cert': cert}, {'sort_keys': True}))
write_files(pending)
maxrow = max((r for key in tab_rows for r, _ in rows[key]), default=0)
print('K', K, 'w', W, 'u', U, 'root', ROOT, 'cap', CAP, 'noledger' if NOLEDGER else '')
print('nodes', NODES[0], 'stats', dict(sorted(STATS.items())), 'open', len(OPEN))
print('rows', len(tab_rows), 'largest prime in a row', maxrow)
if PARTIAL:
    print('partial rows', len(PARTIAL), '(factorization timed out; only proven prime factors '
          'kept; marked in %s)' % ROWS)
if PARTIAL_PM1:
    print('partial pm1', len(PARTIAL_PM1), '(factorization of p - 1 timed out; nothing stored)')
for o in OPEN[:10]:
    print('  OPEN', o)
if (PARTIAL or PARTIAL_PM1) and not OPEN:
    print('not complete: the certificate uses partial results, which check.py and gen.py reject')
if not (OPEN or PARTIAL or PARTIAL_PM1):
    print('closed and validated')
sys.exit(1 if OPEN or PARTIAL or PARTIAL_PM1 else 0)
