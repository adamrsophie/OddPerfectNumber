# Untrusted helper script for the OddPerfect Lean library.
# Independent replay of a defect tree certificate (written by search.py) with the rules of the
# checker of OddPerfect/DefectTreeCode.lean, in exact integer arithmetic: the fact table
# (every fact r ^ k divides its row, r an odd prime), the Pratt certificate written the way
# gen.py writes it, and every node of the tree. Prints the first rejected node, if any.
# Rows: every unmarked row of the table must multiply back to its value up to a power of 2
# (except the nine landed rows of LANDED_PARTIAL, pinned to their recorded facts); a row listed
# in the optional field "partial" of the table (written by search.py when a factorization did
# not finish) is skipped, and a certificate that uses one is rejected.
#
# Run: python3 check.py CERT ROWS [corrupt]
#   python3 check.py cert2.json rows.json
#   With the flag corrupt the certificate is first corrupted exactly as gen.py corrupt does;
#   the corrupted certificate must differ from the input, otherwise the script stops with exit
#   status 3 (no mutation possible: no capacity leaf) before any check.
# Exit status: 0 when the certificate is accepted, 1 when a well formed certificate or table is
# rejected (also a row that does not multiply back, a marked row in use, or a factorization of
# p - 1 with a factor that is not an integer above 1), 2 for malformed input (unreadable JSON,
# an unknown or non text node or chain tag, a missing or surplus field, a repeated key or row, a
# number that is not a natural number, a row the table lacks, a partial entry that is no row;
# read by the strict loader certio.py) or a usage error, 3 for corrupt without a mutation.
# Requires: Python 3 standard library only.
# Untrusted: the Lean kernel check is the one that counts.
# License: GPL 3, same as the repository.

import sys, os, json


def malformed(msg):
    print('malformed input: ' + msg, file=sys.stderr)
    sys.exit(2)


def reject(msg):
    print('rejected', msg)
    sys.exit(1)


if len(sys.argv) not in (3, 4) or sys.argv[3:] not in ([], ['corrupt']):
    print('usage: python3 check.py CERT ROWS [corrupt]', file=sys.stderr)
    sys.exit(2)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certio     # the strict loader shared with search.py and gen.py (exit 2 on violation)

CERT, ROWS = sys.argv[1:3]
c = certio.load_cert(CERT)
rows, pm1, PARTSET = certio.load_rows(ROWS)
P = c['params']
K, W, U, ROOT, CAP = P['K'], P['w'], P['u'], P['root'], P['cap']
for p, m in c['rows']:
    if (p, m) not in rows:
        malformed('%s: row (%d, %d) is not in the table %s' % (CERT, p, m, ROWS))
tab = {(p, m): rows[(p, m)] for p, m in c['rows']}
# Only the loader is shared with gen.py; the arithmetic below is this script's own.

def trial_prime(n):
    return n >= 2 and all(n % k for k in range(2, n))

def strong_composite(n):
    """True when one of the bases 2, 3, 5, 7 proves n (at least 200) composite; then the
    witness scan below n is skipped, so a composite never makes the replay hang."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for b in (2, 3, 5, 7):
        x = pow(b, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return True
    return False

certified = set()

def pratt(p):
    """Pratt check of p from the frozen factorization of p - 1 (as gen.py writes it)."""
    if p < 200 or p in certified:
        return trial_prime(p) if p < 200 else True
    if p not in pm1:
        return False
    fs = pm1[p]
    prod = 1
    for r in fs:
        prod *= r
    if not all(r > 1 for r in fs) or prod != p - 1 or not all(pratt(r) for r in set(fs)):
        return False
    if strong_composite(p):
        return False
    a = 2
    while a < p and not (pow(a, p - 1, p) == 1 and
                         all(pow(a, (p - 1) // r, p) != 1 for r in set(fs))):
        a += 1
    if a == p:
        return False
    certified.add(p)
    return True

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


for (p, m), fs in tab.items():
    if len(set(r for r, _ in fs)) != len(fs):
        reject('table row (%d, %d): repeated prime' % (p, m))
    for r, k in fs:
        if not (r > 2 and 1 <= k <= gs(p, m).bit_length() and gs(p, m) % r ** k == 0):
            reject('table row (%d, %d): false fact (%d, %d)' % (p, m, r, k))
        if not pratt(r):
            reject('table row (%d, %d): %d is not certified prime' % (p, m, r))

for p, m in c['rows']:
    if (p, m) in PARTSET:
        reject('table row (%d, %d) is marked partial (its factorization did not finish)' % (p, m))
for (p, m), fs in sorted(rows.items()):
    if (p, m) in PARTSET or LANDED_PARTIAL.get((p, m)) == fs:
        continue
    n = odd_cofactor(gs(p, m), fs)
    if n is None:
        reject('table row (%d, %d): a fact is not an odd prime power dividing the row' % (p, m))
    if n != 1:
        reject('table row (%d, %d): the facts do not multiply back to the row value (odd '
               'cofactor %d) and the row is not marked partial' % (p, m, n))

def look(p, m):
    return tab.get((p, m), [])

def facts_e(x):
    return look(x[0], x[1]) if x[2] else []

def sp_facts(st):
    return [] if st[1] == 0 else look(st[1], 1)

def all_facts(st):
    out = list(sp_facts(st))
    for x in st[0]:
        out += facts_e(x)
    return out

def k_of(fs, r):
    for y in fs:
        if y[0] == r:
            return y[1]
    return 0

def forced(st, r):
    return any(y[0] == r for y in all_facts(st))

def fresh(st, r):
    return all(x[0] != r for x in st[0]) and r != st[1]

def find(os_, p):
    for x in os_:
        if x[0] == p:
            return x
    return None

def recv_l(fs, c0):
    return sum(k for r, k in fs if r % 3 == 1 and r != c0)

def ent_b(x, c0):
    p, e, _ = x
    fs = facts_e(x)
    if e == 2:
        return max(recv_l(fs, c0) - 1, 0)
    if e >= 4:
        return ((0 if p == 3 else 3 * (e // 2 - 2)) + (e if p % 3 == 2 else 0)
                + 2 * k_of(fs, 3) + recv_l(fs, c0))
    return 0

def bound(st, c0):
    x = find(st[0], 3)
    b = (0 if x is None else max(x[1] // 2 - 2, 0)) + (4 if 3 < U else 0)
    if st[1] != 0:
        b += recv_l(sp_facts(st), c0)
    return b + sum(ent_b(x, c0) for x in st[0])

def cands(st):
    if st[1] != 0:
        return [st[1]]
    return [0] + [y[0] for y in all_facts(st) if y[0] % 4 == 1]

def known(st, p):
    return find(st[0], p) is not None or (p == st[1] and p != 0) or forced(st, p)

def allow(st, p, f):
    x = find(st[0], p)
    if x is not None:
        return f <= x[1]
    if p == st[1] and p != 0:
        return f <= 1
    return forced(st, p) and (f <= 1 or (f <= 2 and (st[1] != 0 or p % 4 != 1)))

def leaf_ok(st, t):
    k = t['t']
    os_ = st[0]
    if k == 'cap':
        x = next((x for x in os_ if x[0] == t['r'] and x[2]), None)
        return x is not None and x[1] < k_of(sp_facts(st), t['r']) + sum(
            k_of(facts_e(y), t['r']) for y in os_)
    if k == 'small':
        return forced(st, t['r']) and t['r'] < U
    if k == 'budget':
        return CAP is not None and CAP < sum(x[1] // 2 - 1 for x in os_)
    if k == 'ledger':
        ks = t['ks']
        return (len(set(ks)) == len(ks) and all(known(st, p) for p in ks) and
                all(K < bound(st, c0) + W * len(ks) for c0 in cands(st)))
    if k == 'abund':
        ws = t['ws']
        ps = [p for p, _ in ws]
        if len(set(ps)) != len(ps):
            return False
        if not all(allow(st, p, k_of(ws, p)) for p in ps):
            return False
        num, den = 1, 1
        for p in ps:
            num *= gs(p, k_of(ws, p))
            den *= p ** k_of(ws, p)
        return 2 * den < num
    return False

BAD = []
COUNT = {}

def go(t, st, mode):
    k = t['t']
    COUNT[k] = COUNT.get(k, 0) + 1
    if k == 'br':
        r = t['r']
        if mode == 'node':
            head = forced(st, r) and fresh(st, r)
        elif mode == 'root':
            head = r == ROOT and pratt(r) and fresh(st, r)
        else:
            head = False
        ok = head
        if ok and st[1] == 0 and r % 4 == 1:
            ok = t['sp'] is not None and go(t['sp'], (st[0], r), 'node')
        ok = ok and chain(t['ch'], st, r, 2)
        if not ok and not BAD:
            BAD.append(('br', st, r))
        return ok
    if mode != 'node' or not leaf_ok(st, t):
        if not BAD:
            BAD.append((k, st, t))
        return False
    return True

def chain(items, st, r, e):
    for i, it in enumerate(items):
        if it['t'] == 'high':
            return i == len(items) - 1 and e >= 4 and go(it['kid'], ([(r, e, False)] + st[0],
                                                                      st[1]), 'node')
        if not go(it['kid'], ([(r, e, True)] + st[0], st[1]), 'node'):
            return False
        e += 2
    return False

def corrupt(t, state):
    if state[0]:
        return
    if t['t'] == 'cap':
        t['r'] = t['r'] + 2
        state[0] = True
        return
    if t['t'] == 'br':
        if t['sp'] is not None:
            corrupt(t['sp'], state)
        for it in t['ch']:
            corrupt(it['kid'], state)

if 'corrupt' in sys.argv[3:]:
    before = json.dumps(c['cert'], sort_keys=True)
    corrupt(c['cert'], [False])
    if json.dumps(c['cert'], sort_keys=True) == before:
        print('no mutation possible: the certificate has no capacity leaf to corrupt',
              file=sys.stderr)
        sys.exit(3)
ok = go(c['cert'], ([], 0), 'root')
print('accepted' if ok else 'rejected', 'node kinds', dict(sorted(COUNT.items())))
if BAD:
    print('first rejected node:', BAD[0])
sys.exit(0 if ok else 1)
