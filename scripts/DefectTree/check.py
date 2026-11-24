# Untrusted helper script for the OddPerfect Lean library.
# Independent replay of a defect tree certificate (written by search.py) with the rules of the
# checker of OddPerfect/DefectTreeCode.lean, in exact integer arithmetic: the fact table
# (every fact r ^ k divides its row, r an odd prime), the Pratt certificate written the way
# gen.py writes it, and every node of the tree. Prints the first rejected node, if any.
#
# Run: python3 check.py CERT ROWS [corrupt]
#   python3 check.py cert2.json rows.json
#   With the flag corrupt the certificate is first corrupted exactly as gen.py corrupt does.
# Requires: Python 3 standard library only.
# Untrusted: the Lean kernel check is the one that counts.
# License: GPL 3, same as the repository.

import sys, json

CERT, ROWS = sys.argv[1:3]
c = json.load(open(CERT))
d = json.load(open(ROWS))
rows = {(p, m): [tuple(f) for f in fs] for p, m, fs in d['rows']}
pm1 = {int(p): fs for p, fs in d['pm1'].items()}
P = c['params']
K, W, U, ROOT, CAP = P['K'], P['w'], P['u'], P['root'], P['cap']
tab = {(p, m): rows[(p, m)] for p, m in c['rows']}

def trial_prime(n):
    return n >= 2 and all(n % k for k in range(2, n))

certified = set()

def pratt(p):
    """Pratt check of p from the frozen factorization of p - 1 (as gen.py writes it)."""
    if p < 200 or p in certified:
        return trial_prime(p) if p < 200 else True
    fs = pm1[p]
    prod = 1
    for r in fs:
        prod *= r
    if prod != p - 1 or not all(pratt(r) for r in set(fs)):
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

for (p, m), fs in tab.items():
    assert len(set(r for r, _ in fs)) == len(fs), ('table nodup', p, m)
    for r, k in fs:
        assert r != 2 and k >= 1 and gs(p, m) % r ** k == 0, ('table fact', p, m, r, k)
        assert pratt(r), ('table prime', r)

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
    corrupt(c['cert'], [False])
ok = go(c['cert'], ([], 0), 'root')
print('accepted' if ok else 'rejected', 'node kinds', dict(sorted(COUNT.items())))
if BAD:
    print('first rejected node:', BAD[0])
