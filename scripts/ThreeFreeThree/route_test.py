# Untrusted helper script for the OddPerfect Lean library.
# Coverage test of the certificate cert3_final.json: routes 100000 random sorted tuples
# (q, r1, r2, r3) of primes through the trees by pins and exclusions only, and asserts that
# the constraints stored in each leaf reached hold for the tuple.
# Used by: the certificate behind OddPerfect/ThreeFreeThree.lean (a sanity test; the Lean
# soundness proof of treeOK does not depend on it).
# Run: python3 -I route_test.py cert3_final.json   (or cert3_final.json.xz)
# Requires: Python 3 standard library. Deterministic (fixed seed 1). Running time: about two
# seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import json, random, sys
from collections import Counter
def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def read_cert(path):
    """Bytes of the certificate, plain or compressed with xz (file name ending in .xz)."""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as fh:
            return fh.read()
    with open(path, 'rb') as fh:
        return fh.read()


d = json.loads(read_cert(sys.argv[1]))
tab = {int(s): v for s, v in d['table'].items()}
tprimes = sorted({p for v in tab.values() for p, e in v})
def cls_of(p):
    if p in (5, 7, 13, 19, 31, 37, 43): return str(p)
    if p % 3 == 2 and p >= 11: return 'n2'
    if p % 3 == 1 and p >= 61: return 'big'
pool = [p for p in range(5, 4000) if is_prime(p) and cls_of(p)] + [p for p in tprimes if cls_of(p)] * 40
qpool = [p for p in range(13, 4000, 12) if is_prime(p)] + [p for p in tprimes if p % 12 == 1] * 10
rng = random.Random(1)
order = ['5', '7', '13', '19', '31', '37', '43', 'n2', 'big']
trees = {tuple(t['triple']): t['tree'] for t in d['triples']}
hits = Counter(); n = 0
while n < 100000:
    rs = rng.sample(pool, 3)
    q = rng.choice(qpool)
    if len(set(rs)) < 3 or q in rs: continue
    rs.sort(key=lambda p: (order.index(cls_of(p)), p))
    t = tuple(cls_of(p) for p in rs)
    if t not in trees: continue
    vals = [q] + rs
    node = trees[t]
    while 'split' in node:
        i = ['q', 'r1', 'r2', 'r3'].index(node['split']['slot'])
        pins = node['split']['pins']
        node = node['children'][pins.index(vals[i])] if vals[i] in pins else node['children'][-1]
    lf = node['leaf']
    for v, s in zip(vals, lf['slots']):
        if 'pinned' in s:
            assert v == s['pinned'], (vals, lf['id'])
        else:
            assert v >= s['least'] and v not in s['excluded'], (vals, lf['id'], s)
    hits[lf['id']] += 1; n += 1
print('routed', n, 'tuples into', len(hits), 'distinct leaves; all constraints held')
