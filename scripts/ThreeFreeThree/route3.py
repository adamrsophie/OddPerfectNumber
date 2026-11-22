# Untrusted helper script for the OddPerfect Lean library.
# Coverage test of the certificate cert3_final.json, independent of the format checks. It
# samples concrete prime tuples (q, r1, r2, r3), sorts the r's as Section 5.1 of SPEC.md says,
# routes them through the tree using only "value equals a pin" and "value is none of the
# pins", and checks that the tuple satisfies the rebuilt leaf constraints and that every table
# prime s whose 1 + s + s^2 has all its prime factors in {q, r1, r2, r3} (and s not among them)
# is in the C of the leaf. A deterministic pass then routes one prime tuple per leaf.
# Used by: the certificate behind OddPerfect/ThreeFreeThree.lean (a sanity test; the Lean
# soundness proof of treeOK does not depend on it).
# Run: python3 -I route3.py cert3_final.json [samples] [seed]   (defaults 300000 and 1;
# cert3_final.json.xz is also accepted). Helper: verify3.py, found next to this script.
# Requires: Python 3 standard library. Deterministic for a given seed. Running time: about
# eight seconds for 400000 samples.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
import verify3 as V  # noqa: E402

FIXED_VALS = {int(c): c for c in V.FIXED}


def cls_of(r):
    if r in FIXED_VALS:
        return FIXED_VALS[r]
    if r % 3 == 2 and r >= 11:
        return 'n2'
    if r % 3 == 1 and r >= 61:
        return 'big'
    raise ValueError('prime %d has no class' % r)


def sieve(n):
    b = bytearray([1]) * (n + 1)
    b[0] = b[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if b[i]:
            b[i * i::i] = bytearray(len(b[i * i::i]))
    return b


def main():
    path = sys.argv[1]
    nsamp = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = random.Random(seed)
    cert = json.loads(V.read_cert(path))
    order = [i for i, _ in sorted(enumerate(V.CLASSES), key=lambda t: t[0])]
    cidx = {c: i for i, c in enumerate(V.CLASSES)}
    roots = {}
    for rec in cert['triples']:
        roots[tuple(rec['triple'])] = rec['tree']

    leafinfo = {}

    def leaf_data(node, slots):
        lid = node['id']
        if lid not in leafinfo:
            ms, _ = V.least_values(slots)
            leafinfo[lid] = (slots, ms, {r['s'] for r in node['leaf']['C']})
        return leafinfo[lid]

    LIM = 2_000_000
    pr = sieve(LIM)
    allp = [p for p in range(5, LIM) if pr[p]]

    def isp(n):
        return pr[n] if n <= LIM else V.is_prime(n)

    # hard pool: table factors, table primes, all pins, and primes near pins
    hard = set()
    for s in V.TABLE_PRIMES:
        hard.add(s)
        for p, _ in V.TABLE[s]:
            hard.add(p)
    for rec in cert['triples']:
        stack = [rec['tree']]
        while stack:
            n = stack.pop()
            if 'split' in n:
                for p in n['split']['pins']:
                    for d in range(-24, 25):
                        if p + d >= 5 and isp(p + d):
                            hard.add(p + d)
                stack.extend(n['children'])
    hard |= {p for p in range(5, 400) if isp(p)}
    hard = sorted(p for p in hard if p >= 5 and isp(p))
    hard_q = [p for p in hard if p % 12 == 1]
    rand_q = [p for p in allp if p % 12 == 1]
    print('hard pool: %d primes (%d are 1 mod 12)' % (len(hard), len(hard_q)))

    fails = []
    n_nontrivial = 0
    n_s_checked = 0
    leaves_hit = set()
    triples_hit = set()
    # per-triple pin pools, for triple-directed sampling
    tpins = {}
    for rec in cert['triples']:
        d = {'q': set(), 'big': set()}
        stack = [rec['tree']]
        while stack:
            n = stack.pop()
            if 'split' in n:
                kind = 'q' if n['split']['slot'] == 'q' else 'big'
                for p in n['split']['pins']:
                    for dd in (-12, -6, 0, 6, 12):
                        if p + dd >= 5 and isp(p + dd):
                            d[kind].add(p + dd)
                stack.extend(n['children'])
        tpins[tuple(rec['triple'])] = {k: sorted(v) for k, v in d.items()}
    tkeys = sorted(tpins)
    hard_n2 = [p for p in hard if p % 3 == 2 and p >= 11]
    hard_big = [p for p in hard if p % 3 == 1 and p >= 61]
    rand_n2 = [p for p in allp if p % 3 == 2 and p >= 11]
    rand_big = [p for p in allp if p % 3 == 1 and p >= 61]

    def draw(lst_pin, lst_hard, lst_rand):
        u = rng.random()
        if lst_pin and u < 0.6:
            return rng.choice(lst_pin)
        if u < 0.85:
            return rng.choice(lst_hard)
        return rng.choice(lst_rand)

    checked = skipped = 0
    for it in range(nsamp):
        mode = it % 10
        if mode >= 5:
            tk = rng.choice(tkeys)
            P = tpins[tk]
            for _ in range(1000):
                q = draw(P['q'], hard_q, rand_q)
                rs = []
                for c in tk:
                    if c in V.FIXED:
                        rs.append(int(c))
                    elif c == 'n2':
                        rs.append(draw([], hard_n2, rand_n2))
                    else:
                        rs.append(draw(P['big'], hard_big, rand_big))
                if len(set(rs + [q])) == 4:
                    break
            if not (q % 12 == 1 and isp(q) and len(set(rs + [q])) == 4):
                skipped += 1
                continue
            rng.shuffle(rs)
        elif mode <= 2:
            q = rng.choice(hard_q)
            pool = lambda: rng.choice(hard)
        elif mode == 3:
            q = rng.choice(hard_q if rng.random() < 0.5 else rand_q)
            pool = lambda: rng.choice(hard) if rng.random() < 0.5 else rng.choice(allp)
        else:
            q = rng.choice(rand_q)
            pool = lambda: rng.choice(allp) if rng.random() < 0.7 else rng.choice(allp[:200])
        if mode < 5:
            rs = []
            while len(rs) < 3:
                r = pool()
                if r != q and r not in rs:
                    rs.append(r)
        # given in random order; sort by class order then value (spec 5.1)
        rs.sort(key=lambda r: (cidx[cls_of(r)], r))
        tup = [q] + rs
        checked += 1
        triple = tuple(cls_of(r) for r in rs)
        triples_hit.add(triple)
        node = roots.get(triple)
        if node is None:
            fails.append((tup, 'no class triple %r' % (triple,)))
            continue
        slots = V.root_slots(list(triple))
        while 'split' in node:
            sp = node['split']
            i = V.NAMES.index(sp['slot'])
            x = tup[i]
            kids = V.apply_split(slots, i, sp['pins'])
            j = sp['pins'].index(x) if x in sp['pins'] else len(sp['pins'])
            node, slots = node['children'][j], kids[j]
        slots, ms, Cset = leaf_data(node, slots)
        lid = node['id']
        leaves_hit.add(lid)
        bad = None
        for sl, m, x in zip(slots, ms, tup):
            if sl['pinned'] is not None:
                if x != sl['pinned']:
                    bad = 'slot %s pinned %d but value %d' % (sl['name'], sl['pinned'], x)
            else:
                if not (x >= m and x >= sl['lb'] and x not in sl['excluded'] and V.residue_ok(sl['kind'], x)):
                    bad = 'slot %s free (lb %d, least %d) rejects value %d' % (sl['name'], sl['lb'], m, x)
            if bad:
                break
        if bad is None:
            T = set(tup)
            for s in V.TABLE_PRIMES:
                if s in T:
                    continue
                n_s_checked += 1
                if all(p in T for p, _ in V.TABLE[s]):
                    n_nontrivial += 1
                    if s not in Cset:
                        bad = 's=%d has all factors in tuple but is not in C of leaf %d' % (s, lid)
                        break
        if bad:
            fails.append((tup, 'leaf %d: %s' % (lid, bad)))
    # deterministic pass: one concrete prime tuple per leaf, must route back to that leaf
    def route(tup, triple):
        node = roots[triple]
        slots = V.root_slots(list(triple))
        while 'split' in node:
            sp = node['split']
            i = V.NAMES.index(sp['slot'])
            kids = V.apply_split(slots, i, sp['pins'])
            j = sp['pins'].index(tup[i]) if tup[i] in sp['pins'] else len(sp['pins'])
            node, slots = node['children'][j], kids[j]
        return node

    det_ok = det_skip = det_bad = 0
    det_empty = []
    for rec in cert['triples']:
        triple = tuple(rec['triple'])
        stack = [(rec['tree'], V.root_slots(list(triple)))]
        while stack:
            n, sl = stack.pop()
            if 'split' in n:
                i = V.NAMES.index(n['split']['slot'])
                stack.extend(zip(n['children'], V.apply_split(sl, i, n['split']['pins'])))
                continue
            pv = V.pinned_values(sl)
            if any(not isp(p) for p in pv):
                det_skip += 1
                continue
            tup = []
            last = {}
            for x in sl:
                if x['pinned'] is not None:
                    v = x['pinned']
                else:
                    v = max(x['lb'], last.get(x['cls'], 0) + 1)
                    while not (isp(v) and V.residue_ok(x['kind'], v) and v not in x['excluded'] and v not in pv and v not in tup):
                        v += 1
                tup.append(v)
                last[x['cls']] = v
            if sorted(tup[1:], key=lambda r: (cidx[cls_of(r)], r)) != tup[1:]:
                # greedy smallest prime per free slot is optimal against an upper bound coming
                # from a later pinned slot of the same class, so this leaf has no prime tuple
                det_empty.append(n['id'])
            elif route(tup, triple)['id'] == n['id']:
                det_ok += 1
                ms, _ = V.least_values(sl)
                Cset = {r['s'] for r in n['leaf']['C']}
                if any(x['pinned'] is None and v < m for x, m, v in zip(sl, ms, tup)):
                    fails.append((tup, 'leaf %d: value below least' % n['id']))
                T = set(tup)
                for t in V.TABLE_PRIMES:
                    if t not in T and all(p in T for p, _ in V.TABLE[t]) and t not in Cset:
                        fails.append((tup, 'leaf %d: s=%d missing from C' % (n['id'], t)))
            else:
                det_bad += 1
                fails.append((tup, 'deterministic tuple for leaf %d routes elsewhere' % n['id']))
    print('deterministic per-leaf tuples: %d routed back to their leaf, %d skipped (composite pin), %d empty (no prime tuple: %r), %d wrong' % (det_ok, det_skip, len(det_empty), det_empty, det_bad))
    print('draws: %d  seed: %d  random tuples actually checked: %d  draws skipped: %d' % (nsamp, seed, checked, skipped))
    print('distinct class triples reached: %d of 102' % len(triples_hit))
    print('distinct leaves reached: %d of %d' % (len(leaves_hit), cert['leaf_count']))
    print('(tuple, s) pairs where all factors of 1+s+s^2 lie in the tuple: %d' % n_nontrivial)
    print('failures: %d' % len(fails))
    for f in fails[:20]:
        print('  FAIL', f)


if __name__ == '__main__':
    main()
