# Untrusted helper script for the OddPerfect Lean library.
# Cut planner for the children of the states [3, 5] (four more primes above 7) and [3, 5, 17]
# (three more primes above 17), using the mirror engine.py. A state with more than CAP engine
# nodes is cut at its first engine action:
#   exponent split of entry i at exponent k  ->  exact (p, k) and inexact (p, nextValid p k)
#   enumeration                              ->  OmegaSix window children (closed_of_window)
# Leaves are closed by one `run 60` kernel check each. Writes plan.json in the current folder.
# Used by: gen.py (OddPerfect/OmegaSevenRootsA.lean .. OmegaSevenRootsD.lean) and gen_final.py
# (the windows in OddPerfect/OmegaSevenFinal.lean). The library uses CAP = 6000; the plan.json
# stored next to this script is the output of that run.
# Run: python3 plan.py 6000 (the default CAP, 12000, is not the one used in the library)
# Requires: Python 3 standard library; engine.py next to this script. Deterministic.
# Running time: several minutes.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: output files are written to the current folder; engine.py is found next to this script.
# License: GPL 3, same as the repository.
import sys, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import engine as E
CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 12000
lad = E.ladder([2**i for i in range(1, 18)]); Y = 10**4; Q = E.primorial(Y)
kmin = E.kmin

def count(l, j, m):
    r, s = E.run(l, j, m, lad, Y, Q)
    return r, s['nodes']

def action(l, j, m):
    # first action of E.solve on the state (copy of its top), assuming no closing test fires
    ln, ld, un, ud = E.nums(l)
    lo = E.lowE(ln, ld, m)
    X, P = E.pickP(lad, lo)
    Pm = E.pickP(lad, m + 1)[1]
    cs = E.chainList(l)
    allEx = all(e[2] for e in l)
    if 0 < j and next((c for c in cs if E.forceOK(c, lo, Y, Q)), 0): return ('force',)
    if j == 0: return ('split', E.pickAux(l, 0), Pm, lo)
    bs = []
    if un < 2*ud:
        bU = E.bsearch(un, ud, j, 200, m, m + 2*j*un // (2*ud - un) + 2)
        if 1 <= bU and not E.cond(un, ud, j, bU + 1): bs.append(bU)
    bs += cs
    B = E.minB(bs)
    if bs and 2 <= j <= 9 and any(not e[2] and e[0]**e[1] < E.CFG['T'] for e in l) and not (B <= lo + E.W):
        return ('split', E.pickAux(l, E.CFG['T']), Pm, lo)
    if bs and (B <= lo + E.W or allEx or 2 <= j): return ('enum',)
    return ('split', E.pickAux(l, 0), Pm, lo)

def window(l, j, m):
    ln, ld, un, ud = E.nums(l)
    lowB = max(m + 1, (ln + (2*ld - ln) - 1) // (2*ld - ln)) if (j == 1 and ln < 2*ld) else m + 1
    bs = []
    if un < 2*ud:
        bU = E.bsearch(un, ud, j, 200, m, m + 2*j*un // (2*ud - un) + 2)
        if 1 <= bU and not E.cond(un, ud, j, bU + 1): bs.append(bU)
    bs += E.chainList(l)
    assert bs, ('no bounds', l, j, m)
    return [q for q in range(lowB, E.minB(bs) + 1) if E.isPrimeQ(q)]

def cand(q):
    X, P = E.pickP(lad, q)
    return E.gcd(q, P) == 1

def bounds_min(l, j, m):
    ln, ld, un, ud = E.nums(l)
    bs = []
    if un < 2*ud:
        bU = E.bsearch(un, ud, j, 200, m, m + 2*j*un // (2*ud - un) + 2)
        if 1 <= bU and not E.cond(un, ud, j, bU + 1): bs.append(bU)
    bs += E.chainList(l)
    assert bs, ('no bounds', l, j, m)
    return E.minB(bs)

def plan(l, j, m, n=None):
    if n is None:
        r, n = count(l, j, m)
        assert r is True, (l, j, m)
    if n <= CAP: return {'t': 'leaf', 'l': l, 'j': j, 'm': m, 'n': n}
    a = action(l, j, m)
    if a[0] == 'split':
        i, Pm, lo = a[1], a[2], a[3]; p, k, ex = l[i]; assert not ex
        k2 = E.adv(l, j, lo, Pm, p, k, 20)
        def chain(kk):
            l1 = l[:i] + [(p, kk, True)] + l[i+1:]
            nk = E.nextValid(p, kk)
            l2 = l[:i] + [(p, nk, False)] + l[i+1:]
            b = plan(l2, j, m) if kk == k2 else chain(nk)
            return {'t': 'split', 'l': l[:i] + [(p, kk, False)] + l[i+1:], 'j': j, 'm': m, 'i': i,
                    'n': None, 'a': plan(l1, j, m), 'b': b}
        return chain(k)
    if a[0] == 'enum':
        B = bounds_min(l, j, m)
        groups, cur, acc = [], [m + 1, m + 1], 0
        for q in range(m + 1, B + 1):
            if not cand(q): cur[1] = q + 1; continue
            child = l + [(q, kmin(q), False)]
            r, c = count(child, j - 1, q); assert r is True, (child, q)
            if c > CAP:
                if cur[1] > cur[0]: groups.append({'t': 'ival', 'a': cur[0], 'b': cur[1], 'n': acc})
                groups.append({'t': 'one', 'q': q, 'c': plan(child, j - 1, q, c)})
                cur, acc = [q + 1, q + 1], 0
                continue
            if acc + c > CAP:
                groups.append({'t': 'ival', 'a': cur[0], 'b': cur[1], 'n': acc}); cur, acc = [q, q], 0
            acc += c; cur[1] = q + 1
        if cur[1] > cur[0]: groups.append({'t': 'ival', 'a': cur[0], 'b': cur[1], 'n': acc})
        return {'t': 'cover', 'l': l, 'j': j, 'm': m, 'n': n, 'B': B, 'g': groups}
    raise Exception(('force at cut', l, j, m, n))

def leaves(t):
    # kernel checks: leaf states and interval checks
    if t['t'] in ('leaf', 'ival'): return [t]
    if t['t'] == 'split': return leaves(t['a']) + leaves(t['b'])
    if t['t'] == 'one': return leaves(t['c'])
    return [x for g in t['g'] for x in leaves(g)]

if __name__ == '__main__':
    root35 = [(3, 2, False), (5, 1, False)]
    out = {}
    # window of [3,5] j=4 m=7 and of [3,5,17] j=3 m=17
    w35 = window(root35, 4, 7); w17 = window(root35 + [(17, 1, False)], 3, 17)
    print('window 3,5 m=7:', w35[:12], '...', w35[-1], len(w35))
    print('window 3,5,17 m=17:', w17[:5], '...', w17[-1], len(w17))
    roots = [(root35 + [(q, kmin(q), False)], 3, q) for q in w35 if q != 17]
    roots += [(root35 + [(17, 1, False), (q, kmin(q), False)], 2, q) for q in w17]
    trees = []
    for l, j, m in roots:
        t = plan(l, j, m); trees.append(t)
        L = leaves(t)
        if len(L) > 1 or t['n'] > 5000: print(l[2:], t['n'], 'leaves', len(L), 'max', max(x['n'] for x in L), 'sum', sum(x['n'] for x in L), flush=True)
    json.dump({'w35': w35, 'w17': w17, 'trees': trees}, open('plan.json', 'w'))
    tot = sum(x['n'] for t in trees for x in leaves(t))
    print('roots', len(trees), 'leaves', sum(len(leaves(t)) for t in trees), 'leaf nodes', tot)
