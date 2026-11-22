# Planner extension for the NotThree* modules. plan.py of scripts/OmegaSeven stops when a state
# over the cap starts with a forced prime. Here such a state becomes a 'force' node: the forced
# prime c (a prime cofactor of the divisor sum of an exact entry (p, k)) is prepended as the
# engine does, closed in Lean by NotThreeTenForce.closed_of_force. Imported for its effect on
# plan.py (plan and leaves are replaced).
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [here, os.path.join(here, '..', 'OmegaSeven')]
import engine as E
import plan as P
_plan, _leaves = P.plan, P.leaves

def forced(l, j, m):
    ln, ld, un, ud = E.nums(l)
    lo = E.lowE(ln, ld, m)
    ps = [2] + [q for (q, _, _) in l]
    for (p, k, ex) in l:
        if ex:
            c = E.strip(E.geomC(p, k), ps)
            if c != 1 and E.forceOK(c, lo, P.Y, P.Q): return p, k, c
    raise Exception(('no forced prime', l, j, m))

def plan(l, j, m, n=None):
    if n is None:
        r, n = P.count(l, j, m)
        assert r is True, (l, j, m)
    if n > P.CAP and P.action(l, j, m)[0] == 'force':
        p, k, c = forced(l, j, m)
        assert E.isPrimeQ(c) and c != 2 and c not in [e[0] for e in l] and E.geomC(p, k) % c == 0
        return {'t': 'force', 'l': l, 'j': j, 'm': m, 'n': None, 'p': p, 'k': k, 'c': c,
                'a': plan([(c, E.kmin(c), False)] + l, j - 1, m)}
    return _plan(l, j, m, n)

def leaves(t):
    if t['t'] == 'force': return leaves(t['a'])
    if t['t'] in ('leaf', 'ival'): return [t]
    if t['t'] == 'split': return leaves(t['a']) + leaves(t['b'])
    if t['t'] == 'one': return leaves(t['c'])
    return [x for g in t['g'] for x in leaves(g)]

P.plan, P.leaves = plan, leaves
