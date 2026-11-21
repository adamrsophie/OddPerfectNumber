# Untrusted helper script for the OddPerfect Lean library.
# Helper: exact rational simplex method (Bland's rule) with a small LP builder.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F

def simplex_min(c, A_eq, b_eq):
    """min c.x s.t. A_eq x = b_eq, x>=0. Returns (status, value, x). Exact, Bland."""
    m = len(A_eq); n = len(c)
    A = [[F(v) for v in row] for row in A_eq]; b = [F(v) for v in b_eq]
    for i in range(m):
        if b[i] < 0:
            A[i] = [-v for v in A[i]]; b[i] = -b[i]
    # phase 1: artificials
    N = n + m
    T = [A[i] + [F(1) if j == i else F(0) for j in range(m)] + [b[i]] for i in range(m)]
    basis = [n + i for i in range(m)]
    def pivot(r, col):
        pv = T[r][col]
        T[r] = [v / pv for v in T[r]]
        for i in range(len(T)):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                T[i] = [a - f * bb for a, bb in zip(T[i], T[r])]
        basis[r] = col
    def run(cost, allowed):
        while True:
            # reduced costs
            cb = [cost[basis[i]] for i in range(m)]
            enter = None
            for j in allowed:
                if j in basis: continue
                rc = cost[j] - sum(cb[i] * T[i][j] for i in range(m))
                if rc < 0:
                    enter = j; break
            if enter is None:
                return 'opt'
            best = None
            for i in range(m):
                if T[i][enter] > 0:
                    ratio = T[i][-1] / T[i][enter]
                    if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                        best = (ratio, i)
            if best is None:
                return 'unbounded'
            pivot(best[1], enter)
    cost1 = [F(0)] * n + [F(1)] * m
    run(cost1, list(range(N)))
    val1 = sum(cost1[basis[i]] * T[i][-1] for i in range(m))
    if val1 != 0:
        return ('infeasible', None, None)
    # drive artificials out
    for i in range(m):
        if basis[i] >= n:
            for j in range(n):
                if T[i][j] != 0:
                    pivot(i, j); break
    cost2 = [F(v) for v in c] + [F(0)] * m
    st = run(cost2, list(range(n)))
    if st == 'unbounded':
        return ('unbounded', None, None)
    x = [F(0)] * n
    for i in range(m):
        if basis[i] < n: x[basis[i]] = T[i][-1]
    return ('opt', sum(c[j] * x[j] for j in range(n)), x)

class LP:
    def __init__(self):
        self.vars = []; self.cons = []  # (dict, sense, rhs)
    def v(self, name):
        if name not in self.vars: self.vars.append(name)
    def add(self, lhs, sense, rhs=0, name=None):
        for k in lhs: self.v(k)
        self.cons.append((lhs, sense, F(rhs), name))
    def solve_min(self, obj):
        for k in obj: self.v(k)
        n0 = len(self.vars); A = []; b = []; nsl = sum(1 for c in self.cons if c[1] != '=')
        cols = n0 + nsl; si = n0
        for lhs, sense, rhs, _ in self.cons:
            row = [F(0)] * cols
            for k, v in lhs.items(): row[self.vars.index(k)] += F(v)
            if sense == '<=': row[si] = F(1); si += 1
            elif sense == '>=': row[si] = F(-1); si += 1
            A.append(row); b.append(rhs)
        c = [F(0)] * cols
        for k, v in obj.items(): c[self.vars.index(k)] = F(v)
        st, val, x = simplex_min(c, A, b)
        return st, val, (dict(zip(self.vars, x[:n0])) if x else None)
