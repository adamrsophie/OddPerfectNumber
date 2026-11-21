# Untrusted helper script for the OddPerfect Lean library.
# Runs gen.py for each root and writes the instruction lists tree<p> and the prime table
# (Pratt data for every forced prime) as Lean text.
# Used by: OddPerfect/LowerBound.lean (the section between "Generated trees (BEGIN)" and
# "Generated trees (END)": the tab definitions, table, table_ok, table_prime and tree3, tree5,
# tree7 with their parts).
# Run: python3 emit.py 79 trees.lean 3: 5:3 7:3,5
# Requires: Python 3, cypari2 (see gen.py). Running time: about a second with cypari2 for B = 79 (with empty caches).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
"""Emit Lean instruction lists for proof trees.  Usage: python3 emit.py B out.lean p0:excl,excl ..."""
import sys
import gen
from nt import factor

TD = 100     # factors below TD are checked in Lean by trial division
TAB = {}     # prime -> (a, factors of p - 1 with multiplicity)

def add(q):
    """Put q and the Pratt data of its factors at least TD into the table."""
    if q in TAB: return
    fs, cof = factor(q - 1, 2000000)
    assert cof == 1, q
    flist = []
    for f, m in sorted(fs.items()): flist += [f] * m
    for a in range(2, 10000):
        if pow(a, q - 1, q) == 1 and all(pow(a, (q - 1) // f, q) != 1 for f in fs): break
    else: raise ValueError(q)
    TAB[q] = (a, flist)
    for f in fs:
        if f >= TD: add(f)

def pc_of(q):
    add(q); return ''

TDEFS = []

def bst(keys):
    """Balanced search tree over the sorted keys; subtrees of at most 127 nodes become
    separate definitions to keep elaboration shallow."""
    if not keys: return 'PT.leaf'
    if len(keys) <= 127:
        return node(keys)
    m = len(keys) // 2; q = keys[m]; a, fs = TAB[q]
    l = bst(keys[:m]); r = bst(keys[m + 1:])
    return 'PT.node %s %d %d %s %s' % (sub(l), q, a, fstr(fs), sub(r))

def sub(t):
    if t == 'PT.leaf': return t
    nm = 'tab%d' % len(TDEFS)
    TDEFS.append('/-- Part of the prime table. -/\ndef %s : PT :=\n  %s\n' % (nm, t))
    return nm

def fstr(fs):
    from collections import Counter
    c = Counter(fs)
    return '[' + ', '.join('(%d, %d)' % (f, c[f]) for f in sorted(c)) + ']'

def node(keys):
    if not keys: return 'PT.leaf'
    m = len(keys) // 2; q = keys[m]; a, fs = TAB[q]
    return '(PT.node %s %d %d %s\n    %s)' % (node(keys[:m]), q, a, fstr(fs), node(keys[m + 1:]))

def cs_str(cs): return '[' + ', '.join('(%d, %d)' % c for c in cs) + ']'

def flatten(t, out):
    k = t[0]
    if k == 'rs':
        out.append('.rs %d %d %d' % (t[1], t[2], t[3]))
        for c in t[4]: flatten(c, out)
    elif k == 'force':
        pc_of(t[1]); out.append('.force %d %d %s' % (t[1], t[2], cs_str(t[3])))
        flatten(t[4], out)
    elif k == 'up':
        out.append('.up %d %d' % (t[1], t[2])); flatten(t[3], out)
    elif k == 'big': out.append('.big %s' % cs_str(t[1]))
    elif k == 'ndc': out.append('.ndc %d' % t[1])
    elif k == 'ovf':
        f = None
        out.append('.ovf %d %d %s' % (t[1], t[3], cs_str(t[2])))
    elif k == 'par2': out.append('.par2 %d %d' % (t[1], t[2]))
    elif k == 'parS': out.append('.parS %d' % t[1])
    elif k == 'abund': out.append('.abund %s' % cs_str(t[1]))
    else: raise ValueError(k)

CHUNK = 400

def emit(name, ins):
    lines, names = [], []
    for i in range(0, len(ins), CHUNK):
        nm = '%s_%d' % (name, i // CHUNK); names.append(nm)
        lines.append('/-- Instructions, part %d. -/' % (i // CHUNK))
        lines.append('def %s : List Ins := [\n  ' % nm + ',\n  '.join(ins[i:i + CHUNK]) + ']\n')
    return lines, names

if __name__ == '__main__':
    B = int(sys.argv[1]); out = sys.argv[2]
    gen.L = 10 ** B
    body, summary = [], []
    for spec in sys.argv[3:]:
        p0, _, ex = spec.partition(':')
        p0 = int(p0); excl = [int(x) for x in ex.split(',') if x]
        st = gen.St(); st.lo[p0] = 1; st.nd = set(excl)
        gen.STATS['nodes'] = 0
        t = gen.solve(st)
        if t is None:
            print('FAIL', p0, gen.FAILS[:3]); sys.exit(1)
        ins = []
        flatten(t, ins)
        lines, names = emit('tree%d' % p0, ins)
        body += lines
        body.append('/-- The tree for `%d`. -/\ndef tree%d : List Ins := %s\n' % (p0, p0, ' ++ '.join(names)))
        summary.append((p0, excl, len(ins)))
        print('root', p0, 'excl', excl, 'instructions', len(ins))
    top = bst(sorted(TAB))
    head = TDEFS + ['/-- The prime table. -/\ndef table : PT :=\n  %s\n' % top,
            '/-- The prime table is valid. -/\ntheorem table_ok : table.allOK table = true := by\n  decide +kernel\n',
            '/-- Every key of the prime table is prime. -/\ntheorem table_prime : ∀ x, table.mem x = true → x.Prime :=\n  PT.prime_of_mem table_ok\n']
    open(out, 'w').write('\n'.join(head + body))
    print('table', len(TAB))
