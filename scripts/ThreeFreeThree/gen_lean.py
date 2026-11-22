# Untrusted helper script for the OddPerfect Lean library.
# Converter from the certificate cert3_final.json to Lean terms of
# OddPerfect.ThreeFreeThreeChecker, with a Python mirror of the Lean checker (leafOK, treeOK).
# Used by: the data modules OddPerfect/ThreeFreeThreeData01.lean .. ThreeFreeThreeData11.lean
# (the theorems u<i>_<k>_ok and their private group lemmas) and the final module
# OddPerfect/ThreeFreeThree.lean (tree0 .. tree101, trees, allOK_trees,
# three_dvd_of_three_mod_exceptions, three_dvd_of_three_exceptions and
# four_le_card_mod_exceptions); the mode data writes all twelve files.
# Run: python3 -I gen_lean.py CERT MODE [ARG], where CERT is cert3_final.json or
# cert3_final.json.xz and MODE is one of
#   mirror             run the mirror on every leaf and compare with the certificate
#   leaf ID            print a Lean theorem checking leaf ID with its node constraints
#   tree TRIPLE_INDEX  print a Lean theorem checking the whole tree of one triple
#   treesplit TRIPLE_INDEX  the same with one theorem per leaf
#   stats              leaf counts per triple
#   data OUTDIR        write every data module and the final module into the folder OUTDIR
#                      (the mode data first checks the SHA-256 of the certificate)
# Requires: Python 3 standard library. Deterministic. Running time: under a second for data,
# about two seconds for mirror.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import json
import sys
from fractions import Fraction

CLS = {'5': 'c5', '7': 'c7', '13': 'c13', '19': 'c19', '31': 'c31', '37': 'c37', '43': 'c43',
       'n2': 'n2', 'big': 'big'}
FIXED = {'5': 5, '7': 7, '13': 13, '19': 19, '31': 31, '37': 37, '43': 43}
SLOTIDX = {'q': 0, 'r1': 1, 'r2': 2, 'r3': 3}
FUEL_LV = 1000
FUEL_SQ = 200
TAILN = 178802  # the tail factor 1/(1 - 1/(2 * 299^2)) = 178802/178801 of finalOK
TAILD = 178801


def prime_factors(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def is_prime(n):
    return n >= 2 and all(n % p for p in range(2, int(n ** 0.5) + 1))


TABLE = [(s, prime_factors(1 + s + s * s)) for s in range(5, 300) if is_prime(s) and s % 3 == 2]

# Mirror of the Lean checker.
# slot: ('pin', p) or ('free', kind, lb, excl)  with kind in 'q', 'n2', 'big'


def ktest(k, x):
    return {'q': x % 12 == 1, 'n2': x % 3 == 2, 'big': x % 3 == 1}[k]


def sortable(c):
    return c in ('n2', 'big')


def same(a, b):
    return sortable(a) and a == b


def pins(nd):
    return [s[1] for s in nd if s[0] == 'pin']


def scan(k, ex, P, start, fuel, x):
    while fuel > 0:
        if ktest(k, x) and x not in ex and x not in P:
            return x
        fuel -= 1
        x += 1
    return start


def lv(s, P, st):
    if s[0] == 'pin':
        return s[1]
    st2 = max(s[2], st)
    return scan(s[1], s[3], P, st2, FUEL_LV, st2)


def least_vals(cl, nd):
    c1, c2, c3 = cl
    P = pins(nd)
    m0 = lv(nd[0], P, 0)
    m1 = lv(nd[1], P, 0)
    m2 = lv(nd[2], P, m1 + 1 if same(c1, c2) else 0)
    m3 = lv(nd[3], P, m2 + 1 if same(c2, c3) else (m1 + 1 if same(c1, c3) else 0))
    return [m0, m1, m2, m3]


def acc(s, P, m, f):
    if s[0] == 'pin':
        return f == s[1]
    return ktest(s[1], f) and m <= f and f not in s[3] and f not in P


def small_list(nd, m):
    P = pins(nd)
    return [s for s, fs in TABLE if s not in P and
            all(any(acc(nd[i], P, m[i], f) for i in range(4)) for f in fs)]


def known2(s):
    return (s[0] == 'pin' and s[1] % 3 == 2) or (s[0] == 'free' and s[1] == 'n2')


def admissible(s, m, w):
    n, d = w
    return (n == 0 and 0 < d and known2(s)) or (0 < n < d and d * d <= n * n * m)


def nsqrt(fuel, m, x):
    while fuel > 0:
        y = (x + (m // x if x else 0)) // 2
        if y < x:
            x = y
            fuel -= 1
        else:
            return x
    return x


def pinv(s):
    return s[1] if s[0] == 'pin' else 1


def step(nd, w, D4, v, stats):
    if all(e % 2 == 0 for e in v):
        return (0, 1)
    if all(e == 0 or (nd[i][0] == 'pin' and w[i][0] != 0) for i, e in enumerate(v)):
        stats['exact'] += 1
        n = 1
        g = 2
        for i, e in enumerate(v):
            n *= pinv(nd[i]) ** e
            g *= pinv(nd[i]) ** ((e + 1) // 2)
        m = 4 * n - 3
        r = nsqrt(FUEL_SQ, m, g)
        if r * r == m:
            s = (r - 1) // 2
            if s < 300:
                return (0, 1)
            stats['hits'].append((tuple(v), s))
            return (s + 1, s * s)
        if r * r < m < (r + 1) * (r + 1):
            return (0, 1)
        return None
    W = 1
    for i, e in enumerate(v):
        W *= w[i][0] ** e * w[i][1] ** (4 - e)
    return (90601 * min(D4, 300 * W), 27000000 * D4)


def padd(x, y):
    a, b = x
    c, d = y
    if b == d:
        return (a + c, b)
    if a == 0:
        return (c, d)
    if c == 0:
        return (a, b)
    return (a * d + c * b, b * d)


BOX = [(a, b, c, d) for a in range(5) for b in range(5) for c in range(5) for d in range(5)]


def tailP(w):
    (n0, d0), (n1, d1), (n2, d2), (n3, d3) = w
    num = 90601 * (n0 ** 5 * (d1 ** 5 * d2 ** 5 * d3 ** 5) + n1 ** 5 * (d0 ** 5 * d2 ** 5 * d3 ** 5)
                   + n2 ** 5 * (d0 ** 5 * d1 ** 5 * d3 ** 5) + n3 ** 5 * (d0 ** 5 * d1 ** 5 * d2 ** 5)) \
        * (d0 * d1 * d2 * d3)
    den = 90000 * (d0 ** 5 * d1 ** 5 * d2 ** 5 * d3 ** 5) * ((d0 - n0) * (d1 - n1) * (d2 - n2) * (d3 - n3))
    return (num, den)


def leaf_ok(cl, nd, w):
    """Returns (ok, info) exactly as the Lean checker would decide."""
    m = least_vals(cl, nd)
    info = {'m': m, 'exact': 0, 'hits': []}
    if not all(admissible(nd[i], m[i], w[i]) for i in range(4)) or not all(x >= 2 for x in m):
        return False, info
    D4 = 1
    for n, d in w:
        D4 *= d ** 4
    # accum is a right fold
    vals = [step(nd, w, D4, v, info) for v in BOX]
    if any(x is None for x in vals):
        return False, info
    B = (0, 1)
    for x in reversed(vals):
        B = padd(x, B)
    X = padd(B, tailP(w))
    C = small_list(nd, m)
    Pn = Pd = 1
    for s in C:
        Pn *= s * s + s + 1
        Pd *= s * s
    # finalOK: each s in C contributes s/(s - 1), and the tail factor TAILN/TAILD covers the
    # ordinary primes s >= 300
    Qn = Qd = 1
    for s in C:
        Qn *= s
        Qd *= s - 1
    info.update(X=X, C=C, B=B)
    ok = X[0] < X[1]
    if ok:
        mm = m[0] * m[1] * m[2] * m[3]
        md = (m[0] - 1) * (m[1] - 1) * (m[2] - 1) * (m[3] - 1)
        lhs = mm * Qn * X[1] * TAILN
        rhs = 2 * md * Qd * (X[1] - X[0]) * TAILD
        ok = lhs <= rhs
        # the bound of the certificate (fv(s) for s in C, no tail factor), for comparison
        info['bound'] = Fraction(mm * Pn * X[1], md * Pd * (X[1] - X[0]))
        info['cbound'] = Fraction(lhs, md * Qd * (X[1] - X[0]) * TAILD)
    return ok, info

# Tree semantics.


def root(triple):
    nd = [('free', 'q', 13, [])]
    for c in triple:
        if c in FIXED:
            nd.append(('pin', FIXED[c]))
        elif c == 'n2':
            nd.append(('free', 'n2', 11, []))
        else:
            nd.append(('free', 'big', 61, []))
    return nd


def bump(s, p):
    return ('free', s[1], max(s[2], p + 1), s[3]) if s[0] == 'free' else s


def add_ex(s, p):
    return ('free', s[1], s[2], [p] + s[3]) if s[0] == 'free' else s


def pin_child(cl, nd, i, p):
    c1, c2, c3 = cl
    nd = list(nd)
    nd[i] = ('pin', p)
    if i == 1:
        if same(c1, c2):
            nd[2] = bump(nd[2], p)
        if same(c1, c3):
            nd[3] = bump(nd[3], p)
    if i == 2 and same(c2, c3):
        nd[3] = bump(nd[3], p)
    return nd


def rest_child(nd, i, p):
    nd = list(nd)
    nd[i] = add_ex(nd[i], p)
    return nd


def bin_tree(node):
    """certificate node -> nested tuple ('leaf', id, weights) / ('split', i, p, t1, t2)"""
    if 'leaf' in node:
        L = node['leaf']
        return ('leaf', node['id'], [tuple(x) for x in L['weights']])
    sp = node['split']
    i = SLOTIDX[sp['slot']]
    kids = node['children']
    t = bin_tree(kids[-1])
    for p, k in reversed(list(zip(sp['pins'], kids[:-1]))):
        t = ('split', i, p, bin_tree(k), t)
    return t


def walk(cl, nd, t, out):
    """collect (id, cl, nd, w) for each leaf, following the Lean semantics"""
    if t[0] == 'leaf':
        out.append((t[1], cl, nd, t[2]))
        return
    _, i, p, t1, t2 = t
    assert nd[i][0] == 'free'
    walk(cl, pin_child(cl, nd, i, p), t1, out)
    walk(cl, rest_child(nd, i, p), t2, out)

# Lean printing.


def lslot(s):
    if s[0] == 'pin':
        return f'.pin {s[1]}'
    return f'.free .{s[1]} {s[2]} [{", ".join(map(str, s[3]))}]'


def lnode(nd):
    return '⟨' + ', '.join(lslot(s) for s in nd) + '⟩'


def lcls(cl):
    return '(.' + ', .'.join(CLS[c] for c in cl) + ')'


def lw(w):
    return '⟨' + ', '.join(f'({n}, {d})' for n, d in w) + '⟩'


def ltree(t, ind=0):
    if t[0] == 'leaf':
        return f'.leaf {lw(t[2])}'
    _, i, p, t1, t2 = t
    return f'.split {i} {p}\n{"  " * (ind + 1)}({ltree(t1, ind + 1)})\n{"  " * (ind + 1)}({ltree(t2, ind + 1)})'


def all_leaves(d):
    res = []
    for ti, T in enumerate(d['triples']):
        cl = tuple(T['triple'])
        out = []
        walk(cl, root(cl), bin_tree(T['tree']), out)
        res += [(ti,) + o for o in out]
    return res


def cert_leaf_map(d):
    m = {}

    def rec(n):
        if 'leaf' in n:
            m[n['id']] = n['leaf']
        for c in n.get('children', []):
            rec(c)
    for T in d['triples']:
        rec(T['tree'])
    return m


# Data modules.

SHA256 = '7c15ea15c1582c81ee89c02bc94e7e13901ca91c17a454168872b44b30b00b41'
UNIT = 130     # largest subtree kept in one piece
MODMAX = 130   # largest number of leaves in one data module
GROUP = 5      # leaves per kernel decision


def nleaves(t):
    return 1 if t[0] == 'leaf' else nleaves(t[3]) + nleaves(t[4])


def leaf_list(cl, nd, t, out):
    if t[0] == 'leaf':
        out.append((nd, t))
        return
    _, i, p, t1, t2 = t
    leaf_list(cl, pin_child(cl, nd, i, p), t1, out)
    leaf_list(cl, rest_child(nd, i, p), t2, out)


def gen_data(d, outdir):
    import os
    units = []        # (ti, k, cl, nd, t, is_root)
    top = {}          # ti -> (tree expr, proof expr) for the final module
    for ti, T in enumerate(d['triples']):
        cl = tuple(T['triple'])
        bt = bin_tree(T['tree'])
        cnt = [0]

        def cut(nd, t, is_root):
            if nleaves(t) <= UNIT:
                k = cnt[0]
                cnt[0] += 1
                units.append((ti, k, cl, nd, t, is_root))
                return f'u{ti}_{k}', f'u{ti}_{k}_ok'
            _, i, p, t1, t2 = t
            a = cut(pin_child(cl, nd, i, p), t1, False)
            b = cut(rest_child(nd, i, p), t2, False)
            return (f'(.split {i} {p} {a[0]} {b[0]})',
                    f'(treeOK_split (by decide) rfl {a[1]} {b[1]})')
        top[ti] = cut(root(cl), bt, True)
    # pack units into modules, in order
    mods = [[]]
    for u in units:
        n = nleaves(u[4])
        if mods[-1] and sum(nleaves(x[4]) for x in mods[-1]) + n > MODMAX:
            mods.append([])
        mods[-1].append(u)
    os.makedirs(outdir, exist_ok=True)
    total = 0
    names = []
    for mi, mod in enumerate(mods, 1):
        name = f'ThreeFreeThreeData{mi:02d}'
        names.append(name)
        nl = sum(nleaves(u[4]) for u in mod)
        total += nl
        tis = sorted({u[0] for u in mod})
        desc = []
        for ti in tis:
            us = [u for u in mod if u[0] == ti]
            whole = len(us) == 1 and us[0][5]
            tri = ', '.join(d['triples'][ti]['triple'])
            desc.append(f'`({tri})`'.replace(', ', '\x00') + ('' if whole else ' (part)'))
        import textwrap
        para = (f'Subtrees of the case analysis certificate for the class triples ' + ', '.join(desc)
                + f', with {nl} leaves in all. Each public theorem states that a subtree passes `treeOK`'
                ' from explicit constraints. The data was found by a search outside Lean; everything in'
                ' this file is rechecked by the kernel through `decide +kernel` on the leaf checks.')
        out = ['import OddPerfect.ThreeFreeThreeChecker', '', '/-!',
               f'# Data for three exceptional primes, part {mi}', ''] + [y for y in textwrap.wrap(
               para, 86, break_on_hyphens=False)]
        out = [x.replace('\x00', ', ') for x in out] + ['-/', '', 'namespace OddPerfect', '',
               'namespace ThreeFreeThree', '']
        pub = []
        for (ti, k, cl, nd, t, is_root) in mod:
            un = f'u{ti}_{k}'
            leaves = []
            leaf_list(cl, nd, t, leaves)
            groups = [leaves[j:j + GROUP] for j in range(0, len(leaves), GROUP)]
            ref = {}
            for gj, grp in enumerate(groups):
                gname = f'{un}_g{gj}'
                terms = [f'leafOK {lcls(cl)} {lnode(lnd)} {lw(lt[2])}' for lnd, lt in grp]
                body = terms[-1]
                for tm in reversed(terms[:-1]):
                    body = f'{tm} &&\n    ({body})'
                if len(terms) > 1:
                    body = f'({body})'
                out.append(f'private theorem {gname} :\n    {body} = true := by\n  decide +kernel\n')
                for pos, (lnd, lt) in enumerate(grp):
                    e = gname
                    for _ in range(pos):
                        e = f'(Bool.and_eq_true_iff.mp {e}).2'
                    if pos < len(grp) - 1:
                        e = f'(Bool.and_eq_true_iff.mp {e}).1'
                    ref[lt[1]] = e

            def asm(tt, ind):
                pad = '  ' * ind
                if tt[0] == 'leaf':
                    return f'treeOK_leaf {ref[tt[1]]}'
                _, i, p, t1, t2 = tt
                return (f'treeOK_split (by decide) rfl\n{pad}  ({asm(t1, ind + 1)})\n'
                        f'{pad}  ({asm(t2, ind + 1)})')
            tri = ', '.join(d['triples'][ti]['triple'])
            out.append(f'/-- Subtree {k} of the class triple `({tri})`, with {nleaves(t)} leaves. -/')
            out.append(f'def {un} : Tree :=\n  {ltree(t, 1)}\n')
            ndtxt = f'(rootNode {lcls(cl)})' if is_root else lnode(nd)
            out.append(f'/-- Subtree {k} of the class triple `({tri})` passes the check. -/')
            out.append(f'theorem {un}_ok : treeOK {lcls(cl)}\n    {ndtxt} {un} = true :=\n  {asm(t, 1)}\n')
            pub.append(f'{un}_ok')
        out += ['end ThreeFreeThree', '', 'end OddPerfect', '']
        out += [f'#print axioms OddPerfect.ThreeFreeThree.{p}' for p in pub]
        open(os.path.join(outdir, name + '.lean'), 'w').write('\n'.join(out) + '\n')
        print(name, 'units', len(mod), 'leaves', nl)
    assert total == len(all_leaves(d)) == 1223
    # final module
    out = [f'import OddPerfect.{n}' for n in names]
    out += ['', '/-!', '# Odd perfect numbers with three exceptional primes are divisible by 3', '',
            'Let `N` be an odd perfect number with special prime `q`, and suppose every prime factor `p`',
            'of `N` except `q`, `r₁`, `r₂` and `r₃` has an exponent `e` with `3 ∣ e + 1` (for example',
            '`e = 2`). We show `3 ∣ N` (`three_dvd_of_three_mod_exceptions`). The case of exponents',
            'exactly 2 is `three_dvd_of_three_exceptions`, which extends `three_dvd_of_two_exceptions` to',
            'three exceptions, and `four_le_card_mod_exceptions` is the counting form: if `3 ∤ N`, at',
            'least four prime factors of `N` other than `q` have an exponent `e` with `3 ∤ e + 1`.', '',
            'For context only (the literature was not screened): Ochem and Zelinsky (arXiv 2607.19746)',
            'treat one exception with exact squares, and Fletcher, Nielsen and Ochem (Math. Comp. 81,',
            '2012) bound the least prime factor when every ordinary exponent `e` has `3 ∣ e + 1` or',
            '`5 ∣ e + 1`, with no exception.', '',
            'Assume `3 ∤ N`. The labels are replaced by three distinct prime factors of `N` other than `q`',
            '(`ThreeFreeThree.ctx4_of_not_three_dvd`). The three primes are then relabeled so',
            'that their classes are sorted (`ThreeFreeThree.Ctx4.cover`), and for each of the 102 sorted',
            'class triples a binary split tree of constraints is checked by `ThreeFreeThree.treeOK`,',
            'whose soundness is `ThreeFreeThree.treeOK_sound`. The 1223 leaves of the trees were found by',
            'a search outside Lean and are rechecked by the kernel in the modules',
            f'`OddPerfect.ThreeFreeThreeData01` to `OddPerfect.{names[-1]}`.',
            '-/', '', 'namespace OddPerfect', '', 'namespace ThreeFreeThree', '']
    for ti, T in enumerate(d['triples']):
        cl = tuple(T['triple'])
        tri = ', '.join(cl)
        out.append(f'/-- The tree of the class triple `({tri})`. -/')
        out.append(f'def tree{ti} : Tree := {top[ti][0]}\n')
        out.append(f'/-- The tree of the class triple `({tri})` passes the check. -/')
        out.append(f'theorem tree{ti}_ok : treeOK {lcls(cl)} (rootNode {lcls(cl)}) tree{ti} = true :=\n  {top[ti][1]}\n')
    out.append('/-- The trees of the 102 sorted class triples. -/')
    out.append('def trees : List (ClassTriple × Tree) :=\n  [' + ',\n    '.join(
        f'({lcls(tuple(T["triple"]))}, tree{ti})' for ti, T in enumerate(d['triples'])) + ']\n')
    out.append('''private theorem forall_cons {P : ClassTriple × Tree → Prop} {a : ClassTriple × Tree}
    {l : List (ClassTriple × Tree)} (ha : P a) (hl : ∀ e ∈ l, P e) : ∀ e ∈ a :: l, P e :=
  List.forall_mem_cons.mpr ⟨ha, hl⟩

private theorem trees_fst : trees.map Prod.fst = triples := by decide +kernel
''')
    pf = '(fun _ h => absurd h List.not_mem_nil)'
    for ti in reversed(range(len(d['triples']))):
        pf = f'forall_cons tree{ti}_ok\n    ({pf})' if ti else f'forall_cons tree{ti}_ok\n    ({pf})'
    out.append('private theorem trees_ok : ∀ e ∈ trees, treeOK e.1 (rootNode e.1) e.2 = true :=\n  ' + pf + '\n')
    out.append('''/-- The check of all trees, assembled from the separate tree checks. -/
theorem allOK_trees : allOK trees = true :=
  allOK_of fun t ht => by
    rw [← trees_fst] at ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    exact ⟨e.2, he, trees_ok e he⟩

end ThreeFreeThree

/-- An odd perfect number `N` with special prime `q`, in which every prime factor `p` other than
`q` and three further numbers `r₁`, `r₂`, `r₃` has an exponent `e = N.factorization p` with
`3 ∣ e + 1`, is divisible by 3. Here `r₁, r₂, r₃` are arbitrary natural numbers: they need not
be distinct, prime, or divisors of `N`, so the cases of fewer exceptional primes are included.
The case analysis behind the proof was found by a search outside Lean and is rechecked by the
kernel. -/
theorem three_dvd_of_three_mod_exceptions {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hmod : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → 3 ∣ N.factorization p + 1) :
    3 ∣ N :=
  ThreeFreeThree.three_dvd_of_three_exceptions_of_check ThreeFreeThree.trees
    ThreeFreeThree.allOK_trees h hq hodd hmod

/-- An odd perfect number in which every prime factor other than the special prime `q` and
three further primes `r₁`, `r₂`, `r₃` has exponent exactly 2 is divisible by 3. Here
`r₁, r₂, r₃` are arbitrary natural numbers: they need not be distinct, prime, or divisors of
`N`, so the cases of fewer exceptional primes are included. This is the case `e = 2` of
`three_dvd_of_three_mod_exceptions`. -/
theorem three_dvd_of_three_exceptions {N q r₁ r₂ r₃ : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → p ≠ r₃ → N.factorization p = 2) :
    3 ∣ N :=
  three_dvd_of_three_mod_exceptions (r₁ := r₁) (r₂ := r₂) (r₃ := r₃) h hq hodd
    fun p hp h0 h1 h2 h3 => by simp [hsq p hp h0 h1 h2 h3]

/-- The counting form of `three_dvd_of_three_mod_exceptions`: if `N` is an odd perfect number
with special prime `q` and `3 ∤ N`, then at least four prime factors `p ≠ q` of `N` have an
exponent `e = N.factorization p` with `3 ∤ e + 1`. -/
theorem four_le_card_mod_exceptions {N q : ℕ} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q)) (h3 : ¬ 3 ∣ N) :
    4 ≤ ((N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1).card := by
  by_contra hc
  set B := (N.primeFactors.erase q).filter fun p => ¬ 3 ∣ N.factorization p + 1
  have hB : B.card ≤ 3 := by omega
  have hU : 3 ≤ (B ∪ {0, 1, 2}).card :=
    le_trans (by decide) (Finset.card_le_card Finset.subset_union_right)
  obtain ⟨R, hBR, -, hR⟩ := Finset.exists_subsuperset_card_eq Finset.subset_union_left hB hU
  obtain ⟨a, b, d, -, -, -, rfl⟩ := Finset.card_eq_three.mp hR
  apply h3
  refine three_dvd_of_three_mod_exceptions (r₁ := a) (r₂ := b) (r₃ := d) h hq hodd
    fun p hp hpq ha hb hd => ?_
  by_contra hn
  have hm := hBR (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hpq, hp⟩, hn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  tauto

end OddPerfect

#print axioms OddPerfect.ThreeFreeThree.allOK_trees
#print axioms OddPerfect.three_dvd_of_three_mod_exceptions
#print axioms OddPerfect.three_dvd_of_three_exceptions
#print axioms OddPerfect.four_le_card_mod_exceptions''')
    open(os.path.join(outdir, 'ThreeFreeThree.lean'), 'w').write('\n'.join(out) + '\n')
    print('modules', len(names), 'leaves', total)


def read_cert(path):
    """Bytes of the certificate, plain or compressed with xz (file name ending in .xz)."""
    if path.endswith('.xz'):
        import lzma
        with lzma.open(path) as fh:
            return fh.read()
    with open(path, 'rb') as fh:
        return fh.read()


def main():
    if len(sys.argv) < 3:
        raise SystemExit('usage: python3 -I gen_lean.py CERT MODE [ARG]; see the header')
    raw = read_cert(sys.argv[1])
    if sys.argv[2] == 'data':
        import hashlib
        h = hashlib.sha256(raw).hexdigest()
        assert h == SHA256, 'certificate hash mismatch'
        gen_data(json.loads(raw), sys.argv[3])
        return
    d = json.loads(raw)
    cmd = sys.argv[2]
    # table check against the certificate
    assert {int(k) for k in d['table']} == {s for s, _ in TABLE}
    for s, fs in TABLE:
        assert sorted(p for p, e in d['table'][str(s)]) == fs
    cm = cert_leaf_map(d)
    leaves = all_leaves(d)
    if cmd == 'mirror':
        bad = 0
        worst = Fraction(0)
        cworst = (Fraction(0), 0)
        maxex = (0, None)
        for ti, lid, cl, nd, w in leaves:
            L = cm[lid]
            ok, info = leaf_ok(cl, nd, w)
            cleast = [s['pinned'] if 'pinned' in s else s['least'] for s in L['slots']]
            cC = sorted(x['s'] for x in L['C'])
            Xc = Fraction(*L['X'])
            bc = Fraction(*L['bound'])
            agree = (info['m'] == cleast and info.get('C') == cC and 'X' in info
                     and Fraction(*info['X']) == Xc and info.get('bound') == bc
                     and [tuple(x) for x in L['weights']] == list(w))
            # slot constraints agree with the certificate
            for s, cs in zip(nd, L['slots']):
                if 'pinned' in cs:
                    agree &= s == ('pin', cs['pinned'])
                else:
                    agree &= s[0] == 'free' and s[2] == cs['lb'] and sorted(s[3]) == sorted(cs['excluded'])
            if not ok or not agree:
                bad += 1
                print('MISMATCH', lid, ok, info['m'], cleast)
            worst = max(worst, info.get('bound', 0))
            cworst = max(cworst, (info.get('cbound', 0), lid))
            if info['exact'] > maxex[0]:
                maxex = (info['exact'], lid)
        print('leaves', len(leaves), 'bad', bad, 'worst', float(worst), 'max exact', maxex)
        print('worst corrected bound %d/%d ~ %.9f at leaf %d' % (cworst[0].numerator,
              cworst[0].denominator, float(cworst[0]), cworst[1]))
    elif cmd == 'leaf':
        lid = int(sys.argv[3])
        for ti, l, cl, nd, w in leaves:
            if l == lid:
                ok, info = leaf_ok(cl, nd, w)
                print(f'-- leaf {lid}, triple {cl}, mirror ok={ok}, exact vectors {info["exact"]}')
                print(f'theorem leaf_{lid} : leafOK {lcls(cl)}\n    {lnode(nd)}\n    {lw(w)} = true := by\n  decide +kernel')
    elif cmd == 'tree':
        ti = int(sys.argv[3])
        T = d['triples'][ti]
        cl = tuple(T['triple'])
        n = sum(1 for x in leaves if x[0] == ti)
        print(f'-- triple {ti} {cl}, {n} leaves')
        print(f'def tree_{ti} : Tree :=\n  {ltree(bin_tree(T["tree"]), 1)}')
        print(f'theorem tree_{ti}_ok : treeOK {lcls(cl)} (rootNode {lcls(cl)}) tree_{ti} = true := by\n  decide +kernel')
    elif cmd == 'treesplit':
        # one declaration per leaf, assembled with treeOK_split and treeOK_leaf
        ti = int(sys.argv[3])
        T = d['triples'][ti]
        cl = tuple(T['triple'])
        bt = bin_tree(T['tree'])
        lines = []

        def proof(nd, t, ind):
            pad = '  ' * ind
            if t[0] == 'leaf':
                lines.append(f'theorem t{ti}_leaf_{t[1]} : leafOK {lcls(cl)}\n    {lnode(nd)}\n    {lw(t[2])} = true := by\n  decide +kernel')
                return f'treeOK_leaf t{ti}_leaf_{t[1]}'
            _, i, p, t1, t2 = t
            a = proof(pin_child(cl, nd, i, p), t1, ind + 1)
            b = proof(rest_child(nd, i, p), t2, ind + 1)
            return f'treeOK_split (by decide) rfl\n{pad}  ({a})\n{pad}  ({b})'
        pf = proof(root(cl), bt, 1)
        print(f'-- triple {ti} {cl}')
        print('\n\n'.join(lines))
        print(f'def tree_{ti} : Tree :=\n  {ltree(bt, 1)}')
        print(f'theorem tree_{ti}_ok : treeOK {lcls(cl)} (rootNode {lcls(cl)}) tree_{ti} = true :=\n  {pf}')
    elif cmd == 'stats':
        import collections
        c = collections.Counter(x[0] for x in leaves)
        for ti, T in enumerate(d['triples']):
            print(ti, T['triple'], c[ti])


if __name__ == '__main__':
    main()
