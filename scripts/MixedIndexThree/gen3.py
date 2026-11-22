"""Generate the Lean data modules of the MixedIndexThree trees.

Inputs: root configurations cfg_<tag>.json and pruned certificates cert_<tag>.json or
cert_<tag>.json.xz (made by cert3.py). Each tree is cut into chunks of at most LIMIT branching nodes, packed into MODULES modules; a
chunk is checked from its own state, and the top of the tree ends in `cut` leaves whose states
form the list `Acc`. Every chunk and every top is first checked by a Python mirror of
`MixedIndexThree.chk3`.

Usage: python3 -I gen3.py OUTDIR LIMIT MODULES TAG [TAG ...]
Writes OUTDIR/MixedIndexThreePrimes.lean and OUTDIR/MixedIndexThreeData<j>.lean.
"""
import json, sys, os, lzma
from math import prod
from sympy import factorint, isprime

T = 100


def geom(p, a):
    return sum(p ** i for i in range(a + 1))


def conv(t):
    if 'close' in t:
        return ('abund', [tuple(x) for x in t['set']])
    p = t['p']
    ch = []
    for k in (3, 5, 7):
        c = t['br'][str(k)]
        ch.append(('shut', p, k) if 'close' in c else ('force', p, k, c['force'], conv(c['next'])))
    return ('node', p, *ch)


def is_at(p, k, t):
    return t[0] in ('force', 'shut') and t[1] == p and t[2] == k


def nd(l):
    return len(set(l)) == len(l)


def chk3(P, B, c3, c5, Acc, st, t):
    """Mirror of `chk3`; st = (K, I, A3, a5) with lists."""
    K, I, A3, a5 = st
    if t[0] == 'abund':
        l = t[1]
        ok = all(x[0] in K and (x[1] <= 2 or any(y[0] == x[0] and x[1] + 1 <= y[1] for y in I))
                 for x in l)
        L = B + l
        return (ok and nd([x[0] for x in L]) and
                2 * prod(p ** e for p, e in L) < prod(geom(p, e) for p, e in L))
    if t[0] == 'node':
        _, p, t3, t5, t7 = t
        return (p in K and is_at(p, 3, t3) and is_at(p, 5, t5) and is_at(p, 7, t7) and
                all(chk3(P, B, c3, c5, Acc, st, c) for c in (t3, t5, t7)))
    if t[0] == 'force':
        _, p, k, rs, nxt = t
        f = geom(p, k - 1)
        return (all(r in P and r not in (2, 3, 5) and f % r == 0 for r in rs) and
                nxt[0] not in ('force', 'shut') and
                chk3(P, B, c3, c5, Acc, child_state(st, t), nxt))
    if t[0] == 'shut':
        _, p, k = t
        f = geom(p, k - 1)
        return (f % 7 == 0 or (c3 != 0 and f % 3 == 0 and nd([p] + A3) and c3 < len(A3) + 2) or
                (c5 and f % 5 == 0 and a5 != 0 and a5 != p))
    return any(s == st for s in Acc)


def child_state(st, t):
    K, I, A3, a5 = st
    _, p, k, rs, _ = t
    f = geom(p, k - 1)
    return (list(rs) + K, [(p, k)] + I, ([p] + A3) if f % 3 == 0 else A3, p if f % 5 == 0 else a5)


def size(t):
    if t[0] == 'node':
        return 1 + sum(size(c[4]) for c in t[2:] if c[0] == 'force')
    return 0


def split(t, st, limit, chunks):
    """Replace subtrees (at `next` positions) by cuts so that every part has at most `limit`
    branching nodes; returns the top tree."""
    if t[0] != 'node' or size(t) <= limit:
        return t
    _, p, *cs = t
    new = []
    for c in cs:
        if c[0] == 'force':
            s2 = child_state(st, c)
            sub = c[4]
            if size(sub) <= limit:
                if size(sub) > limit // 8:
                    chunks.append((s2, sub))
                    sub = ('cut',)
            else:
                sub = split(sub, s2, limit, chunks)
            c = ('force', c[1], c[2], c[3], sub)
        new.append(c)
    return ('node', p, *new)


def primes_of(t, acc):
    if t[0] == 'node':
        for c in t[2:]:
            if c[0] == 'force':
                acc.update(c[3]); primes_of(c[4], acc)


def lean(t):
    if t[0] == 'abund':
        return '(abund [%s])' % ', '.join('(%d, %d)' % x for x in t[1])
    if t[0] == 'node':
        return '(node %d %s %s %s)' % (t[1], lean(t[2]), lean(t[3]), lean(t[4]))
    if t[0] == 'force':
        return '(force %d %d [%s] %s)' % (t[1], t[2], ', '.join(map(str, t[3])), lean(t[4]))
    if t[0] == 'shut':
        return '(shut %d %d)' % (t[1], t[2])
    return 'cut'


def lst(xs):
    return '[%s]' % ', '.join(xs)


def lean_st(s):
    K, I, A3, a5 = s
    return '(%s, %s, %s, %d)' % (lst(map(str, K)), lst('(%d, %d)' % y for y in I),
                                 lst(map(str, A3)), a5)


def pratt(primes):
    need = set()

    def add(p):
        if p < T or p in need:
            return
        need.add(p)
        for q in factorint(p - 1):
            add(q)
    for p in primes:
        add(p)
    out = []
    for p in sorted(need):
        f = factorint(p - 1)
        fs = [q for q in sorted(f) for _ in range(f[q])]
        a = 2
        while not (pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q in f)):
            a += 1
        assert prod(fs) == p - 1
        out.append((p, a, fs))
    return out


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from primes3 import primes_module  # noqa: E402


DATA = '''import %s

/-!
# The mixed index family 3, 5, 7 with special prime 5: tree data, part %d

Generated by the script `gen3.py`. %s
-/

namespace OddPerfect

namespace MixedIndexThree

open Tr
%s
end MixedIndexThree

end OddPerfect

%s'''

STATE = '''
/-- State of the chunk `%s`. -/
def st_%s : St :=
  %s
'''

CHUNK = '''
/-- Chunk `%s` of the tree `%s`. -/
def tr_%s : Tr :=
  %s

/-- The chunk `%s` is accepted from its state. -/
theorem ok_%s : chk3 primes [%s] %d %s [] st_%s.1 st_%s.2.1 st_%s.2.2.1 st_%s.2.2.2 tr_%s = true := by
  decide +kernel
'''

TOP = '''
/-- The states of the chunks of the tree `%s`. -/
def acc_%s : List St :=
  [%s]

/-- The top of the tree `%s`; it ends in `cut` at the chunk states. -/
def tr_%s_top : Tr :=
  %s

/-- The top of the tree `%s` is accepted from the root state. -/
theorem ok_%s_top : chk3 primes [%s] %d %s acc_%s [%d] [] [] 0 tr_%s_top = true := by
  decide +kernel
'''

if __name__ == '__main__':
    sys.setrecursionlimit(50000)
    outdir, limit, per = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    tags = sys.argv[4:]
    items, acc_pr, info = [], set(), []
    for tag in tags:
        cfg = json.load(open('cfg_%s.json' % tag))
        fn = 'cert_%s.json' % tag
        t = conv(json.load(open(fn)) if os.path.exists(fn) else json.load(lzma.open(fn + '.xz', 'rt')))
        primes_of(t, acc_pr)
        acc_pr |= set(cfg['pend'])
        B = [tuple(x) for x in cfg['base']]
        c3 = cfg['cap3'] or 0
        c5 = cfg['cap5'] is not None
        assert len(cfg['pend']) == 1
        root = ([cfg['pend'][0]], [], [], 0)
        chunks = []
        top = split(t, root, limit, chunks)
        items.append((tag, B, c3, c5, root, top, chunks))
    P = sorted(acc_pr)
    assert all(isprime(p) and p < 2 ** 64 for p in P)
    Ps = set(P)
    blocks = []  # (weight, text, names)
    states = []  # chunk state definitions, placed in the primes module
    for tag, B, c3, c5, root, top, chunks in items:
        Bs = ', '.join('(%d, %d)' % x for x in B)
        c5s = 'true' if c5 else 'false'
        Acc = [s for s, _ in chunks]
        assert chk3(Ps, B, c3, c5, Acc, root, top), tag
        for i, (s, sub) in enumerate(chunks):
            assert chk3(Ps, B, c3, c5, [], s, sub), (tag, i)
            n = '%s_%d' % (tag, i)
            states.append(STATE % (n, n, lean_st(s)))
            blocks.append((size(sub), CHUNK % (n, tag, n, lean(sub), n, n, Bs, c3,
                                               c5s, n, n, n, n, n), ['ok_' + n]))
        blocks.append((size(top), TOP % (tag, tag, ', '.join('st_%s_%d' % (tag, i) for i in range(len(Acc))), tag, tag,
                                         lean(top), tag, tag, Bs, c3, c5s, tag, root[0][0], tag),
                       ['ok_%s_top' % tag]))
        info.append('%s: %d chunks, top %d nodes, chunk sizes %s' %
                    (tag, len(chunks), size(top), [size(c) for _, c in chunks]))
    pc = pratt(P)
    os.makedirs(outdir, exist_ok=True)
    ptext, nsmall, nbig = primes_module(P, pc)
    k = ptext.index('\nend MixedIndexThree')
    ptext = ptext[:k] + ''.join(states) + ptext[k:]
    open(os.path.join(outdir, 'MixedIndexThreePrimes.lean'), 'w').write(ptext)
    # pack blocks into `per` modules: largest block first into the lightest module
    # (ties: lowest module number); blocks keep their generation order inside a module
    load = [0] * per
    where = {}
    for i in sorted(range(len(blocks)), key=lambda i: (-blocks[i][0], i)):
        j = min(range(per), key=lambda j: (load[j], j))
        where[i] = j; load[j] += blocks[i][0]
    mods = [[blocks[i] for i in range(len(blocks)) if where[i] == j] for j in range(per)]
    mods = [m for m in mods if m]
    for j, m in enumerate(mods, 1):
        names = [n for b in m for n in b[2]]
        desc = 'It holds the accepted trees %s.' % ', '.join('`%s`' % n for n in names)
        text = DATA % ('OddPerfect.MixedIndexThreePrimes', j, desc, ''.join(b[1] for b in m),
                       ''.join('#print axioms OddPerfect.MixedIndexThree.%s\n' % n for n in names))
        open(os.path.join(outdir, 'MixedIndexThreeData%d.lean' % j), 'w').write(text)
    print('primes', len(P), 'small', nsmall, 'pratt', nbig, 'modules', len(mods),
          'weights', [sum(b[0] for b in m) for m in mods])
    for s in info:
        print(s)
