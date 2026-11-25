# Untrusted helper script for the OddPerfect Lean library.
# Writes the Lean data module of a defect tree certificate (written by search.py): the
# parameters, the flat Pratt certificate, the fact table and the certificate term, and the
# kernel check `check params pratt tab cert = true` for the checker of
# OddPerfect/DefectTreeCode.lean (soundness in OddPerfect/DefectTreeCheck.lean).
#
# Run: python3 gen.py CERT ROWS NAME OUT.lean [corrupt] [split]
#   With the flag split (and optionally gnodes=G) the data goes to several modules (OUTP.lean,
#   OUTT.lean, OUTG0.lean, ..., OUT.lean): the Pratt certificate and the fact table in parts,
#   subtrees of at most G nodes, each with its own kernel check, so that a large certificate
#   stays inside the time and memory budget of one module (see the comment at `if SPLIT`;
#   the options pper=N, tper=N, pmods=M and tmods=M are described there).
#   statement A, K = 2: python3 gen.py cert2.json rows.json Two DefectTreeTwoData.lean
#   NAME is the suffix of the Lean names. With the flag corrupt the first capacity leaf gets
#   a wrong witness and the module states `check ... = false` instead (a control, not landed).
# Options: gnodes, pper and tper at least 1, pmods and tmods at least 0 (decimal digits only);
# NAME letters and digits only; OUT ends with .lean; corrupt and split exclude each other.
# Rows: every unmarked row of ROWS must multiply back to its value up to a power of 2 (except
# the nine landed rows of LANDED_PARTIAL, pinned to their recorded facts), and the certificate
# must use no row of the field "partial". Pratt certificate: every prime from 200 on that the
# Lean checker tests (each fact prime of the table and the root prime); each factorization of
# p - 1 it uses must list integers above 1 (no booleans) that multiply back to p - 1, each prime
# (below 200 by trial division, from 200 on by its own entry), and the witness is searched
# below p only. The inputs are read by the strict loader certio.py (exact types, natural
# numbers, a closed set of fields and tags).
# Output: every file is first written under a temporary name in its target folder and renamed
# into place only after all were written; a failure before the renames removes the temporary
# files and changes no target. The renames are one after another, not one atomic step.
# Exit status: 0 when the module is written, 1 when a check fails (nothing is written) or a
# file cannot be written, 2 for a usage error or malformed input.
# Requires: Python 3 standard library only. The Pratt witnesses are computed from the frozen
# factorizations of p - 1 in ROWS.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.

import sys, os, hashlib


def usage(why):
    print('usage: python3 gen.py CERT ROWS NAME OUT.lean [corrupt] [split] [gnodes=G] [pper=N] '
          '[tper=N] [pmods=M] [tmods=M]: %s' % why, file=sys.stderr)
    sys.exit(2)


def malformed(msg):
    print('malformed input: ' + msg, file=sys.stderr)
    sys.exit(2)


def fail(msg):
    print('rejected: %s; nothing written' % msg, file=sys.stderr)
    sys.exit(1)


if len(sys.argv) < 5:
    usage('expected at least 4 arguments')
CERT, ROWS, NAME, OUT = sys.argv[1:5]
if not (NAME.isascii() and NAME.isalnum()):
    usage('NAME must consist of letters and digits, got %r' % NAME)
if not OUT.endswith('.lean') or OUT.split('/')[-1] == '.lean':
    usage('OUT must be a file name ending with .lean, got %r' % OUT)
LOW = {'gnodes': 1, 'pper': 1, 'tper': 1, 'pmods': 0, 'tmods': 0}
seen = set()
for a in sys.argv[5:]:
    key, eq, val = a.partition('=')
    if a in ('corrupt', 'split') and a not in seen:
        seen.add(a)
    elif eq and key in LOW and key not in seen and val.isascii() and val.isdigit() and \
            int(val) >= LOW[key]:
        seen.add(key)
    else:
        usage('unknown, repeated or out of range flag %r' % a)
CORRUPT = 'corrupt' in sys.argv[5:]
SPLIT = 'split' in sys.argv[5:]
if CORRUPT and SPLIT:
    usage('corrupt and split exclude each other')


sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import certio     # the strict loader shared with search.py and check.py (exit 2 on violation)

c = certio.load_cert(CERT)
rows, pm1, PARTSET = certio.load_rows(ROWS)
P = c['params']
for p, m in c['rows']:
    if (p, m) not in rows:
        malformed('%s: row (%d, %d) is not in the table %s' % (CERT, p, m, ROWS))
tab = [(p, m, rows[(p, m)]) for p, m in c['rows']]


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


for p, m, fs in tab:
    if (p, m) in PARTSET:
        fail('the certificate uses the row (%d, %d), marked partial in %s' % (p, m, ROWS))
for (p, m), fs in sorted(rows.items()):
    if (p, m) in PARTSET or LANDED_PARTIAL.get((p, m)) == [tuple(f) for f in fs]:
        continue
    n = odd_cofactor(gs(p, m), [tuple(f) for f in fs])
    if n != 1:
        fail('the facts of the row (%d, %d) do not multiply back to its value' % (p, m))

# Pratt certificate, in dependency order, for every prime from 200 on that the Lean checker
# tests with isPr (OddPerfect/DefectTreeCode.lean): each fact prime of the table (tabOK) and
# the root prime (brHead at the root). A branch at a node needs no certificate of its own: its
# prime is forced, so it is a fact prime of the table. Primes below 200 must pass the trial
# division of isPr.
out, done = [], set()

def pratt(p):
    if p < 200:
        if not certio.trial_prime(p):
            fail('%d is below 200 and not prime by trial division' % p)
        return
    if p in done:
        return
    if p not in pm1:
        fail('no factorization of %d - 1 for the Pratt certificate' % p)
    fs = pm1[p]
    bad = certio.pm1_problem(p, fs)
    if bad:
        fail(bad)
    for r in sorted(set(fs)):
        pratt(r)
    # a < p: when no such a exists, p is not prime (or the factor list is wrong).
    a = certio.pratt_witness(p, fs)
    if a is None:
        fail('no Pratt witness below %d for the factorization %r of %d - 1' % (p, fs, p))
    done.add(p)
    out.append((p, a, fs))

for p, m, fs in tab:
    for r, k in fs:
        pratt(r)
pratt(P['root'])

def lean_cert(t):
    k = t['t']
    if k == 'cap':
        return '(.leaf (.cap %d))' % t['r']
    if k == 'small':
        return '(.leaf (.small %d))' % t['r']
    if k == 'budget':
        return '(.leaf .budget)'
    if k == 'ledger':
        return '(.leaf (.ledger [%s]))' % ', '.join(map(str, t['ks']))
    if k == 'abund':
        return '(.leaf (.abund [%s]))' % ', '.join('(%d, %d)' % (p, f) for p, f in t['ws'])
    if k == 'br':
        sp = '.nil' if t['sp'] is None else lean_cert(t['sp'])
        return '(.br %d %s %s)' % (t['r'], sp, lean_chain(t['ch']))
    if k == 'open':
        fail('the certificate has an open leaf')
    malformed('%s: unknown node %r' % (CERT, k))

def lean_chain(items):
    s = ''
    for it in reversed(items):
        if it['t'] == 'high':
            if s != '':
                fail('a chain item high that is not the last of its chain')
            s = '(.high %s)' % lean_cert(it['kid'])
        else:
            s = '(.ord %s %s)' % (lean_cert(it['kid']), s)
    return s

def corrupt(t, state):
    """Change the first capacity witness to a prime that is not an exact entry."""
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

if CORRUPT:
    st = [False]
    corrupt(c['cert'], st)
    if not st[0]:
        fail('corrupt: the certificate has no capacity leaf')

def wrap(items, per=6):
    lines = []
    for i in range(0, len(items), per):
        lines.append('  ' + ', '.join(items[i:i + per]))
    return ',\n'.join(lines)

cap = 'none' if P['cap'] is None else '(some %d)' % P['cap']
sha = hashlib.sha256(open(CERT, 'rb').read()).hexdigest()
L = []
L.append('import OddPerfect.DefectTreeCode')
L.append('')
L.append('/-!')
L.append('# Defect tree certificate `%s`: data and kernel check' % NAME)
L.append('')
L.append('Generated by `scripts/DefectTree/gen.py` from the certificate `%s`' % CERT.split('/')[-1])
L.append('(sha256 `%s`) and the frozen row table `%s`.' % (sha, ROWS.split('/')[-1]))
L.append('The parameters are `K = %d`, `w = %d`, `u = %d`, root `%d`, cap `%s`.'
         % (P['K'], P['w'], P['u'], P['root'], cap))
L.append('The table has %d rows; the Pratt certificate has %d entries.' % (len(tab), len(out)))
L.append('This module only evaluates the checker; what an accepted certificate means is the')
L.append('soundness theorem `OddPerfect.DefectTree.check_sound`.')
L.append('-/')
L.append('')
L.append('namespace OddPerfect')
L.append('')
L.append('namespace DefectTree')
L.append('')
L.append('/-- The parameters of the certificate. -/')
L.append('def params%s : Params := { K := %d, w := %d, u := %d, root := %d, cap := %s }'
         % (NAME, P['K'], P['w'], P['u'], P['root'], cap))
L.append('')
L.append('/-- The flat Pratt certificate for the fact primes from 200 on. -/')
L.append('def pratt%s : PCert := [' % NAME)
L.append(',\n'.join('  (%d, %d, [%s])' % (p, a, ', '.join(map(str, fs))) for p, a, fs in out)
         + ']')
L.append('')
L.append('/-- The fact table: rows `(p, m)` with facts `(r, k)`, `r ^ k ∣ 1 + p + ... + p ^ m`. -/')
L.append('def tab%s : Tab := [' % NAME)
L.append(',\n'.join('  (%d, %d, [%s])' % (p, m, ', '.join('(%d, %d)' % (r, k) for r, k in fs))
                    for p, m, fs in tab) + ']')
L.append('')
L.append('/-- The certificate term. -/')
L.append('def cert%s : Cert :=' % NAME)
try:       # the whole tree once, before any output: shape errors end here
    L.append('  ' + lean_cert(c['cert']))
except (KeyError, TypeError, IndexError) as e:
    malformed('%s: a node with missing or wrong fields: %r' % (CERT, e))
L.append('')
if CORRUPT:
    L.append('/-- The corrupted certificate is rejected. -/')
    L.append('theorem check_%s_bad : check params%s pratt%s tab%s cert%s = false := by'
             % (NAME, NAME, NAME, NAME, NAME))
else:
    L.append('/-- The certificate is accepted. -/')
    L.append('theorem check_%s : check params%s pratt%s tab%s cert%s = true := by'
             % (NAME, NAME, NAME, NAME, NAME))
L.append('  decide +kernel')
L.append('')
L.append('end DefectTree')
L.append('')
L.append('end OddPerfect')
L.append('')
L.append('#print axioms OddPerfect.DefectTree.check_%s%s' % (NAME, '_bad' if CORRUPT else ''))
def fold(line, width=100, ind='    '):
    if len(line) <= width:
        return [line]
    out, cur = [], ''
    for tok in line.split(' '):
        cand = tok if cur == '' else cur + ' ' + tok
        if len(cand) > width and cur.strip():
            out.append(cur)
            cur = ind + tok
        else:
            cur = cand
    out.append(cur)
    return out

def fold_ind(line, width=100):
    # Like fold, but keeps the indentation of the line (needed for tactic lines).
    ind = line[:len(line) - len(line.lstrip(' '))]
    return [ind + x if k == 0 else x for k, x in
            enumerate(fold(line[len(ind):], width - len(ind), ind + '    '))]

PENDING = []     # (path, text): written only after every check has passed


def emit(path, lines, f=fold):
    text = '\n'.join(x for l in '\n'.join(lines).split('\n') for x in f(l))
    PENDING.append((path, text + '\n'))

def opt(key, default):
    for a in sys.argv[5:]:
        if a.startswith(key + '='):
            return int(a.split('=')[1])
    return default

def size(t):
    if t['t'] != 'br':
        return 1
    return 1 + (0 if t['sp'] is None else size(t['sp'])) + sum(size(it['kid']) for it in t['ch'])

def lean_st(os_, sp):
    return '⟨[%s], %d⟩' % (', '.join('(%d, %d, %s)' % (p, e, 'true' if x else 'false')
                                    for p, e, x in os_), sp)

if SPLIT:
    # Modules: OUTP.lean (parameters, Pratt certificate in parts of 150 entries, one kernel
    # check per part), OUTT.lean (fact table in parts of 150 rows, one kernel check per part),
    # OUTG0.lean, OUTG1.lean, ... (subtrees of at most `gnodes` nodes with the states at which
    # they sit, one kernel check per subtree, at most `gnodes` nodes per module), and OUT.lean
    # (the remaining tree with the subtrees by name, assembled by `simp`, and the full check).
    # Options: pper=N and tper=N change the part sizes (default 150); pmods=M (tmods=M) moves
    # the Pratt parts (table parts) to the modules OUTP0.lean, OUTP1.lean, ... (OUTT0.lean,
    # ...), M parts each, and leaves in OUTP.lean (OUTT.lean) only the joined list and its
    # check. Without these options the output is unchanged.
    PER = 150
    GN = opt('gnodes', 10 ** 9)
    base = OUT[:-len('.lean')]
    mod = 'OddPerfect.' + base.split('/')[-1]
    hdr = L[:L.index('namespace OddPerfect')]
    title = hdr.index('# Defect tree certificate `%s`: data and kernel check' % NAME)
    ns = ['namespace OddPerfect', '', 'namespace DefectTree', '']
    end = ['end DefectTree', '', 'end OddPerfect', '']
    pn, tn = 'pratt%s' % NAME, 'tab%s' % NAME
    args = 'params%s %s %s' % (NAME, pn, tn)

    def parts(items, per):
        return [items[i:i + per] for i in range(0, len(items), per)] or [[]]

    def nest(names):
        """`a ++ (b ++ (c ++ ...))`, built from the right without recursion (many parts with
        tper=1 or pper=1)."""
        s = names[-1]
        for n in reversed(names[:-1]):
            s = '%s ++ (%s)' % (n, s)
        return s

    def chunked(X, blocks, M, sfx, what, thm):
        """Without M (the default) the blocks go into X. With M, the blocks go to the modules
        OUT<sfx>0.lean, OUT<sfx>1.lean, ..., M blocks each, each importing the one before (the
        first takes the import and the beginning of X); X keeps the header and imports the
        last of them."""
        if M == 0:
            return X + [x for b in blocks for x in b]
        groups = [list(range(i, min(i + M, len(blocks)))) for i in range(0, len(blocks), M)]
        for j, ks in enumerate(groups):
            Y = list(X[:len(hdr)])
            if j > 0:
                Y[0] = 'import %s%s%d' % (mod, sfx, j - 1)
            Y[title] = '# Defect tree certificate `%s`, %s, parts %d to %d' % (NAME, what,
                                                                            ks[0], ks[-1])
            Y += (X[len(hdr):] if j == 0 else ns) + [x for k in ks for x in blocks[k]] + end
            Y += ['#print axioms OddPerfect.DefectTree.%s_%s_%d' % (thm, NAME, k) for k in ks]
            emit('%s%s%d.lean' % (base, sfx, j), Y, fold_ind)
        Z = list(X[:len(hdr)])
        Z[0] = 'import %s%s%d' % (mod, sfx, len(groups) - 1)
        return Z + ns

    prs = parts(['  (%d, %d, [%s])' % (p, a, ', '.join(map(str, fs))) for p, a, fs in out],
               opt('pper', PER))
    A = list(hdr)
    A[0] = 'import OddPerfect.DefectTreeSplit'
    A[title] = '# Defect tree certificate `%s`, part 1: parameters and Pratt certificate' % NAME
    A += ns + ['/-- The parameters of the certificate. -/',
               'def params%s : Params := { K := %d, w := %d, u := %d, root := %d, cap := %s }'
               % (NAME, P['K'], P['w'], P['u'], P['root'], cap), '']
    known = '[]'
    pblocks = []
    for i, part in enumerate(prs):
        pblocks.append(['/-- Part %d of the Pratt certificate. -/' % i,
              'def %s_%d : PCert := [' % (pn, i), ',\n'.join(part) + ']', '',
              '/-- Part %d of the Pratt certificate is accepted. -/' % i,
              'theorem prattOK_%s_%d : Pratt.checkAux %s %s_%d = true := by' % (NAME, i, known,
                                                                                pn, i),
              '  decide +kernel', ''])
        known = '(%s_%d.reverse.map Prod.fst ++ %s)' % (pn, i, known)
    A = chunked(A, pblocks, opt('pmods', 0), 'P', 'Pratt certificate', 'prattOK')
    names = ['%s_%d' % (pn, i) for i in range(len(prs))]
    steps = []
    for i in range(len(prs)):
        if i < len(prs) - 1:
            steps.append('checkAux_append')
        steps.append('prattOK_%s_%d' % (NAME, i))
    A += ['/-- The Pratt certificate: the parts joined. -/',
          'def %s : PCert := %s' % (pn, nest(names)), '',
          '/-- The Pratt certificate is accepted. -/',
          'theorem prattOK_%s : Pratt.check %s = true := by' % (NAME, pn),
          '  rw [Pratt.check, %s, %s]' % (pn, ', '.join(steps))]
    A += (['  all_goals decide'] if len(prs) > 1 else []) + [''] + end
    if not opt('pmods', 0):
        A += ['#print axioms OddPerfect.DefectTree.prattOK_%s_%d' % (NAME, i)
              for i in range(len(prs))]
    A += ['#print axioms OddPerfect.DefectTree.prattOK_%s' % NAME]

    tbs = parts(['  (%d, %d, [%s])' % (p, m, ', '.join('(%d, %d)' % (r, k) for r, k in fs))
                 for p, m, fs in tab], opt('tper', PER))
    B = list(hdr)
    B[0] = 'import %sP' % mod
    B[title] = '# Defect tree certificate `%s`, part 2: fact table' % NAME
    B += ns
    tblocks = []
    for i, part in enumerate(tbs):
        tblocks.append(['/-- Part %d of the fact table. -/' % i,
              'def %s_%d : Tab := [' % (tn, i), ',\n'.join(part) + ']', '',
              '/-- Part %d of the fact table is accepted. -/' % i,
              'theorem tabOK_%s_%d : tabOK %s %s_%d = true := by' % (NAME, i, pn, tn, i),
              '  decide +kernel', ''])
    B = chunked(B, tblocks, opt('tmods', 0), 'T', 'fact table', 'tabOK')
    steps = []
    for i in range(len(tbs)):
        if i < len(tbs) - 1:
            steps.append('tabOK_append')
        steps.append('tabOK_%s_%d' % (NAME, i))
    B += ['/-- The fact table: the parts joined. -/',
          'def %s : Tab := %s' % (tn, nest(['%s_%d' % (tn, i) for i in range(len(tbs))])), '',
          '/-- The fact table is accepted. -/',
          'theorem tabOK_%s : tabOK %s %s = true := by' % (NAME, pn, tn),
          '  rw [%s, %s]' % (tn, ', '.join(steps))]
    B += (['  all_goals decide'] if len(tbs) > 1 else []) + [''] + end
    if not opt('tmods', 0):
        B += ['#print axioms OddPerfect.DefectTree.tabOK_%s_%d' % (NAME, i)
              for i in range(len(tbs))]
    B += ['#print axioms OddPerfect.DefectTree.tabOK_%s' % NAME]

    # Cut the tree into subtrees of at most GN nodes; the rest stays in the final module.
    pieces = []
    def cut(t, os_, sp):
        """The Lean term of the node t at the state (os_, sp) in node mode."""
        if size(t) <= GN and t is not c['cert']:
            pieces.append((t, os_, sp))
            return 'piece%s_%d' % (NAME, len(pieces) - 1)
        if t['t'] != 'br':      # unreachable: a leaf has size 1 <= GN
            fail('split: a leaf above the node limit')
        r = t['r']
        if t['sp'] is None:
            spk = '.nil'
        else:
            if not (sp == 0 and r % 4 == 1):
                fail('split: a special child of the branch on %d at a state where it is not '
                     'allowed' % r)
            spk = cut(t['sp'], os_, r)
        s, e = '', 2
        terms = []
        for it in t['ch']:
            terms.append((it['t'], cut(it['kid'], [(r, e, it['t'] == 'ord')] + os_, sp)))
            e += 2
        for k, term in reversed(terms):
            s = '(.high %s)' % term if k == 'high' else '(.ord %s %s)' % (term, s)
        return '(.br %d %s %s)' % (r, spk, s)
    if size(c['cert']) <= GN:
        skel = '  ' + lean_cert(c['cert'])
    else:
        skel = '  ' + cut(c['cert'], [], 0)
    groups, cur, cs = [], [], 0
    for k, pc_ in enumerate(pieces):
        n = size(pc_[0])
        if cur and cs + n > GN:
            groups.append(cur)
            cur, cs = [], 0
        cur.append(k)
        cs += n
    if cur:
        groups.append(cur)
    gmods = []
    for g, ks in enumerate(groups):
        G = list(hdr)
        G[0] = 'import %sT' % mod
        G[title] = '# Defect tree certificate `%s`, subtrees %d to %d' % (NAME, ks[0], ks[-1])
        G += ns
        for k in ks:
            t, os_, sp = pieces[k]
            G += ['/-- Subtree %d (%d nodes). -/' % (k, size(t)),
                  'def piece%s_%d : Cert :=' % (NAME, k), '  ' + lean_cert(t), '',
                  '/-- Subtree %d is accepted at its state. -/' % k,
                  'theorem goPiece_%s_%d : go %s piece%s_%d %s .node = true := by'
                  % (NAME, k, args, NAME, k, lean_st(os_, sp)),
                  '  decide +kernel', '']
        G += end
        G += ['#print axioms OddPerfect.DefectTree.goPiece_%s_%d' % (NAME, k) for k in ks]
        emit('%sG%d.lean' % (base, g), G, fold_ind)
        gmods.append('%sG%d' % (mod, g))
    C = list(hdr)
    C[0] = '\n'.join('import %s' % m for m in (gmods or ['%sT' % mod]))
    C[title] = '# Defect tree certificate `%s`, part 3: tree and kernel check' % NAME
    C += ns + ['/-- The certificate term. -/', 'def cert%s : Cert :=' % NAME, skel, '']
    C += ['/-- The tree is accepted. -/',
          'theorem go_%s : go %s cert%s ⟨[], 0⟩ .root = true := by' % (NAME, args, NAME)]
    if pieces:
        C += ['  simp only [cert%s, go, %s, Nat.reduceAdd, Bool.and_true, Bool.true_and]'
              % (NAME, ', '.join('goPiece_%s_%d' % (NAME, k) for k in range(len(pieces)))),
              '  all_goals decide +kernel', '']
    else:
        C += ['  decide +kernel', '']
    C += ['/-- The certificate is accepted. -/',
          'theorem check_%s : check %s cert%s = true := by' % (NAME, args, NAME),
          '  simp only [check, prattOK_%s, tabOK_%s, go_%s, Bool.and_self]' % (NAME, NAME, NAME),
          ''] + end
    C += ['#print axioms OddPerfect.DefectTree.go_%s' % NAME,
          '#print axioms OddPerfect.DefectTree.check_%s' % NAME]
    emit(base + 'P.lean', A, fold_ind)
    emit(base + 'T.lean', B, fold_ind)
    emit(OUT, C, fold_ind)
else:
    emit(OUT, L)


def write_all(pending):
    """Writes every file under a temporary name next to its target (created new, so no
    existing file is touched), then renames each into place once all are written. On a
    failure before the renames, the temporary files created here are removed by their exact
    names and no target changes. The renames are one after another, not one atomic step."""
    made = []
    try:
        for path, text in pending:
            if os.path.isdir(path):
                raise OSError('%s is a folder' % path)
            tmp = os.path.join(os.path.dirname(path) or '.',
                               '.%s.%d.tmp' % (os.path.basename(path), os.getpid()))
            with open(tmp, 'x') as f:
                made.append(tmp)
                f.write(text)
    except OSError as e:
        for tmp in made:
            try:
                os.remove(tmp)
            except OSError:
                pass
        fail('cannot write the output: %s' % e)
    done_ = []
    try:
        for (path, _), tmp in zip(pending, made):
            os.replace(tmp, path)
            done_.append(path)
    except OSError as e:
        for tmp in made[len(done_):]:
            try:
                os.remove(tmp)
            except OSError:
                pass
        print('error: renamed %d of %d files into place before: %s' % (len(done_), len(made), e),
              file=sys.stderr)
        sys.exit(1)


write_all(PENDING)
print('wrote', OUT, 'rows', len(tab), 'pratt', len(out), 'max pratt prime',
      max((p for p, _, _ in out), default=0))
