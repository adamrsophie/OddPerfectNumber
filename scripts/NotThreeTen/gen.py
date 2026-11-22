# Untrusted helper script for the OddPerfect Lean library.
# Generates the module family OddPerfect/NotThree<Name>*.lean for the bound K + 1: the search
# state with no listed primes and K further primes, all above 4 (an odd perfect number with
# exactly K prime factors and 3 not dividing it), is closed through its window
# (OmegaSevenSearch.closed_of_window). Each child is cut by the planner plan.py of
# scripts/OmegaSeven at CAP mirror nodes (exponent splits, covers and single kernel checks of
# OddPerfect/OmegaSevenSplit.lean) and closed by `run 60` kernel checks of the verified engine.
# The checks are packed into run files of at most BUDGET mirror nodes; the last file assembles.
# Run: python3 -I gen.py OUTDIR (OUTDIR must exist). engine.py and plan.py of scripts/OmegaSeven
# are found next to this script or in ../OmegaSeven.
# Requires: Python 3 standard library. Deterministic.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [here, os.path.join(here, '..', 'OmegaSeven')]
sys.argv, out = sys.argv[:1], sys.argv[1]
import engine as E
import plan as P
import planx

K = 9                      # exactly K prime factors are excluded
NAME = 'Ten'               # module family OddPerfect/NotThree<NAME>*.lean
WORD = 'ten'               # theorem <WORD>_le_card_primeFactors_of_not_three_dvd
PREV = ('NotThreeNine', 'nine')   # module and word of the bound K
CAP = 3000
BUDGET = 50000
P.CAP = CAP

def lit(l): return '[' + ', '.join('⟨%d, %d, %s⟩' % (p, k, 'true' if ex else 'false') for p, k, ex in l) + ']'

out_thms = []
def thm(name, stmt, proof, cost=0, refs=()):
    out_thms.append(dict(name=name, body='theorem %s :\n    %s :=\n  %s\n' % (name, stmt, proof),
                         cost=cost, refs=list(refs)))

class Namer:
    def __init__(s, tag): s.tag, s.n = tag, 0
    def __call__(s):
        s.n += 1; return '%s_%d' % (s.tag, s.n)

def node(t, nm, name=None):
    name = name or nm()
    l = [tuple(e) for e in t['l']]; j, m = t['j'], t['m']
    stmt = 'Closed %s %d %d' % (lit(l), j, m)
    if t['t'] == 'leaf':
        thm(name, stmt, 'closed_of_run (f := 60) (by decide +kernel)', t['n'])
    elif t['t'] == 'force':
        c = t['c']
        assert [tuple(e) for e in t['a']['l']] == [(c, E.kmin(c), False)] + l and t['a']['j'] == j - 1
        a = node(t['a'], nm)
        thm(name, stmt, 'closed_of_force (p := %d) (k := %d) (c := %d) (by decide) (by norm_num)\n'
            '    (by decide) (by simp) (by decide +kernel) (by decide) %s' % (t['p'], t['k'], c, a), 0, (a,))
    elif t['t'] == 'split':
        i = t['i']; p, k, ex = l[i]; assert not ex
        a = node(t['a'], nm); b = node(t['b'], nm)
        assert [tuple(e) for e in t['a']['l']] == l[:i] + [(p, k, True)] + l[i+1:]
        assert [tuple(e) for e in t['b']['l']] == l[:i] + [(p, E.nextValid(p, k), False)] + l[i+1:]
        thm(name, stmt, 'closed_of_split (pre := %s) (post := %s) (by decide) %s %s'
            % (lit(l[:i]), lit(l[i+1:]), a, b), 0, (a, b))
    else:
        assert j >= 1
        pieces, pos, refs = [], m + 1, []
        for g in t['g']:
            if g['t'] == 'ival':
                assert g['a'] == pos; pos = g['b']; n2 = nm()
                thm(n2, '∀ q, %d ≤ q → q < %d → Closed (%s ++ [⟨q, kmin q, false⟩]) (%d - 1) q'
                    % (g['a'], g['b'], lit(l), j), 'ival_sound (by decide +kernel)', g['n'])
                pieces.append((g['b'], n2)); refs.append(n2)
            else:
                q = g['q']; assert q == pos; pos = q + 1
                c = node(g['c'], nm); refs.append(c)
                pieces.append((q + 1, '(cover_one (a := %d) (b := %d) rfl %s)' % (q, q + 1, c)))
        assert pos == t['B'] + 1, (pos, t['B'])
        chain = pieces[-1][1]
        for b, n2 in reversed(pieces[:-1]):
            chain = '(cover_join (b := %d) %s\n    %s)' % (b, n2, chain)
        thm(name, stmt, 'closed_of_cover (a := %d) (c := %d) (by decide) (by decide +kernel)\n'
            '    (by decide +kernel) (by decide +kernel)\n    %s' % (m + 1, t['B'] + 1, chain), 0, refs)
    return name

w = P.window([], K, 4)
total, checks, biggest, kids = 0, 0, 0, []
for q in w:
    t = P.plan([(q, E.kmin(q), False)], K - 1, q)
    L = P.leaves(t)
    total += sum(x['n'] for x in L); checks += len(L); biggest = max([biggest] + [x['n'] for x in L])
    kids.append(node(t, Namer('n%d' % q), 'closed_%d' % q))
    print('child', q, 'checks', len(L), 'max', max(x['n'] for x in L), 'sum', sum(x['n'] for x in L))

files, cur, acc = [], [], 0
for e in out_thms:
    if cur and acc + e['cost'] > BUDGET: files.append(cur); cur, acc = [], 0
    cur.append(e); acc += e['cost']
files.append(cur)
letters = 'ABCDEFGH'
assert len(files) <= len(letters)
mods = ['NotThree%s%s' % (NAME, letters[i]) for i in range(len(files))]
where = {e['name']: i for i, f in enumerate(files) for e in f}
for e in out_thms: e['public'] = e['name'].startswith('closed_')
for i, f in enumerate(files):
    for e in f:
        for r in e['refs']:
            if where[r] != i: [x for x in files[where[r]] if x['name'] == r][0]['public'] = True

HEAD = '''import OddPerfect.%s

/-!
# Odd perfect numbers not divisible by 3 with exactly %d prime factors: kernel runs, part %s

The theorems `closed_q` close the children of the search state with no listed primes and %d
further primes, all above `4`, whose smallest prime is `q` (as produced by
`OmegaSevenSearch.closed_of_window`); they are assembled in `OddPerfect/NotThree%s.lean`. The
proofs run the verified engine `OmegaSevenEngine.run` in the kernel, cut into checks of at most
%d search nodes (Python mirror count) by the exponent splits and covers of
`OddPerfect/OmegaSevenSplit.lean` and the forcing step of `OddPerfect/NotThreeTenForce.lean`.
Generated by `scripts/NotThree%s/gen.py`. Mirror nodes in this file: %d.
-/

set_option Elab.async false

namespace OddPerfect.NotThree%s

open OmegaSixSearch (Ent kmin)
open OmegaSevenSearch (Closed)
open OmegaSevenEngine (closed_of_run)
open OmegaSevenSplit
open NotThreeTenForce (closed_of_force)

set_option maxRecDepth 100000

'''
for i, f in enumerate(files):
    imp = 'NotThreeTenForce' if i == 0 else mods[i - 1]
    txt = HEAD % (imp, K, letters[i], K, NAME, CAP, NAME, sum(e['cost'] for e in f), NAME)
    txt += '\n'.join(('' if e['public'] else 'private ') + e['body'] for e in f)
    txt += '\nend OddPerfect.NotThree%s\n\n' % NAME + ''.join(
        '#print axioms OddPerfect.NotThree%s.%s\n' % (NAME, e['name']) for e in f if e['public'])
    open(os.path.join(out, mods[i] + '.lean'), 'w').write(txt)
    print(mods[i], 'nodes', sum(e['cost'] for e in f), 'theorems', len(f), 'checks', sum(1 for e in f if e['cost']))

FIN = '''import OddPerfect.%s
import OddPerfect.%s

/-!
# Odd perfect numbers not divisible by 3 have at least %s distinct prime factors

`%s_le_card_primeFactors_of_not_three_dvd`: if `3 ∤ N` for an odd perfect number `N`, then `N`
has at least %d distinct prime factors. This is known mathematics: Hagis (1983) and Kishore
(1983) proved eleven, and Nielsen (2007) proved twelve, for odd perfect numbers not divisible by
`3`. Only %d is proved here.

Proof. By `%s_le_card_primeFactors_of_not_three_dvd` it suffices to exclude exactly %d prime
factors. Such an `N` satisfies the search state with no listed primes and %d further primes, all
above `4`. Its window (`OmegaSevenSearch.closed_of_window`) is `%s`; the children are closed in
`OddPerfect/NotThree%sA.lean` and the following run files by kernel checks of the verified
engine `OmegaSevenEngine.run`, cut into checks of at most %d search nodes in the Python mirror
`scripts/OmegaSeven/engine.py`. No structural fact beyond the engine's own cuts is used. Mirror
nodes: %d in %d checks, the largest %d. Generated by `scripts/NotThree%s/gen.py`.
-/

namespace OddPerfect.NotThree%s

open OmegaSixSearch (Ent Holds kmin)
open OmegaSevenSearch (Closed closed_of_window window)

set_option maxRecDepth 100000

/-- Exactly %d prime factors, none of them `3`, is impossible. -/
theorem closed_root : Closed [] %d 4 := by
  apply closed_of_window (by decide) (by decide +kernel)
  rw [show window [] %d 4 = [%s] by decide +kernel]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨%s⟩

end OddPerfect.NotThree%s

namespace OddPerfect

open OmegaSixSearch (Holds)

/-- If `3 ∤ N` for an odd perfect number `N`, then `N` has at least %d distinct prime factors.
Known: Hagis (1983) and Kishore (1983) proved eleven, Nielsen (2007) twelve. -/
theorem %s_le_card_primeFactors_of_not_three_dvd {N : ℕ} (h : OddPerfect N) (h3 : ¬ 3 ∣ N) :
    %d ≤ N.primeFactors.card := by
  have hK := %s_le_card_primeFactors_of_not_three_dvd h h3
  by_contra hlt
  have hk : N.primeFactors.card = %d := by omega
  have H : Holds N [] %d 4 := by
    refine ⟨h, by simp, by simp, by simp [hk], ?_⟩
    intro q hq _
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hd := Nat.dvd_of_mem_primeFactors hq
    have : q ≠ 2 := fun e => h.not_two_dvd (e ▸ hd)
    have : q ≠ 3 := fun e => h3 (e ▸ hd)
    have : q ≠ 4 := fun e => by subst e; norm_num at hqp
    have := hqp.two_le
    omega
  exact NotThree%s.closed_root N H

end OddPerfect

#print axioms OddPerfect.NotThree%s.closed_root
#print axioms OddPerfect.%s_le_card_primeFactors_of_not_three_dvd
'''
ws = ', '.join(map(str, w))
txt = FIN % (mods[-1], PREV[0], WORD, WORD, K + 1, K + 1, PREV[1], K, K, ws, NAME, CAP,
             total, checks, biggest, NAME, NAME, K, K, K, ws, ', '.join(kids), NAME,
             K + 1, WORD, K + 1, PREV[1], K, K, NAME, NAME, WORD)
open(os.path.join(out, 'NotThree%s.lean' % NAME), 'w').write(txt)
print('total checks', checks, 'nodes', total, 'largest', biggest, 'files', len(files) + 1)
