"""Untrusted helper script for the OddPerfect Lean library.

Generator of the ten Lean modules of the two exception certificate: writes
TwoExceptionTwoPrimes.lean, TwoExceptionTwoData1.lean .. TwoExceptionTwoData8.lean and
TwoExceptionTwo.lean, which hold every literal behind two_exceptions_three_ne_two and
two_exceptions_six_le_three (checked by OddPerfect/TwoExcEngineCheck.lean and
TwoExcEngineTail.lean).

Run (any folder):
  python3 -I gen.py plan [CERT]          print the split of the certificate into parts
  python3 -I gen.py two OUTDIR [CERT]    write the ten modules into the existing folder OUTDIR
CERT defaults to cert.jsonl.xz next to this script; a decompressed copy may be given instead.
The certificate is translated to a term (engine.Translator) and run once in the Python mirror of
the Lean checker (engine.Mirror, instrumented here), which gives the state at every step node, the
subtree costs and the primes the checker asks the oracle about. Oracle primes below 4096 are
handled by the verified table (primeB); the others, with the primes of their Pratt certificates
above 100, go into one flat Pratt certificate sorted by size (a valid dependency order) and a
balanced search tree over the same primes. The step subtrees whose estimated kernel time is at most
CAP and whose Lean text is at most SIZECAP characters become parts, packed into K data modules in
tree order; the top of the tree, with `ext` at the roots of the parts, goes into
TwoExceptionTwo.lean. The module texts name this script by its working name `gen_two.py` and the
certificate by its working name `cert_v5_e2_100000.jsonl`; both names are kept so that the output
equals the landed modules byte for byte.
Requires: Python 3 and sympy (factorint and isprime for the Pratt certificates; checked with
sympy 1.14.0). Running time: a few seconds, one process, about 200 MB.
Deterministic: the output depends only on the certificate.
Untrusted: every module is checked by the Lean kernel.
License: GPL 3, same as the repository.
"""
import sys, os, threading, hashlib, lzma
sys.setrecursionlimit(1000000)
threading.stack_size(512 * 1024 * 1024)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine
from sympy import factorint, isprime

CERT = os.path.join(HERE, 'cert.jsonl.xz')
CAP = 12000.0     # largest part, estimated milliseconds of kernel time
SIZECAP = 50000   # largest part, characters of Lean text
MINSIZE = 400    # smaller subtrees stay in the top file
MINCOST = 200.0   # unless their estimated kernel time is at least this
K = 8             # number of data files


def cost(c):
    return 3.0 * c.get('rec', 0) + 0.16 * c.get('gen', 0)


SMALL = 100  # factors of p - 1 at most SMALL are left to the trial division of Pratt.check


def pratt(p, out, seen):
    """Appends to out the Pratt certificate entries (p, a, factors of p - 1) of p and of the
    primes above SMALL that it needs, each after the entries it depends on."""
    if p in seen or p <= SMALL:
        return
    if not isprime(p):
        raise SystemExit('oracle number %d is not prime' % p)
    f = factorint(p - 1)
    for q in f:
        pratt(q, out, seen)
    fs = sorted(q for q, e in f.items() for _ in range(e))
    for a in range(2, p):
        if pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // q, p) != 1 for q in f):
            break
    out.append((p, a, fs))
    seen.add(p)


def instrument(fn):
    """Runs the mirror on the certificate and records, for every apply and step node, its
    context and the operation counts of its subtree."""
    recs = engine.load(fn)
    T = engine.Translator(recs)
    term = T.root()
    P = engine.params(recs[0])
    M = engine.Mirror(P)
    entries = []
    oa, os_ = engine.Mirror.go_apply, engine.Mirror.go_step

    def snap():
        c = dict(engine.COUNT)
        c.update({'L_' + k: v for k, v in M.leaves.items()})
        c['oracle'] = len(engine.ORACLE)
        return c

    def diff(a, b):
        return {k: b.get(k, 0) - a.get(k, 0) for k in set(a) | set(b) if b.get(k, 0) - a.get(k, 0)}
    depth = [0]

    def go_apply(self, st, pend, comp, node):
        a = snap()
        depth[0] += 1
        r = oa(self, st, pend, comp, node)
        depth[0] -= 1
        entries.append(('apply', (st, [list(e) for e in pend], comp), node, diff(a, snap()), depth[0]))
        return r

    def go_step(self, st, node):
        a = snap()
        depth[0] += 1
        r = os_(self, st, node)
        depth[0] -= 1
        entries.append(('step', (st,), node, diff(a, snap()), depth[0]))
        return r
    engine.Mirror.go_apply = go_apply
    engine.Mirror.go_step = go_step
    orig_apply_items = engine.apply_items

    def ai(*args):
        engine.COUNT['rec'] += 1
        return orig_apply_items(*args)
    engine.apply_items = ai
    try:
        ok = M.go_apply(engine.ROOT_STATE, [], 3, term)
    finally:
        engine.Mirror.go_apply, engine.Mirror.go_step, engine.apply_items = oa, os_, orig_apply_items
    return P, term, entries, ok


def run(fn):
    engine.ORACLE.clear()
    engine.COUNT.clear()
    P, term, entries, ok = instrument(fn)
    if ok is not True:
        raise SystemExit('the mirror rejects the certificate')
    steps = {id(e[2]): e for e in entries if e[0] == 'step'}
    return P, term, steps, sorted(engine.ORACLE)


def oracle_lean(primes, sfx):
    big = [p for p in primes if p >= 4096]
    out, seen = [], set()
    for p in big:
        pratt(p, out, seen)
    out.sort()
    ps = [e[0] for e in out]
    assert set(big) <= set(ps)

    def tree(xs):
        if not xs:
            return '.leaf'
        m = len(xs) // 2
        return '(.node %s %d %s)' % (tree(xs[:m]), xs[m], tree(xs[m + 1:]))
    cert = ',\n  '.join('(%d, %d, [%s])' % (p, a, ', '.join(map(str, fs))) for p, a, fs in out)
    s = f'''/-- A flat Pratt certificate for the oracle primes from 4096 on, with the primes above 100 of
their certificates, sorted by size. -/
def pratt{sfx} : List (ℕ × ℕ × List ℕ) := [
  {cert}]

theorem pratt{sfx}_ok : Pratt.check pratt{sfx} = true := by decide +kernel

/-- A search tree over the primes of `pratt{sfx}`. -/
def tree{sfx} : PTree := {tree(ps)}

theorem tree{sfx}_toList : tree{sfx}.toList = pratt{sfx}.map Prod.fst := by decide +kernel

/-- The primality oracle: the verified table below 4096, the search tree from 4096 on. -/
def pr{sfx} (n : ℕ) : Bool := cond (Nat.blt n 4096) (primeB n) (tree{sfx}.mem n)

/-- Soundness of the oracle. -/
theorem pr{sfx}_sound : ∀ n, pr{sfx} n = true → n.Prime := by
  intro n h
  unfold pr{sfx} at h
  cases hb : Nat.blt n 4096
  · simp only [hb, cond_false] at h
    have hm := PTree.mem_toList h
    rw [tree{sfx}_toList] at hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact Pratt.check_sound pratt{sfx}_ok e he
  · simp only [hb, cond_true] at h
    exact primeB_sound h
'''
    return s, len(out)


def step_children(t):
    """The step positions directly below a node, and the other children."""
    k = t[0]
    if k == 'apply':
        return [], [t[2]]
    if k in ('force',):
        return [], list(t[1])
    if k == 'receipt':
        return [], list(t[2])
    if k == 'snd':
        return [], [t[3]]
    if k == 'closed':
        return [t[1]], []
    if k == 'decide':
        return [t[2]], list(t[1])
    if k == 'split':
        return [], [t[2], t[3]]
    return [], []


def select(term, steps):
    """Maximal step subtrees within CAP (estimated kernel time) and SIZECAP (characters of Lean text);
    those of at least MINSIZE characters become parts, the others stay in the top file."""
    parts = []

    def visit(t, is_step):
        if is_step and t[0] != 'ext' and (cost(steps[id(t)][3]) <= CAP or t[0] == 'check'):
            n = len(engine.lean_term(t))
            if n <= SIZECAP:
                if n >= MINSIZE or cost(steps[id(t)][3]) >= MINCOST:
                    parts.append(t)
                return
        st, other = step_children(t)
        for c in st:
            visit(c, True)
        for c in other:
            visit(c, False)
    visit(term, False)
    return parts


def cut(t, ids):
    if id(t) in ids:
        return ('ext',)
    k = t[0]
    if k == 'apply':
        return ('apply', t[1], cut(t[2], ids))
    if k == 'force':
        return ('force', [cut(c, ids) for c in t[1]])
    if k == 'receipt':
        return ('receipt', t[1], [cut(c, ids) for c in t[2]])
    if k == 'snd':
        return ('snd', t[1], t[2], cut(t[3], ids))
    if k == 'closed':
        return ('closed', cut(t[1], ids))
    if k == 'decide':
        return ('decide', [cut(c, ids) for c in t[1]], cut(t[2], ids))
    if k == 'split':
        return ('split', t[1], cut(t[2], ids), cut(t[3], ids))
    return t


def count(t, acc):
    acc[t[0]] = acc.get(t[0], 0) + 1
    st, other = step_children(t)
    for c in st + other:
        count(c, acc)
    if t[0] == 'check':
        pass
    return acc


HDR = '''set_option maxRecDepth 100000
'''


def plan(cert):
    P, term, steps, primes = run(cert)
    parts = select(term, steps)
    tot = cost(steps_root_counts(term, steps))
    s = 0
    for i, t in enumerate(parts):
        c = steps[id(t)][3]
        s += cost(c)
        print('part %d: size %d x %d keys %d rec %d gen %d estimate %.1f s' % (
            i + 1, len(engine.lean_term(t)), steps[id(t)][1][0]['x'], len(steps[id(t)][1][0]['keys']), c.get('rec', 0),
            c.get('gen', 0), cost(c) / 1000))
    print('top text', len(engine.lean_term(cut(term, {id(t) for t in parts}))))
    print('parts', len(parts), 'estimate in parts %.1f s, total %.1f s, top %.1f s' % (s / 1000, tot / 1000, (tot - s) / 1000))
    print('oracle primes', len(primes), 'from 4096', sum(p >= 4096 for p in primes))


def steps_root_counts(term, steps):
    # the root is an apply node; its cost is the sum over the whole tree
    acc = {'rec': 0, 'gen': 0}
    def walk(t, is_step):
        if is_step and id(t) in steps:
            c = steps[id(t)][3]
            acc['rec'] += c.get('rec', 0); acc['gen'] += c.get('gen', 0)
            return
        if t[0] == 'apply':
            acc['rec'] += 1
        st, other = step_children(t)
        for c in st:
            walk(c, True)
        for c in other:
            walk(c, False)
    walk(term, False)
    return acc


USAGE = 'usage: python3 -I gen.py plan [CERT] | python3 -I gen.py two OUTDIR [CERT]'


def main():
    a = sys.argv[1:]
    if len(a) in (1, 2) and a[0] == 'plan':
        plan(a[1] if len(a) == 2 else CERT)
    elif len(a) in (2, 3) and a[0] == 'two' and os.path.isdir(a[1]):
        two(a[1], a[2] if len(a) == 3 else CERT)
    else:
        print(USAGE)
        return 2
    return 0


def pack(parts, steps, k):
    """Split the parts, in tree order, into k consecutive groups of about equal compile weight."""
    w = [0.25 * len(engine.lean_term(t)) + cost(steps[id(t)][3]) for t in parts]
    tot = sum(w)
    groups, cur, acc = [], [], 0.0
    for t, x in zip(parts, w):
        cur.append(t)
        acc += x
        if acc >= tot * (len(groups) + 1) / k and len(groups) < k - 1:
            groups.append(cur)
            cur = []
    groups.append(cur)
    return [g for g in groups if g]


def two(outdir, cert):
    lines = engine.read_lines(cert)
    sha = hashlib.sha256(''.join(lines).encode()).hexdigest()
    nrec = len(lines)
    P, term, steps, primes = run(cert)
    parts = select(term, steps)
    top = cut(term, {id(t) for t in parts})
    kinds = count(term, {})
    orc, n = oracle_lean(primes, 'Two')
    groups = pack(parts, steps, K)
    od = os.path.join(outdir, '')
    open(od + 'TwoExceptionTwoPrimes.lean', 'w').write(f"""import OddPerfect.TwoExcEngineCheck

/-!
# The two exception certificate: parameters and primality oracle

Generated by `gen_two.py` from `cert_v5_e2_100000.jsonl` (sha256 `{sha}`).
This module gives the checker parameters of the certificate header, the statement `RefutedTwo`
that a state holds for no `N` and `q`, and the primality oracle `prTwo` with its soundness
theorem. The checker asks the oracle about {len(primes)} primes; the
{sum(p < 4096 for p in primes)} below 4096 are covered by the verified table `primeB`, the
others by one flat Pratt certificate of {n} entries and a search tree over its primes.
-/

open OddPerfect.TwoExcEngine

{HDR}
namespace OddPerfect

namespace TwoExceptionTwo

/-- The parameters of the certificate header: two exceptions, enumeration limit `10 ^ 30`,
exponent cap 64, landed facts used. -/
def paramsTwo : Params := {engine.lean_params(P)}

/-- The state with keys `ks` and scan position `x` holds for no `N` and `q`. -/
def RefutedTwo (ks : List Key) (x : ℕ) : Prop := ∀ N q, Holds paramsTwo N q ks x → False

{orc}
end TwoExceptionTwo

end OddPerfect

#print axioms OddPerfect.TwoExceptionTwo.prattTwo_ok
#print axioms OddPerfect.TwoExceptionTwo.treeTwo_toList
#print axioms OddPerfect.TwoExceptionTwo.prTwo_sound
""")
    j = 0
    for g, grp in enumerate(groups):
        k = g + 1
        body, names = [], []
        recs = sum(steps[id(t)][3].get('rec', 0) for t in grp)
        gens = sum(steps[id(t)][3].get('gen', 0) for t in grp)
        for t in grp:
            j += 1
            st = steps[id(t)][1][0]
            ctx = '(.step keysTwo_%d %d)' % (j, st['x'])
            names.append((j, st['x']))
            body.append(f"""def keysTwo_{j} : List Key := {engine.lean_keys(st['keys'])}

def certTwo_{j} : Cert := {engine.lean_term(t)}

private theorem certTwo_{j}_ok : go paramsTwo prTwo (fun _ _ => false) {ctx} certTwo_{j} = true := by
  decide +kernel

private theorem refuteTwo_{j} : RefutedTwo keysTwo_{j} {st['x']} := fun N q h =>
  go_sound (P := paramsTwo) (N := N) (q := q) (defSound paramsTwo) prTwo_sound
    (fun _ _ hd _ => Bool.false_ne_true hd) (fun _ => by decide) certTwo_{j} {ctx}
    certTwo_{j}_ok h
""")
        rl = ',\n    '.join('(keysTwo_%d, %d)' % (i, x) for i, x in names)
        pats = ' | '.join('rfl' for _ in names)
        exs = ', '.join('refuteTwo_%d' % i for i, _ in names)
        sep = '\n'
        open(od + 'TwoExceptionTwoData%d.lean' % k, 'w').write(f"""import OddPerfect.TwoExceptionTwoPrimes
import OddPerfect.TwoExcEngineTail

/-!
# The two exception certificate, part {k} of {len(groups)}

Generated by `gen_two.py` from `cert_v5_e2_100000.jsonl`. This part holds {len(grp)} subtrees of
the certificate, each below one step ({recs} records and {gens} generated values in deficient
leaves in all). Each subtree is accepted by the checker, checked by one kernel evaluation, so by
`go_sound`, `defSound` and the soundness of the oracle its root state holds for no `N` and `q`.
The list `rootsTwo{k}` collects these root states; the top of the tree reaches each of them
through `ext`.
-/

open OddPerfect.TwoExcEngine

{HDR}
namespace OddPerfect

namespace TwoExceptionTwo

{sep.join(body)}
/-- The root states of the subtrees of part {k}. -/
def rootsTwo{k} : List (List Key × ℕ) := [
    {rl}]

/-- No root state of part {k} holds. -/
theorem rootsTwo{k}_refuted : ∀ r ∈ rootsTwo{k}, RefutedTwo r.1 r.2 := by
  intro r hr
  simp only [rootsTwo{k}, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with {pats}
  exacts [{exs}]

end TwoExceptionTwo

end OddPerfect

#print axioms OddPerfect.TwoExceptionTwo.rootsTwo{k}_refuted
""")
    K2 = len(groups)
    imports = '\n'.join('import OddPerfect.TwoExceptionTwoData%d' % k for k in range(1, K2 + 1))
    app = 'rootsTwo%d' % K2
    for k in range(K2 - 1, 0, -1):
        app = 'rootsTwo%d ++ (%s)' % (k, app) if k < K2 - 1 else 'rootsTwo%d ++ %s' % (k, app)
    steps_top = ''.join('  rcases List.mem_append.mp hr with h | hr\n  · exact rootsTwo%d_refuted r h\n' % k
                        for k in range(1, K2))
    steps_top += '  exact rootsTwo%d_refuted r hr' % K2
    leaves = ', '.join('%d %s' % (kinds.get(key, 0), name) for key, name in [
        ('leaf', 'contradiction leaves'), ('abundant', 'abundant leaves'),
        ('landedL', 'rule L leaves'), ('check', 'deficient leaves')])
    inner = ', '.join('%d %s' % (kinds.get(key, 0), name) for key, name in [
        ('force', 'forced nodes'), ('receipt', 'receipt nodes'), ('snd', 'sender nodes'),
        ('inf', 'infeasible sender leaves'), ('closed', 'closed nodes'),
        ('decide', 'decide nodes'), ('split', 'exponent splits')])
    open(od + 'TwoExceptionTwo.lean', 'w').write(f"""{imports}
import OddPerfect.TwoExceptionFourEmpty

/-!
# Two exceptional primes: the exponent of 3 is not 2

Let `N` be an odd perfect number with special prime `q` in which every prime factor other than
`q`, `r₁` and `r₂` has exponent exactly 2. This module proves `N.factorization 3 ≠ 2`
(`two_exceptions_three_ne_two`) and, with `three_dvd_of_two_exceptions` and
`two_exceptions_three_ne_four`, that the exponent of 3 in such an `N` is at least 6
(`two_exceptions_six_le_three`). This concerns only this restricted family, not odd perfect
numbers in general. Whether these statements are new was not verified against the literature.

## The proof

The proof is a kernel checked certificate for the checker of `OddPerfect.TwoExcEngine`, a tool
whose soundness theorem `check_sound` is proved in `TwoExcEngineCheck` and `TwoExcEngineTail`
(`defSound`). The certificate `cert_v5_e2_100000.jsonl` (sha256
`{sha}`, {nrec} lines) is the output of an exact
search; its header fixes two exceptions, the enumeration limit `10 ^ 30`, the exponent cap 64
and the use of the landed facts. As a checker term it has {kinds.get('apply', 0)} records,
{leaves}, and {inner}. The term is checked in {len(parts) + 1} kernel evaluations: {len(parts)}
subtrees in `TwoExceptionTwoData1` to `TwoExceptionTwoData{K2}` and the top below, which reaches
each subtree through `ext`; `doneTwo` recognizes exactly the root states of these subtrees.
Primality enters only through the verified oracle `prTwo`.

## Landed theorems used

* In the role rule of the checker (`roles_exh` in `TwoExcEngineCheck`): the facts on the
  special prime under two exceptions, `two_exceptions_five_three_ne_two`,
  `two_exceptions_three_ne_two_of_nine_dvd` and `two_exceptions_three_ne_two_of_mod_nine`.
* Rule L: `false_of_three_sq_of_index_three`.
* The tail bound of the deficient leaves, through `defSound` and `RankinTailGeneral`.
* For the corollary: `three_dvd_of_two_exceptions`, `two_exceptions_three_ne_four`,
  `special_mod_four` and `even_factorization_of_ne`.
-/

open OddPerfect.TwoExcEngine

{HDR}
namespace OddPerfect

namespace TwoExceptionTwo

/-- The root states of all subtrees. -/
def rootsTwo : List (List Key × ℕ) := {app}

theorem rootsTwo_refuted : ∀ r ∈ rootsTwo, RefutedTwo r.1 r.2 := by
  intro r hr
  unfold rootsTwo at hr
{steps_top}

/-- Recognizes exactly the root states of the subtrees. -/
def doneTwo (ks : List Key) (x : ℕ) : Bool := rootsTwo.any fun r => r.2 == x && r.1 == ks

theorem doneTwo_sound : ∀ ks x N q, doneTwo ks x = true → Holds paramsTwo N q ks x → False := by
  intro ks x N q h hH
  obtain ⟨r, hr, hb⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨h1, h2⟩ := hb
  subst h1 h2
  exact rootsTwo_refuted r hr N q hH

/-- The top of the certificate, with `ext` at the roots of the subtrees. -/
def certTwo : Cert := {engine.lean_term(top)}

private theorem certTwo_ok : check paramsTwo prTwo doneTwo certTwo = true := by decide +kernel

end TwoExceptionTwo

open TwoExceptionTwo

/-- Let `N` be an odd perfect number with special prime `q` in which every prime factor other
than `q`, `r₁` and `r₂` has exponent exactly 2 (a restricted family with two exceptional
exponents). Then the exponent of 3 in `N` is not 2. This concerns only this restricted family,
not odd perfect numbers in general. Whether this statement is new was not verified against the
literature. -/
theorem two_exceptions_three_ne_two {{N q r₁ r₂ : ℕ}} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    N.factorization 3 ≠ 2 := fun h3 =>
  check_sound (defSound paramsTwo) prTwo_sound doneTwo_sound (fun _ => by decide) certTwo_ok
    (fam_two h hq hodd h3 hsq)

/-- In the same family the exponent of 3 is at least 6. The prime 3 divides `N`
(`three_dvd_of_two_exceptions`) and is not the special prime (that one is 1 modulo 4), so its
exponent is even and positive, and it is neither 2 (`two_exceptions_three_ne_two`) nor 4
(`two_exceptions_three_ne_four`). -/
theorem two_exceptions_six_le_three {{N q r₁ r₂ : ℕ}} (h : OddPerfect N) (hq : q.Prime)
    (hodd : Odd (N.factorization q))
    (hsq : ∀ p ∈ N.primeFactors, p ≠ q → p ≠ r₁ → p ≠ r₂ → N.factorization p = 2) :
    6 ≤ N.factorization 3 := by
  have h3 := three_dvd_of_two_exceptions h hq hodd hsq
  have hq3 : (3 : ℕ) ≠ q := by
    rintro rfl
    have := (special_mod_four h hq hodd).1
    omega
  obtain ⟨j, hj⟩ := even_factorization_of_ne h hq hodd Nat.prime_three hq3
  have h1 := (Nat.prime_three.dvd_iff_one_le_factorization h.ne_zero).mp h3
  have h2 := two_exceptions_three_ne_two h hq hodd hsq
  have h4 := two_exceptions_three_ne_four h hq hodd hsq
  omega

end OddPerfect

#print axioms OddPerfect.TwoExceptionTwo.rootsTwo_refuted
#print axioms OddPerfect.TwoExceptionTwo.doneTwo_sound
#print axioms OddPerfect.two_exceptions_three_ne_two
#print axioms OddPerfect.two_exceptions_six_le_three
""")
    print('sha256', sha, 'lines', nrec, 'subtrees', len(parts), 'files', K2, 'pratt', n, 'kinds', kinds)


if __name__ == '__main__':
    status = []
    th = threading.Thread(target=lambda: status.append(main()))
    th.start()
    th.join()
    sys.exit(status[0] if status else 1)
