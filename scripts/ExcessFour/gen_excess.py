"""Untrusted helper script for the OddPerfect Lean library.

Generator of the three Lean modules of the fixed exponent certificates: writes
ExcessFourS1.lean, ExcessFourS2a.lean and ExcessFourS2b.lean, which hold every literal behind
excessS1, excessS2a and excessS2b (checked by `TwoExcEngine.checkV`, whose soundness theorem
`checkV_sound` is proved in OddPerfect/TwoExcEngineCheck.lean and TwoExcEngineTail.lean).

Run (any folder):
  python3 -I gen_excess.py OUTDIR CERT_S1 CERT_S2a CERT_S2b
writes the three modules into the existing folder OUTDIR. The certificates are the outputs of the
exact search for the three families (one JSON record per line, a header with the fields FAM and
V3); the modules name each certificate by its file name, and these are the certificates used:
  cert_ex_S1_100000_nojump_nolanded.jsonl   sha256 162b09f35a59f3ec665ea177aad7d4b0f7c542388be8cb135831ee0fa56c967f
  cert_ex_S2a_100000_nojump_nolanded.jsonl  sha256 ddd47311c212c627096df16af4b99d9ff29ad812f917f6171469c0ebb6056b43
  cert_ex_S2b_100000_nolanded_ruleL.jsonl   sha256 12fd8d079b8bbfe3bc42ac877bbfe33bb911d6016333ec22cf6fe0257802b4c2
Each certificate is translated to a term (engine.Translator, with the factor lists of the records
sorted) and run once in the Python mirror of the Lean checker (engine.checkV), which must accept
it and gives the primes the checker asks the oracle about. Oracle primes below 4096 are handled by
the verified table (primeB); the others, with the primes of their Pratt certificates above 100,
go into one flat Pratt certificate sorted by size and a balanced search tree (gen.oracle_lean).
Each term is small enough for one kernel evaluation, so each module holds the whole term.
Helpers: engine.py and gen.py of scripts/TwoExceptionTwo, looked up next to this script and in
../TwoExceptionTwo.
Requires: Python 3 and sympy (through gen.py, for the Pratt certificates; checked with sympy
1.14.0). Running time: a few seconds, one process.
Deterministic: the output depends only on the certificates.
Untrusted: every module is checked by the Lean kernel.
License: GPL 3, same as the repository.
"""
import sys, os, threading, hashlib
sys.setrecursionlimit(1000000)
threading.stack_size(512 * 1024 * 1024)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'TwoExceptionTwo'))
sys.path.insert(0, HERE)
import engine
import gen

FAMS = ['S1', 'S2a', 'S2b']

# What each family excludes, for the module docstrings.
WHAT = {
    'S1': ('exponent 6 at 3, at most one further prime `r` of exponent 4, every other prime '
           'factor except `q` of exponent 2'),
    'S2a': ('exponent 4 at 3, at most two further primes `r₁`, `r₂` of exponent 4, every other '
            'prime factor except `q` of exponent 2'),
    'S2b': ('exponent 2 at 3, at most three primes `r₁`, `r₂`, `r₃` of exponent 4, every other '
            'prime factor except `q` of exponent 2'),
}
NOVELTY = {
    'S1': ('In this family the special exponent `a` satisfies `Ω(N) - 2 * ω(N) ≤ a + 4`, so for '
           '`a ≤ 45` this exclusion also follows from the published inequality '
           '`Ω(N) ≥ 2 * ω(N) + 51` of Ochem and Rao (Math. Comp. 83, 2014). Whether the case of '
           'a larger special exponent is new has not been verified against the literature.'),
    'S2a': ('Every index in this family is 3 or 5 and 3 divides N, so this exclusion also follows '
            'from the published theorem of Fletcher, Nielsen and Ochem (Math. Comp. 81, 2012); '
            'it is proved here independently by a kernel checked certificate.'),
}
NOVELTY['S2b'] = NOVELTY['S2a']
# The binders of each statement and the arguments of its bridge.
INTRO = {'S1': 'N q r', 'S2a': 'N q r₁ r₂', 'S2b': 'N q r₁ r₂ r₃'}
HYPS = {'S1': 'hr', 'S2a': 'hr₁ hr₂', 'S2b': 'hr₁ hr₂ hr₃'}
HE = {'S1': 2, 'S2a': 3, 'S2b': 3}


def wrap(s, width=96):
    """Breaks a paragraph into lines of at most width characters."""
    out, cur = [], ''
    for w in s.split():
        if cur and len(cur) + 1 + len(w) > width:
            out.append(cur)
            cur = w
        else:
            cur = w if not cur else cur + ' ' + w
    out.append(cur)
    return '\n'.join(out)


def module(fam, cert):
    lines = engine.read_lines(cert)
    sha = hashlib.sha256(''.join(lines).encode()).hexdigest()
    recs = engine.load(cert)
    hdr = recs[0]
    if hdr.get('FAM') != fam:
        raise SystemExit('%s: header family %r, expected %s' % (cert, hdr.get('FAM'), fam))
    engine.ORACLE.clear()
    engine.COUNT.clear()
    term = engine.Translator(recs).root()
    P = engine.params(hdr)
    M = engine.Mirror(P)
    if engine.checkV(P, M, term) is not True:
        raise SystemExit('the mirror rejects %s' % cert)
    primes = sorted(engine.ORACLE)
    orc, n = gen.oracle_lean(primes, fam)
    kinds = gen.count(term, {})
    name = os.path.basename(cert)
    def listing(rows):
        return ', '.join('%d %s' % (kinds[key], one if kinds[key] == 1 else many)
                         for key, one, many in rows if kinds.get(key, 0))
    leaves = listing([('leaf', 'contradiction leaf', 'contradiction leaves'),
                      ('abundant', 'abundant leaf', 'abundant leaves'),
                      ('check', 'deficient leaf', 'deficient leaves')])
    inner = listing([('force', 'forced node', 'forced nodes'),
                     ('receipt', 'receipt node', 'receipt nodes'),
                     ('snd', 'sender node', 'sender nodes'),
                     ('inf', 'infeasible sender leaf', 'infeasible sender leaves'),
                     ('closed', 'closed node', 'closed nodes'),
                     ('decide', 'decide node', 'decide nodes'),
                     ('split', 'exponent split', 'exponent splits')])
    for k in kinds:
        if k not in ('apply', 'leaf', 'abundant', 'check', 'force', 'receipt', 'snd', 'inf',
                     'closed', 'decide', 'split'):
            raise SystemExit('%s: unexpected node kind %s' % (cert, k))
    e3 = 'the prime 3 is a key of exact exponent %d and counts as one of them' % P['V3'] \
        if P['V3'] != 2 else 'the prime 3 is a square key'
    para1 = ('Let `N` be an odd perfect number with special prime `q` and ' + WHAT[fam] + '. '
             'This module proves that no such `N` exists (`excess%s : Excess%s`, the statement of '
             '`ExcessFourReduction`). This concerns only this restricted family, not odd perfect '
             'numbers in general. ' % (fam, fam) + NOVELTY[fam])
    para2 = ('The proof is a kernel checked certificate for the checker `checkV` of '
             '`OddPerfect.TwoExcEngine`, a tool whose soundness theorem `checkV_sound` is proved in '
             '`TwoExcEngineCheck` and `TwoExcEngineTail` (`defSound`). The certificate `%s` '
             '(sha256 `%s`, %d lines) is the output of an exact search. The checker parameters '
             'allow %d exceptional primes (%s), every exception other than 3 of exponent exactly '
             '4, and do not use the landed facts. As a checker term it has %d records, %s, and '
             '%s. The term is checked in one kernel evaluation; primality enters only through '
             'the verified oracle `pr%s`, which the checker asks about %d primes (%d below 4096, '
             'covered by the verified table `primeB`; the others by one flat Pratt certificate of '
             '%d entries and a search tree over its primes). The bridge `famV_%s` turns the '
             'hypotheses of `Excess%s` into the family of the parameters.') % (
        name, sha, len(lines), P['E'], e3, kinds.get('apply', 0), leaves, inner, fam,
        len(primes), sum(p < 4096 for p in primes), n, fam, fam)
    para3 = ('Landed theorems used: the tail bound of the deficient leaves, through `defSound` '
             'and `RankinTailGeneral`; nothing else beyond the engine.')
    thdoc = wrap('/-- Exclusion %s: no odd perfect number with special prime `q` has %s. This '
                 'concerns only this restricted family, not odd perfect numbers in general. -/' % (
                     fam, WHAT[fam]))
    text = f"""import OddPerfect.ExcessFourReduction
import OddPerfect.TwoExcEngineTail

/-!
# Total excess at least 4: exclusion {fam}

{wrap(para1)}

## The proof

{wrap(para2)}

Generated by `gen_excess.py` from `{name}`.

{wrap(para3)}
-/

open OddPerfect.TwoExcEngine

{gen.HDR}
namespace OddPerfect

namespace ExcessFour{fam}

/-- The parameters of the certificate header. -/
def params{fam} : Params := {engine.lean_params(P)}

{orc}
/-- The certificate as a checker term. -/
def cert{fam} : Cert := {engine.lean_term(term)}

private theorem cert{fam}_ok : checkV params{fam} pr{fam} (fun _ _ => false) cert{fam} = true := by
  decide +kernel

end ExcessFour{fam}

open ExcessFour{fam}

{thdoc}
theorem excess{fam} : Excess{fam} := by
  intro {INTRO[fam]} h hq hodd h3 {HYPS[fam]} hsq
  exact checkV_sound (defSound params{fam}) pr{fam}_sound (fun _ _ _ _ hd _ => Bool.false_ne_true hd)
    (fun hl => absurd hl (by decide)) cert{fam}_ok
    (famV_{fam} (P := params{fam}) rfl (by decide) h hq hodd h3 {HYPS[fam]} hsq)

end OddPerfect

#print axioms OddPerfect.ExcessFour{fam}.pratt{fam}_ok
#print axioms OddPerfect.ExcessFour{fam}.tree{fam}_toList
#print axioms OddPerfect.ExcessFour{fam}.pr{fam}_sound
#print axioms OddPerfect.excess{fam}
"""
    print('%s sha256 %s lines %d records %d oracle %d pratt %d kinds %s' % (
        fam, sha, len(lines), kinds.get('apply', 0), len(primes), n, kinds))
    return text


def main():
    a = sys.argv[1:]
    if len(a) != 4 or not os.path.isdir(a[0]):
        print('usage: python3 -I gen_excess.py OUTDIR CERT_S1 CERT_S2a CERT_S2b')
        return 2
    for fam, cert in zip(FAMS, a[1:]):
        open(os.path.join(a[0], 'ExcessFour%s.lean' % fam), 'w').write(module(fam, cert))
    return 0


if __name__ == '__main__':
    status = []
    th = threading.Thread(target=lambda: status.append(main()))
    th.start()
    th.join()
    sys.exit(status[0] if status else 1)
