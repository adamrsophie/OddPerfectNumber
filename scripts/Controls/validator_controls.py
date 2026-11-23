#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Permanent controls for the published validators EqualExponentChain/checker.py,
# LowerBound/check.py, CommonFamilies/verify.py and CommonFamilies/est.py, and for the helpers
# under ThreeFreeThree/ (check3.py, verify3.py, gen_lean.py, route3.py), SecondLargestPrimeFast/
# (validate.py, knuth.py, reach.py, mkfast.py), LedgerThreeFree/check.py, MixedIndex/verify.py,
# MixedIndexThree/ (verify3.py, cert3.py), the process count argument of
# LargestPrimeFactor/gen6.py, and Controls/ (source_scan.py, replay.sh, contribution_scan.py):
# every archived valid
# input must pass with exit status 0, and each mutated input must be rejected with the expected
# nonzero status (1: a well formed input fails a check; 2: malformed input or usage), with no
# Python traceback. The validators run as subprocesses with `sys.executable -I -B`, in normal and
# in optimized (-O) mode, so a check written as an `assert` would show up as a failure.
# Mutated inputs are built from the archived certificates in a temporary folder; nothing is
# written inside the repository.
# Run: python3 -I scripts/Controls/validator_controls.py [--stdlib-only]
# With --stdlib-only the controls that need sympy (CommonFamilies/verify.py, LedgerThreeFree,
# MixedIndex and MixedIndexThree) are skipped (each is listed as SKIP); without it a missing sympy
# is a failure. The controls of replay.sh run it with a stand in for lake on PATH, so they need
# neither the toolchain nor a build; they need sh and a python3 on PATH with tomllib (3.11 or
# later), which the source scan imports.
# Requires: Python 3.11 or later (tomllib, for the source scan controls), sympy for the controls
# named above. Running time: about two minutes.
# Exit status: 0 when every control behaves as expected, 1 otherwise, 2 for a usage error.
# License: GPL 3, same as the repository.

import ast
import importlib.util
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SC = os.path.join(ROOT, 'scripts')
CHECKER = os.path.join(SC, 'EqualExponentChain', 'checker.py')
LBCHECK = os.path.join(SC, 'LowerBound', 'check.py')
VERIFY = os.path.join(SC, 'CommonFamilies', 'verify.py')
EST = os.path.join(SC, 'CommonFamilies', 'est.py')
TF = os.path.join(SC, 'ThreeFreeThree')
SLP = os.path.join(SC, 'SecondLargestPrimeFast')
SLP_VALIDATE = os.path.join(SLP, 'validate.py')
LEDGER = os.path.join(SC, 'LedgerThreeFree', 'check.py')
MIX = os.path.join(SC, 'MixedIndex')
MIX_VERIFY = os.path.join(MIX, 'verify.py')
MIX3 = os.path.join(SC, 'MixedIndexThree')
MIX3_VERIFY = os.path.join(MIX3, 'verify3.py')
MIX3_CERT = os.path.join(MIX3, 'cert3.py')
GEN6 = os.path.join(SC, 'LargestPrimeFactor', 'gen6.py')
SCAN = os.path.join(SC, 'Controls', 'source_scan.py')
REPLAY = os.path.join(SC, 'Controls', 'replay.sh')
CONTRIB_SCAN = os.path.join(SC, 'Controls', 'contribution_scan.py')
TWO = os.path.join(SC, 'TwoExceptionTwo')
TWO_ENGINE = os.path.join(TWO, 'engine.py')
TF_CERT = os.path.join(TF, 'cert3_final.json.xz')
EQ_CERTS = sorted(os.path.join(SC, f, 'certs', n) for f in ('EqualExponentChain', 'EqualExponentChainMore')
                  for n in os.listdir(os.path.join(SC, f, 'certs')) if n.endswith('.json'))
CF57 = os.path.join(SC, 'CommonFamilies', 'certs', 'cert_d5_7.json')
CF65 = os.path.join(SC, 'CommonFamilies', 'certs', 'cert_d65.json')
LB_LEAN = os.path.join(ROOT, 'OddPerfect', 'LowerBound.lean')
LB_TREES = ['79', '3:', '5:3', '7:3,5']
CLAIM57 = {'d': 5, 'seeds': [5, 7], 'special_test': [12, 1], 'excluded_primes': [], 'exponents': {}}
CLAIM65 = {'d': 65, 'seeds': [5, 13], 'special_test': [12, 1], 'excluded_primes': [], 'exponents': {}}

results = {'PASS': 0, 'FAIL': 0, 'SKIP': 0}


def report(verdict, name, detail=''):
    results[verdict] += 1
    print(f'{verdict} {name}' + (f': {detail}' if detail else ''), flush=True)


def control(name, script, args, want, modes=('', '-O'), cwd=None, timeout=60, expect=None):
    """Runs the script in each mode and requires exit status `want`, no traceback, and the
    line fragment `expect` (if given) in its output."""
    for mode in modes:
        # -B: no __pycache__ folders next to the scripts that the validators import
        cmd = [sys.executable, '-I', '-B'] + ([mode] if mode else []) + [script] + args
        label = f'{name} [{"python -O" if mode else "python"}]'
        try:
            p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            report('FAIL', label, f'no result within {timeout} s')
            continue
        if 'Traceback' in p.stderr:
            report('FAIL', label, 'traceback: ' + p.stderr.strip().splitlines()[-1])
        elif p.returncode != want:
            report('FAIL', label, f'exit status {p.returncode}, expected {want}')
        elif expect is not None and expect not in p.stdout + p.stderr:
            report('FAIL', label, f'no line with {expect!r}')
        else:
            report('PASS', label, f'exit status {want}')


def skip(name):
    for mode in ('python', 'python -O'):
        report('SKIP', f'{name} [{mode}]', 'sympy controls skipped (--stdlib-only)')


def write_json(path, obj):
    with open(path, 'w') as f:
        json.dump(obj, f)
    return path


def load(path):
    with open(path) as f:
        return json.load(f)


def mutate_text(src, dst, old, new):
    with open(src) as f:
        text = f.read()
    if text.count(old) != 1:
        raise SystemExit(f'control setup: {old!r} does not occur exactly once in {src}')
    with open(dst, 'w') as f:
        f.write(text.replace(old, new))
    return dst


def no_asserts():
    """The validators and this script must not rely on `assert`, which python -O removes."""
    for path in (CHECKER, LBCHECK, VERIFY, EST, SLP_VALIDATE, LEDGER, MIX_VERIFY, MIX3_VERIFY, TWO_ENGINE,
                 os.path.abspath(__file__)):
        with open(path) as f:
            tree = ast.parse(f.read(), path)
        lines = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Assert)]
        rel = os.path.relpath(path, ROOT)
        if lines:
            report('FAIL', f'no assert in {rel}', f'assert at lines {lines}')
        else:
            report('PASS', f'no assert in {rel}')


def equal_exponent_chain(t):
    control('checker.py accepts the archived certificates', CHECKER, EQ_CERTS, 0)
    c5 = load(os.path.join(SC, 'EqualExponentChain', 'certs', 'cert_5.json'))
    bad = dict(c5, spec=['bogus'])
    control('checker.py: unknown node tag', CHECKER, [write_json(f'{t}/eq_tag.json', bad)], 2)
    c31 = load(os.path.join(SC, 'EqualExponentChainMore', 'certs', 'cert_31.json'))
    if c31['spec'] != ['mod4']:
        raise SystemExit('control setup: cert_31.json no longer has the special part ["mod4"]')
    bad = dict(c31, spec=['mod4', 12345])
    control('checker.py: extra field on the nullary node mod4', CHECKER,
            [write_json(f'{t}/eq_mod4.json', bad)], 2)
    bad = dict(c5, spec=['mod4'])  # well formed, but the special prime 5 is 1 (mod 4)
    control('checker.py: well formed certificate that is rejected', CHECKER,
            [write_json(f'{t}/eq_reject.json', bad)], 1)
    with open(f'{t}/eq_trunc.json', 'w') as f:
        f.write('{"l": 5, "pratt": [')
    control('checker.py: unreadable JSON', CHECKER, [f'{t}/eq_trunc.json'], 2)
    control('checker.py: no certificate given', CHECKER, [], 2)


def lower_bound(t):
    control('check.py accepts the table and the trees of LowerBound.lean', LBCHECK, [LB_LEAN] + LB_TREES, 0)
    split = mutate_text(LB_LEAN, f'{t}/lb_split.lean', '.rs 3 1 167,', '.rs 3 1 163,')
    control('check.py: changed split instruction in tree 3', LBCHECK, [split] + LB_TREES, 1)
    table = mutate_text(LB_LEAN, f'{t}/lb_table.lean', 'PT.leaf 3 2 [(2, 1)]', 'PT.leaf 3 1 [(2, 1)]')
    control('check.py: wrong witness in the prime table', LBCHECK, [table, '79', '3:'], 1)
    control('check.py: no tree requested', LBCHECK, [LB_LEAN, '79'], 2)
    control('check.py: requested tree absent from the file', LBCHECK, [LB_LEAN, '79', '11:'], 2)


def common_families(t, stdlib_only):
    names = ['verify.py accepts the archived certificates', 'verify.py --expect, d = 5 certificate',
             'verify.py --expect, d = 65 certificate', 'verify.py --expect: claim differs',
             'verify.py: deficient singleton 781/625', 'verify.py: conflicting duplicate case',
             'verify.py: missing case', 'verify.py: extra case', 'verify.py: empty residue profile (1, 1)',
             'verify.py: excluded prime 1 (empty profile)', 'verify.py: duplicate row', 'verify.py: seed 0',
             'verify.py --expect: a repeated seed is the same claim']
    if stdlib_only:
        for n in names:
            skip(n)
        return
    if importlib.util.find_spec('sympy') is None:
        report('FAIL', 'verify.py controls', 'sympy is not installed (use --stdlib-only to skip them)')
        return
    control(names[0], VERIFY, [CF57, CF65], 0)
    control(names[1], VERIFY, ['--expect', json.dumps(CLAIM57), CF57], 0)
    control(names[2], VERIFY, ['--expect', json.dumps(CLAIM65), CF65], 0)
    control(names[3], VERIFY, ['--expect', json.dumps(CLAIM57), CF65], 1)
    tiny = {'d': 5, 'seeds': [5], 'special_test': [12, 1], 'exponent': 4, 'rows': [], 'targets': [5],
            'cases': [{'q': 'none', 'sigma_over_D': '781/625'}]}
    control(names[4], VERIFY, [write_json(f'{t}/cf_deficient.json', tiny)], 1)
    c = load(CF57)
    bad = dict(c, cases=[{'q': 'none', 'sigma_over_D': '1/1'}] + c['cases'])
    control(names[5], VERIFY, [write_json(f'{t}/cf_dup.json', bad)], 2)
    bad = dict(c, cases=c['cases'][:-1])
    control(names[6], VERIFY, [write_json(f'{t}/cf_missing.json', bad)], 1)
    bad = dict(c, cases=c['cases'] + [{'q': 5, 'sigma_over_D': '3'}])
    control(names[7], VERIFY, [write_json(f'{t}/cf_extra.json', bad)], 1)
    bad = dict(c, special_test=[1, 1], cases=[x for x in c['cases'] if x['q'] == 'none'])
    control(names[8], VERIFY, [write_json(f'{t}/cf_empty.json', bad)], 2)
    bad = dict(c, excluded_primes=[1], cases=[x for x in c['cases'] if x['q'] == 'none'])
    control(names[9], VERIFY, [write_json(f'{t}/cf_excl1.json', bad)], 2)
    bad = dict(c, rows=c['rows'] + [c['rows'][0]])
    control(names[10], VERIFY, [write_json(f'{t}/cf_duprow.json', bad)], 2)
    bad = dict(c, seeds=[0] + c['seeds'])
    control(names[11], VERIFY, [write_json(f'{t}/cf_seed0.json', bad)], 2)
    control(names[12], VERIFY, ['--expect', json.dumps(dict(CLAIM57, seeds=[5, 7, 5])), CF57], 0)


def estimator(t):
    d57 = f'{t}/est57'
    os.mkdir(d57)
    with open(os.path.join(ROOT, 'OddPerfect', 'CommonFiveSeven.lean')) as f, open(f'{d57}/57.lean.txt', 'w') as g:
        g.write(f.read())
    write_json(f'{d57}/57.meta.json', {})
    control('est.py runs on the d = 5 table of CommonFiveSeven.lean', EST, ['57', '5'], 0, cwd=d57)
    dx = f'{t}/estX'
    os.mkdir(dx)
    with open(f'{dx}/X.lean.txt', 'w') as f:
        f.write('def nodesX : List ℕ :=\n  [5, 19, 13]\n\ndef rowsX : List (List ℕ) :=\n  [[], [], []]\n\n'
                'def valsX : List ℕ :=\n  [5, 19, 13]\n\ndef tmX : ℕ :=\n  4\n')
    write_json(f'{dx}/X.meta.json', {})
    control('est.py: unreachable target (fixed point)', EST, ['X', '5'], 1, cwd=dx, timeout=20)
    if os.path.exists(f'{dx}/X.est.json'):
        report('FAIL', 'est.py: unreachable target writes no estimate file', 'X.est.json was written')
    else:
        report('PASS', 'est.py: unreachable target writes no estimate file')


def tf_leaves(node):
    if 'leaf' in node:
        yield node['leaf']
    else:
        for kid in node['children']:
            yield from tf_leaves(kid)


def tf_forge(t, name, change):
    """A copy of the three exception certificate with one change applied to it."""
    import lzma
    with lzma.open(TF_CERT) as f:
        doc = json.loads(f.read())
    change([leaf for tr in doc['triples'] for leaf in tf_leaves(tr['tree']) if leaf['status'] == 'closed'])
    return write_json(f'{t}/{name}.json', doc)


def three_free_three(t):
    """check3.py must reject malformed leaves, and the helpers must report failures by exit status."""
    def tf(name):
        return os.path.join(TF, name)

    def fifth_weight(leaves):
        leaves[0]['weights'].append([0, 1])

    def negative_witness(leaves):
        x = next(x for leaf in leaves for x in leaf['witnesses'] if x['kind'] == 'small')
        x['s'] = -(x['s'] + 1)

    def three_slots(leaves):
        leaves[0]['slots'].pop()

    def bound_lowered(leaves):
        leaves[0]['bound'][0] -= 1

    def small_primes_dropped(leaves):
        for leaf in leaves:
            if leaf['C']:
                leaf['C'].pop()

    control('check3.py accepts the published certificate', tf('check3.py'), [TF_CERT], 0)
    control('check3.py: fifth weight', tf('check3.py'), [tf_forge(t, 'w5', fifth_weight)], 1)
    control('check3.py: negative square witness', tf('check3.py'), [tf_forge(t, 'neg', negative_witness)], 1)
    control('check3.py: three slots', tf('check3.py'), [tf_forge(t, 'slots3', three_slots)], 1)
    control('verify3.py accepts the published certificate', tf('verify3.py'), [TF_CERT], 0, modes=('',))
    control('verify3.py --tamper: every tamper is rejected', tf('verify3.py'), [TF_CERT, '--tamper'], 0, modes=('',))
    blind = mutate_text(tf('verify3.py'), f'{t}/verify3_blind.py',
                        "            verify(c)\n            print('NOT REJECTED", "            print('NOT REJECTED")
    control('verify3.py --tamper: a verifier that accepts everything fails the run', blind, [TF_CERT, '--tamper'],
            1, modes=('',))
    control('gen_lean.py mirror agrees with the published certificate', tf('gen_lean.py'), [TF_CERT, 'mirror'],
            0, modes=('',))
    control('gen_lean.py mirror: stored bound lowered', tf('gen_lean.py'),
            [tf_forge(t, 'bound', bound_lowered), 'mirror'], 1, modes=('',))
    control('route3.py: published certificate', tf('route3.py'), [TF_CERT, '0', '1'], 0, modes=('',))
    control('route3.py: small prime sets shortened', tf('route3.py'),
            [tf_forge(t, 'cdrop', small_primes_dropped), '0', '1'], 1, modes=('',))
    out = f'{t}/tfdata'
    os.mkdir(out)
    control('gen_lean.py data runs', tf('gen_lean.py'), [TF_CERT, 'data', out], 0, modes=('',))
    names = sorted(n for n in os.listdir(out) if n.endswith('.lean'))
    differ = []
    for n in names:
        with open(os.path.join(out, n), 'rb') as f, open(os.path.join(ROOT, 'OddPerfect', n), 'rb') as g:
            if f.read() != g.read():
                differ.append(n)
    if len(names) == 12 and not differ:
        report('PASS', 'gen_lean.py data: 12 of 12 modules byte equal')
    else:
        report('FAIL', 'gen_lean.py data: modules byte equal', f'{len(names)} files written, differing: {differ}')


def second_largest_prime(t):
    """validate.py must reject an incomplete or altered chain of chunks; the search tools must
    report a search that did not close by their exit status."""
    def repo(name, old=None, new=None, module=9):
        d = os.path.join(t, name, 'OddPerfect')
        os.makedirs(d)
        for m in range(1, 10):
            n = f'SecondLargestPrimeFastData{m}.lean'
            src = os.path.join(ROOT, 'OddPerfect', n)
            if old is not None and m == module:
                mutate_text(src, os.path.join(d, n), old, new)
            else:
                with open(src) as f, open(os.path.join(d, n), 'w') as g:
                    g.write(f.read())
        return os.path.join(t, name)

    head = ' : runF 72 557940830126698960967415390 10 500 '
    control('validate.py accepts the published chunks', SLP_VALIDATE, [ROOT], 0)
    control('validate.py: last run with bound 73', SLP_VALIDATE,
            [repo('slp_bound', 'theorem run202' + head, 'theorem run202 : runF 73 557940830126698960967415390 10 500 ')], 1)
    control('validate.py: wrong modulus', SLP_VALIDATE,
            [repo('slp_mod', 'theorem run5' + head, 'theorem run5 : runF 72 557940830126698960967415391 10 500 ', 1)], 1)
    control('validate.py: last run renamed (unfinished prefix)', SLP_VALIDATE,
            [repo('slp_prefix', 'private theorem run202' + head, 'private theorem final' + head)], 1)
    control('validate.py: run renumbered', SLP_VALIDATE,
            [repo('slp_number', 'theorem run7' + head, 'theorem run9007' + head, 1)], 1)
    control('knuth.py: one probe', os.path.join(SLP, 'knuth.py'), ['60', '1'], 0, modes=('',))
    control('reach.py: node limit is not closure', os.path.join(SLP, 'reach.py'), ['72', '10001', '10', '500', '1000'],
            1, modes=('',))
    control('mkfast.py: zero fuel', os.path.join(SLP, 'mkfast.py'), ['72', '0', '10001', '9', f'{t}/mk0'], 2, modes=('',))
    control('mkfast.py: zero modules', os.path.join(SLP, 'mkfast.py'), ['72', '500', '10001', '0', f'{t}/mk1'], 2,
            modes=('',))
    # Argument checks that end the run before any search starts, so both modes are cheap.
    control('knuth.py: zero probes', os.path.join(SLP, 'knuth.py'), ['60', '0'], 2)
    control('knuth.py: no probe count', os.path.join(SLP, 'knuth.py'), ['60'], 2)
    control('reach.py: zero chunk size', os.path.join(SLP, 'reach.py'), ['72', '10001', '10', '0'], 2)
    control('reach.py: six arguments', os.path.join(SLP, 'reach.py'), ['72', '10001', '10', '500', '1000', '1'], 2)
    control('mkfast.py: lower bound above 10001', os.path.join(SLP, 'mkfast.py'),
            ['72', '500', '10002', '9', f'{t}/mk2'], 2)
    control('mkfast.py: no output folder', os.path.join(SLP, 'mkfast.py'), ['72', '500', '10001', '9'], 2)


def ledger_three_free(t, stdlib_only):
    """LedgerThreeFree/check.py must end with exit status 1 when a comparison of the proof fails."""
    names = ['check.py (LedgerThreeFree) accepts the published numbers', 'check.py: false envelope 19/10',
             'check.py: envelope 1995/1000, too loose for q0 = 229', 'check.py: nine large primes at q = 109',
             'check.py: wrong survivor']
    if stdlib_only:
        for n in names:
            skip(n)
        return
    if importlib.util.find_spec('sympy') is None:
        report('FAIL', 'LedgerThreeFree/check.py controls', 'sympy is not installed (use --stdlib-only to skip them)')
        return
    with open(LEDGER) as f:
        text = f.read()

    def mutant(name, old, new, count):
        if text.count(old) != count:
            raise SystemExit(f'control setup: {old!r} does not occur {count} times in {LEDGER}')
        with open(f'{t}/{name}.py', 'w') as f:
            f.write(text.replace(old, new))
        return f'{t}/{name}.py'

    control(names[0], LEDGER, [], 0)
    control(names[1], mutant('ledger_env', 'Fr(19901, 10000)', 'Fr(19, 10)', 3), [], 1)
    control(names[2], mutant('ledger_loose', 'Fr(19901, 10000)', 'Fr(1995, 1000)', 3), [], 1)
    control(names[3], mutant('ledger_big', 'Fr(661, 660) ** 2', 'Fr(661, 660) ** 9', 1), [], 1)
    control(names[4], mutant('ledger_surv', '491: 603791}, "survivor map")', '491: 603793}, "survivor map")', 1), [], 1)


def first_force(node):
    """The first branch (in key order, depth first) whose forced list has two primes."""
    for k in sorted(node.get('br', {})):
        c = node['br'][k]
        if len(c.get('force', [])) >= 2:
            return c
        if 'next' in c:
            found = first_force(c['next'])
            if found is not None:
                return found
    return None


def forced_variants(cert):
    """Copies of a certificate with its first forced prime made negative, a float, and composite."""
    out = []
    for tag, change in (('negative', lambda r: [-r[0]] + r[1:]), ('float', lambda r: [float(r[0])] + r[1:]),
                        ('composite', lambda r: [r[0] * r[1]] + r[2:])):
        doc = json.loads(json.dumps(cert))
        c = first_force(doc)
        if c is None:
            raise SystemExit('control setup: no forced list with two primes in the certificate')
        c['force'] = change(c['force'])
        out.append((tag, doc))
    return out


def mixed_index(t, stdlib_only):
    """MixedIndex/verify.py and MixedIndexThree/verify3.py must decide by explicit checks (python -O
    keeps them), reject a duplicated base component and malformed forced primes; cert3.py must
    report an unfinished search by its exit status."""
    names = ['verify.py (MixedIndex) accepts cert.json', 'verify.py (MixedIndex): empty abundance set at the root',
             'verify.py (MixedIndex): forced prime negative', 'verify.py (MixedIndex): forced prime float',
             'verify.py (MixedIndex): forced prime composite', 'verify.py (MixedIndex): no certificate given',
             'verify3.py (MixedIndexThree) accepts g1', 'verify3.py (MixedIndexThree) accepts g9',
             'verify3.py (MixedIndexThree): empty abundance set at the root',
             'verify3.py (MixedIndexThree): duplicated base component',
             'verify3.py (MixedIndexThree): forced prime negative', 'verify3.py (MixedIndexThree): forced prime float',
             'verify3.py (MixedIndexThree): forced prime composite', 'verify3.py (MixedIndexThree): no tag given',
             'cert3.py: node limit 0 is not closure']
    if stdlib_only:
        for n in names:
            skip(n)
        return
    if importlib.util.find_spec('sympy') is None:
        report('FAIL', 'MixedIndex controls', 'sympy is not installed (use --stdlib-only to skip them)')
        return
    # verify.py writes cert_primes.json into its working folder, cert3.py a factor cache.
    d1 = f'{t}/mix1'
    os.mkdir(d1)
    cert = load(os.path.join(MIX, 'cert.json'))
    empty = write_json(f'{d1}/empty.json', {'close': 'abund', 'set': []})
    control(names[0], MIX_VERIFY, [os.path.join(MIX, 'cert.json')], 0, cwd=d1, expect='ACCEPTED')
    control(names[1], MIX_VERIFY, [empty], 1, cwd=d1, expect='not abundant')
    for i, (tag, doc) in enumerate(forced_variants(cert)):
        control(names[2 + i], MIX_VERIFY, [write_json(f'{d1}/force_{tag}.json', doc)], 1, cwd=d1)
    control(names[5], MIX_VERIFY, [], 2, cwd=d1)
    # verify3.py reads cfg_TAG.json and cert_TAG.json from its working folder and writes nothing.
    control(names[6], MIX3_VERIFY, ['g1'], 0, cwd=MIX3, expect='g1 ACCEPTED')
    control(names[7], MIX3_VERIFY, ['g9'], 0, cwd=MIX3, expect='g9 ACCEPTED')
    d3 = f'{t}/mix3'
    os.mkdir(d3)
    cfg = load(os.path.join(MIX3, 'cfg_g1.json'))

    def case(tag, c, doc):
        write_json(f'{d3}/cfg_{tag}.json', c)
        write_json(f'{d3}/cert_{tag}.json', doc)
        return tag

    control(names[8], MIX3_VERIFY, [case('empty', cfg, {'close': 'abund', 'set': []})], 1, cwd=d3,
            expect='not abundant')
    if [3, 6] not in cfg['base']:
        raise SystemExit('control setup: cfg_g1.json no longer has the base component [3, 6]')
    dup = dict(cfg, base=cfg['base'] + [[3, 6]])  # 3^6 counted twice makes the root abundant
    control(names[9], MIX3_VERIFY, [case('dup', dup, {'close': 'abund', 'set': []})], 1, cwd=d3,
            expect='duplicate base prime')
    for i, (tag, doc) in enumerate(forced_variants(load(os.path.join(MIX3, 'cert_g1.json')))):
        control(names[10 + i], MIX3_VERIFY, [case(tag, cfg, doc)], 1, cwd=d3)
    control(names[13], MIX3_VERIFY, [], 2, cwd=d3)
    d4 = f'{t}/cert3'
    os.mkdir(d4)
    control(names[14], MIX3_CERT, [os.path.join(MIX3, 'cfg_g1.json'), 'min', f'{d4}/out.json', '0'], 1, cwd=d4,
            expect='"closed": false')
    if os.path.exists(f'{d4}/out.json'):
        report('FAIL', 'cert3.py: unfinished search writes no tree', 'out.json was written')
    else:
        report('PASS', 'cert3.py: unfinished search writes no tree')


def gen6_jobs_argument(t):
    """gen6.py reads its process count J only after the whole search, so a run cannot show where
    it looks for J in seconds. This control evaluates the assignment of `jobs_at` in the source,
    for both modes, against the place of [J] in the usage lines of the file header; a copy with
    the former index 7 must fail the same comparison."""
    def check(path):
        with open(path) as f:
            text = f.read()
        tree = ast.parse(text, path)
        exprs = [n.value for n in ast.walk(tree) if isinstance(n, ast.Assign)
                 and [getattr(x, 'id', None) for x in n.targets] == ['jobs_at']]
        if len(exprs) != 1:
            return f'{len(exprs)} assignments of jobs_at'
        code = compile(ast.Expression(exprs[0]), path, 'eval')
        usages = [line.lstrip('# ').split()[2:] for line in text.splitlines()
                  if line.lstrip('# ').startswith('python3 -I gen6.py ') and '[J]' in line.split()]
        if sorted(u[2] for u in usages) != ['lean', 'mirror']:
            return f'usage lines with [J] in the header: {usages}'
        # u is sys.argv of the documented command: u[0] the script, u[2] the mode
        bad = [' '.join(u[:u.index('[J]') + 1]) for u in usages
               if eval(code, {'__builtins__': {}}, {'mode': u[2]}) != u.index('[J]')]
        return ', '.join(bad) or None

    problem = check(GEN6)
    report('FAIL' if problem else 'PASS', 'gen6.py: process count read at the place of [J] in both modes',
           problem or '')
    old = mutate_text(GEN6, f'{t}/gen6_old.py', "jobs_at = 3 if mode == 'mirror' else 6",
                      "jobs_at = 3 if mode == 'mirror' else 7")
    problem = check(old)
    report('PASS' if problem else 'FAIL', 'gen6.py: the former index 7 is detected', problem or 'not detected')


def source_scan(t):
    """The source scan must reject a quoted attribute name, an interpolated string with a tactic
    block, an escaped lakefile key and an unreadable lakefile, and accept ordinary strings and
    comments that mention the same words."""
    d = f'{t}/scan'
    os.mkdir(d)

    def put(name, text):
        with open(f'{d}/{name}', 'w', encoding='utf-8') as f:
            f.write(text)
        return f'{d}/{name}'

    control('source_scan.py: attribute named by a quoted identifier', SCAN,
            [put('quoted.lean', '@[\u00abcommand_elab\u00bb Lean.Parser.Command.check]\ndef f : Nat := 1\n')], 1,
            expect='quoted.lean:1: attribute that runs code')
    control('source_scan.py: tactic block inside an interpolated string', SCAN,
            [put('interp.lean', 'def s : String := s!"{(by exact 0 : Nat)}"\n')], 1,
            expect='interp.lean:1: interpolated string syntax s!')
    control('source_scan.py: lakefile key written with Unicode escapes', SCAN,
            [put('escaped.toml', '[package]\nname = "x"\n\n[[lean_lib]]\nname = "X"\n'
                 '"more\\u004cean\\u0041rgs" = ["-DmaxHeartbeats=0"]\n')], 1,
            expect='escaped.toml:6: lakefile option moreLeanArgs')
    control('source_scan.py: unreadable lakefile', SCAN, [put('broken.toml', '[package\nname =\n')], 1,
            expect='invalid TOML')
    control('source_scan.py: the same words in comments and ordinary strings', SCAN,
            [put('words.lean', '/-- Mentions command_elab, run_cmd, s!"{by exact 0}" and \u00abtactic\u00bb. -/\n'
                 'def w : String := "run_cmd, @[command_elab], \u00abtactic\u00bb and s! in a string"\n'
                 '-- s!"{by exact 0}" in a line comment\ntheorem w_eq : w = w := rfl\n')], 0,
            expect='source scan OK: 1 files')
    control('source_scan.py: the same words in a lakefile comment and value', SCAN,
            [put('words.toml', '[package]\nname = "x"\n# moreLeanArgs in a comment\n'
                 'description = "moreLeanArgs in a value"\n')], 0, expect='source scan OK: 1 files')


def contribution_scan(t):
    """The format scan of contributed proofs must accept the format example, also with the
    forbidden words in comments, and reject a file that runs code at elaboration time, skips
    the kernel, hides text in a string or a quoted identifier, imports foreign code or does not
    prove the step it is named after. In pull request mode the change must add exactly one
    contributed file and touch nothing else."""
    d = f'{t}/contrib'
    os.mkdir(d)
    head = 'import OddPerfect.Steps\nnamespace OddPerfect.Proofs\n'
    tail = ('theorem Example : OddPerfect.Steps.Example := by\n  intro N h h2\n'
            '  have h1 := Nat.odd_iff.mp h.odd\n  omega\nend OddPerfect.Proofs\n')

    def case(key, name, mid, want, expect, head=head, tail=tail):
        os.mkdir(f'{d}/{key}')
        with open(f'{d}/{key}/Example.lean', 'w', encoding='utf-8') as f:
            f.write(head + mid + tail)
        control('contribution_scan.py: ' + name, CONTRIB_SCAN, [f'{d}/{key}/Example.lean'], want,
                expect=expect)

    case('ok', 'the format example', '', 0, '1 files, 0 findings')
    case('words', 'forbidden words in comments only',
         '/- #eval, run_cmd and "strings" are described here /- nested -/ -/\n-- open Lean\n', 0,
         '1 files, 0 findings')
    case('eval', 'an indented #eval', '  #eval 1\n', 1, 'start with #')
    case('runcmd', 'run_cmd', 'run_cmd pure ()\n', 1, 'run_cmd is not allowed')
    case('kernel', 'an option that skips the kernel', 'set_option debug.skipKernelTC true in\n', 1,
         'set_option is allowed only')
    case('string', 'a string literal', 'def s := "run_cmd"\n', 1, 'string literals')
    case('quoted', 'a quoted identifier', 'def \u00abrun_cmd\u00bb := 1\n', 1, 'quoted identifiers')
    case('lean', 'the metaprogramming namespace', 'open Lean in\n', 1, 'Lean is not allowed')
    case('attr', 'an attribute other than simp', '@[implemented_by f] def g := 1\n', 1,
         'the only attribute allowed')
    case('import', 'a foreign import', '', 1, 'only Mathlib and OddPerfect modules',
         head='import Evil.Module\n' + head)
    case('native', 'decide +native', '', 1, 'native is not allowed',
         tail=tail.replace('omega', 'decide +native'))
    case('name', 'a theorem that is not named after the file', '', 1, 'exactly one line starting',
         tail=tail.replace('theorem Example', 'theorem Other'))

    # pull request mode, on a small repository built here
    def git(repo, *args):
        subprocess.run(['git', '-C', repo, '-c', 'user.name=control', '-c',
                        'user.email=control@example.invalid', '-c', 'commit.gpgsign=false', *args],
                       check=True, capture_output=True)

    for key, extra, want, expect in (('pr_ok', False, 0, '1 files, 0 findings'),
                                     ('pr_two', True, 1, 'changes nothing else')):
        repo = f'{d}/{key}'
        os.makedirs(f'{repo}/Contributions')
        git(repo, 'init', '-q')
        with open(f'{repo}/README.md', 'w', encoding='utf-8') as f:
            f.write('base\n')
        git(repo, 'add', '-A')
        git(repo, 'commit', '-q', '-m', 'base')
        with open(f'{repo}/Contributions/Example.lean', 'w', encoding='utf-8') as f:
            f.write(head + tail)
        if extra:
            with open(f'{repo}/README.md', 'w', encoding='utf-8') as f:
                f.write('changed\n')
        git(repo, 'add', '-A')
        git(repo, 'commit', '-q', '-m', 'change')
        control('contribution_scan.py: pull request ' +
                ('that also changes another file' if extra else 'that adds one contributed file'),
                CONTRIB_SCAN, ['--pull-request', 'HEAD~1'], want, cwd=repo, expect=expect)


def replay_list(t):
    """replay.sh with a stand in for lake: the default module list must be every library file,
    an import written with two spaces must still be listed, a file missing from the root file and
    an empty explicit selection must end with exit status 2."""
    stub = f'{t}/stub'
    os.makedirs(f'{stub}/bin')
    os.makedirs(f'{stub}/prefix/bin')
    with open(f'{stub}/bin/lake', 'w') as f:
        f.write('#!/bin/sh\n# stand in: lake env lean --print-prefix, lake env CHECKER MODULE\n'
                '[ "$1" = env ] || exit 3\nshift\n'
                'if [ "$1" = lean ] && [ "$2" = --print-prefix ]; then echo "$STUB_PREFIX"; exit 0; fi\n'
                'echo "$2" >> "$STUB_LOG"\n')
    with open(f'{stub}/prefix/bin/leanchecker', 'w') as f:
        f.write('#!/bin/sh\nexit 0\n')
    os.chmod(f'{stub}/bin/lake', 0o755)
    os.chmod(f'{stub}/prefix/bin/leanchecker', 0o755)

    def run(name, cwd, args, want, check=None):
        log = f'{stub}/log_{results["PASS"] + results["FAIL"]}.txt'
        open(log, 'w').close()
        env = dict(os.environ, PATH=f'{stub}/bin' + os.pathsep + os.environ.get('PATH', ''),
                   STUB_PREFIX=f'{stub}/prefix', STUB_LOG=log)
        try:
            p = subprocess.run(['sh', os.path.join(cwd, 'scripts', 'Controls', 'replay.sh')] + args, cwd=cwd,
                               env=env, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            report('FAIL', name, 'no result within 120 s')
            return
        with open(log) as f:
            replayed = f.read().split()
        problem = None
        if 'Traceback' in p.stderr:
            problem = 'traceback: ' + p.stderr.strip().splitlines()[-1]
        elif p.returncode != want:
            problem = f'exit status {p.returncode}, expected {want}'
        elif check is not None:
            problem = check(replayed)
        report('FAIL' if problem else 'PASS', name, problem or f'exit status {want}')

    lib = sorted(os.path.relpath(os.path.join(r, n), ROOT)[:-5].replace(os.sep, '.')
                 for r, _, ns in os.walk(os.path.join(ROOT, 'OddPerfect')) for n in ns if n.endswith('.lean'))
    run('replay.sh: default list is every library file', ROOT, [], 0,
        lambda got: None if got == lib and lib else f'{len(got)} modules replayed, {len(lib)} library files')
    small = f'{t}/replaytree'
    os.makedirs(f'{small}/OddPerfect')
    os.makedirs(f'{small}/scripts/Controls')
    for src in (SCAN, REPLAY):
        with open(src) as f, open(f'{small}/scripts/Controls/{os.path.basename(src)}', 'w') as g:
            g.write(f.read())
    with open(f'{small}/OddPerfect.lean', 'w') as f:
        f.write('import  OddPerfect.A\nimport OddPerfect.B\n')
    for m in ('A', 'B'):
        with open(f'{small}/OddPerfect/{m}.lean', 'w') as f:
            f.write(f'theorem {m.lower()}_true : True := trivial\n')
    run('replay.sh: import written with two spaces is listed', small, [], 0,
        lambda got: None if got == ['OddPerfect.A', 'OddPerfect.B'] else f'replayed {got}')
    run('replay.sh: empty explicit selection', small, [''], 2)
    with open(f'{small}/OddPerfect/C.lean', 'w') as f:
        f.write('theorem c_true : True := trivial\n')
    run('replay.sh: library file not imported by the root file', small, [], 2,
        lambda got: None if not got else f'replayed {got}')


def two_exception(t):
    """The independent recheck and the mirror accept the archived certificate; the mirror
    also accepts the three excess certificates. Negative rational witnesses and an out-of-range
    strong pseudoprime must not be admitted as Lean Nat data and certified primes."""
    cert = os.path.join(TWO, 'cert.jsonl.xz')
    control('TwoExceptionTwo/check.py accepts the archived certificate', os.path.join(TWO, 'check.py'),
            [cert], 0, expect='VERDICT PASS')
    control('TwoExceptionTwo/engine.py accepts the archived certificate', TWO_ENGINE,
            [cert], 0, expect='accepted True')
    ex = os.path.join(SC, 'ExcessFour')
    for name in sorted(n for n in os.listdir(ex) if n.startswith('cert_') and n.endswith('.jsonl')):
        control('TwoExceptionTwo/engine.py accepts ' + name, TWO_ENGINE,
                [os.path.join(ex, name)], 0, expect='accepted True')
    state = {'x': 5, 'q': None, 'exq': [], 'S': {'3': []}, 'F': {}, 'R': {}}
    records = [
        {'id': 0, 'kind': 'header', 'root': 1, 'EMAX': 2, 'MHIT': 10**30, 'KCAP': 64,
         'flags': ['cert']},
        {'id': 1, 'kind': 'apply', 'state': state, 'values': [], 'items': [],
         'outcome': 'closed', 'next_x': 5, 'children': [2]},
        {'id': 2, 'kind': 'check', 'state': state, 'x': 5, 'reason': 'deficient',
         'proof': {'x': 5, 'H': '13/9', 'U': '0', 'a': 1, 'b': 2, 'c': 2, 'd': 4,
                   'u': 3, 'hits': [], 'K': [], 'extra_ab': 0, 'extra_cd': 0, 'nonhits': [],
                   'rankin': {'mode': 'theta', 'alpha_x': [0, 11, 10], 'alpha': {},
                              'k': 3, 'mL': '-1', 'mM': '-1'}}}]
    negative = os.path.join(t, 'negative_rankin.jsonl')
    with open(negative, 'w') as f:
        for r in records:
            f.write(json.dumps(r) + '\n')
    control('TwoExceptionTwo/engine.py rejects negative Rankin numerators', TWO_ENGINE,
            [negative], 1, expect='natural number')
    control('TwoExceptionTwo/check.py rejects the forged root closure', os.path.join(TWO, 'check.py'),
            [negative], 1, expect='VERDICT FAIL')
    probe = os.path.join(t, 'pseudoprime.py')
    with open(probe, 'w') as f:
        f.write('import runpy, sys\n'
                'm = runpy.run_path(sys.argv[1])\n'
                'n = 399165290221 * 798330580441\n'
                'try:\n'
                '    print("oracle result", m["pr"](n))\n'
                'except m["Reject"] as e:\n'
                '    print("REJECTED", e); sys.exit(1)\n')
    control('TwoExceptionTwo/engine.py rejects out-of-range pseudoprime', probe,
            [TWO_ENGINE], 1, expect='deterministic range')
    # The mirror scans 1000 positions, like `scanNext` in TwoExcEngineCode.lean: with every odd
    # prime through 997 a key, a scan from 3 ends at 1002 and rejects; without the key 997 it
    # returns 997.
    fuel = os.path.join(t, 'scan_fuel.py')
    with open(fuel, 'w') as f:
        f.write('import runpy, sys\n'
                'm = runpy.run_path(sys.argv[1])\n'
                'odd = [p for p in range(3, 998) if all(p % d for d in range(2, p))]\n'
                'keys = [(p,) for p in odd if p <= int(sys.argv[2])]\n'
                'try:\n'
                '    print("scan result", m["scan_next"]({"x": 3, "keys": keys}))\n'
                'except m["Reject"] as e:\n'
                '    print("REJECTED", e); sys.exit(1)\n')
    control('TwoExceptionTwo/engine.py scan stops after 1000 positions', fuel,
            [TWO_ENGINE, '997'], 1, expect='REJECTED scan')
    control('TwoExceptionTwo/engine.py scan finds a prime inside 1000 positions', fuel,
            [TWO_ENGINE, '996'], 0, expect='scan result 997')
    # The second path of the tail test. No archived certificate reaches it, so the leaf is built
    # here: only the key 3 as a square, x = 1000, Rankin witnesses k = 3, B = 1, rx = 10,
    # mL = 1/10 and mM = 1/n. With n = 4 the first path fails (U0/(1 - S) is about 2.05) and
    # the second passes (about 1.94); with n = 3 both fail (the second is about 2.11).
    tail = os.path.join(t, 'tail_paths.py')
    with open(tail, 'w') as f:
        f.write('import runpy, sys\n'
                'm = runpy.run_path(sys.argv[1])\n'
                'P = {"E": 2, "MHIT": 10**30, "KCAP": 64}\n'
                'st = {"x": 1000, "keys": [(3, ("sq",), [])]}\n'
                'dd = (None, 3, 1, [], 10, (1, 10), (1, int(sys.argv[2])), [])\n'
                'try:\n'
                '    print("deficient", m["deficient"](P, st, dd), dict(m["COUNT"]))\n'
                'except m["Reject"] as e:\n'
                '    print("REJECTED", e); sys.exit(1)\n')
    control('TwoExceptionTwo/engine.py accepts a leaf on the second tail path', tail,
            [TWO_ENGINE, '4'], 0, expect="'pade_accepted': 1")
    control('TwoExceptionTwo/engine.py rejects a leaf that fails both tail paths', tail,
            [TWO_ENGINE, '3'], 1, expect='fails on both paths')
    # The same failure through the whole pipeline of engine.py: a root leaf at x = 5 with valid
    # witnesses, where the bound is about 10. (check.py computes its own witnesses and stops
    # earlier on this leaf, at S >= 3; its second path has no control here.)
    both = os.path.join(t, 'both_paths_fail.jsonl')
    records[2]['proof']['rankin'].update(mL='1', mM='1')
    with open(both, 'w') as f:
        for r in records:
            f.write(json.dumps(r) + '\n')
    control('TwoExceptionTwo/engine.py rejects a certificate whose leaf fails both tail paths',
            TWO_ENGINE, [both], 1, expect='fails on both paths')


def main(argv):
    if argv[1:] not in ([], ['--stdlib-only']):
        print('usage: python3 -I scripts/Controls/validator_controls.py [--stdlib-only]', file=sys.stderr)
        return 2
    no_asserts()
    with tempfile.TemporaryDirectory() as t:
        equal_exponent_chain(t)
        lower_bound(t)
        common_families(t, argv[1:] == ['--stdlib-only'])
        estimator(t)
        three_free_three(t)
        second_largest_prime(t)
        ledger_three_free(t, argv[1:] == ['--stdlib-only'])
        mixed_index(t, argv[1:] == ['--stdlib-only'])
        two_exception(t)
        gen6_jobs_argument(t)
        source_scan(t)
        contribution_scan(t)
        replay_list(t)
    print(f'validator controls: {results["PASS"]} passed, {results["FAIL"]} failed, {results["SKIP"]} skipped')
    return 1 if results['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
