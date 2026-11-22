#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Permanent controls for the published validators EqualExponentChain/checker.py,
# LowerBound/check.py, CommonFamilies/verify.py and CommonFamilies/est.py, and for the helpers
# under ThreeFreeThree/ (check3.py, verify3.py, gen_lean.py, route3.py): every archived valid
# input must pass with exit status 0, and each mutated input must be rejected with the expected
# nonzero status (1: a well formed input fails a check; 2: malformed input or usage), with no
# Python traceback. The validators run as subprocesses with `sys.executable -I`, in normal and
# in optimized (-O) mode, so a check written as an `assert` would show up as a failure.
# Mutated inputs are built from the archived certificates in a temporary folder; nothing is
# written inside the repository.
# Run: python3 -I scripts/Controls/validator_controls.py [--stdlib-only]
# With --stdlib-only the controls of CommonFamilies/verify.py, which needs sympy, are skipped
# (each is listed as SKIP); without it a missing sympy is a failure.
# Requires: Python 3 standard library (sympy for the verify.py controls). Running time: about
# half a minute.
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


def control(name, script, args, want, modes=('', '-O'), cwd=None, timeout=60):
    """Runs the script in each mode and requires exit status `want` and no traceback."""
    for mode in modes:
        cmd = [sys.executable, '-I'] + ([mode] if mode else []) + [script] + args
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
    for path in (CHECKER, LBCHECK, VERIFY, EST, os.path.abspath(__file__)):
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
             'verify.py: excluded prime 1 (empty profile)', 'verify.py: duplicate row', 'verify.py: seed 0']
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
    print(f'validator controls: {results["PASS"]} passed, {results["FAIL"]} failed, {results["SKIP"]} skipped')
    return 1 if results['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
