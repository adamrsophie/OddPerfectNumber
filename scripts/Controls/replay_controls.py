#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Permanent controls for the replay and generator helpers DefectTree/ (check.py, search.py,
# gen.py), ShapeSmall/ (replay.py, gen.py), SpecialFive/ (replay.py, stage1.py, gen.py) and
# SpecialFiveMore/ (replay.py, gen.py): every archived valid input must pass with exit status 0,
# and each mutated input must be rejected with the expected nonzero status (1: a well formed
# input fails a check; 2: malformed input, a usage error or an unreadable file), with no Python
# traceback. The helpers run as subprocesses with `sys.executable -I -B`, in normal and in
# optimized (-O) mode, so a check written as an `assert` would show up as a failure.
# SpecialFive and SpecialFiveMore keep no certificate in the repository: the controls build
# them in a temporary folder (SpecialFive/gen.py 24, whose certificate and Lean module must
# equal the published ones, and SpecialFiveMore/gen.py 12 with small chunks). The factoring
# deadline of DefectTree/search.py and the stuck count of SpecialFive/stage1.py are controlled
# with a stand in for sympy (a factorint that sleeps or finds nothing), loaded by a small
# driver before the script runs. Mutated inputs are built in a temporary folder; nothing is
# written inside the repository.
# Run: python3 -I scripts/Controls/replay_controls.py [--stdlib-only]
# With --stdlib-only the controls that need sympy (SpecialFive/gen.py and stage1.py, and the
# SpecialFive replay controls, which use the certificate built by gen.py) are listed as SKIP.
# Requires: Python 3, sympy for the controls named above. Running time: about one minute of
# CPU time (five minutes of wall time on a heavily loaded machine).
# Exit status: 0 when every control behaves as expected, 1 otherwise, 2 for a usage error.
# License: GPL 3, same as the repository.

import ast
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SC = os.path.join(ROOT, 'scripts')
LIB = os.path.join(ROOT, 'OddPerfect')
DT = os.path.join(SC, 'DefectTree')
DT_CHECK = os.path.join(DT, 'check.py')
DT_SEARCH = os.path.join(DT, 'search.py')
DT_GEN = os.path.join(DT, 'gen.py')
DT_ROWS = os.path.join(DT, 'rows.json')
DT_CERTS = sorted(n for n in os.listdir(DT) if n.startswith('cert') and n.endswith('.json'))
SS = os.path.join(SC, 'ShapeSmall')
SS_REPLAY = os.path.join(SS, 'replay.py')
SS_GEN = os.path.join(SS, 'gen.py')
SS_LEAN = os.path.join(LIB, 'ShapeSmall.lean')
SS_GEN_SHA = '58d1bad5c674000aab7b1ef5b8b54e7a73c09077bcf92051997b6c3a020fcea5'
SF = os.path.join(SC, 'SpecialFive')
SF_REPLAY = os.path.join(SF, 'replay.py')
SF_STAGE1 = os.path.join(SF, 'stage1.py')
SF_CERT_SHA = 'c758d9ddf446d385045d85968c08be633b4269c93a403636e94888d682da3caa'
SFM = os.path.join(SC, 'SpecialFiveMore')
SFM_REPLAY = os.path.join(SFM, 'replay.py')
HARDENED = [DT_CHECK, DT_SEARCH, SS_REPLAY, SS_GEN, SF_REPLAY, SF_STAGE1, SFM_REPLAY]

# Loads a stand in for sympy, then runs the script given after the mode with the remaining
# arguments. Modes: both (factorint of 13 sleeps, also with a limit), first (it sleeps only
# without a limit), empty (factorint finds no factor at all).
DRIVER = '''import runpy, sys, time, types
mode, script = sys.argv[1], sys.argv[2]
def factorint(n, limit=None):
    if mode == 'empty':
        return {}
    if n == 13 and (limit is None or mode == 'both'):
        while True:
            time.sleep(1)
    out, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out
def isprime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))
stub = types.ModuleType('sympy')
stub.factorint, stub.isprime = factorint, isprime
sys.modules['sympy'] = stub
sys.argv = [script] + sys.argv[3:]
runpy.run_path(script, run_name='__main__')
'''

results = {'PASS': 0, 'FAIL': 0, 'SKIP': 0}


def report(verdict, name, detail=''):
    results[verdict] += 1
    print(f'{verdict} {name}' + (f': {detail}' if detail else ''), flush=True)


def control(name, script, args, want, modes=('', '-O'), cwd=None, timeout=60, expect=None,
            after=None):
    """Runs the script in each mode and requires exit status `want`, no traceback, the line
    fragment `expect` (if given) in its output, and `after()` (if given) to return None."""
    for mode in modes:
        cmd = [sys.executable, '-I', '-B'] + ([mode] if mode else []) + [script] + args
        label = f'{name} [{"python -O" if mode else "python"}]'
        try:
            p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            report('FAIL', label, f'no result within {timeout} s')
            continue
        problem = after() if after is not None and p.returncode == want else None
        if 'Traceback' in p.stderr:
            report('FAIL', label, 'traceback: ' + p.stderr.strip().splitlines()[-1])
        elif p.returncode != want:
            report('FAIL', label, f'exit status {p.returncode}, expected {want}')
        elif expect is not None and expect not in p.stdout + p.stderr:
            report('FAIL', label, f'no line with {expect!r}')
        elif problem:
            report('FAIL', label, problem)
        else:
            report('PASS', label, f'exit status {want}')


def skip(name, why):
    for mode in ('python', 'python -O'):
        report('SKIP', f'{name} [{mode}]', why)


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


def truncated(path):
    with open(path, 'w') as f:
        f.write('{"K": 2, "rows": [')
    return path


def sha(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def same(pairs):
    """None when each produced file equals its reference byte for byte."""
    for got, ref in pairs:
        if not os.path.exists(got) or sha(got) != sha(ref):
            return f'{os.path.basename(got)} differs from {os.path.relpath(ref, ROOT)}'
    return None


def no_asserts():
    """The hardened helpers and this script must not rely on `assert`, which python -O
    removes."""
    for path in HARDENED + [os.path.abspath(__file__)]:
        with open(path) as f:
            tree = ast.parse(f.read(), path)
        lines = [n.lineno for n in ast.walk(tree) if isinstance(n, ast.Assert)]
        rel = os.path.relpath(path, ROOT)
        if lines:
            report('FAIL', f'no assert in {rel}', f'assert at lines {lines}')
        else:
            report('PASS', f'no assert in {rel}')


def first_node(t, tag):
    """The first node with the given tag in a SpecialFive tree (lists), depth first."""
    stack = [t]
    while stack:
        x = stack.pop()
        if x[0] == tag:
            return x
        stack += [y for y in reversed(x[1:]) if type(y) is list]
    raise SystemExit(f'control setup: no node {tag}')


def defect_tree(t):
    for n in DT_CERTS:
        control(f'DefectTree/check.py accepts {n}', DT_CHECK, [n, 'rows.json'], 0, cwd=DT,
                timeout=120, expect='accepted')
    control('DefectTree/check.py: wrong tree (gen.py corrupt)', DT_CHECK,
            ['cert2.json', 'rows.json', 'corrupt'], 1, cwd=DT, expect='first rejected node')
    c, d = load(os.path.join(DT, 'cert2.json')), load(DT_ROWS)

    def rows_with(fn, name):
        dd = copy.deepcopy(d)
        fn(dd)
        return write_json(f'{t}/{name}', dd)

    def add_fact(dd, fact):
        for row in dd['rows']:
            if row[:2] == [3, 2]:
                row[2].append(fact)

    def cert_with(fn, name):
        cc = copy.deepcopy(c)
        fn(cc)
        return write_json(f'{t}/{name}', cc)

    control('DefectTree/check.py: false table fact (3, 2) in the row 3^2 = 13', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: add_fact(dd, [3, 2]), 'dt_fact.json')], 1,
            cwd=DT, expect='false fact')
    control('DefectTree/check.py: table fact (0, 1)', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: add_fact(dd, [0, 1]), 'dt_zero.json')], 1,
            cwd=DT)
    if d['pm1']['331'] != [2, 3, 5, 11]:
        raise SystemExit('control setup: rows.json no longer has pm1[331] = [2, 3, 5, 11]')
    control('DefectTree/check.py: bad Pratt data (factors of 330 given as 2 3 5 13)', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd['pm1'].update({'331': [2, 3, 5, 13]}),
                                     'dt_pratt.json')], 1, cwd=DT, expect='not certified')
    control('DefectTree/check.py: no Pratt data for 331', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd['pm1'].pop('331'), 'dt_pratt3.json')], 1,
            cwd=DT, expect='not certified')
    control('DefectTree/check.py: Pratt entry that is not a list', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd['pm1'].update({'331': 330}),
                                     'dt_pratt2.json')], 2, cwd=DT)

    def tag(cc):
        cc['cert']['ch'][0]['t'] = 'bogus'
    control('DefectTree/check.py: unknown chain tag', DT_CHECK,
            [cert_with(tag, 'dt_tag.json'), 'rows.json'], 2, cwd=DT)

    def leaf_tag(cc):
        cc['cert']['ch'][0]['kid'] = {'t': 'capp', 'r': 3}
    control('DefectTree/check.py: unknown leaf tag', DT_CHECK,
            [cert_with(leaf_tag, 'dt_leaf.json'), 'rows.json'], 2, cwd=DT)
    control('DefectTree/check.py: surplus field in a node', DT_CHECK,
            [cert_with(lambda cc: cc['cert'].update(extra=1), 'dt_surplus.json'), 'rows.json'],
            2, cwd=DT)
    control('DefectTree/check.py: missing field cap', DT_CHECK,
            [cert_with(lambda cc: cc['params'].pop('cap'), 'dt_missing.json'), 'rows.json'], 2,
            cwd=DT)
    for name, val in (('negative', -1), ('float', 2.0), ('boolean', True)):
        control(f'DefectTree/check.py: {name} K', DT_CHECK,
                [cert_with(lambda cc: cc['params'].update(K=val), f'dt_{name}.json'),
                 'rows.json'], 2, cwd=DT)
    control('DefectTree/check.py: negative branch prime', DT_CHECK,
            [cert_with(lambda cc: cc['cert'].update(r=-3), 'dt_negr.json'), 'rows.json'], 2,
            cwd=DT)
    control('DefectTree/check.py: unreadable JSON', DT_CHECK,
            [truncated(f'{t}/dt_trunc.json'), 'rows.json'], 2, cwd=DT)
    control('DefectTree/check.py: missing argument', DT_CHECK, ['cert2.json'], 2, cwd=DT)
    control('DefectTree/check.py: unknown flag', DT_CHECK, ['cert2.json', 'rows.json', 'x'], 2,
            cwd=DT)
    control('DefectTree/check.py: file not found', DT_CHECK, [f'{t}/none.json', 'rows.json'], 2,
            cwd=DT)

    # search.py: the archived searches, the factoring deadline and the arguments.
    for k in ('2', '4'):
        rows = f'{t}/dt_rows_{k}.json'
        out = f'{t}/dt_cert_{k}.json'
        for mode in ('', '-O'):
            shutil.copyfile(DT_ROWS, rows)
            control(f'DefectTree/search.py regenerates cert{k}.json and rows.json', DT_SEARCH,
                    [k, '0', '3', '3', 'none', rows, out], 0, modes=(mode,), cwd=t,
                    after=lambda: same([(out, os.path.join(DT, f'cert{k}.json')),
                                        (rows, DT_ROWS)]))
    driver = f'{t}/driver.py'
    with open(driver, 'w') as f:
        f.write(DRIVER)
    d32 = copy.deepcopy(d)
    d32['rows'] = [r for r in d32['rows'] if r[:2] != [3, 2]]
    rows = f'{t}/dt_rows_no32.json'
    out = f'{t}/dt_cert_no32.json'
    for mode in ('', '-O'):
        write_json(rows, d32)
        # With the row 3^2 empty the state 3^2 has no forced prime: an open leaf, status 1.
        control('DefectTree/search.py: both factoring steps of the row 13 time out (stand in)',
                driver, ['both', DT_SEARCH, '2', '0', '3', '3', 'none', rows, out,
                         'factor_seconds=1'], 1, modes=(mode,), cwd=t, timeout=30,
                expect='PARTIAL row 3 2 factor_seconds 1 kept []')
        write_json(rows, d32)
        control('DefectTree/search.py: the full factorization of 13 times out (stand in)',
                driver, ['first', DT_SEARCH, '2', '0', '3', '3', 'none', rows, out,
                         'factor_seconds=1'], 0, modes=(mode,), cwd=t, timeout=30,
                expect='partial rows 1',
                after=lambda: same([(out, os.path.join(DT, 'cert2.json'))]))
    control('DefectTree/search.py: factor_seconds=0', DT_SEARCH,
            ['2', '0', '3', '3', 'none', f'{t}/dt_r0.json', f'{t}/dt_o0.json',
             'factor_seconds=0'], 2, cwd=t)
    control('DefectTree/search.py: missing argument', DT_SEARCH, ['2', '0', '3'], 2, cwd=t)
    control('DefectTree/search.py: unreadable row table', DT_SEARCH,
            ['2', '0', '3', '3', 'none', truncated(f'{t}/dt_rtrunc.json'), f'{t}/dt_o1.json'], 2,
            cwd=t)

    # gen.py is unchanged; its output for the two small certificates must stay byte equal.
    for k, name, mod in (('2', 'Two', 'DefectTreeTwoData'), ('4', 'Four', 'DefectTreeFourData')):
        out = f'{t}/{mod}.lean'
        control(f'DefectTree/gen.py writes {mod}.lean byte for byte', DT_GEN,
                [f'cert{k}.json', 'rows.json', name, out], 0, cwd=DT,
                after=lambda: same([(out, os.path.join(LIB, f'{mod}.lean'))]))


def shape_small(t):
    gen_out = f'{t}/ss_gen_out.txt'

    def gen_sha():
        return None if sha(gen_out) == SS_GEN_SHA else 'output differs from the README hash'
    for mode in ('', '-O'):
        cmd = [sys.executable, '-I', '-B'] + ([mode] if mode else []) + [SS_GEN]
        with open(gen_out, 'w') as f:
            p = subprocess.run(cmd, stdout=f, stderr=subprocess.PIPE, text=True, timeout=60)
        label = f'ShapeSmall/gen.py output is unchanged [{"python -O" if mode else "python"}]'
        problem = gen_sha() if p.returncode == 0 else f'exit status {p.returncode}'
        report('FAIL' if problem else 'PASS', label, problem or 'SHA-256 ' + SS_GEN_SHA[:16])
    control('ShapeSmall/replay.py accepts ShapeSmall.lean', SS_REPLAY, [SS_LEAN], 0)
    control('ShapeSmall/replay.py: its two negative controls are rejected', SS_REPLAY,
            [SS_LEAN, 'bad'], 0, expect='REJECTED c6')
    control('ShapeSmall/gen.py --check accepts ShapeSmall.lean', SS_GEN, ['--check', SS_LEAN], 0,
            expect='0 differences')
    muts = [
        ('a chunk theorem that names the list L5 (wrong list)', 'chk 6 L6 32771', 'chk 6 L5 32771'),
        ('L6_ok checks maskOK 5', 'L6.all (fun mm => maskOK 6', 'L6.all (fun mm => maskOK 5'),
        ('prime_le_6 uses c5', '(D := 65536) c6', '(D := 65536) c5'),
        ('no_sol_6 uses the chunk chk6_0 twice', 'chk_sound _ _ chk6_1', 'chk_sound _ _ chk6_0'),
        ('wrong tree: case split i < 32769', 'i < 32768', 'i < 32769'),
        ('false mask: bit 0 for the modulus 17 in L5', '(17, 32754)', '(17, 32755)'),
        ('bad certificate coefficient 9924 in c6', '9923]', '9924]'),
        ('missing last show of no_sol_6',
         '  rwa [show 98307 + 2 * (i - 49152) = 3 + 2 * i by omega] at this\n', ''),
    ]
    with open(SS_LEAN) as f:
        text = f.read()
    a = text.index('/-- Residue masks for `e = 10`')
    b = text.index('/-- Residue masks for `e = 12`')
    missing = f'{t}/ss_missing.lean'
    with open(missing, 'w') as f:
        f.write(text[:a] + text[b:])
    files = [(name, mutate_text(SS_LEAN, f'{t}/ss_{i}.lean', old, new))
             for i, (name, old, new) in enumerate(muts)]
    files.append(('missing family 5 (L5, L5_ok, chk5_0, no_sol_5)', missing))
    for name, path in files:
        control(f'ShapeSmall/replay.py: {name}', SS_REPLAY, [path], 1)
        control(f'ShapeSmall/gen.py --check: {name}', SS_GEN, ['--check', path], 1)
    notlean = f'{t}/ss_notlean.lean'
    with open(notlean, 'w') as f:
        f.write('theorem x : True := trivial\n')
    for script, pre in ((SS_REPLAY, []), (SS_GEN, ['--check'])):
        base = os.path.relpath(script, SC)
        control(f'{base}: a file without the text of the module', script, pre + [notlean], 2)
        control(f'{base}: file not found', script, pre + [f'{t}/none.lean'], 2)
        control(f'{base}: missing argument', script, pre, 2)


def special_five(t, stdlib_only):
    """Replay controls on the certificate of SpecialFive/gen.py 24 (needs sympy)."""
    names = ['SpecialFive/gen.py 24 and replay.py', 'SpecialFive/stage1.py']
    if stdlib_only:
        for n in names:
            skip(n, 'sympy controls skipped (--stdlib-only)')
        return
    out = f'{t}/sf24'
    control('SpecialFive/gen.py 24 writes the published certificate and SpecialFiveData.lean',
            os.path.join(SF, 'gen.py'), ['24', out], 0, modes=('',), cwd=t, timeout=600,
            after=lambda: (None if os.path.exists(f'{out}/cert.json') and
                           sha(f'{out}/cert.json') == SF_CERT_SHA else 'cert.json hash differs')
            or same([(f'{out}/SpecialFiveData.lean', os.path.join(LIB, 'SpecialFiveData.lean'))]))
    cert = f'{out}/cert.json'
    if not os.path.exists(cert):
        report('FAIL', 'SpecialFive/replay.py controls', 'no certificate from gen.py')
        return
    control('SpecialFive/replay.py accepts the certificate', SF_REPLAY, [cert, 'tree'], 0,
            expect='ACCEPT tree for B = 10^24')
    control('SpecialFive/replay.py rejects its corrupted tree bad', SF_REPLAY, [cert, 'bad'], 1,
            expect='REJECT bad')
    c = load(cert)

    def mut(fn, name):
        cc = copy.deepcopy(c)
        fn(cc)
        return write_json(f'{t}/{name}', cc)

    def cap_plus(cc):
        node = first_node(cc['tree'], 'cap')
        node[1] += 2
    if c['tab'][0] != [3, 2, [[13, 1]]] or c['pratt'][0] != [307, 5, [2, 3, 3, 17]]:
        raise SystemExit('control setup: SpecialFive certificate has another first row or entry')
    cases = [
        ('wrong tree: first capacity witness plus 2', cap_plus, 1),
        ('false table fact (3, 1) for 3^2 = 13', lambda cc: cc['tab'][0][2].append([3, 1]), 1),
        ('bad Pratt witness 1 for 307', lambda cc: cc['pratt'][0].__setitem__(1, 1), 1),
        ('Pratt entry with two fields', lambda cc: cc['pratt'][0].pop(), 2),
        ('unknown tag', lambda cc: first_node(cc['tree'], 'abund').__setitem__(0, 'abundant'), 2),
        ('surplus field in a cap node', lambda cc: first_node(cc['tree'], 'cap').append(0), 2),
        ('surplus top level field', lambda cc: cc.update(extra=0), 2),
        ('missing field bad', lambda cc: cc.pop('bad'), 2),
        ('negative K', lambda cc: cc.update(K=-1), 2),
        ('float K', lambda cc: cc.update(K=24.0), 2),
        ('boolean in a table fact', lambda cc: cc['tab'][0][2][0].__setitem__(1, True), 2),
    ]
    for i, (name, fn, want) in enumerate(cases):
        control(f'SpecialFive/replay.py: {name}', SF_REPLAY, [mut(fn, f'sf_{i}.json')], want)
    control('SpecialFive/replay.py: unreadable JSON', SF_REPLAY, [truncated(f'{t}/sf_t.json')], 2)
    control('SpecialFive/replay.py: unknown mode', SF_REPLAY, [cert, 'K'], 2)
    control('SpecialFive/replay.py: missing argument', SF_REPLAY, [], 2)
    control('SpecialFive/replay.py: file not found', SF_REPLAY, [f'{t}/none.json'], 2)

    control('SpecialFive/stage1.py closes B = 10^6', SF_STAGE1, ['1000000'], 0,
            expect='result=closed')
    driver = f'{t}/driver.py'
    with open(driver, 'w') as f:
        f.write(DRIVER)
    control('SpecialFive/stage1.py: a stuck node (stand in factorint finds nothing)', driver,
            ['empty', SF_STAGE1, '10000'], 1, expect='result=stuck')
    control('SpecialFive/stage1.py: node limit reached', SF_STAGE1, ['1000000', '3'], 1,
            expect='result=LIMIT')
    control('SpecialFive/stage1.py: unknown order', SF_STAGE1, ['10000', '100', 'middle'], 2)
    control('SpecialFive/stage1.py: B not a number', SF_STAGE1, ['ten'], 2)
    control('SpecialFive/stage1.py: missing argument', SF_STAGE1, [], 2)


def special_five_more(t):
    out = f'{t}/sfm12'
    control('SpecialFiveMore/gen.py 12 with small chunks', os.path.join(SFM, 'gen.py'),
            ['12', out, '40', '30', '20', '60'], 0, modes=('',), cwd=t, timeout=120)
    cert = f'{out}/cert.json'
    if not os.path.exists(cert):
        report('FAIL', 'SpecialFiveMore/replay.py controls', 'no certificate from gen.py')
        return
    control('SpecialFiveMore/replay.py accepts the certificate', SFM_REPLAY, [cert], 0,
            expect='ACCEPT tree for B = 10^12')
    control('SpecialFiveMore/replay.py rejects its corrupted piece bad', SFM_REPLAY,
            [cert, 'bad'], 1, expect='REJECT bad')
    c = load(cert)
    if len(c['pratt_chunks']) < 2 or len(c['tab_chunks']) < 2 or len(c['pieces']) < 2:
        raise SystemExit('control setup: the SpecialFiveMore certificate has too few chunks')

    def mut(fn, name):
        cc = copy.deepcopy(c)
        fn(cc)
        return write_json(f'{t}/{name}', cc)

    def false_fact(cc):
        cc['tab_chunks'][0][0][2].append([3, 1])   # row 3^2 = 13 in every certificate

    def bad_witness(cc):
        cc['pratt_chunks'][0]['entries'][0][1] = 1

    def wrong_state(cc):
        cc['pieces'][1]['state'] = cc['pieces'][0]['state']
    if c['tab_chunks'][0][0][:2] != [3, 2]:
        raise SystemExit('control setup: the first table row is not 3^2')
    cases = [
        ('wrong tree: a piece recorded at another state', wrong_state, 1),
        ('wrong tree: skeleton refers to a missing piece',
         lambda cc: cc.update(skeleton=['piece', len(cc['pieces'])]), 1),
        ('false table fact (3, 1) for 3^2 = 13', false_fact, 1),
        ('bad Pratt witness 1', bad_witness, 1),
        ('known prime that no earlier chunk certifies',
         lambda cc: cc['pratt_chunks'][0]['known'].append(211), 1),
        ('unknown tag in a piece', lambda cc: cc['pieces'][0]['tree'].__setitem__(0, 'branch'), 2),
        ('surplus field in a stop node',
         lambda cc: first_node(cc['pieces'][0]['tree'], 'stop').append(0), 2),
        ('surplus field in a piece', lambda cc: cc['pieces'][0].update(extra=0), 2),
        ('missing field skeleton', lambda cc: cc.pop('skeleton'), 2),
        ('K = -1', lambda cc: cc.update(K=-1), 2),
        ('K = 12.0', lambda cc: cc.update(K=12.0), 2),
        ('negative prime in a state', lambda cc: cc['pieces'][0]['state'][0].__setitem__(0, -3), 2),
    ]
    for i, (name, fn, want) in enumerate(cases):
        control(f'SpecialFiveMore/replay.py: {name}', SFM_REPLAY, [mut(fn, f'sfm_{i}.json')], want)
    control('SpecialFiveMore/replay.py: unreadable JSON', SFM_REPLAY,
            [truncated(f'{t}/sfm_t.json')], 2)
    control('SpecialFiveMore/replay.py: unknown mode', SFM_REPLAY, [cert, 'trees'], 2)
    control('SpecialFiveMore/replay.py: missing argument', SFM_REPLAY, [], 2)
    control('SpecialFiveMore/replay.py: file not found', SFM_REPLAY, [f'{t}/none.json'], 2)


def main(argv):
    if argv[1:] not in ([], ['--stdlib-only']):
        print('usage: python3 -I scripts/Controls/replay_controls.py [--stdlib-only]',
              file=sys.stderr)
        return 2
    no_asserts()
    with tempfile.TemporaryDirectory() as t:
        defect_tree(t)
        shape_small(t)
        special_five(t, argv[1:] == ['--stdlib-only'])
        special_five_more(t)
    print(f'replay controls: {results["PASS"]} passed, {results["FAIL"]} failed')
    return 1 if results['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
