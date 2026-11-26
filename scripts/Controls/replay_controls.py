#!/usr/bin/env python3
# Untrusted helper script for the OddPerfect Lean library.
# Permanent controls for the replay and generator helpers DefectTree/ (check.py, search.py,
# gen.py, with the shared loader certio.py), ShapeSmall/ (replay.py, gen.py), SpecialFive/
# (replay.py, stage1.py, gen.py), SpecialFiveMore/ (replay.py, gen.py) and the factor list checks
# of Pratt/gen.py: every archived valid input must pass with exit status 0,
# and each mutated input must be rejected with the expected nonzero status (1: a well formed
# input fails a check; 2: malformed input, a usage error or an unreadable file; 3: a search
# that closed on facts that fail validation; 4: a replay or a search root left undecided),
# with no Python traceback. The helpers run as subprocesses with `sys.executable -I -B`, in
# normal and in optimized (-O) mode, so a check written as an `assert` would show up as a
# failure. The root admission of DefectTree/search.py from 2 ^ 32 on (an 87 bit prime, a forged
# witness, a strong pseudoprime, a nested factoring timeout) is controlled in defect_tree_root.
# SpecialFive and SpecialFiveMore keep no certificate in the repository: the controls build
# them in a temporary folder (SpecialFive/gen.py 24, whose certificate and Lean module must
# equal the published ones, and SpecialFiveMore/gen.py 12 with small chunks). The partial rows
# of DefectTree (marked in the field partial of the row table), the factoring deadlines of
# DefectTree/search.py (rows and p - 1) and the stuck count of SpecialFive/stage1.py are controlled
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
SF_GEN = os.path.join(SF, 'gen.py')
SFM_GEN = os.path.join(SFM, 'gen.py')
DT_IO = os.path.join(DT, 'certio.py')
PRATT_GEN = os.path.join(SC, 'Pratt', 'gen.py')
HARDENED = [DT_CHECK, DT_SEARCH, DT_GEN, DT_IO, SS_REPLAY, SS_GEN, SF_REPLAY, SF_STAGE1, SF_GEN,
            SFM_REPLAY, SFM_GEN, PRATT_GEN]

# Loads a stand in for sympy, then runs the script given after the mode with the remaining
# arguments. Modes: both (factorint of 13 sleeps, also with a limit), first (it sleeps only
# without a limit), empty (factorint finds no factor at all), pm1 (factorint of 330 = 331 - 1
# sleeps), plain (trial division, nothing sleeps), row (the full factorization of
# sigma(88741^10) sleeps, the one with a limit finds only 89), sleep (every factorint sleeps).
DRIVER = '''import runpy, sys, time, types
mode, script = sys.argv[1], sys.argv[2]
def factorint(n, limit=None):
    if mode == 'empty':
        return {}
    if mode == 'row' and n == sum(88741 ** i for i in range(11)):
        if limit is not None:
            return {89: 1}
        while True:
            time.sleep(1)
    if mode == 'sleep' or (mode == 'both' and n == 13) or (mode == 'first' and n == 13 and limit is None) or \\
            (mode == 'pm1' and n == 330):
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
    def set_row(dd, key, facts):
        for row in dd['rows']:
            if row[:2] == key:
                row[2] = facts
    control('DefectTree/check.py: a row that does not multiply back (3^2 = 13 with no fact)',
            DT_CHECK, ['cert2.json', rows_with(lambda dd: set_row(dd, [3, 2], []),
                                               'dt_mb.json')], 1, cwd=DT, expect='multiply back')
    control('DefectTree/check.py: a landed partial row with a fact removed (88741^10, unused)',
            DT_CHECK, ['cert2.json', rows_with(lambda dd: set_row(dd, [88741, 10], []),
                                               'dt_mb2.json')], 1, cwd=DT, expect='multiply back')
    control('DefectTree/check.py: a false fact (89, 2) in an unused row', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: set_row(dd, [88741, 10], [[89, 2]]),
                                     'dt_mb3.json')], 1, cwd=DT, expect='not an odd prime power')
    control('DefectTree/check.py: the certificate uses a row marked partial', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd.update(partial=[[3, 2]]), 'dt_mk.json')], 1,
            cwd=DT, expect='marked partial')
    control('DefectTree/check.py accepts a mark on an unused row', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd.update(partial=[[88741, 10]]),
                                     'dt_mk2.json')], 0, cwd=DT, expect='accepted')
    control('DefectTree/check.py: a partial entry that is no row', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd.update(partial=[[3, 1000]]), 'dt_mk3.json')], 2,
            cwd=DT)
    control('DefectTree/check.py: a partial field that is not a list', DT_CHECK,
            ['cert2.json', rows_with(lambda dd: dd.update(partial=True), 'dt_mk4.json')], 2,
            cwd=DT)
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
                expect='the factorization with a limit is complete',
                after=lambda: same([(out, os.path.join(DT, 'cert2.json')), (rows, DT_ROWS)]))
        write_json(rows, d32)
        control('DefectTree/search.py: a partial row is marked in the row table (stand in)',
                driver, ['both', DT_SEARCH, '2', '0', '3', '3', 'none', rows, out,
                         'factor_seconds=1'], 1, modes=(mode,), cwd=t, timeout=30,
                after=lambda: None if load(rows).get('partial') == [[3, 2]] else
                'no mark partial [[3, 2]] in the row table')
        marked = copy.deepcopy(d)
        marked['partial'] = [[3, 2]]
        write_json(rows, marked)
        control('DefectTree/search.py factors a marked row again and drops the mark (stand in)',
                driver, ['plain', DT_SEARCH, '2', '0', '3', '3', 'none', rows, out], 0,
                modes=(mode,), cwd=t, timeout=60,
                after=lambda: same([(out, os.path.join(DT, 'cert2.json')), (rows, DT_ROWS)]))
        no88741 = copy.deepcopy(d)
        no88741['rows'] = [r for r in no88741['rows'] if r[:2] != [88741, 10]]
        write_json(rows, no88741)
        control('DefectTree/search.py: the tree closes but uses a partial row (stand in)',
                driver, ['row', DT_SEARCH, '31', '1', '17', '17', '5', rows, out,
                         'factor_seconds=1'], 1, modes=(mode,), cwd=t, timeout=60,
                expect='not complete',
                after=lambda: same([(out, os.path.join(DT, 'cert_excess6_17.json'))]) or
                (None if load(rows).get('partial') == [[88741, 10]] else
                 'no mark partial [[88741, 10]] in the row table'))
        no331 = copy.deepcopy(d)
        no331['pm1'].pop('331')
        write_json(rows, no331)
        control('DefectTree/search.py: the factorization of 331 - 1 times out (stand in)',
                driver, ['pm1', DT_SEARCH, '2', '0', '3', '3', 'none', rows, out,
                         'factor_seconds=1'], 1, modes=(mode,), cwd=t, timeout=30,
                expect='PARTIAL pm1 331 factor_seconds 1 nothing stored',
                after=lambda: None if '331' not in load(rows)['pm1'] else
                'a factorization of 330 was stored')
    control('DefectTree/search.py: factor_seconds=0', DT_SEARCH,
            ['2', '0', '3', '3', 'none', f'{t}/dt_r0.json', f'{t}/dt_o0.json',
             'factor_seconds=0'], 2, cwd=t)
    control('DefectTree/search.py: missing argument', DT_SEARCH, ['2', '0', '3'], 2, cwd=t)
    base = ['2', '0', '3', '3', 'none', f'{t}/dt_r0.json', f'{t}/dt_o0.json']
    for name, i, val in (('negative K', 0, '-1'), ('K = 2.5', 0, '2.5'), ('negative W', 1, '-1'),
                         ('U = 2', 2, '2'), ('U = 0', 2, '0'), ('ROOT = 9 (not prime)', 3, '9'),
                         ('ROOT = 0', 3, '0'), ('negative CAP', 4, '-1'), ('CAP = x', 4, 'x')):
        control(f'DefectTree/search.py: {name}', DT_SEARCH, base[:i] + [val] + base[i + 1:], 2,
                cwd=t)
    for opt in ('maxnodes=0', 'maxexp=1', 'maxnodes=-5', 'factor_seconds=1.5', 'nodes=3'):
        control(f'DefectTree/search.py: option {opt}', DT_SEARCH, base + [opt], 2, cwd=t)
    control('DefectTree/search.py: repeated option', DT_SEARCH,
            base + ['maxexp=8', 'maxexp=9'], 2, cwd=t)
    for name, fn in (
            ('a row that does not multiply back (3^2 = 13 with no fact)',
             lambda dd: [r.__setitem__(2, []) for r in dd['rows'] if r[:2] == [3, 2]]),
            ('a factorization of 330 given as 2 3 5 13',
             lambda dd: dd['pm1'].update({'331': [2, 3, 5, 13]})),
            ('a partial entry that is no row', lambda dd: dd.update(partial=[[3]]))):
        control(f'DefectTree/search.py: row table with {name}', DT_SEARCH,
                base[:5] + [rows_with(fn, 'dt_rbad.json'), f'{t}/dt_o2.json'], 2, cwd=t)
    control('DefectTree/search.py: unreadable row table', DT_SEARCH,
            ['2', '0', '3', '3', 'none', truncated(f'{t}/dt_rtrunc.json'), f'{t}/dt_o1.json'], 2,
            cwd=t)

    # gen.py: its output for the two small certificates must stay byte equal; every new
    # rejection ends before a file is written.
    for k, name, mod in (('2', 'Two', 'DefectTreeTwoData'), ('4', 'Four', 'DefectTreeFourData')):
        out = f'{t}/{mod}.lean'
        control(f'DefectTree/gen.py writes {mod}.lean byte for byte', DT_GEN,
                [f'cert{k}.json', 'rows.json', name, out], 0, cwd=DT,
                after=lambda: same([(out, os.path.join(LIB, f'{mod}.lean'))]))
    control('DefectTree/gen.py corrupt writes the control module', DT_GEN,
            ['cert2.json', 'rows.json', 'Bad', f'{t}/dt_bad.lean', 'corrupt'], 0, cwd=DT,
            expect='wrote')
    out = f'{t}/dt_gen.lean'

    def nothing_written():
        return f'{out} was written' if os.path.exists(out) else None

    def tiny(kid, sp=None, ch=None):
        return {'params': {'K': 2, 'w': 0, 'u': 3, 'root': 3, 'cap': None}, 'rows': [],
                'cert': {'t': 'br', 'r': 3, 'sp': sp,
                         'ch': ch or [{'t': 'high', 'kid': kid}]}}
    budget = {'t': 'budget'}
    gen_cases = [
        ('the certificate uses a row marked partial', 'cert2.json',
         rows_with(lambda dd: dd.update(partial=[[3, 2]]), 'dt_gmk.json'), [], 1),
        ('a row that does not multiply back (3^2 = 13 with no fact)', 'cert2.json',
         rows_with(lambda dd: set_row(dd, [3, 2], []), 'dt_gmb.json'), [], 1),
        ('a factorization of 330 given as 2 3 5 13', 'cert2.json',
         rows_with(lambda dd: dd['pm1'].update({'331': [2, 3, 5, 13]}), 'dt_gpr.json'), [], 1),
        ('no factorization of 330', 'cert2.json',
         rows_with(lambda dd: dd['pm1'].pop('331'), 'dt_gpr2.json'), [], 1),
        ('an open leaf', write_json(f'{t}/dt_gopen.json', tiny({'t': 'open'})), DT_ROWS, [], 1),
        ('a chain item high that is not the last',
         write_json(f'{t}/dt_ghigh.json', tiny(None, ch=[{'t': 'high', 'kid': budget},
                                                         {'t': 'ord', 'kid': budget}])),
         DT_ROWS, [], 1),
        ('corrupt without a capacity leaf', write_json(f'{t}/dt_gnocap.json', tiny(budget)),
         DT_ROWS, ['corrupt'], 1),
        ('split: a special child of the branch on 3',
         write_json(f'{t}/dt_gsp.json', tiny(budget, sp=budget)), DT_ROWS,
         ['split', 'gnodes=1'], 1),
        ('an unknown leaf tag', write_json(f'{t}/dt_gtag.json', tiny({'t': 'bogus'})), DT_ROWS,
         [], 2),
        ('a partial entry that is no row', 'cert2.json',
         rows_with(lambda dd: dd.update(partial=[[3, 1000]]), 'dt_gmk2.json'), [], 2),
        ('a capacity leaf without its prime',
         write_json(f'{t}/dt_gcap.json', tiny({'t': 'cap'})), DT_ROWS, [], 2),
        ('unreadable JSON', truncated(f'{t}/dt_gtrunc.json'), DT_ROWS, [], 2),
        ('corrupt together with split', 'cert2.json', 'rows.json', ['corrupt', 'split'], 2),
        ('gnodes=0', 'cert2.json', 'rows.json', ['split', 'gnodes=0'], 2),
        ('pmods=-1', 'cert2.json', 'rows.json', ['split', 'pmods=-1'], 2),
        ('tper=x', 'cert2.json', 'rows.json', ['split', 'tper=x'], 2),
        ('unknown flag', 'cert2.json', 'rows.json', ['splitt'], 2),
    ]
    for name, cert, rows_, flags, want in gen_cases:
        control(f'DefectTree/gen.py: {name}', DT_GEN, [cert, rows_, 'X', out] + flags, want,
                cwd=DT, after=nothing_written)
    control('DefectTree/gen.py: a name with a dash', DT_GEN,
            ['cert2.json', 'rows.json', 'X-1', out], 2, cwd=DT, after=nothing_written)
    control('DefectTree/gen.py: an output name without .lean', DT_GEN,
            ['cert2.json', 'rows.json', 'X', f'{t}/dt_gen.txt'], 2, cwd=DT)
    control('DefectTree/gen.py: missing argument', DT_GEN, ['cert2.json', 'rows.json', 'X'], 2,
            cwd=DT)


def defect_tree_three(t):
    """Controls of the third hardening pass of DefectTree (and Pratt/gen.py): each repaired
    defect has a negative control next to a positive one."""
    T = f'{t}/h3'
    os.makedirs(T, exist_ok=True)
    driver = f'{t}/driver.py'
    with open(driver, 'w') as f:
        f.write(DRIVER)
    d = load(DT_ROWS)

    def row(key):
        return next(r for r in d['rows'] if r[:2] == key)

    def nothing(path):
        return lambda: f'{path} was written' if os.path.exists(path) else None

    def contains(path, frag):
        def check():
            with open(path) as f:
                return None if frag in f.read() else f'{os.path.basename(path)} lacks {frag!r}'
        return check

    # 1. The root prime 211 needs Pratt data (brHead at the root tests isPr), in search and gen.
    r211 = [row([211, 2])]
    c211 = {'params': {'K': 0, 'w': 0, 'u': 212, 'root': 211, 'cap': 0}, 'rows': [[211, 2]],
            'cert': {'t': 'br', 'r': 211, 'sp': None,
                     'ch': [{'t': 'ord', 'kid': {'t': 'small', 'r': 3}},
                            {'t': 'high', 'kid': {'t': 'budget'}}]}}
    cert211 = write_json(f'{T}/c211.json', c211)
    rows_pm = write_json(f'{T}/r211_pm.json', {'rows': r211, 'pm1': {'211': [2, 3, 5, 7]}})
    rows_no = write_json(f'{T}/r211_no.json', {'rows': r211, 'pm1': {}})
    rows_s, out_s = f'{T}/r211_s.json', f'{T}/c211_s.json'
    for mode in ('', '-O'):
        write_json(rows_s, {'rows': r211, 'pm1': {}})
        control('DefectTree/search.py stores Pratt data for the root prime 211 (stand in)',
                driver, ['plain', DT_SEARCH, '0', '0', '212', '211', '0', rows_s, out_s], 0,
                modes=(mode,), cwd=t, timeout=60,
                after=lambda: None if load(rows_s)['pm1'].get('211') == [2, 3, 5, 7] and
                load(out_s) == c211 else 'no factorization of 210 stored, or another tree')
    control('DefectTree/check.py accepts the root 211 with its Pratt data', DT_CHECK,
            [cert211, rows_pm], 0, cwd=t, expect='accepted')
    control('DefectTree/check.py: the root 211 without Pratt data', DT_CHECK,
            [cert211, rows_no], 1, cwd=t, expect='first rejected node')
    g1 = f'{T}/g211.lean'
    control('DefectTree/gen.py writes the Pratt entry of the root prime 211', DT_GEN,
            [cert211, rows_pm, 'R', g1], 0, cwd=t, after=contains(g1, '(211, 2, [2, 3, 5, 7])'))
    g1n = f'{T}/g211n.lean'
    control('DefectTree/gen.py: the root 211 without Pratt data', DT_GEN,
            [cert211, rows_no, 'R', g1n], 1, cwd=t, expect='no factorization of 211 - 1',
            after=nothing(g1n))

    # 2. The factor list of p - 1: integers above 1, prime, product p - 1; bounded witness.
    r71 = row([71, 4])         # facts 5, 11, 211, 2221
    pm = {str(q): d['pm1'][str(q)] for q, _ in r71[2] if q >= 200 and q != 211}
    cert71 = write_json(f'{T}/c71.json', {
        'params': {'K': 0, 'w': 0, 'u': 3, 'root': 71, 'cap': 0}, 'rows': [[71, 4]],
        'cert': {'t': 'br', 'r': 71, 'sp': None, 'ch': [{'t': 'high', 'kid': {'t': 'budget'}}]}})
    for name, f211, want in (('the factors 2 3 5 7 of 210', [2, 3, 5, 7], 0),
                             ('an extra factor 1 in the factors of 210', [1, 2, 3, 5, 7], 1),
                             ('the factor true in the factors of 210', [2, 3, 5, 7, True], 2),
                             ('the composite factor 105 of 210', [2, 105], 1),
                             ('the factor 0 of 210', [0, 2, 3, 5, 7], 1)):
        rp = write_json(f'{T}/r71_{len(f211)}_{f211[-1]}.json',
                        {'rows': [r71], 'pm1': dict(pm, **{'211': f211})})
        g = f'{T}/g71_{want}_{len(f211)}.lean'
        control(f'DefectTree/gen.py: {name}', DT_GEN, [cert71, rp, 'X', g], want, cwd=t,
                timeout=30, after=contains(g, '(211, 2, [2, 3, 5, 7])') if want == 0 else
                nothing(g))
    one = copy.deepcopy(d)
    one['pm1']['331'] = [1, 2, 3, 5, 11]
    one_p = write_json(f'{T}/r331_one.json', one)
    control('DefectTree/check.py: an extra factor 1 in the factors of 330', DT_CHECK,
            ['cert2.json', one_p], 1, cwd=DT, timeout=60, expect='not certified')
    control('DefectTree/search.py: row table with an extra factor 1 in the factors of 330',
            DT_SEARCH, ['2', '0', '3', '3', 'none', one_p, f'{T}/o331.json'], 2, cwd=t)
    for name, args, want, frag in (('a prime', ['4294967291'], 0, '(4294967291, '),
                                   ('the composite 1000001', ['1000001'], 1, 'rejected'),
                                   ('an argument that is no number', ['x'], 2, None)):
        control(f'Pratt/gen.py: {name}', PRATT_GEN, args, want, cwd=t, timeout=30, expect=frag)

    # 3. Many split parts (tper=1): the joined list is built without recursion; the landed
    # options still give the 36 library files byte for byte.
    def same_folder(folder, n):
        def check():
            names = sorted(os.listdir(folder))
            if len(names) != n:
                return f'{len(names)} files, expected {n}'
            return same([(os.path.join(folder, x), os.path.join(LIB, x)) for x in names])
        return check
    for mode in ('', '-O'):
        o = f'{T}/e73{mode}'
        os.makedirs(o, exist_ok=True)
        control('DefectTree/gen.py split writes ExcessSevenData3 (36 files) byte for byte',
                DT_GEN, ['cert_excess7_3.json', 'rows.json', 'Excess7R3',
                         f'{o}/ExcessSevenData3.lean', 'split', 'gnodes=600', 'pmods=5',
                         'tper=75', 'tmods=4'], 0, modes=(mode,), cwd=DT, timeout=120,
                after=same_folder(o, 36))
    o1 = f'{T}/e73one'
    os.makedirs(o1, exist_ok=True)
    control('DefectTree/gen.py split tper=1 (1012 table parts) on cert_excess7_3.json', DT_GEN,
            ['cert_excess7_3.json', 'rows.json', 'E', f'{o1}/E.lean', 'split', 'gnodes=600',
             'tper=1'], 0, cwd=DT, timeout=120,
            after=contains(f'{o1}/ET.lean', 'def tabE : Tab := tabE_0 ++ (tabE_1 ++ (tabE_2 ++ ('))

    # 4. One strict loader: exact types, natural numbers, closed fields and tags.
    c2 = load(os.path.join(DT, 'cert2.json'))
    schema = [('fractional K = 2.75', lambda c: c['params'].update(K=2.75)),
              ('K = true', lambda c: c['params'].update(K=True)),
              ('negative K', lambda c: c['params'].update(K=-1)),
              ('surplus field in params', lambda c: c['params'].update(extra=0)),
              ('missing field cap', lambda c: c['params'].pop('cap')),
              ('unknown chain tag', lambda c: c['cert']['ch'][0].update(t='bogus')),
              ('list valued node tag', lambda c: c['cert']['ch'][0]['kid'].update(t=['cap'])),
              ('surplus top level field', lambda c: c.update(extra=0))]
    for i, (name, fn) in enumerate(schema):
        cc = copy.deepcopy(c2)
        fn(cc)
        bad = write_json(f'{T}/schema{i}.json', cc)
        g = f'{T}/schema{i}.lean'
        control(f'DefectTree/gen.py: {name}', DT_GEN, [bad, DT_ROWS, 'X', g], 2, cwd=t,
                expect='malformed input', after=nothing(g))
        if i in (0, 3, 6, 7):
            control(f'DefectTree/check.py: {name}', DT_CHECK, [bad, DT_ROWS], 2, cwd=t,
                    expect='malformed input')
    with open(DT_ROWS) as f:
        text = f.read()
    dup = f'{T}/r_dupkey.json'
    with open(dup, 'w') as f:
        f.write(text.replace('"pm1": {', '"pm1": {"331": [2, 3, 5, 11], ', 1))
    for name, rows_ in (
            ('a boolean in a factorization of p - 1',
             write_json(f'{T}/r_bool.json', dict(d, pm1=dict(d['pm1'], **{'331': [2, 3, 5, 11,
                                                                                  True]})))),
            ('a repeated row', write_json(f'{T}/r_dup.json', dict(d, rows=d['rows'] +
                                                                  [d['rows'][0]]))),
            ('a pm1 key with a leading zero',
             write_json(f'{T}/r_lead.json', dict(d, pm1=dict(d['pm1'], **{'0331': [2, 3, 5, 11]})))),
            ('a repeated JSON key', dup)):
        control(f'DefectTree/search.py: row table with {name}', DT_SEARCH,
                ['2', '0', '3', '3', 'none', rows_, f'{T}/o_schema.json'], 2, cwd=t,
                expect='malformed input')
        control(f'DefectTree/check.py: row table with {name}', DT_CHECK, ['cert2.json', rows_],
                2, cwd=DT, expect='malformed input')

    # 5. check.py corrupt must change the certificate.
    control('DefectTree/check.py corrupt: no capacity leaf, no mutation possible', DT_CHECK,
            [cert211, rows_pm, 'corrupt'], 3, cwd=t, expect='no mutation possible')

    # 6. Resuming a marked row merges: the landed row 88741^10 keeps its factor 89.
    marked = copy.deepcopy(d)
    marked['partial'] = [[88741, 10]]
    rows6, out6 = f'{T}/r6.json', f'{T}/c6.json'
    for mode in ('', '-O'):
        write_json(rows6, marked)
        control('DefectTree/search.py: a resumed marked row keeps its factor (89, 1) (stand in '
                'finds nothing)', driver, ['empty', DT_SEARCH, '31', '1', '17', '17', '5', rows6,
                                           out6, 'factor_seconds=1'], 1, modes=(mode,), cwd=t,
                timeout=120, expect='not complete',
                after=lambda: same([(out6, os.path.join(DT, 'cert_excess6_17.json'))]) or
                (None if row_of(load(rows6), [88741, 10]) == [[89, 1]] and
                 load(rows6).get('partial') == [[88741, 10]] else 'the row lost its factor'))
        false = copy.deepcopy(marked)
        for r in false['rows']:
            if r[:2] == [88741, 10]:
                r[2] = [[89, 2]]
        write_json(rows6, false)
        control('DefectTree/search.py: a resumed marked row with the false fact (89, 2)',
                driver, ['empty', DT_SEARCH, '31', '1', '17', '17', '5', rows6, out6,
                         'factor_seconds=1'], 2, modes=(mode,), cwd=t, timeout=120,
                expect='do not divide')

    # 9. gen.py writes all files under temporary names before any rename.
    for mode in ('', '-O'):
        for kind, want in (('a folder in place of XT.lean', 1), ('old files', 0)):
            o = f'{T}/w{mode}{want}'
            os.makedirs(o, exist_ok=True)
            for x in ('X.lean', 'XP.lean'):
                with open(f'{o}/{x}', 'w') as f:
                    f.write('old\n')
            if want:
                os.makedirs(f'{o}/XT.lean', exist_ok=True)
            else:
                with open(f'{o}/XT.lean', 'w') as f:
                    f.write('old\n')

            def kept(o=o, want=want):
                if sorted(os.listdir(o)) != ['X.lean', 'XP.lean', 'XT.lean']:
                    return f'files in the folder: {sorted(os.listdir(o))}'
                with open(f'{o}/XP.lean') as f:
                    old = f.read() == 'old\n'
                return None if old == bool(want) else 'XP.lean ' + ('changed' if want else
                                                                    'not written')
            control(f'DefectTree/gen.py split with {kind}', DT_GEN,
                    ['cert2.json', 'rows.json', 'X', f'{o}/X.lean', 'split'], want,
                    modes=(mode,), cwd=DT, after=kept)


def defect_tree_four(t):
    """Controls of the fourth hardening pass of DefectTree: one negative control per repaired
    defect, and the positive control that the root 211 still closes and validates."""
    T = f'{t}/h4'
    os.makedirs(T, exist_ok=True)
    driver = f'{t}/driver.py'
    with open(driver, 'w') as f:
        f.write(DRIVER)
    d = load(DT_ROWS)

    def row(key):
        return next(r for r in d['rows'] if r[:2] == key)

    def nothing(*paths):
        return lambda: next((f'{x} was written' for x in paths if os.path.exists(x)), None)

    def br(r, ch):
        return {'t': 'br', 'r': r, 'sp': None, 'ch': ch}
    small3 = {'t': 'ord', 'kid': {'t': 'small', 'r': 3}}
    high_budget = {'t': 'high', 'kid': {'t': 'budget'}}

    # Positive: the root 211 still closes, validates, and stores the witness 2 of 210.
    c211 = {'params': {'K': 0, 'w': 0, 'u': 212, 'root': 211, 'cap': 0}, 'rows': [[211, 2]],
            'cert': br(211, [small3, high_budget])}
    rows_s, out_s = f'{T}/r211.json', f'{T}/c211.json'
    for mode in ('', '-O'):
        write_json(rows_s, {'rows': [row([211, 2])], 'pm1': {}})
        control('DefectTree/search.py: the root 211 still succeeds (closed and validated, '
                'witness stored)', driver, ['plain', DT_SEARCH, '0', '0', '212', '211', '0',
                                            rows_s, out_s], 0, modes=(mode,), cwd=t,
                timeout=60, expect='closed and validated',
                after=lambda: None if load(out_s) == c211 and
                load(rows_s).get('witness') == {'211': 2} else 'another tree or no witness')
    control('DefectTree/check.py accepts the root 211 with its stored witness', DT_CHECK,
            [out_s, rows_s], 0, cwd=t, expect='accepted')
    g = f'{T}/g211.lean'
    control('DefectTree/gen.py accepts the root 211 with its stored witness', DT_GEN,
            [out_s, rows_s, 'R', g], 0, cwd=t, expect='wrote')
    bad_w = write_json(f'{T}/r211_w4.json', {'rows': [row([211, 2])],
                                             'pm1': {'211': [2, 3, 5, 7]}, 'witness': {'211': 4}})
    control('DefectTree/check.py: the stored witness 4 of 211 fails (a square)', DT_CHECK,
            [out_s, bad_w], 1, cwd=t, expect='first rejected node')
    g = f'{T}/g211_w4.lean'
    control('DefectTree/gen.py: the stored witness 4 of 211 fails', DT_GEN,
            [out_s, bad_w, 'R', g], 1, cwd=t, expect='stored Pratt witness', after=nothing(g))
    control('DefectTree/check.py: a witness for a prime without pm1 entry', DT_CHECK,
            [out_s, write_json(f'{T}/r211_w9.json', {'rows': [row([211, 2])], 'pm1': {},
                                                      'witness': {'211': 2}})], 2, cwd=t,
            expect='malformed input')

    # 1 to 3: facts that fail validation leave the search raw closed, exit 3, nothing written.
    c67 = write_json(f'{T}/c67.json', {
        'params': {'K': 0, 'w': 0, 'u': 200, 'root': 67, 'cap': 0}, 'rows': [[67, 2]],
        'cert': br(67, [small3, high_budget])})
    r67 = write_json(f'{T}/r67.json', {'rows': [[67, 2, [[3, 1], [7, 1], [7, 1], [31, 1]]]],
                                       'pm1': {}})
    cases = [
        ('a composite fact 121 in the row 3^4 = 121 (cache row)',
         {'rows': [row([3, 2]), [3, 4, [[121, 1]]]], 'pm1': {}},
         ['0', '0', '200', '3', '1'], 'not prime by trial division'),
        ('the prime 7 in two entries of the row 67^2', None,
         ['0', '0', '200', '67', '0'], 'lists a prime in two entries'),
        ('211 - 1 factored as 6 5 7', {'rows': [row([211, 2])], 'pm1': {'211': [6, 5, 7]}},
         ['0', '0', '212', '211', '0'], 'the root prime: 6 is below 200')]
    for i, (name, table, args, frag) in enumerate(cases):
        for mode in ('', '-O'):
            rows_i, out_i = f'{T}/rv{i}{mode}.json', f'{T}/cv{i}{mode}.json'
            write_json(rows_i, table) if table else shutil.copyfile(r67, rows_i)
            control(f'DefectTree/search.py: {name} is raw closed, not validated', DT_SEARCH,
                    args + [rows_i, out_i, 'noledger'], 3, modes=(mode,), cwd=t,
                    expect=frag, after=nothing(out_i))
    g = f'{T}/g67.lean'
    control('DefectTree/gen.py: the prime 7 in two entries of the row 67^2', DT_GEN,
            [c67, r67, 'X', g], 1, cwd=t, expect='two entries', after=nothing(g))

    # 4. The strong pseudoprime 3215031751 = 151 * 751 * 28351 (bases 2, 3, 5, 7) as the root.
    big = 3215031751
    pm_big = {str(big): [2, 3, 3, 3, 3, 5, 5, 5, 7, 37, 613], '613': [2, 2, 3, 3, 17]}
    c_big = write_json(f'{T}/c_big.json', {
        'params': {'K': 0, 'w': 0, 'u': 3, 'root': big, 'cap': 0}, 'rows': [],
        'cert': br(big, [{'t': 'ord', 'kid': {'t': 'budget'}}, high_budget])})
    control('DefectTree/check.py: the pseudoprime 3215031751 without a witness is undecided',
            DT_CHECK, [c_big, write_json(f'{T}/r_big.json', {'rows': [], 'pm1': pm_big})], 4,
            cwd=t, timeout=30, expect='undecided')
    control('DefectTree/check.py: the pseudoprime 3215031751 with the witness 2 is rejected',
            DT_CHECK, [c_big, write_json(f'{T}/r_bigw.json', {'rows': [], 'pm1': pm_big,
                                                              'witness': {str(big): 2}})], 1,
            cwd=t, timeout=30, expect='first rejected node')
    # 4b. The composite 318665857834031151167461 = 399165290221 * 798330580441 passes the
    # prefilter certio.composite and has a complete factorization of p - 1 (each factor from 200
    # on with its own): the witness scan of gen.py stops at LEGACY_SCAN, undecided.
    huge = 318665857834031151167461
    pm_huge = {str(huge): [2, 2, 3, 3, 3, 5, 11, 17, 474349721, 6652754837],
               '474349721': [2, 2, 2, 5, 13, 912211], '6652754837': [2, 2, 7, 13, 18276799],
               '912211': [2, 3, 5, 13, 2339], '18276799': [2, 3, 3046133], '2339': [2, 7, 167],
               '3046133': [2, 2, 761533], '761533': [2, 2, 3, 17, 3733], '3733': [2, 2, 3, 311],
               '311': [2, 5, 31]}
    c_huge = write_json(f'{T}/c_huge.json', {
        'params': {'K': 0, 'w': 0, 'u': 3, 'root': huge, 'cap': 0}, 'rows': [],
        'cert': br(huge, [{'t': 'ord', 'kid': {'t': 'budget'}}, high_budget])})
    g = f'{T}/g_huge.lean'
    control('DefectTree/gen.py: the composite 318665857834031151167461 without a witness is '
            'undecided', DT_GEN, [c_huge, write_json(f'{T}/r_huge.json', {
                'rows': [], 'pm1': pm_huge}), 'X', g], 1, cwd=t, timeout=30,
            expect='no Pratt witness found below 10000', after=nothing(g))
    control('DefectTree/gen.py: the composite 318665857834031151167461 with the witness 2 is '
            'rejected', DT_GEN, [c_huge, write_json(f'{T}/r_hugew.json', {
                'rows': [], 'pm1': pm_huge, 'witness': {str(huge): 2}}), 'X', g], 1, cwd=t,
            timeout=30, expect='stored Pratt witness 2', after=nothing(g))

    # 5. ROWS and OUT the same file: by path, through a symbolic link, through a hard link.
    for kind in ('the same path', 'a symbolic link', 'a hard link'):
        for mode in ('', '-O'):
            rows5 = f'{T}/r5_{kind[2:5]}{mode}.json'
            out5 = rows5 if kind == 'the same path' else f'{T}/o5_{kind[2:5]}{mode}.json'
            shutil.copyfile(DT_ROWS, rows5)
            if kind == 'a symbolic link':
                os.symlink(rows5, out5)
            elif kind == 'a hard link':
                os.link(rows5, out5)
            control(f'DefectTree/search.py: OUT is {kind} to ROWS', DT_SEARCH,
                    ['2', '0', '3', '3', 'none', rows5, out5], 2, modes=(mode,), cwd=t,
                    expect='name the same file', after=lambda r=rows5: same([(r, DT_ROWS)]))

    # 6. A chain that is empty or has only ordinary entries: gen writes nothing.
    ord_budget = {'t': 'ord', 'kid': {'t': 'budget'}}
    for name, ch in (('an empty chain', []), ('a chain with only an ordinary entry', [ord_budget])):
        c6 = write_json(f'{T}/c6_{len(ch)}.json', {
            'params': {'K': 2, 'w': 0, 'u': 3, 'root': 3, 'cap': None}, 'rows': [],
            'cert': br(3, ch)})
        g = f'{T}/g6_{len(ch)}.lean'
        control(f'DefectTree/gen.py: {name}', DT_GEN, [c6, DT_ROWS, 'X', g], 1, cwd=t,
                expect='does not end with an item high', after=nothing(g))

    # 7. Decimal strings of 5000 digits: malformed input or usage, exit 2, no traceback.
    long_ = '1' * 5000
    r7 = write_json(f'{T}/r7.json', dict(d, pm1=dict(d['pm1'], **{long_: [2]})))
    control('DefectTree/check.py: a pm1 key of 5000 digits', DT_CHECK, ['cert2.json', r7], 2,
            cwd=DT, expect='malformed input')
    g = f'{T}/g7.lean'
    control('DefectTree/gen.py: a pm1 key of 5000 digits', DT_GEN, ['cert2.json', r7, 'X', g],
            2, cwd=DT, expect='malformed input', after=nothing(g))
    control('DefectTree/search.py: a pm1 key of 5000 digits', DT_SEARCH,
            ['2', '0', '3', '3', 'none', r7, f'{T}/o7.json'], 2, cwd=t,
            expect='malformed input', after=nothing(f'{T}/o7.json'))
    control('DefectTree/search.py: K of 5000 digits', DT_SEARCH,
            [long_, '0', '3', '3', 'none', f'{T}/r7k.json', f'{T}/o7k.json'], 2, cwd=t)
    control('DefectTree/gen.py: gnodes of 5000 digits', DT_GEN,
            ['cert2.json', 'rows.json', 'X', g, 'split', 'gnodes=' + long_], 2, cwd=DT,
            after=nothing(g))
    big_row = write_json(f'{T}/r7b.json', dict(d, rows=d['rows'] + [[10 ** 3000 + 1, 2, []]]))
    control('DefectTree/check.py: an unused row of 6001 digits that does not multiply back',
            DT_CHECK, ['cert2.json', big_row], 1, cwd=DT, expect='bits) and the row is not')

    # 8. The node budget is enforced: maxnodes=1 expands the root only.
    rows8 = f'{T}/r8.json'
    shutil.copyfile(DT_ROWS, rows8)
    control('DefectTree/search.py: maxnodes=1 reports one node', DT_SEARCH,
            ['2', '0', '3', '3', 'none', rows8, f'{T}/o8.json', 'maxnodes=1'], 1, cwd=t,
            expect="nodes 1 stats {'br': 1} open 1")


def defect_tree_root(t):
    """Controls of the root admission of DefectTree/search.py from 2 ^ 32 on: a root is admitted
    only by its exact Pratt certificate, missing data is searched under the factoring deadline,
    and every failure or UNKNOWN exit leaves the existing ROWS and OUT byte for byte unchanged."""
    T = f'{t}/root'
    os.makedirs(T, exist_ok=True)
    driver = f'{t}/driver.py'
    with open(driver, 'w') as f:
        f.write(DRIVER)
    p87 = 140194179307171898833699259
    pm87 = {'809': [2, 2, 2, 101], '2887': [2, 3, 13, 37], '6473': [2, 2, 2, 809],
            '28871': [2, 5, 2887], '346453': [2, 2, 3, 28871], '2304389': [2, 2, 89, 6473],
            '22223351': [2, 5, 5, 19, 149, 157],
            '13568242433': [2, 2, 2, 2, 2, 2, 2, 2, 23, 2304389],
            str(p87): [2, 11, 61, 346453, 22223351, 13568242433]}
    wit87 = {'809': 3, '2887': 5, '6473': 3, '28871': 13, '346453': 2, '2304389': 2,
             '22223351': 19, '13568242433': 3, str(p87): 2}
    old = b'previous certificate\n'

    def prepared(name, table):
        rows_, out_ = f'{T}/r_{name}.json', f'{T}/o_{name}.json'
        write_json(rows_, table)
        with open(out_, 'wb') as f:
            f.write(old)
        return rows_, out_

    def unchanged(rows_, out_, table):
        def check():
            with open(out_, 'rb') as f:
                if f.read() != old or \
                        sha(rows_) != hashlib.sha256(json.dumps(table).encode()).hexdigest():
                    return 'an existing output file changed'
            left = [x for x in os.listdir(T) if x.endswith('.tmp')]
            return f'temporary files left: {left}' if left else None
        return check

    budget = ['maxnodes=1', 'factor_seconds=1']
    for mode in ('', '-O'):
        # 1. The 87 bit prime, maxnodes=1 factor_seconds=1: bounded in both dispositions.
        table = {'rows': [], 'pm1': {}}
        rows_, out_ = prepared('87sleep', table)
        control('DefectTree/search.py: the 87 bit prime root, factoring of p - 1 times out '
                '(stand in): UNKNOWN', driver, ['sleep', DT_SEARCH, '2', '0', '3', str(p87),
                                                'none', rows_, out_] + budget, 4,
                modes=(mode,), cwd=t, timeout=30, expect='UNKNOWN: the root prime',
                after=unchanged(rows_, out_, table))
        table = {'rows': [], 'pm1': pm87, 'witness': wit87}
        rows_, out_ = prepared('87data', table)
        control('DefectTree/search.py: the 87 bit prime root with its Pratt data is admitted, '
                'one node', DT_SEARCH, ['2', '0', '3', str(p87), 'none', rows_, out_] + budget,
                1, modes=(mode,), cwd=t, timeout=30, expect="nodes 1 stats {'br': 1} open 1",
                after=lambda r=rows_: None if load(r) == {'rows': [], 'pm1': pm87,
                                                          'witness': wit87} else
                'the row table changed')
        # 2. A forged certificate for the prime: the stored witness 4 (a square) fails.
        table = {'rows': [], 'pm1': pm87, 'witness': dict(wit87, **{str(p87): 4})}
        rows_, out_ = prepared('87forged', table)
        control('DefectTree/search.py: the 87 bit prime root with a forged witness is rejected',
                DT_SEARCH, ['2', '0', '3', str(p87), 'none', rows_, out_] + budget, 3,
                modes=(mode,), cwd=t, timeout=30, expect='stored Pratt witness 4',
                after=unchanged(rows_, out_, table))
        # 3. The composite 318665857834031151167461 passes the Miller and Rabin bases 2 to 37;
        # with a complete factorization of p - 1 it stays undecided, never admitted.
        huge = 318665857834031151167461
        table = {'rows': [], 'pm1': {
            str(huge): [2, 2, 3, 3, 3, 5, 11, 17, 474349721, 6652754837],
            '474349721': [2, 2, 2, 5, 13, 912211], '6652754837': [2, 2, 7, 13, 18276799],
            '912211': [2, 3, 5, 13, 2339], '18276799': [2, 3, 3046133], '2339': [2, 7, 167],
            '3046133': [2, 2, 761533], '761533': [2, 2, 3, 17, 3733],
            '3733': [2, 2, 3, 311], '311': [2, 5, 31]}}
        rows_, out_ = prepared('huge', table)
        control('DefectTree/search.py: the strong pseudoprime 318665857834031151167461 as root '
                'is UNKNOWN, not admitted', DT_SEARCH, ['2', '0', '3', str(huge), 'none', rows_,
                                                         out_] + budget, 4,
                modes=(mode,), cwd=t, timeout=30, expect='undecided',
                after=unchanged(rows_, out_, table))
        table = {'rows': [], 'pm1': {}}
        rows_, out_ = prepared('fermat', table)
        control('DefectTree/search.py: the root 2 ^ 32 + 1 is proven composite (usage error)',
                DT_SEARCH, ['2', '0', '3', str(2 ** 32 + 1), 'none', rows_, out_] + budget, 2,
                modes=(mode,), cwd=t, timeout=30, expect='proves it composite',
                after=unchanged(rows_, out_, table))
        # 4. A nested timeout: 4295069903 - 1 = 2 * 31 * 47 * 61 * 73 * 331 is factored, the
        # factorization of 330 sleeps; ROWS and OUT stay unchanged, the checkpoint keeps it.
        table = {'rows': [], 'pm1': {}}
        rows_, out_ = prepared(f'nested{mode}', table)
        disc = rows_ + '.discovery.json'
        control('DefectTree/search.py: a nested factoring timeout leaves the files unchanged '
                '(stand in)', driver, ['pm1', DT_SEARCH, '2', '0', '3', '4295069903', 'none',
                                       rows_, out_] + budget, 4, modes=(mode,), cwd=t,
                timeout=30, expect='PARTIAL pm1 331',
                after=lambda r=rows_, o=out_, tb=table, dc=disc: unchanged(r, o, tb)() or (
                    None if os.path.exists(dc) and load(dc)['pm1'] ==
                    {'4295069903': [2, 31, 47, 61, 73, 331]} else
                    'no discovery checkpoint with the factorization of 4295069902'))


def row_of(dd, key):
    return next((r[2] for r in dd['rows'] if r[:2] == key), None)


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
        ('no_sol_2 applies chk2_0 at i - 1, its rewrite uses i - 0',
         'chk_sound _ _ chk2_0 (i - 0)', 'chk_sound _ _ chk2_0 (i - 1)'),
        ('no_sol_2 excludes p <= 31 only, prime_le_2 proves p <= 64',
         '(hB : p ≤ 64) :\n    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 2 + 1)',
         '(hB : p ≤ 31) :\n    2 * t ^ 2 ≠ 1 + ∑ i ∈ range (2 * 2 + 1)'),
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
    names = ['SpecialFive/gen.py 24 and replay.py', 'SpecialFive/stage1.py',
             'SpecialFive/gen.py 1']
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
    control('SpecialFive/gen.py 1: no chain with two exponents, nothing written', SF_GEN,
            ['1', f'{t}/sf1'], 1, expect='nothing written',
            after=lambda: f'{t}/sf1 was written' if os.path.exists(f'{t}/sf1') else None)


def special_five_args(t):
    """Arguments of SpecialFive/gen.py (checked before sympy is imported)."""
    for name, args in (('K = 0', ['0', f'{t}/sfa']), ('K = -1', ['-1', f'{t}/sfa']),
                       ('K = x', ['x', f'{t}/sfa']), ('missing argument', ['24']),
                       ('surplus argument', ['24', f'{t}/sfa', '1'])):
        control(f'SpecialFive/gen.py: {name}', SF_GEN, args, 2)


def special_five_more(t):
    for k, why in (('1', 'no chain with two exponents'), ('2', 'Pratt certificate is empty')):
        o = f'{t}/sfm{k}'
        control(f'SpecialFiveMore/gen.py {k}: {why}, nothing written', SFM_GEN, [k, o], 1,
                expect=why, after=lambda: f'{o} was written' if os.path.exists(o) else None)
    for name, args in (('K = 0', ['0', f'{t}/sfma']), ('K = -1', ['-1', f'{t}/sfma']),
                       ('PRATT_CHUNK = 0', ['12', f'{t}/sfma', '0']),
                       ('TREE_CAP = 1.5', ['12', f'{t}/sfma', '40', '30', '20', '1.5']),
                       ('missing argument', ['12']),
                       ('surplus argument', ['12', f'{t}/sfma', '1', '1', '1', '1', '1'])):
        control(f'SpecialFiveMore/gen.py: {name}', SFM_GEN, args, 2)
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
        ('module manifest names only a piece that does not exist',
         lambda cc: cc.update(modules=[[len(cc['pieces'])]]), 1),
        ('module manifest omits the last piece', lambda cc: cc['modules'][-1].pop(), 1),
        ('a piece in two modules', lambda cc: cc['modules'][0].append(cc['modules'][-1][0]), 1),
        ('an empty module', lambda cc: cc['modules'].append([]), 1),
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
        defect_tree_three(t)
        defect_tree_four(t)
        defect_tree_root(t)
        shape_small(t)
        special_five(t, argv[1:] == ['--stdlib-only'])
        special_five_args(t)
        special_five_more(t)
    print(f'replay controls: {results["PASS"]} passed, {results["FAIL"]} failed')
    return 1 if results['FAIL'] else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
