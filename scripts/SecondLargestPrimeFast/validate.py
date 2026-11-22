# Untrusted helper script for the OddPerfect Lean library.
# Checks that slp.py reproduces every chunk of the B = 72 certificate exactly: it reads the
# stacks of the data modules REPO/OddPerfect/<PREFIX>1.lean .. <PREFIX>9.lean and recomputes
# each 500 step chunk from the previous stack. It fails (exit status 1) unless every run statement
# has the expected bound, modulus, window and fuel, the runs are numbered consecutively from 0,
# consecutive stacks are linked, the first stack is the initial one and the last stack is empty. The stacks of the former modules
# SecondLargestPrimeData1 .. 9 were computed by running SLP.run in Lean; they agreed exactly.
# Used by: checking slp.py (not needed to generate a module).
# Run: python3 -I validate.py REPO [PREFIX]   (PREFIX defaults to SecondLargestPrimeFastData)
# Requires: Python 3.8 or later, standard library only. Deterministic; about 5 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: imports slp.py from the folder of this script; reads REPO/OddPerfect only.
# License: GPL 3, same as the repository.
import re, sys, time, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slp import *


def fail(msg):
    print('FAIL:', msg)
    sys.exit(1)


if len(sys.argv) < 2:
    print('usage: python3 -I validate.py REPO [PREFIX]'); sys.exit(2)
R = sys.argv[1].rstrip('/') + '/OddPerfect/'
PRE = sys.argv[2] if len(sys.argv) > 2 else 'SecondLargestPrimeFastData'
B, W, K = 72, 10, 500
M = Mof(B)
stacks = []
for m in range(1, 10):
    txt = open(f'{R}{PRE}{m}.lean').read()
    defs = dict(re.findall(r'def (\w+) : List State :=\n  (.*)\n', txt))
    runs = re.findall(r'theorem run(\d+) : (\w+) (\d+) (\d+) (\d+) (\d+) (\w+) = some (\w+) :=', txt)
    # every run statement must have the expected shape: none may be skipped
    if len(runs) != len(re.findall(r'theorem run\d+\b', txt)): fail(f'module {m}: malformed run statement')
    for i, fn, b, mod, w, k, a, c in runs:
        if fn not in ('run', 'runF'): fail(f'run{i}: unknown function {fn}')
        if (int(b), int(mod), int(w), int(k)) != (B, M, W, K): fail(f'run{i}: wrong bound, modulus, window or fuel')
        if a not in defs or c not in defs: fail(f'run{i}: unknown stack name')
        if not stacks: stacks.append(defs[a])
        if int(i) != len(stacks) - 1: fail(f'run{i}: expected run{len(stacks) - 1}')
        if stacks[-1] != defs[a]: fail(f'run{i}: stack not linked to the previous run')
        stacks.append(defs[c])
print('chunks', len(stacks) - 1)
if not stacks: fail('no run statement found')
if fmt_stack(init(B, 10001)) != stacks[0]: fail('the first stack is not the initial stack')
L = init(B, 10001); stats = {}
t = time.time()
for i in range(len(stacks) - 1):
    L = run(B, M, W, K, L, stats)
    if L is None: fail(f'chunk {i}: the search is stuck')
    if fmt_stack(L) != stacks[i + 1]: fail(f'chunk {i} differs')
if L: fail(f'unfinished: {len(L)} states left after the last chunk')
print('all chunks reproduced, final stack empty', stats, sum(stats.values()), 'time', time.time() - t)
