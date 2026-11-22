# Untrusted helper script for the OddPerfect Lean library.
# Checks that slp.py reproduces every chunk of the B = 72 certificate exactly: it reads the
# stacks of the data modules REPO/OddPerfect/<PREFIX>1.lean .. <PREFIX>9.lean and recomputes
# each 500 step chunk from the previous stack. The stacks of the former modules
# SecondLargestPrimeData1 .. 9 were computed by running SLP.run in Lean; they agreed exactly.
# Used by: checking slp.py (not needed to generate a module).
# Run: python3 -I validate.py REPO [PREFIX]   (PREFIX defaults to SecondLargestPrimeFastData)
# Requires: Python 3.8 or later, standard library only. Deterministic; about 5 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: imports slp.py from the folder of this script; reads REPO/OddPerfect only.
# License: GPL 3, same as the repository.
import re, sys, time, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slp import *
R = sys.argv[1].rstrip('/') + '/OddPerfect/'
stacks = []
PRE = sys.argv[2] if len(sys.argv) > 2 else 'SecondLargestPrimeFastData'
for m in range(1, 10):
    txt = open(f'{R}{PRE}{m}.lean').read()
    defs = dict(re.findall(r'def (\w+) : List State :=\n  (.*)\n', txt))
    runs = re.findall(r'theorem run(\d+) : runF? 72 \d+ 10 500 (\w+) = some (\w+)', txt)
    for i, a, b in runs:
        if not stacks: stacks.append(defs[a])
        assert stacks[-1] == defs[a], (m, i)
        stacks.append(defs[b])
print('chunks', len(stacks) - 1)
B, W, K = 72, 10, 500
M = Mof(B)
assert fmt_stack(init(B, 10001)) == stacks[0]
L = init(B, 10001); stats = {}
t = time.time()
for i in range(len(stacks) - 1):
    L = run(B, M, W, K, L, stats)
    assert fmt_stack(L) == stacks[i + 1], i
print('all chunks reproduced', stats, sum(stats.values()), 'time', time.time() - t)
