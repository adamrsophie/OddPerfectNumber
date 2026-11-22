# Untrusted helper script for the OddPerfect Lean library.
# Runs the full search of OddPerfect.SecondLargestPrime (exact port slp.py) for a bound B until
# the stack is empty (closes), a state is stuck, or MAXNODES steps; prints progress every 10^6
# steps and a RESULT line with steps, kinds of steps, number of K step chunks and the total
# size of the chunk stacks as Lean text. Used for the reach record of the bound.
# Used by: no module (measurement only).
# Run: python3 -I reach.py B [LO] [W] [K] [MAXNODES]   (defaults 10001 10 500 unlimited)
# Requires: Python 3.8 or later, standard library only. Deterministic; about 45 microseconds per
# step (B = 72: 5 seconds; B = 100: 3 minutes; B = 110: 48 minutes).
# Untrusted: every result is checked again by the Lean kernel.
# Paths: imports slp.py from the folder of this script; writes only to standard output.
# License: GPL 3, same as the repository.
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slp import *
B = int(sys.argv[1]); LO = int(sys.argv[2]) if len(sys.argv) > 2 else 10001
W = int(sys.argv[3]) if len(sys.argv) > 3 else 10
K = int(sys.argv[4]) if len(sys.argv) > 4 else 500
MAXN = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 12
M = Mof(B)
R = init(B, LO)[::-1]
stats = {}; nodes = 0; t0 = time.time(); chars = 0; chunks = 0; maxstack = 0; res = 'limit'
while True:
    if nodes % K == 0:
        chunks += 1; chars += len(fmt_stack(R[::-1]))
    if not R: res = 'closes'; break
    if nodes >= MAXN: break
    s = R.pop()
    cs = expand(B, M, W, s, stats)
    nodes += 1
    if cs is None: res = 'stuck'; break
    R.extend(reversed(cs)); maxstack = max(maxstack, len(R))
    if nodes % 1000000 == 0:
        print('PROGRESS nodes', nodes, 'stack', len(R), 'time', round(time.time() - t0), stats, flush=True)
print('RESULT B', B, 'LO', LO, 'W', W, res, 'nodes', nodes, 'kinds', stats, 'chunksK', chunks,
      'chars', chars, 'maxstack', maxstack, 'cpu', round(time.process_time(), 1), flush=True)
# exit status 0 only when the search closes; `limit` and `stuck` are not closure
sys.exit(0 if res == 'closes' else 1)
