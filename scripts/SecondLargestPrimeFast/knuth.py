# Untrusted helper script for the OddPerfect Lean library.
# Estimates the number of steps of the search of OddPerfect.SecondLargestPrime for a bound B by
# Knuth's random probes (exact port slp.py); prints the estimate, its standard error and the
# number of probes that met a stuck state. A probe estimate is not a proof that the search closes.
# Used by: no module (measurement only).
# Run: python3 -I knuth.py B PROBES [SEED]
# Requires: Python 3.8 or later, standard library only. Deterministic for a given SEED (default 1);
# minutes for B up to 200 with 200000 probes.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: imports slp.py from the folder of this script; writes only to standard output.
# License: GPL 3, same as the repository.
import sys, os, random, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from slp import *
def usage():
    print('usage: knuth.py B PROBES [SEED] with B >= 1 and PROBES >= 1', file=sys.stderr)
    sys.exit(2)

if len(sys.argv) not in (3, 4): usage()
try:
    B, N = int(sys.argv[1]), int(sys.argv[2])
    seed = int(sys.argv[3]) if len(sys.argv) == 4 else 1
except ValueError:
    usage()
if B < 1 or N < 1: usage()
random.seed(seed)
M = Mof(B); W = 10
ests = []; stuck = 0
for i in range(N):
    s = init(B, 10001)[0]; w = 1; tot = 0
    while True:
        tot += w
        cs = expand(B, M, W, s)
        if cs is None: stuck += 1; break
        if not cs: break
        w *= len(cs); s = random.choice(cs)
    ests.append(tot)
    if (i + 1) % max(1, N // 10) == 0:
        m = sum(ests) / len(ests); sd = math.sqrt(sum((x - m) ** 2 for x in ests) / max(1, len(ests) - 1))
        print('B', B, 'probes', i + 1, 'estimate %.3e' % m, 'stderr %.2e' % (sd / math.sqrt(len(ests))), 'stuck', stuck, flush=True)
