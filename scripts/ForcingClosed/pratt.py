# Untrusted helper script for the OddPerfect Lean library.
# Pratt certificates for the primes given on the command line (entries below 1000 are left
# to trial division).
# Used by: OddPerfect/ForcingClosed.lean (pr_3169, pr_5419, pr_1674289, pr_3348577,
# pr_934415109937, pr_3737657091169).
# Run: python3 pratt.py 3169 5419 1674289 3348577 934415109937 3737657091169
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rows import fac
def cert(p, out, done):
    if p < 1000 or p in done: return
    f = fac(p - 1)
    for r in f: cert(r, out, done)
    fl = [r for r, k in sorted(f.items()) for _ in range(k)]
    a = 2
    while not (pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // r, p) != 1 for r in f)): a += 1
    out.append((p, a, fl)); done.add(p)
for p in map(int, sys.argv[1:]):
    out = []; cert(p, out, set())
    print(p, '[' + ', '.join(f'({x}, {a}, [{", ".join(map(str, fl))}])' for x, a, fl in out) + ']')
