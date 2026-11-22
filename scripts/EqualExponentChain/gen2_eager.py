# Untrusted helper script for the OddPerfect Lean library.
# The search of gen2.py with one change: in the first branch of every split (the case in
# which the new prime is the special prime), the search starts in eager mode (all divisors
# m of the current modulus and the expo steps), where gen2.py starts with m = 2 only and
# turns eager mode on when no safe candidate is left. With this change the certificates
# certs/cert_5.json and certs/cert_7.json are reproduced byte for byte; for larger l the
# Pollard rho steps start at random points, so a rerun matches a stored tree only by chance
# (see the README). The special trees have no split, so they are the same with both scripts.
# Used by: OddPerfect/EqualExponentChain.lean (pc5 .. pc29, ord5 .. ord29, spec5 .. spec29).
# Build the helper first: cc -O2 -o osearch osearch.c (or set OSEARCH to its path).
# Run: python3 gen2_eager.py L ord|spec   writes tree_L_ord.json or tree_L_spec.json
#      python3 gen2.py L merge           joins the two trees into cert_L.json
#      python3 gen2_eager.py L           writes cert_L.json in one run
# Requires: Python 3 standard library and a C compiler. Running time: seconds for
# l = 5 to 13; up to about ten CPU minutes per part for l = 17 to 29.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""gen2.py with eager mode at the start of the first branch of every split."""
import sys
import os
import json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen2

_solve = gen2.solve


def solve(l, known, qs, ex, M, maxknown, done_expo=(), depth=0, eager=False):
    # The recursive calls inside gen2.solve resolve to this function. A call with a
    # special prime below the root is the first branch of a split.
    if qs is not None and depth > 0:
        eager = True
    return _solve(l, known, qs, ex, M, maxknown, done_expo, depth, eager)


gen2.solve = solve

if __name__ == '__main__':
    l = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] in ('ord', 'spec'):
        gen2.part(l, sys.argv[2])
    elif len(sys.argv) > 2 and sys.argv[2] == 'merge':
        gen2.merge(l)
    else:
        cert = gen2.main(l)
        with open(f'cert_{l}.json', 'w') as f:
            json.dump(cert, f)
