# Untrusted helper script for the OddPerfect Lean library.
# Factoring with PARI under a time limit.
# Used by: nt.py and gen.py when cypari2 is installed.
# Run: imported, not run directly.
# Requires: cypari2 and cysignals.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""PARI based factoring with a time limit (used when cypari2 is available)."""
import cypari2
from cysignals.signals import AlarmInterrupt
pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 9, silent=True)

def pfactor(n, secs):
    """(dict prime -> mult, unfactored cofactor) using PARI within roughly secs seconds."""
    try:
        m = pari('alarm(%d, factor(%d))' % (secs, n))
        fs = {int(p): int(e) for p, e in zip(m[0], m[1])}
        return fs, 1
    except AlarmInterrupt:
        pass
    m = pari('factor(%d, 10^7)' % n)
    fs, cof = {}, 1
    for p, e in zip(m[0], m[1]):
        p, e = int(p), int(e)
        if pari('ispseudoprime(%d)' % p): fs[p] = fs.get(p, 0) + e
        else: cof *= p ** e
    return fs, cof

def isprime(n): return bool(pari('isprime(%d)' % n))
