# Untrusted helper script for the OddPerfect Lean library.
# Helper for pratt.py: exact factorization fac, and a table of sigma(p^2) and p + 1 for the
# primes of the forcing tree (printed on import).
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fc import odd_factors, is_prime
def fac(n):
    out = {}
    fs, big = odd_factors(n, 10**40, limit=10**7); assert not big
    m = n
    while m % 2 == 0: out[2] = out.get(2, 0) + 1; m //= 2
    for p in sorted(fs):
        while m % p == 0: out[p] = out.get(p, 0) + 1; m //= p
    assert m == 1; return out
for p in [3,7,13,19,31,61,97,127,181,331,3169,5419,1674289,3348577,934415109937,3737657091169,79,5]:
    print(p, 'row2', p*p+p+1, fac(p*p+p+1), ' q+1:', fac(p+1) if p % 4 == 1 else '')
