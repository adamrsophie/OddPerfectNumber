# Untrusted helper script for the OddPerfect Lean library.
# Helper: trial division primality test and prime ranges.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

def isprime(n):
    if n<2: return False
    d=2
    while d*d<=n:
        if n%d==0: return False
        d+=1
    return True
def primerange(a,b): return [p for p in range(a,b) if isprime(p)]
