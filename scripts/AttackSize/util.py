# Untrusted helper script for the OddPerfect Lean library.
# Helper: trial division primality test, factorization and prime ranges.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
def factor(n):
    f={};i=2
    while i*i<=n:
        while n%i==0: f[i]=f.get(i,0)+1; n//=i
        i+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def primes(a,b): return [p for p in range(a,b) if isprime(p)]
