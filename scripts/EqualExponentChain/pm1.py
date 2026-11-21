# Untrusted helper script for the OddPerfect Lean library.
# Helper for gen2.py: the primes below 2 * 10^6 (PR) and a Pollard p - 1 routine.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import math
def primes_upto(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
PR = primes_upto(2*10**6)
def pm1(n, B1=10**6, extra=1):
    a = pow(3, extra, n)
    for p in PR:
        if p > B1: break
        pk = p
        while pk * p <= B1: pk *= p
        a = pow(a, pk, n)
    g = math.gcd(a-1, n)
    return g if 1 < g < n else None
