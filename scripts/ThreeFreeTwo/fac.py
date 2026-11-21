# Untrusted helper script for the OddPerfect Lean library.
# Helper: sieve factorization of x^2 + x + 1 for x up to X. explore.py and genlean.py
# execute this file.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys
def primes_upto(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
def factor_table(X):
    # factor x^2+x+1 for x<=X via sieving primes l=1 mod 3 up to X
    vals=[x*x+x+1 for x in range(X+1)]
    fac=[dict() for _ in range(X+1)]
    for l in primes_upto(X):
        if l==3:
            roots=[1]
        elif l%3!=1: continue
        else:
            # find roots of x^2+x+1 mod l
            roots=[]
            # cube root of unity: g^((l-1)/3)
            for g in range(2,l):
                w=pow(g,(l-1)//3,l)
                if w!=1: break
            roots=[w,(w*w)%l]
        for r0 in roots:
            for x in range(r0,X+1,l):
                while vals[x]%l==0:
                    vals[x]//=l; fac[x][l]=fac[x].get(l,0)+1
    for x in range(X+1):
        if vals[x]>1: fac[x][vals[x]]=fac[x].get(vals[x],0)+1
    return fac
