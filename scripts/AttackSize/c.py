# Untrusted helper script for the OddPerfect Lean library.
# The bound 2 * 12 * 59 / (13 * 61) = 1416/793 and the partial products of p/(p - 1)
# over the primes 2 mod 3 (and over 5, 7, 11, 13, 17), showing where they pass the bound;
# then the pure prime candidates p = 11 mod 12 with 1 + p + p^2 a prime power.
# Used by: OddPerfect/AttackSize.lean (1416/793 and the sets {5, 11, ..., 89} and
# {5, 7, 11, 13}).
# Run: python3 c.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
from util import *
bound=F(2*12*59,13*61); print(bound, float(bound))
ps=[p for p in primes(5,200) if p%3==2]
P=F(1)
for i,p in enumerate(ps[:14]):
    P*=F(p,p-1); print(i+1,p,float(P), P<bound)
P=F(1)
for i,p in enumerate([5,7,11,13,17]):
    P*=F(p,p-1); print(i+1,p,float(P),P<bound)
# q-pure squares candidates p = 11 mod 12 up to 10^6
for p in primes(5,10**6):
    if p%12!=11: continue
    f=factor(p*p+p+1)
    if len(f)==1:
        (qq,a),=f.items()
        if qq%12==1: print('pure',p,qq,a); 
        if p>5000: break
