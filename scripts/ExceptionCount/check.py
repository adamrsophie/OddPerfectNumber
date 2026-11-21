# Untrusted helper script for the OddPerfect Lean library.
# Numbers behind OddPerfect/ExceptionCount.lean: the forcing of small special primes,
# the factorizations of 1 + p + p^2 for the pure prime candidates, the lists of the smallest
# primes at least 5 that are 2 mod 3, and the envelope comparisons.
# Used by: OddPerfect/ExceptionCount.lean (ecL29, ecL31 and the facts quoted in the module
# docstring).
# Run: python3 check.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nt import isprime, factorint
def sq(s): return F(s*s+s+1, s*s)
def C(m): return sq(m)*(1+F(2,13*m))
def H(L):
    r=F(1)
    for x in L: r*=F(x,x-1)
    return r
print([ (q,factorint(q+1)) for q in range(2,200) if isprime(q) and q%12==1])
for p in [59,71,83,107,89,101,113]: print(p,p%12,p*p+p+1,factorint(p*p+p+1))
print(factorint(3542),factorint(5114), isprime(2557), 2557%3)
P2=[p for p in range(5,2000) if isprime(p) and p%3==2]
print(P2[:31], P2[28])
t1=F(2*108,109)/(1+F(2,1000)); t1b=F(2*108,109)/C(1138); t2=F(2*3540,3541)/C(131); t2b=F(2*3540,3541)/(1+F(2,131))
print("t1",t1,"t2",t2)
for n in range(27,34):
    h=H(P2[:n]); print(n,P2[n-1],float(h), h<t1, h<t1b, h<t2, h<t2b)
print(H(P2[:29]))
t13=F(24,13)/C(59); t37=F(72,37)/C(59)
print(t13,t37,H([5,7,11,17,19]),H([5,7,11,13,17]),H([5,7,11,17,19])<t13,H([5,7,11,13,17])<t37)
print(float(t13),float(t37),float(H([5,7,11,17,19,23])),float(H([5,7,11,13,17,19])))
print(1137**2+1137+1, 109**3)
