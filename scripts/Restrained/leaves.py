# Untrusted helper script for the OddPerfect Lean library.
# Parameters of the three closed leaves with the 3 adic budget spent (C4, C7, C9): checks
# alpha^4 g >= 1, beta^4 B >= 1, evaluates the abundancy bound and lists the t with
# sigma(t^2) < B supported on the four generators.
# Used by: OddPerfect/Restrained.lean (B, the four alpha arguments and beta in the calls of
# close_leaf for the three leaves, set as constants in this script and checked here; the
# printed roots, with 0 added, are the ok lists of the three leaves).
# Run: python3 leaves.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from nt import isprime
from fractions import Fraction as F
from math import isqrt
def fv(p,e=2): return F(sum(p**i for i in range(e+1)),p**e)
def sols(gens,caps,B):
    out=[]
    def rec(i,V,es):
        if i==len(gens):
            t=isqrt(V)
            if t*t+t+1==V: out.append((t,isprime(t),t%3,tuple(es)))
            return
        e=0;W=V
        while W<B and (caps[i] is None or e<=caps[i]):
            rec(i+1,W,es+[e]); W*=gens[i]; e+=1
    rec(0,1,[]); return out
def check(name,known,gens,caps,alphas,B,beta,extra=F(1)):
    for g,a in zip(gens,alphas): assert a**4*g>=1,(g,a)
    assert beta**4*B>=1
    C=F(1)
    for (p,kind) in known:
        C*= fv(p) if kind=='sq' else F(p,p-1)
    P=F(1)
    for a in alphas: P*=1/(1-a)
    S=beta*P
    tot=C*extra/(1-2*S)
    print(name,float(C),float(extra),float(S),float(tot),tot<2, sols(gens,caps,B))
check("C4",[(3,'sq'),(7,'sq'),(19,'sq'),(13,'q'),(127,'q')],[7,19,13,127],[1,1,None,None],[F(13,20),F(12,25),F(53,100),F(3,10)],10**16,F(1,10**4),fv(107))
check("C7",[(3,'sq'),(13,'sq'),(31,'sq'),(61,'q'),(331,'q')],[13,31,61,331],[1,1,None,None],[F(53,100),F(43,100),F(9,25),F(6,25)],10**12,F(1,10**3))
check("C9",[(3,'sq'),(13,'sq'),(61,'sq'),(97,'q'),(7,'q')],[13,61,97,7],[0,1,None,None],[F(53,100),F(9,25),F(8,25),F(13,20)],10**12,F(1,10**3))
# abundant divisors
print(fv(3)*fv(7)*fv(11)*fv(13,1)*fv(19), fv(3)*fv(5)*fv(13)*fv(31)*fv(61,1))
print(float(fv(3)*fv(7)*fv(11)*fv(13,1)*fv(19)), float(fv(3)*fv(5)*fv(13)*fv(31)*fv(61,1)))
