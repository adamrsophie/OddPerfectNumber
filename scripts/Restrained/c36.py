# Untrusted helper script for the OddPerfect Lean library.
# Exact search for x and t with sigma(x^2) = 3 m or sigma(t^2) = m below 10^24, m
# supported on the known primes, for the two leaves with one free slot.
# Used by: OddPerfect/Restrained.lean (the root lists given to ok in box_13_19_t,
# box_13_19_x, box_61_31_t, box_61_31_x).
# Run: python3 c36.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from nt import isprime
from math import isqrt
def gen(gens,caps,B):
    out=[]
    def rec(i,V,es):
        if i==len(gens): out.append((V,tuple(es))); return
        e=0;W=V
        while W<B and (caps[i] is None or e<=caps[i]):
            rec(i+1,W,es+[e]); W*=gens[i]; e+=1
    rec(0,1,[]); return out
def roots(Vs,mult=1):
    r=[]
    for V,es in Vs:
        W=mult*V; t=isqrt(W)
        if t*t+t+1==W: r.append((t,isprime(t),t%3,es))
    return r
B=10**24
print("C3 x:",roots(gen([7,13,19],[1,None,None],B),3))
print("C3 t:",roots(gen([7,13,19],[1,None,None],B)))
print("C6 x:",roots(gen([13,31,61],[1,None,None],B),3))
print("C6 t:",roots(gen([13,31,61],[1,None,None],B)))
