# Untrusted helper script for the OddPerfect Lean library.
# Lists the supports {3, p, r, s} of a four prime odd perfect number allowed by the
# abundancy bound, and the pairs (p, r) that leave s unbounded.
# Used by: OddPerfect/OmegaFive.lean (the support ranges in the module docstring and in
# tab5, tab7, tab11, tab13).
# Run: python3 sup.py
# Requires: Python 3 standard library. Running time: about 2 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
from pr import *
P=list(primerange(5,2000))
res=[]
for i,p in enumerate(P):
  for j,r in enumerate(P[i+1:]):
    base=F(3,2)*F(p,p-1)*F(r,r-1)
    if base*F(r+1,r) <= 2: break
    if base*F(r+2,r+1)>2 and False: pass
    # p4 > r
    if base*F(r+1,r) <= 2: continue
    # check unbounded
    if base>2: print("unbounded",p,r); continue
    ss=[s for s in primerange(r+1,10**5) if base*F(s,s-1)>2]
    for s in ss:
      if {p,r,s}>={5,7}: continue
      res.append((p,r,s))
print(len(res))
from collections import Counter
print(Counter((a,b) for a,b,c in res))
