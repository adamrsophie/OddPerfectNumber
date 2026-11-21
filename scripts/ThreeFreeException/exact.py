# Untrusted helper script for the OddPerfect Lean library.
# Exact value of the box product and the geometric tail bound for the two cases of the
# one exception theorem, for box sizes M = 4, 5, 6.
# Used by: OddPerfect/ThreeFreeException.lean (boxProd 13 31 5 5 <= 1717/1000 and
# boxProd 13 7 17 5 <= 1450/1000, with alpha = 5/18 and beta = 2/11 or 5/13).
# Run: python3 exact.py
# Prints, per M, (total bound, number of pairs, box product, tail) for each case.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as Fr
from math import isqrt
def f(s): return Fr(s*s+s+1,s*s)
def run(Q,R,fl,M,al,be,A1,c=Fr(2)):
    assert al*al*Q>=1 and be*be*R>=1
    box=Fr(1); n=0
    for a in range(M):
        for b in range(M):
            if a%2==0 and b%2==0: continue
            box*=f(max(fl,isqrt(Q**a*R**b))); n+=1
    tail=c*(al**M+be**M)/((1-al)*(1-be))
    tot=A1*box/(1-tail)
    return float(tot), n, float(box), float(tail)
for M in [4,5,6]:
  print(M, run(13,31,5,M,Fr(5,18),Fr(2,11),Fr(13,12)*Fr(31,30)), run(13,7,17,M,Fr(5,18),Fr(5,13),Fr(13,12)*Fr(7,6)))
