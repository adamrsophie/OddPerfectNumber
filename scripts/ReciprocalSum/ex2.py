# Untrusted helper script for the OddPerfect Lean library.
# Rational upper bounds a_p >= log(p/(p - 1)) - 1/p for p in {3, 5, 7, 11, 13, 17, 19}
# from a truncated series, rounded up to seven decimals, and the resulting lower bound.
# Used by: OddPerfect/ReciprocalSum.lean (721327/10000000, 28933/1250000, 44017/10000000,
# 1561/500000, 18017/10000000, 359/250000 in twentythree_fortieths_lt_sum_inv and its
# lemmas).
# Run: python3 ex2.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
from math import log, ceil
def ser(x,n): return sum(x**(i+1)/(i+1) for i in range(n))
def up(x,n): return ser(x,n)+x**(n+1)/(1-x)
tot=F(0)
for p,n in [(3,12),(5,7),(7,6),(11,5),(13,4),(17,4),(19,4)]:
    x=F(1,p); b=up(x,n)-x
    a=F(ceil(b*10**7),10**7)
    print(p,n, a, float(a)-(-log(1-1/p)-1/p))
    if p!=7: tot+=a
L=F(6931471803,10**10)
print('lower', float(L-tot-F(1,84)))
