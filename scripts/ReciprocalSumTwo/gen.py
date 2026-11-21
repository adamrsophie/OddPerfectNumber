# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of the rational check of lt_sum_inv_of_check: for the cutoffs B = 101 and
# B = 1009 it prints the number of odd primes below B, the margin by which
# log2 - (sum of u(p) over L, minus u(7)) - 1/(4(B - 2)) exceeds the target t (29/50 and
# 581/1000), whether u(7) <= u(5) <= u(3), and the prime lists L.
# Used by: OddPerfect/ReciprocalSumTwo.lean (the lists L in twentynine_fiftieths_lt_sum_inv and
# sum_inv_gt_581_div_1000; the trial divisor bounds K = 11 and 32 there are not printed, they are
# the least integers above the square roots of the cutoffs).
# Run: python3 gen.py
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
from fractions import Fraction as F
import sys
def primes(B): return [p for p in range(3,B) if all(p%d for d in range(2,p))]
def u(p):
    x=F(1,p); return sum(x**(i+2)/(i+2) for i in range(11)) + x**13/(1-x)
l2=F(6931471803,10**10)
for B,t in [(101,F(29,50)),(1009,F(581,1000))]:
    L=primes(B); s=sum(u(p) for p in L)-u(7)
    lb=l2-s-F(1,4*(B-2))
    print(B,len(L),float(lb),float(lb-t), lb>t, u(7)<=u(5)<=u(3))
    print(L)
print("L101 :=", "[" + ", ".join(map(str, primes(101))) + "]")
print("L1009 :=", "[" + ", ".join(map(str, primes(1009))) + "]")
