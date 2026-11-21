# Untrusted helper script for the OddPerfect Lean library.
# For each lower bound m on the smallest prime factor, the number of consecutive primes from
# m needed before the product of p/(p - 1) exceeds 2, and the supports of seven primes at
# least 5 whose product exceeds 2.
# Used by: OddPerfect/SmallPrimes.lean (the bounds L and the counts 7, 15, 27, 41, 62, 85,
# 115 in seven_le_card_of_five_le_minFac .. oneHundredFifteen_le_card_of_twentyThree_le_minFac;
# L is the prime just before the printed prime; the four supports in
# eight_le_card_primeFactors_of_not_three_dvd).
# Run: python3 a.py
# Requires: Python 3 standard library. Running time: about 2 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from pr import primerange, isprime
for m in [3,5,7,11,13,17,19,23]:
    P=F(1); b=0; L=None
    for p in primerange(m,10**5):
        P*=F(p,p-1); b+=1
        if P>2: L=p;break
    print(m,b,L, float(P))
# 7-supports primes>=5 with P>2
ps=list(primerange(5,2000))
res=[]
def rec(start,chosen,P,need):
    if need==0:
        if P>2: res.append(tuple(chosen))
        return
    for i in range(start,len(ps)):
        p=ps[i]
        # max possible: P * prod of next need primes from i
        Q=P
        for j in range(i,i+need): Q*=F(ps[j],ps[j]-1)
        if Q<=2: break
        rec(i+1,chosen+[p],P*F(p,p-1),need-1)
rec(0,[],F(1),7)
print(len(res))
for s in res: print(s, float( __import__('math').prod(F(p,p-1) for p in s)))
