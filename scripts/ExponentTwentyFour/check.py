# Untrusted helper script for the OddPerfect Lean library.
# Exact arithmetic check of the literals of the module: sigma(5^24) and its prime factors
# 11, 71, 101, 251, 401, 9384251; the forced primes 3221, 211, 2221, 6586781, 181, 191, 1361,
# 292661 dividing Phi_5 of their sources, with residues mod 5 and mod 4; the fourteen primes
# distinct and = 1 (mod 5); sigma(3^24) = 121 * 8951 * 391151; the abundancy 57722/28125 of
# 3^4 5^5 11^2.
# Used by: OddPerfect/ExponentTwentyFour.lean (sigma_five_24, sigma_three_24, the p* and d*
# lemmas, the set U and two_lt_abundancy).
# Run: python3 check.py
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
def isp(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
phi5=lambda p:1+p+p**2+p**3+p**4
s5=sum(5**i for i in range(25)); print("sigma(5^24)",s5, s5==(5**25-1)//4)
for r in [11,71,101,251,401,9384251]: print(r, s5%r==0, isp(r), r%5, r%4)
pairs=[(11,3221),(71,211),(71,2221),(251,6586781),(9384251,181),(9384251,191),(211,1361),(211,292661)]
for p,r in pairs: print(p,r,phi5(p)%r==0,isp(r),r%5,p%4)
P=[11,71,101,251,401,9384251,3221,211,2221,6586781,181,191,1361,292661]
print(len(set(P)), all(x%5==1 for x in P))
s3=sum(3**i for i in range(25)); print("sigma(3^24)",s3, s3%11, isp(8951),isp(391151), s3==121*8951*391151)
ab=lambda p,k:F(sum(p**i for i in range(k+1)),p**k)
a=ab(3,4)*ab(5,5)*ab(11,2); print(a, float(a), a>2)
