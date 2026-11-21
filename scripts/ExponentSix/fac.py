# Untrusted helper script for the OddPerfect Lean library.
# Factor table for exponent six: breadth first from 7, factors sigma(p^6) and prints the
# prime factors with their residues mod 4. The forcing chains of the Lean proof were chosen
# by hand from these factorizations; the branches starting at 3 and 263 use the same
# factor function.
# Used by: OddPerfect/ExponentSix.lean (the chains in the module docstring).
# Run: python3 fac.py STEPS, for example python3 fac.py 12
# Requires: Python 3 standard library. Running time: under a second for 12 steps.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import random, math, sys
def isp(n):
    if n<2: return False
    for p in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def rho(n):
    if n%2==0: return 2
    while True:
        c=random.randrange(1,n);f=lambda x:(x*x+c)%n
        x=y=random.randrange(2,n);d=1
        while d==1:
            x=f(x);y=f(f(y));d=math.gcd(abs(x-y),n)
        if d!=n: return d
def factor(n,lim=None):
    out=[]
    for p in range(2,10000):
        while n%p==0: out.append(p);n//=p
    st=[n] if n>1 else []
    while st:
        m=st.pop()
        if isp(m): out.append(m);continue
        d=rho(m);st+= [d,m//d]
    return sorted(out)
def s6(p): return (p**7-1)//(p-1)
if __name__=='__main__':
    seen={7};queue=[7]
    for _ in range(int(sys.argv[1])):
        p=queue.pop(0)
        fs=factor(s6(p))
        print(p, p%4, p%7, fs, [f%4 for f in fs])
        for f in fs:
            if f not in seen: seen.add(f);queue.append(f)
        queue.sort()
