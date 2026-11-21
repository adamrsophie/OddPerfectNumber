# Untrusted helper script for the OddPerfect Lean library.
# Helper for gen.py: probable prime test, Pollard rho and odd prime factors (opf).
# gen.py executes the part of this file before the abundancy function; the rest is an
# earlier tree search.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
import random, math, sys
def isprime(n):
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
        c=random.randrange(1,n);x=y=random.randrange(2,n);d=1
        while d==1:
            x=(x*x+c)%n;y=(y*y+c)%n;y=(y*y+c)%n;d=math.gcd(abs(x-y),n)
        if d!=n: return d
def pf(n):
    if n==1: return []
    if isprime(n): return [n]
    for p in range(2,1000):
        if n%p==0:
            r=[p]
            while n%p==0:n//=p
            return sorted(set(r+pf(n)))
    d=rho(n); return sorted(set(pf(d)+pf(n//d)))
def opf(n): return [p for p in pf(n) if p!=2]
def ab(st):
    r=F(1)
    for p,s in st.items():
        e=2 if s=='O' else 1
        r*=F(sum(p**i for i in range(e+1)),p**e)
    return r
def propagate(st):
    st=dict(st)
    while True:
        if ab(st)>2: return st
        hasS=any(s=='S' for s in st.values())
        cand=[p for p,s in st.items() if s=='U' and (hasS or p%4==3)]
        if not cand: return st
        t=min(cand); st[t]='O'
        for r in opf(t*t+t+1):
            if r not in st: st[r]='U'
def show(st): return ' '.join(f"{p}{'' if s=='U' else ('^2' if s=='O' else '*')}" for p,s in sorted(st.items()))
def search(st,d):
    st=propagate(st)
    a=ab(st)
    if a>2: print('  '*d+'CLOSE '+show(st)+f'  ab={float(a):.5f}'); return
    unk=sorted(p for p,s in st.items() if s=='U')
    if not unk: print('  '*d+'OPEN',show(st)); return
    t=unk[0]
    print('  '*d+f'{t} ordinary:')
    st2=dict(st);st2[t]='O'
    for r in opf(t*t+t+1):
        if r not in st2: st2[r]='U'
    search(st2,d+1)
    print('  '*d+f'{t} special:')
    st3=dict(st);st3[t]='S'
    for r in opf(t+1):
        if r not in st3: st3[r]='U'
    search(st3,d+1)
search({3:'O',13:'U'},0)
