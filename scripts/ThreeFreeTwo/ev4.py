# Untrusted helper script for the OddPerfect Lean library.
# Helper for gen.py (step 2): leaf evaluation for the two exception theorem: admissible
# small ordinary primes, box sums and the abundancy bound per pair of classes. Reads feas.pkl
# from the current folder. gen.py executes the part before the main block.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import pickle, itertools, math
from fractions import Fraction as Fr
out=pickle.load(open('feas.pkl','rb'))
fac=dict(out)
PR=[p for p,_ in out]
def fq(s): return Fr(s*s+s+1,s*s)
def ratalpha(R):
    # smallest-ish rational a/b >= 1/sqrt(R) with b<=40, minimizing value
    best=None
    for b in range(1,41):
        a=math.isqrt(b*b//R) 
        while a*a*R<b*b: a+=1
        x=Fr(a,b)
        if best is None or x<best: best=x
    return best
# spec: ('e',v) explicit ; ('n2',) r%3==2, r>=11 ; ('big',B) r%3==1 r>=B ; extra constraints list of ('ne',val)
def compat(x,spec):
    k=spec[0]
    if k=='e': return x==spec[1]
    if k=='n2': return False
    if k=='big': return x%3==1 and x>=spec[1] and x not in spec[2]
def V(s,s1,s2,qcon):
    f=fac.get(s)
    if f is None: return False
    for sp in (s1,s2):
        if sp[0]=='e' and sp[1]==s: return False
    items=list(f.items())
    for roles in itertools.product('qbc',repeat=len(items)):
        if len(set(roles))<len(roles): continue
        ok=True
        for (x,e),ro in zip(items,roles):
            if ro=='q':
                if x%12!=1 or not qcon(x): ok=False
                for sp in (s1,s2):
                    if sp[0]=='e' and sp[1]==x: ok=False
            elif ro=='b':
                if not compat(x,s1): ok=False
            else:
                if not compat(x,s2): ok=False
        if ok: return True
    return False
def Rof(sp):
    k=sp[0]
    if k=='e': return sp[1] if sp[1]%3==1 else None
    if k=='n2': return None
    return sp[1]
def rhoof(sp):
    k=sp[0]
    if k=='e': return Fr(sp[1],sp[1]-1)
    if k=='n2': return Fr(11,10)
    return Fr(sp[1],sp[1]-1)
def boxsum(al,be,ga,cap,M):
    tot=Fr(0)
    for a in range(M):
     for b in range(M):
      for c in range(M):
        if a%2==0 and b%2==0 and c%2==0: continue
        w=al**a*be**b*ga**c
        tot+=min(Fr(1,cap),w)
    T=(al**M+be**M+ga**M)/((1-al)*(1-be)*(1-ga))
    return tot,T
def leaf(s1,s2,cap,M,qcon=lambda x:True,forced_out=(),show=False):
    C=[s for s in PR if s<cap and s not in forced_out and V(s,s1,s2,qcon)]
    pc=Fr(1)
    for s in C: pc*=fq(s)
    R1,R2=Rof(s1),Rof(s2)
    al=ratalpha(13); be=ratalpha(R1) if R1 else Fr(0); ga=ratalpha(R2) if R2 else Fr(0)
    bs,T=boxsum(al,be,ga,cap,M)
    pre=Fr(13,12)*rhoof(s1)*rhoof(s2)
    kk=(1+Fr(1,cap))**2; tot=pre*pc/(1-kk*(bs+T))
    return float(tot), C, (al,be,ga), float(bs), float(T)
if __name__=='__main__':
    import sys
    cap=int(sys.argv[1]); M=int(sys.argv[2])
    small=[7,13,19,31,37,43]
    classes=[('e',5),('n2',)]+[('e',x) for x in small]+[('big',61,())]
    for i in range(len(classes)):
        for j in range(i,len(classes)):
            a,b=classes[i],classes[j]
            if a==b and a[0]=='e': continue
            r=leaf(a,b,cap,M); print(a,b,round(r[0],4),len(r[1]),r[2],round(r[3],4),round(r[4],4))
