# Untrusted helper script for the OddPerfect Lean library.
# Integer mirror of the solver solve in OddPerfect/OmegaSix.lean, used to choose the
# window W and the fuel.
# Used by: OddPerfect/OmegaSix.lean (W = 10, search_four and search_five with fuel 30).
# Run: python3 mirror.py W J FUEL, for example python3 mirror.py 10 3 30 and
# python3 mirror.py 10 4 30 (J = 3 and J = 4 further prime factors after 3).
# Prints True when the search closes, with node counts.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Integer mirror of the Lean solver.
import sys
sys.setrecursionlimit(100000)
W=int(sys.argv[1]) if len(sys.argv)>1 else 200
J0=int(sys.argv[2]) if len(sys.argv)>2 else 4
FUEL=int(sys.argv[3]) if len(sys.argv)>3 else 60
st={'nodes':0,'ptests':0,'tdiv':0}
def geom(p,k): return (p**(k+1)-1)//(p-1)
def strip(g,ps):
    for y in ps:
        if y>=2:
            while g%y==0: g//=y
    return g
def isPrimeQ(q):
    st['ptests']+=1
    if q<2: return False
    d=2
    while d*d<=q:
        st['tdiv']+=1
        if q%d==0: return False
        d+=1
    return True
def valid(p,e): return e%2==0 or (p%4==1 and e%4==1)
def nextvalid(p,k): return k+1 if valid(p,k+1) else k+2
def kmin(q): return 1 if q%4==1 else 2
def cond(Un,Ud,j,q): return Un*q**j > 2*Ud*(q-1)**j
def bsearch(Un,Ud,j,a,b,f):
    # invariant intended: cond(a) true or a=m, cond(b) false
    if f==0 or b<=a+1: return a
    c=(a+b)//2
    return bsearch(Un,Ud,j,c,b,f-1) if cond(Un,Ud,j,c) else bsearch(Un,Ud,j,a,c,f-1)
def minB(l):
    return l[0] if len(l)==1 else min(l[0],minB(l[1:]))
def pick(known):
    best=None;bi=0
    for i,(p,k,ex) in enumerate(known):
        if not ex:
            num=p*p**k; den=(p-1)*geom(p,k)
            if best is None or num*best[1]>best[0]*den: best=(num,den);bi=i
    return bi
def solve(fuel,known,j,m):
    st['nodes']+=1
    if fuel==0: print("FUEL",known,j,m); return False
    f=fuel-1
    Ln=1;Ld=1;Un=1;Ud=1
    for (p,k,ex) in known:
        g=geom(p,k);Ln*=g;Ld*=p**k
        if ex: Un*=g;Ud*=p**k
        else: Un*=p;Ud*=p-1
    if 2*Ld<Ln or (j>0 and 2*Ld<=Ln): return True
    if any(a[2] and b[2] and a[1]%2==1 and b[1]%2==1 and a[0]!=b[0] for a in known for b in known): return True
    ps=[2]+[p for (p,_,_) in known]
    cs=[strip(geom(p,k),ps) for (p,k,ex) in known if ex]
    cs=[c for c in cs if c!=1]
    if any(j==0 or c<=m for c in cs): return True
    allex=all(e[2] for e in known)
    if j==0:
        if allex: 
            if 2*Ld==Ln: print("SOLUTION",known)
            return 2*Ld!=Ln
        if Un<=2*Ud: return True
        return split(f,known,j,m)
    bounds=[]
    if Un<2*Ud:
        bU=bsearch(Un,Ud,j,m,bhi(Un,Ud,j,m),200)
        if not cond(Un,Ud,j,bU+1): bounds.append(bU)
    bounds+=cs
    lo=m+1
    if j==1 and Ln<2*Ld:
        D=2*Ld-Ln; lo=max(lo,(Ln+D-1)//D)
    if bounds:
        B=minB(bounds)
        if B<=lo+W or allex or j>=2:
            ok=True
            for q in range(lo,B+1):
                if isPrimeQ(q):
                    if not solve(f,known+[(q,kmin(q),False)],j-1,q): ok=False
            return ok
    if allex: print("STUCK",known,j,m); return False
    return split(f,known,j,m)
def bhi(Un,Ud,j,m):
    # an upper end where cond fails: U*(q/(q-1))^j>2 fails once q-1 >= j*U/(2-U)... use q = m + 2*j*Un//(2*Ud-Un) + 2
    return m+(2*j*Un)//(2*Ud-Un)+2
def split(f,known,j,m):
    i=pick(known); p,k,ex=known[i]
    a=solve(f,known[:i]+[(p,k,True)]+known[i+1:],j,m)
    b=solve(f,known[:i]+[(p,nextvalid(p,k),False)]+known[i+1:],j,m)
    return a and b
print(solve(FUEL,[(3,2,False)],J0,3),st)
