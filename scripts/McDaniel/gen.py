# Untrusted helper script for the OddPerfect Lean library.
# Forcing tree for McDaniel's theorem, case 3 | N: branches on whether a forced prime is
# the special prime and closes every leaf with an abundant divisor.
# Used by: OddPerfect/McDaniel.lean (the tree in the module docstring and the proof of
# mcdaniel_of_three_dvd).
# Run from any folder: python3 gen.py
# Writes tree.txt (the tree in the docstring), tree_body.txt (the Lean proof body) and
# primes.txt to the current folder. Requires tree2.py next to this file.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import os
import sys
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tree2.py')).read().split('def ab(')[0])
from fractions import Fraction as F
def abund(items):  # items: list of (p,a)
    r=F(1)
    for p,a in items: r*=F(sum(p**i for i in range(a+1)),p**a)
    return r
# state: dict p -> dict(status, par, kind, idx, neq)
cnt=[0]
def add(st,r,par,kind):
    if r not in st:
        cnt[0]+=1; st[r]=dict(status='U',par=par,kind=kind,idx=cnt[0],neq=None)
def setO(st,t,neq):
    st[t]=dict(st[t]); st[t]['status']='O'; st[t]['neq']=neq
    for r in opf(t*t+t+1): add(st,r,t,'O')
def setS(st,t):
    st[t]=dict(st[t]); st[t]['status']='S'
    for r in opf(t+1): add(st,r,t,'S')
def items(st,keys=None):
    return [(p,2 if st[p]['status']=='O' else 1) for p in (keys if keys is not None else st)]
def spec(st):
    for p,v in st.items():
        if v['status']=='S': return p
    return None
def propagate(st):
    while True:
        if abund(items(st))>2: return st
        s=spec(st)
        cand=[p for p,v in st.items() if v['status']=='U' and (s is not None or p%4==3)]
        if not cand: return st
        t=min(cand)
        setO(st,t,('spec',s) if t%4!=3 else ('mod4',))
primes_needed=set()
tree_txt=[]
def ind(d): return '  '*d
def emit_leaf(st,d,out):
    keys=sorted(st,key=lambda p:-p)
    C=list(st)
    for p in keys:
        C2=[x for x in C if x!=p]
        if abund(items(st,C2))>2: C=C2
    C.sort()
    # needed facts
    need_d=set();need_e=set()
    def needd(p):
        if p in need_d: return
        need_d.add(p); v=st[p]
        if v['kind']=='O': neede(v['par'])
    def neede(t):
        need_e.add(t); needd(t)
    for p in C:
        needd(p)
        if st[p]['status']=='O': neede(p)
    order=sorted(need_d|need_e,key=lambda p:st[p]['idx'])
    lines=[]
    for p in order:
        v=st[p]
        if p in need_d and v['kind']!='root':
            if v['kind']=='O':
                lines.append(f"have d{p} : {p} ∣ N := ord_dvd hN pr_{v['par']} e{v['par']} (by decide) (by norm_num)")
                primes_needed.add(v['par'])
            else:
                lines.append(f"have d{p} : {p} ∣ N := spec_dvd hN hq hodd (by decide) (by norm_num)")
        if p in need_e:
            primes_needed.add(p)
            n=v['neq']
            if n is None: n=('mod4',) if p%4==3 else None
            if n[0]=='mod4': ne=f"(ne3 {p} (by norm_num))"
            elif n[0]=='branch': ne=n[1]
            else: ne="(by norm_num)"
            lines.append(f"have e{p} := E {p} pr_{p} d{p} {ne}")
    lines.append("have c := start N")
    for p in C:
        primes_needed.add(p)
        if st[p]['status']=='O':
            lines.append(f"have c := step c pr_{p} (ord_sq hN pr_{p} e{p}) (by norm_num)")
        else:
            lines.append(f"have c := step c (a := 1) pr_{p} (by rw [pow_one]; exact d{p}) (by norm_num)")
    lines.append("exact not_perfect_of_dvd_of_two_lt_abundancy c.1 (by rw [c.2]; norm_num [Finset.sum_range_succ]) hN")
    for l in lines: out.append(ind(d)+l)
    tree_txt.append(ind(d)+'CLOSE '+' '.join(f"{p}^{a}" for p,a in items(st,C))+f'  abundancy {float(abund(items(st,C))):.5f}')
def search(st,d,out):
    st=propagate(st)
    if abund(items(st))>2: emit_leaf(st,d,out); return
    s=spec(st)
    assert s is None
    unk=sorted(p for p,v in st.items() if v['status']=='U')
    t=unk[0]; assert t%4==1
    out.append(ind(d)+f"by_cases hs{t} : {t} = q")
    out.append(ind(d)+"· subst hs"+str(t))
    tree_txt.append(ind(d)+f'{t} special')
    st3={k:dict(v) for k,v in st.items()}; setS(st3,t)
    search(st3,d+1,out)
    out.append(ind(d)+"· ")
    tree_txt.append(ind(d)+f'{t} ordinary')
    st2={k:dict(v) for k,v in st.items()}; setO(st2,t,('branch',f"hs{t}"))
    search(st2,d+1,out)
st={}
cnt[0]+=1; st[3]=dict(status='O',par=None,kind='root',idx=0,neq=('mod4',))
add(st,13,3,'O')
out=[]
search(st,0,out)
# fix bullets: lines "· " followed by next line: merge
res=[]
i=0
while i<len(out):
    l=out[i]
    if l.strip()=='·' or l.rstrip().endswith('· subst hs'+l.split('hs')[-1]) and False: pass
    res.append(l); i+=1
open('tree_body.txt','w').write('\n'.join(out))
open('tree.txt','w').write('\n'.join(tree_txt))
open('primes.txt','w').write(' '.join(map(str,sorted(primes_needed))))
print('\n'.join(tree_txt)); print(sorted(primes_needed))
