# Untrusted helper script for the OddPerfect Lean library.
# Prints the split trees of the branch and bound of c.py.
# Used by: OddPerfect/SmallPrimes.lean (the case splits and leaves of excl_23_13,
# excl_29_13, excl_31_13, excl_37_13, excl_37_37).
# Run: python3 e.py   (c.py and pr.py must be next to this file)
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from pr import *
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'c.py')).read().split('nodes=0')[0])
def bb(s,sp,state,ind=''):
    lo=F(1); up=F(1)
    for p in s:
        kind,e=state[p]
        lo*=h(p,e)
        up*= h(p,e) if kind=='eq' else F(p,p-1)
    fx={p:e for p,(k,e) in state.items() if k=='eq'}
    if lo>2: print(ind+'LO>2', {p:e for p,(k,e) in state.items()}, float(lo)); return
    if up<2: print(ind+'UP<2 fixed',fx, float(up)); return
    free=[p for p in s if state[p][0]=='ge']
    p=max(free, key=lambda q: F(q,q-1)/h(q,state[q][1]))
    a=state[p][1]
    print(ind+f'split {p}: ={a} | >={nxt(p,a,p==sp)}')
    st1=dict(state); st1[p]=('eq',a)
    st2=dict(state); st2[p]=('ge',nxt(p,a,p==sp))
    bb(s,sp,st1,ind+'  '); bb(s,sp,st2,ind+'  ')
for s in [(5,7,11,13,17,19,23),(5,7,11,13,17,19,29),(5,7,11,13,17,19,31),(5,7,11,13,17,19,37)]:
    for sp in [q for q in s if q%12==1]:
        print(s,sp)
        bb(s,sp,{p:('ge',nxt(p,0,p==sp)) for p in s})
# check products for missing r
P=lambda L: __import__('math').prod(F(p,p-1) for p in L)
base=[5,7,11,13,17,19,23,29,31]
for r in [5,7,11,13,17,19]:
    T=[p for p in base if p!=r][:7]; print(r,T,float(P(T)), P(T)<=2)
P6=P([5,7,11,13,17,19]); print(P6, [q for q in range(23,60) if isprime(q) and P6*F(q,q-1)>2])
