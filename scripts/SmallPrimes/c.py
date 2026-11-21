# Untrusted helper script for the OddPerfect Lean library.
# Branch and bound over the exponents of the four seven prime supports with 3 not dividing
# N. Prints whether each (support, special prime) closes and the node count. e.py executes
# the part of this file before the node counter.
# Run: python3 c.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from pr import *
from fractions import Fraction as F
sys.setrecursionlimit(10000)
def h(p,e): return F(p**(e+1)-1, p**e*(p-1))
def allowed(p,e,special):
    if special: return e%2==1 and e%4==1 and not (p%3==1 and e%3==2)
    if e%2: return False
    if p%3==1 and e%3==2: return False
    return e>=2
def nxt(p,a,sp):
    e=a+1
    while not allowed(p,e,sp): e+=1
    return e
nodes=0
def bb(s,sp,state,depth=0):
    global nodes; nodes+=1
    if nodes>200000: return 'ABORT'
    lo=F(1); up=F(1)
    for p in s:
        kind,e=state[p]
        lo*=h(p,e)
        up*= h(p,e) if kind=='eq' else F(p,p-1)
    if lo>2: return True
    if up<2: return True
    free=[p for p in s if state[p][0]=='ge']
    if not free:
        return lo!=2 or 'PERFECT'
    # branch on prime with largest gap? choose smallest prime free
    p=max(free, key=lambda q: F(q,q-1)/h(q,state[q][1]))
    a=state[p][1]
    st1=dict(state); st1[p]=('eq',a)
    st2=dict(state); st2[p]=('ge',nxt(p,a,p==sp))
    r1=bb(s,sp,st1,depth+1)
    if r1 is not True: return r1
    return bb(s,sp,st2,depth+1)
for s in [(5,7,11,13,17,19,23),(5,7,11,13,17,19,29),(5,7,11,13,17,19,31),(5,7,11,13,17,19,37)]:
    for sp in [q for q in s if q%12==1]:
        nodes=0
        st={p:('ge',nxt(p,0,p==sp)) for p in s}
        print(s,sp,bb(s,sp,st),nodes)
