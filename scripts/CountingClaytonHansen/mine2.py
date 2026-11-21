# Untrusted helper script for the OddPerfect Lean library.
# Linear program over the merged ledger of OddPerfect/CountingClaytonHansen.lean
# (ch_ledger): the least slope a with Omega >= a omega + b, and the best b for that slope,
# for all odd perfect numbers and for 3 not dividing N.
# Used by: OddPerfect/CountingClaytonHansen.lean (the constants 99/37, 187/37 and 51/19,
# 46/19 of the main theorems; the merged ledger rows give the paper's optimum).
# Run: python3 mine2.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
from simplex import LP
def system(not3=False, homog=False, drop=()):
    k = 0 if homog else 1
    L = LP()
    c = {
     1: ({'f3':1,'S':2,'G':1,'Om':-1},'=',0),
     2: ({'om':1,'S':-1,'Tp':-1},'=' if not3 else '<=', (0 if not3 else 1)*k),
     3: ({'Tp':4,'G':-1},'<=',3*k),
     5: ({'S':1,'S1':-1,'S21':-1,'S22':-1,'S31':-1,'S32':-1,'S41':-1,'S42':-1},'=',0),
     9: ({'S1':1,'S1S':-1,'S1T':-1},'<=',k),
     12:({'S31':1,'S32':1,'XS':-1,'XT':-1},'<=',0),
     14:({'S21':1,'S31':1,'S41':1,'f3':-1},'<=',0),
     15:({'S1':1,'S21':1,'S22':2,'S31':2,'S32':3,'S41':3,'S42':4,'G':-1,'S21':-1,'S31':0,'S41':1},'<=',0),
     16:({'S1':1,'S21':1,'S22':1,'Tp':-1,'S21':0,'S31':-1,'S41':-1},'<=',0),
     17:({'S1':2,'S21':2,'S22':1,'S31':1,'Tp':-2,'S21':0,'S31':-1,'S41':-2},'<=',0),
     18:({'S1S':2,'XS':1,'S21':-2,'S31':-2,'S41':-2},'<=',0),
     19:({'S1T':4,'XT':1,'G':-1},'<=',0),
    }
    for i,(l,s,r) in c.items():
        if i not in drop: L.add(l,s,r,name=i)
    if not3: L.add({'f3':1},'=',0)
    return L
def best(not3=False, drop=()):
    L = system(not3, True, drop); L.add({'om':1},'=',1)
    st,a,_ = L.solve_min({'Om':1})
    if st!='opt': return st
    st,b,x = system(not3, False, drop).solve_min({'Om':1,'om':-a})
    return a,b
print(best()); print(best(True))
