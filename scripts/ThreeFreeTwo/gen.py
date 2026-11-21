# Untrusted helper script for the OddPerfect Lean library.
# Step 2 of 3 for OddPerfect/ThreeFreeTwo.lean: box bounds B (rounded up) for the nine
# level pairs and the 41 leaves (class pairs, set C of small ordinary primes, bound below 2).
# Run from the folder holding feas.pkl: python3 gen.py   writes leaves.pkl.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ev4.py')).read().split("if __name__")[0])
from fractions import Fraction as Fr
import math
L={'0':Fr(0),'7':Fr(14,37),'13':Fr(5,18),'31':Fr(2,11)}
LS={'0':'0','7':'14 / 37','13':'5 / 18','31':'2 / 11'}
al=Fr(5,18); cap=300; M=5
kk=Fr(301,300)**2
def tlv(a,b,c): return (a**M+b**M+c**M)/((1-a)*(1-b)*(1-c))
pairs=[('0','0'),('0','7'),('0','13'),('0','31'),('7','13'),('7','31'),('13','13'),('13','31'),('31','31')]
Bv={}
for p in pairs:
    bs,_=boxsum(al,L[p[0]],L[p[1]],cap,M)
    # round up to 4 decimals
    B=Fr(math.ceil(bs*10000)+1,10000)
    Bv[p]=B
    print(p,float(bs),B)
# classes: name -> (lean hyp, level, m lower bound, spec for python)
CL={
 '5':('r = 5','0',5,('e',5)),
 'n2':('r % 3 = 2 ∧ 11 ≤ r','0',11,('n2',)),
 '7':('r = 7','7',7,('e',7)),
 '13':('r = 13','13',13,('e',13)),
 '19':('r = 19','13',19,('e',19)),
 '31':('r = 31','31',31,('e',31)),
 '37':('r = 37','31',37,('e',37)),
 '43':('r = 43','31',43,('e',43)),
 'big':('r % 3 = 1 ∧ 61 ≤ r','31',61,('big',61,())),
 'big307':('r % 3 = 1 ∧ 61 ≤ r ∧ r ≠ 307','31',61,('big',61,(307,))),
 '307':('r = 307','31',307,('e',307)),
}
order=['5','n2','7','13','19','31','37','43','big']
leaves=[]
for i in range(len(order)):
    for j in range(i,len(order)):
        a,b=order[i],order[j]
        if a==b and CL[a][3][0]=='e': continue
        if (a,b)==('7','31'):
            leaves+=[(a,b,'q = 409',lambda x:x==409),(a,b,'q = 3541',lambda x:x==3541),(a,b,'q ≠ 409 ∧ q ≠ 3541',lambda x:x not in (409,3541))]
        elif (a,b)==('7','big'):
            leaves+=[(a,'307',None,lambda x:True),(a,'big307',None,lambda x:True)]
        else: leaves.append((a,b,None,lambda x:True))
worst=0
res=[]
for a,b,qh,qc in leaves:
    s1,s2=CL[a][3],CL[b][3]
    C=[s for s in PR if s<cap and V(s,s1,s2,qc)]
    pc=Fr(1)
    for s in C: pc*=fq(s)
    la,lb=CL[a][1],CL[b][1]
    B=Bv[(la,lb)]
    K=kk*(B+tlv(al,L[la],L[lb]))
    assert K<1
    ma,mb=CL[a][2],CL[b][2]
    tot=Fr(13,12)*Fr(ma,ma-1)*Fr(mb,mb-1)*pc/(1-K)
    worst=max(worst,tot)
    res.append((a,b,qh,C,la,lb,float(tot)))
    print(a,b,qh,float(tot),C)
print('worst',float(worst))
import pickle; pickle.dump((res,{k:(v.numerator,v.denominator) for k,v in Bv.items()}),open('leaves.pkl','wb'))
