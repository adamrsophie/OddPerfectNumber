# Untrusted helper script for the OddPerfect Lean library.
# Abundancy bound for the two leaves with one free slot (C3 and C6) with the alpha and
# beta parameters used in the Lean proof.
# Used by: OddPerfect/Restrained.lean (the alpha arguments and beta of the two one slot
# leaves, set as constants in this script and checked here).
# Run: python3 c36b.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from fractions import Fraction as F
def fv(p,e=2): return F(sum(p**i for i in range(e+1)),p**e)
def run(name,C,alphas,beta):
    P=F(1)
    for a in alphas: P*=1/(1-a)
    S=beta*P
    print(name, float(C), float(S), C < 2*(1-2*S), float(2*(1-2*S)))
cx=1+F(1,10**11)
C3=fv(3)*fv(7)*F(13,12)*F(19,18)*cx*fv(653)
run("C3",C3,[F(13,20),F(53,100),F(12,25),F(1,1000)],F(1,1000))
C6=fv(3)*fv(13)*F(61,60)*F(31,30)*cx
run("C6",C6,[F(53,100),F(43,100),F(9,25),F(1,1000)],F(1,1000))
print(13**22>10**24, 19**19>=10**24, 31**17, 61**14>=10**24, 31**17>=10**24)
