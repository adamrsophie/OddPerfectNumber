# Untrusted helper script for the OddPerfect Lean library.
# Step 1 of 3 for OddPerfect/ThreeFreeTwo.lean: factors 1 + p + p^2 for the primes
# p = 2 (mod 3), 5 <= p <= 200000, and keeps those with at most three prime factors.
# Run from any folder: python3 explore.py   writes feas.pkl to the current folder.
# Requires: Python 3 standard library. Running time: about a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'fac.py')).read())
X=200000
fac=factor_table(X)
P=set(primes_upto(X))
out=[]
for p in sorted(P):
    if p%3!=2 or p<5: continue
    f=fac[p]
    if len(f)<=3: out.append((p,f))
import pickle; pickle.dump(out,open('feas.pkl','wb'))
for p,f in out:
    if p<3000: print(p,f)
print(len(out))
