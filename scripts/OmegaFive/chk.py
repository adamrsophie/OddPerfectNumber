# Untrusted helper script for the OddPerfect Lean library.
# Mirror of checkSupport in OddPerfect/OmegaFive.lean over the ranges of tab5, tab7,
# tab11 and tab13. Prints the number of supports and the list of supports that fail.
# Run: python3 chk.py
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from pr import isp
def geom(x,e): return (x**(e+1)-1)//(x-1)
def cands(S,x):
  c=[1] if x%4==1 else []
  for y in S:
    for d in range(y):
      if 3<=d and y%d==1 and ((d-1)%2==0 or (x%4==1 and (d-1)%4==1)): c.append(d-1)
  return c
def prod(S):
  p=1
  for y in S: p*=y
  return p
def bad(S,x,e): return pow(2*prod(S),(e+1)*x, geom(x,e))!=0
def checkX(S,x): return all(bad(S,x,e) for e in cands(S,x))
def check(S): return any(checkX(S,x) for x in S)
fails=[]
n=0
for r in range(17,32):
  for s in range(r+1,256):
    if 16*(r-1)*(s-1)<15*r*s and isp(r) and isp(s):
      n+=1
      if not check([3,5,r,s]): fails.append((5,r,s))
for r in range(8,16):
  for s in range(r+1,27):
    if 8*(r-1)*(s-1)<7*r*s and isp(r) and isp(s):
      n+=1
      if not check([3,7,r,s]): fails.append((7,r,s))
for s in range(12,100):
  if isp(s): n+=1; (check([3,5,11,s]) or fails.append((5,11,s)))
for s in range(14,47):
  if isp(s): n+=1; (check([3,5,13,s]) or fails.append((5,13,s)))
print(n,fails)
