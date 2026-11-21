# Untrusted helper script for the OddPerfect Lean library.
# Helper: trial division primality test, prime ranges and factorization.
# Requires: Python 3 standard library.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

def isp(n):
  if n<2: return False
  i=2
  while i*i<=n:
    if n%i==0: return False
    i+=1
  return True
def primerange(a,b): return [n for n in range(a,b) if isp(n)]
def factor(n):
  f={};d=2
  while d*d<=n:
    while n%d==0: f[d]=f.get(d,0)+1; n//=d
    d+=1
  if n>1: f[n]=f.get(n,0)+1
  return f
