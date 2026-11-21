# Untrusted helper script for the OddPerfect Lean library.
# Pratt primality certificates as flat lists of entries (p, a, prime factors of p - 1)
# in dependency order, the format checked by OddPerfect.Pratt.check.
# Used by: OddPerfect/Pratt.lean (witnessCert, prime_9701563) and
# OddPerfect/SupportBridges.lean (prime_4294967291).
# Run: python3 gen.py 47116128896261596331524418282573
# Factors p - 1 by trial division to 10^6 plus the list KNOWN of large primes, so a new
# prime may need its large factors added to KNOWN.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys
KNOWN=[1738423,966563189,666928600411,12004714807399,192750846182877882539,9701563,27779]
SMALL=200
def factor(n):
    fs=[];d=2
    while d<=10**6 and d*d<=n:
        while n%d==0: fs.append(d); n//=d
        d+=1
    for k in KNOWN:
        while n%k==0 and n>1: fs.append(k); n//=k
    if n>1:
        assert n<=10**12 or n in KNOWN, n
        fs.append(n)
    return sorted(fs)
out=[];done=set()
def cert(p):
    if p<SMALL or p in done: return
    fs=factor(p-1)
    for q in sorted(set(fs)): cert(q)
    a=2
    while not (pow(a,p-1,p)==1 and all(pow(a,(p-1)//q,p)!=1 for q in set(fs))): a+=1
    done.add(p); out.append((p,a,fs))
for x in sys.argv[1:]: cert(int(x))
print("[" + ",\n  ".join("(%d, %d, [%s])"%(p,a,", ".join(map(str,fs))) for p,a,fs in out)+"]")
