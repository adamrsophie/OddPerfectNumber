# Untrusted helper script for the OddPerfect Lean library.
# Pratt primality certificates as flat lists of entries (p, a, prime factors of p - 1)
# in dependency order, the format checked by OddPerfect.Pratt.check.
# Used by: OddPerfect/Pratt.lean (witnessCert, prime_9701563) and
# OddPerfect/SupportBridges.lean (prime_4294967291).
# Run: python3 gen.py 47116128896261596331524418282573
# Factors p - 1 by trial division to 10^6 plus the list KNOWN of large primes, so a new
# prime may need its large factors added to KNOWN. Every factor of p - 1 must be an integer
# above 1 and prime (below 200 by trial division, from 200 on by its own entry), the product
# must be p - 1, a number that a Miller and Rabin base proves composite is rejected, and the
# witness is searched below p only.
# Exit status: 0 when the certificate is printed, 1 when a number or a factor list fails (a
# message, nothing printed on standard output), 2 for an argument that is not a decimal number.
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
        if not (n<=10**12 or n in KNOWN):
            fail("the cofactor %d is neither below 10^12 nor in KNOWN" % n)
        fs.append(n)
    return sorted(fs)
def fail(msg):
    print("rejected: " + msg, file=sys.stderr); sys.exit(1)
def composite(n):
    """True when a Miller and Rabin base proves the odd n > 3 composite (so the witness scan
    below n is not started for a composite)."""
    d,s=n-1,0
    while d%2==0: d//=2; s+=1
    for b in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(b,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return True
    return False
out=[];done=set()
def cert(p):
    # Every factor of p - 1 must be an integer above 1, prime (below SMALL by trial division,
    # from SMALL on by its own entry), the product must be p - 1, and the witness is searched
    # below p only: no hang when p or a listed factor is not prime.
    if p<SMALL:
        if not (p>=2 and all(p%d for d in range(2,p))): fail("%d is not prime" % p)
        return
    if p in done: return
    fs=factor(p-1)
    prod=1
    for q in fs: prod*=q
    if not all(type(q) is int and q>1 for q in fs) or prod!=p-1:
        fail("the factor list %r of %d - 1 is not a factorization" % (fs, p))
    for q in sorted(set(fs)): cert(q)
    if composite(p): fail("%d is composite (a strong witness)" % p)
    a=next((a for a in range(2,p) if pow(a,p-1,p)==1 and
            all(pow(a,(p-1)//q,p)!=1 for q in set(fs))),None)
    if a is None: fail("no Pratt witness below %d: %d is not prime" % (p, p))
    done.add(p); out.append((p,a,fs))
for x in sys.argv[1:]:
    if not (x.isascii() and x.isdigit()):
        print("usage: python3 gen.py P [P ...] (decimal numbers): got %r" % x, file=sys.stderr)
        sys.exit(2)
    cert(int(x))
print("[" + ",\n  ".join("(%d, %d, [%s])"%(p,a,", ".join(map(str,fs))) for p,a,fs in out)+"]")
