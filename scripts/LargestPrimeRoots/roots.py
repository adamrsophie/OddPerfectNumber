# Untrusted helper script for the OddPerfect Lean library.
# Root tables for OddPerfect/LargestPrimeRoots.lean: the tenth roots of unity modulo
# 167772161 = 5 * 2^25 + 1 (generator 3) with their factorizations, and, for the primes
# P < 200000 whose odd part m of P - 1 satisfies 1 < m <= 15, those for which no 2m-th root
# of unity modulo P is prime, printed as (P, m, sorted roots).
# Used by: OddPerfect/LargestPrimeRoots.lean (the list in the table_167772161_* lemmas, and
# the list [1, 6048, 6049, 6240, 6241, 12288] in exists_primeFactor_gt_12289, which is the
# printed line for P = 12289).
# Run: python3 roots.py
# Requires: Python 3 and sympy. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Tenth roots of unity mod 167772161, and a search for small instances of the criterion.
from sympy import isprime, factorint
P = 167772161
assert isprime(P) and P - 1 == 5 * 2**25
g = 3
assert pow(g, (P-1)//2, P) != 1 and pow(g, (P-1)//5, P) != 1
w = pow(g, (P-1)//10, P)
R = sorted(pow(w, k, P) for k in range(10))
print(R, [isprime(r) for r in R])
for r in R: print(r, factorint(r))
# small instances: primes P = k*2^a+1, m = odd part of P-1, all 2m-th roots non prime
out = []
for P in range(3, 200000):
    if not isprime(P): continue
    m = P - 1
    while m % 2 == 0: m //= 2
    if m == 1 or m > 15: continue
    gg = next(x for x in range(2, P) if all(pow(x, (P-1)//q, P) != 1 for q in factorint(P-1)))
    ww = pow(gg, (P-1)//(2*m), P)
    rs = sorted(pow(ww, k, P) for k in range(2*m))
    if not any(isprime(r) for r in rs): out.append((P, m, rs))
for o in out[:15]: print(o)
