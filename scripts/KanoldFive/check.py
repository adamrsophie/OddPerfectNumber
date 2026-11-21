# Untrusted helper script for the OddPerfect Lean library.
# Exact arithmetic check of the literals of the module: the factorizations of sigma(5^4) and
# of Phi_5(p) for p = 11, 71, 211, primality and residues mod 5 of 11, 71, 211, 1361, 2221,
# 3221, and sigma(5^9) = 2441406 with its prime factors 11, 71, 521 and their residues mod 5
# and mod 25.
# Used by: OddPerfect/KanoldFive.lean (the primality and divisibility lemmas of the ordinary
# case and the sigma(5^9) step of the special case).
# Run: python3 check.py
# Requires: Python 3 and sympy. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

from sympy import factorint, isprime
phi5=lambda p:1+p+p*p+p**3+p**4
print("sigma(5^4)",factorint(phi5(5)))
for p in [11,71,211]: print(p, p%4, factorint(phi5(p)))
for p in [11,71,211,1361,2221,3221]: print(p,isprime(p),p%5)
s=(5**10-1)//4; print("sigma(5^9)",s,factorint(s))
for p in [11,71,521]: print(p,p%5,p%25)
