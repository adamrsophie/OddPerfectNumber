# Untrusted helper script for the OddPerfect Lean library.
# Prints the odd x < P with x^k = 1 (mod P) for (P, k) = (40961, 10) and (18433, 18), then
# 4481^9 mod 18433, 4481^18 - 1 mod 18433, and whether 18433^2 does not divide 4481^18 - 1.
# Used by: OddPerfect/LargestPrimeCapacityTwo.lean (the root lists in chk_40961, cov_40961,
# chk_18433, cov_18433 and the facts about 4481 in the module docstring).
# Run: python3 roots.py
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.
for P,k in [(40961,10),(18433,18)]:
    L=[x for x in range(P) if x%2==1 and pow(x,k,P)==1]
    print(P,k,L)
print(pow(4481,9,18433), (4481**18-1)%18433, (4481**18-1)%18433**2!=0)
