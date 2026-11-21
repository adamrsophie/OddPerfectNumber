# Untrusted helper script for the OddPerfect Lean library.
# Step 1 for OddPerfect/ForcingClosedBound.lean: splits the odd primes l with 2 l + 1 <= P
# into small and big lengths and writes the small ones to small_l_P.txt.
# Used by: OddPerfect/ForcingClosedBound.lean as an independent derivation of the deletion
# rounds: for P = 1000 the removal rounds in cert_1000.txt are those of round1 .. round9 and
# iterate_eq (nine rounds); the Lean lemmas themselves are written by mkrounds.py.
# Run: python3 classify.py 1000
# Requires: Python 3 standard library. Running time: under a second for P = 1000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Classify odd primes l with 2l+1 <= P.
# l is "big" when l * prod(R_l) < 3^(l-1), R_l = primes r <= P with r % (2l) == 1.
# For big l, a P-smooth Phi_l(p) (p >= 3 odd prime) needs some r in R_l with r^2 | Phi_l(p):
# otherwise its P-smooth part is at most l * prod(R_l) < 3^(l-1) <= p^(l-1) < Phi_l(p).
# Writes the small l (all others) to small_l_<P>.txt, one per line.
import sys

def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return s

P = int(sys.argv[1])
isp = primes_upto(P)
small = []
for l in range(3, (P - 1) // 2 + 1):
    if not isp[l]: continue
    A = l
    for r in range(2 * l + 1, P + 1, 2 * l):
        if isp[r]: A *= r
    # 2^(158 (l-1) / 100) <= 3^(l-1) since log2 3 > 1.58, so the first test is a safe shortcut
    if A.bit_length() <= (158 * (l - 1)) // 100: continue
    if not (A < 3 ** (l - 1)):
        small.append(l)
with open(f"small_l_{P}.txt", "w") as f:
    for l in small: f.write(f"{l}\n")
print("small l count", len(small), "max", max(small))
