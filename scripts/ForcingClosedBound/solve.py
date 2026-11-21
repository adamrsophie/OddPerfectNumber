# Untrusted helper script for the OddPerfect Lean library.
# Step 3 for OddPerfect/ForcingClosedBound.lean: exact smoothness of the candidates from
# gen.c, then the greatest fixed point (deletion rounds) of the odd primes up to P. Writes
# moves_P.txt, cert_P.txt (removal round per prime) and ustar_P.json.
# Used by: OddPerfect/ForcingClosedBound.lean as an independent derivation of the deletion
# rounds: for P = 1000 the removal rounds in cert_1000.txt are those of round1 .. round9 and
# iterate_eq (nine rounds); the Lean lemmas themselves are written by mkrounds.py.
# Run: python3 solve.py 1000 cand_1000.txt [control]
# Requires: Python 3 standard library. Running time: under a second for P = 1000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Exact smoothness of candidates from gen.c, then the greatest fixed point.
# usage: solve.py P cand_file [control]
# Writes moves_<P>.txt (every P-smooth Phi_l(p): "p l r:v r:v ...") and
# cert_<P>[_control].txt ("p round", round 0 = survives in U*).
import sys, json

P = int(sys.argv[1]); cand = sys.argv[2]; control = len(sys.argv) > 3

spf = list(range(P + 2))
for i in range(2, int((P + 1) ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, P + 2, i):
            if spf[j] == j: spf[j] = i
isp = lambda n: n >= 2 and spf[n] == n
odd = [p for p in range(3, P + 1) if isp(p)]

def val(p, l, r):
    # exponent of r in p^l - 1
    k = 0
    while pow(p, l, r ** (k + 1)) == 1: k += 1
    return k

def exact(p, l, hits):
    """Return factor dict if Phi_l(p) is P-smooth, else None. hits = all r in R_l, ord_r(p) = l."""
    fac = {}
    M = 1
    if p % l == 1:
        v = val(p, l, l) - val(p, 1, l)   # v_l(Phi_l(p)) = v_l(p^l - 1) - v_l(p - 1)
        fac[l] = v; M *= l ** v
    for r in hits:
        assert r % (2 * l) == 1 and p % r != 1 and pow(p, l, r) == 1
        v = val(p, l, r)                  # r does not divide p - 1, so v_r(Phi_l(p)) = v_r(p^l - 1)
        fac[r] = v; M *= r ** v
    # M divides Phi_l(p), and p^(l-1) < Phi_l(p) < 1.5 p^(l-1) with Phi_l(p) odd,
    # so Phi_l(p) is P-smooth iff M > p^(l-1)
    if M.bit_length() <= (l - 1) * (p.bit_length() - 1): return None
    if M > p ** (l - 1):
        assert M == (p ** l - 1) // (p - 1)
        return fac
    return None

moves = {}   # p -> list of (l, fac)
seen = set()
with open(cand) as f:
    for line in f:
        t = line.split(); kind, p, l = t[0], int(t[1]), int(t[2])
        if (p, l) in seen: continue
        seen.add((p, l))
        if kind == 'C':
            hits = [int(x) for x in t[3:]]
        else:
            hits = [r for r in range(2 * l + 1, P + 1, 2 * l) if isp(r) and p % r != 1 and pow(p, l, r) == 1]
        fac = exact(p, l, hits)
        if fac is not None: moves.setdefault(p, []).append((l, fac))

def odd_factors(n):
    s = set()
    while n > 1:
        q = spf[n]; n //= q
        if q != 2: s.add(q)
    return s

special = {p: odd_factors(p + 1) for p in odd if control or p % 4 == 1}

U = set(odd); rnd = {}; k = 0
while True:
    k += 1
    rem = []
    for p in U:
        ok = any(set(fac) <= U for l, fac in moves.get(p, []))
        if not ok and p in special and special[p] <= U: ok = True
        if not ok: rem.append(p)
    if not rem: break
    for p in rem: rnd[p] = k
    U -= set(rem)
tag = "_control" if control else ""
if not control:
    with open(f"moves_{P}.txt", "w") as f:
        for p in sorted(moves):
            for l, fac in sorted(moves[p]):
                f.write(f"{p} {l} " + " ".join(f"{r}:{v}" for r, v in sorted(fac.items())) + "\n")
with open(f"cert_{P}{tag}.txt", "w") as f:
    for p in odd: f.write(f"{p} {rnd.get(p, 0)}\n")
nm = sum(len(v) for v in moves.values())
print(f"P={P} control={control} smooth moves={nm} primes with a move={len(moves)} rounds={k - 1} |U*|={len(U)}")
print("U* (first 80):", sorted(U)[:80])
json.dump(sorted(U), open(f"ustar_{P}{tag}.json", "w"))
