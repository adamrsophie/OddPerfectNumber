# Untrusted helper script for the OddPerfect Lean library.
# Independent checker for solve.py: recomputes the smooth pairs (p, l) by vectorized
# modular powers, compares them with moves_P.txt and verifies the removal certificate
# cert_P.txt. It does not import the generator.
# Used by: OddPerfect/ForcingClosedBound.lean as an independent derivation of the deletion
# rounds: for P = 1000 the removal rounds in cert_1000.txt are those of round1 .. round9 and
# iterate_eq (nine rounds); the Lean lemmas themselves are written by mkrounds.py.
# Run: python3 check.py 1000
# Requires: numpy (version 2.5.3 was used). Running time: under a second for P = 1000.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

# Independent checker (does not import the generator). usage: check.py P
# 1. Recomputes independently, by direct vectorized modular powers over all p (not by sieving
#    roots of unity), the set of pairs (p, l) with Phi_l(p) P-smooth, and checks every such
#    factorization by exact division of the integer Phi_l(p).
# 2. Compares that set with moves_<P>.txt.
# 3. Checks the removal certificate cert_<P>.txt: every odd prime <= P appears once; a prime
#    removed in round k has, for each of its moves (special and ordinary), a factor removed in
#    an earlier round; it still had a move before round k - 1 ended; every survivor has a move
#    inside the survivors.
import sys, math, time
import numpy as np

P = int(sys.argv[1]); t0 = time.time()
sv = np.ones(P + 1, dtype=bool); sv[:2] = False
for i in range(2, int(P ** 0.5) + 1):
    if sv[i]: sv[i * i::i] = False
primes = [int(x) for x in np.nonzero(sv)[0]]
oddp = [p for p in primes if p > 2]
pv = np.array(oddp, dtype=np.int64)
lg = np.log2(pv.astype(np.float64))
pos = {p: i for i, p in enumerate(oddp)}

def vpow(b, e, m):  # b^e mod m, m < 2^31
    r = np.ones_like(b); b = b % m
    while e:
        if e & 1: r = r * b % m
        b = b * b % m; e >>= 1
    return r

def mulmod40(a, b, m):  # a, b < m < 2^40
    t = (a * (b >> 20)) % m
    t = (t << 20) % m
    return (t + (a * (b & 0xFFFFF)) % m) % m

def vpow40(b, e, m):
    r = np.ones_like(b); b = b % m
    while e:
        if e & 1: r = mulmod40(r, b, m)
        b = mulmod40(b, b, m); e >>= 1
    return r

def exact_factor(p, l, hits):
    n = (p ** l - 1) // (p - 1); fac = {}
    for r in ([l] if p % l == 1 else []) + hits:
        while n % r == 0: n //= r; fac[r] = fac.get(r, 0) + 1
    return fac if n == 1 else None

Ls = [l for l in oddp if 2 * l + 1 <= P]
smooth = {}
nbig = nsmall = 0
for l in Ls:
    R = [r for r in range(2 * l + 1, P + 1, 2 * l) if sv[r]]
    prodR = l * math.prod(R)
    big = prodR < 3 ** (l - 1)
    if big:
        # a P-smooth Phi_l(p) then needs r^2 | Phi_l(p) for some r in R
        nbig += 1
        cands = set()
        for r in R:
            x = vpow(pv, l, r)
            idx = np.nonzero((x == 1) & (pv % r != 1))[0]
            if len(idx) == 0: continue
            x2 = vpow40(pv[idx], l, r * r)
            for i in idx[x2 == 1]: cands.add(int(i))
        for i in cands:
            p = oddp[i]
            hits = [r for r in R if p % r != 1 and pow(p, l, r) == 1]
            fac = exact_factor(p, l, hits)
            if fac: smooth[(p, l)] = fac
    else:
        nsmall += 1
        acc = np.zeros(len(oddp)); wf = np.zeros(len(oddp), dtype=bool); hitl = []
        for r in R:
            x = vpow(pv, l, r)
            idx = np.nonzero((x == 1) & (pv % r != 1))[0]
            if len(idx) == 0: continue
            acc[idx] += math.log2(r); hitl.append((r, idx))
            x2 = vpow40(pv[idx], l, r * r)
            wf[idx[x2 == 1]] = True
        acc += np.where(pv % l == 1, math.log2(l), 0.0)
        # without any r^2 | Phi_l(p), the smooth part is at most 2^acc; Phi_l(p) > p^(l-1)
        cand = wf | (acc >= (l - 1) * lg - 1e-6)
        hl = {int(i): [] for i in np.nonzero(cand)[0]}
        for r, idx in hitl:
            for i in idx[cand[idx]]: hl[int(i)].append(r)
        for i, hits in hl.items():
            fac = exact_factor(oddp[i], l, hits)
            if fac: smooth[(oddp[i], l)] = fac
print(f"P={P}: {nsmall} small l, {nbig} big l, {len(smooth)} smooth pairs, {time.time() - t0:.0f}s")

gen = {}
for line in open(f"moves_{P}.txt"):
    t = line.split()
    gen[(int(t[0]), int(t[1]))] = {int(a): int(b) for a, b in (x.split(':') for x in t[2:])}
assert gen == smooth, "move list mismatch"
print("move list matches the independent recomputation")

rnd = {}
for line in open(f"cert_{P}.txt"):
    p, k = map(int, line.split()); assert p not in rnd; rnd[p] = k
assert sorted(rnd) == oddp
INF = 10 ** 9
key = lambda r: INF if rnd[r] == 0 else rnd[r]   # survivors count as never removed
def oddf(n):
    s = set(); d = 3
    while n % 2 == 0: n //= 2
    while d * d <= n:
        while n % d == 0: s.add(d); n //= d
        d += 2
    if n > 1: s.add(n)
    return s
movesof = {}
for (p, l), fac in smooth.items(): movesof.setdefault(p, []).append(set(fac))
for p in oddp:
    if p % 4 == 1: movesof.setdefault(p, []).append(oddf(p + 1))
for p in oddp:
    k = key(p); ms = movesof.get(p, [])
    # first round in which each move dies (INF if never)
    death = [min(key(r) for r in m) if m else INF for m in ms]
    if k == INF:
        assert any(d == INF for d in death), p
    else:
        assert all(d < k for d in death), p          # sound removal
        assert k == 1 or any(d >= k - 1 for d in death), p   # not removable earlier
maxr = max(rnd.values()); surv = [p for p in oddp if rnd[p] == 0]
print(f"certificate verified: rounds={maxr}, |U*|={len(surv)}, total {time.time() - t0:.0f}s")
