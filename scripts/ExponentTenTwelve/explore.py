# Untrusted helper script for the OddPerfect Lean library.
# Forcing graph for exponent l - 1: starting from the given primes, factors
# sigma(p^(l-1)) for the smallest unexplored prime p, repeatedly, and records the graph.
# The forcing edges in gen.py were chosen by hand from this output.
# Used by: OddPerfect/ExponentTenTwelve.lean (the forcing chains).
# Run: python3 explore.py L BUDGET [START], for example python3 explore.py 11 40,
# python3 explore.py 11 40 11,3,2633 and python3 explore.py 13 40.
# Writes graphL.json to the current folder.
# Requires: sympy (version 1.14.0 was used). Running time: about 10 to 30 seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json, heapq, math, random
from sympy import isprime

l = int(sys.argv[1]); e = l - 1
budget = int(sys.argv[2])
start = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [l]
TD = 2 * 10**6

def sig(p): return (p**(e+1)-1)//(p-1)

def rho(n, iters=200000):
    for c in (1, 3, 5, 7):
        y, r, q, g = 2, 1, 1, 1
        x = ys = 2
        cnt = 0
        while g == 1 and cnt < iters:
            x = y
            for _ in range(r): y = (y*y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(128, r - k)):
                    y = (y*y + c) % n; q = q * abs(x - y) % n
                g = math.gcd(q, n); k += 128
            r *= 2; cnt += r
        if g == n:
            g = 1
            while g == 1:
                ys = (ys*ys + c) % n; g = math.gcd(abs(x - ys), n)
        if 1 < g < n: return g
    return None

def factor(n):
    """primes of n assuming every prime factor is l or 1 mod 2l; returns (primes, cofactor)."""
    ps = []
    while n % l == 0: n //= l; ps.append(l) if l not in ps else None
    t = 2*l + 1
    while t < TD and t*t <= n:
        if n % t == 0:
            ps.append(t)
            while n % t == 0: n //= t
        t += 2*l
    stack, co = [n] if n > 1 else [], 1
    while stack:
        m = stack.pop()
        if isprime(m): ps.append(m); continue
        if m.bit_length() > 400: co *= m; continue
        g = rho(m)
        if g is None: co *= m
        else: stack += [g, m // g]
    return sorted(set(ps)), co

graph = {}
heap = list(start); heapq.heapify(heap); seen = set(start)
while heap and budget > 0:
    p = heapq.heappop(heap); budget -= 1
    ps, co = factor(sig(p))
    graph[p] = (ps, co)
    print(p, p % 4, "->", [q for q in ps if q != l], f"cof{co.bit_length()}" if co > 1 else "", flush=True)
    for q in ps:
        if q not in seen:
            seen.add(q); heapq.heappush(heap, q)
json.dump({str(k): [v[0], str(v[1])] for k, v in graph.items()}, open(f"graph{l}.json", "w"))
