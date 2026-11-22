# Untrusted helper script for the OddPerfect Lean library.
# Generator of the data of the leaf r = 13 (branch q = 1 mod 12): the forcing kill trees for
# every prime q = 1 (mod 12) below 337 (root state (q, [], [])) and for every prime slot z = 1
# (mod 3) below 1225 with q unknown (root state (0, [z], [])), in the exact format checked by
# RestrainedFive.check, and a flat Pratt certificate for the forced primes from 100 up.
# See SPEC.md for the format. Also prints the three dummy primes = 11 (mod 12) above 10^6.
# Used by: OddPerfect/RestrainedFive.lean (prattCert, qRoots, zRoots).
# Run: python3 -I gen13.py [output file]   (default data13.lean in the current folder)
# Requires: Python 3 and sympy (factorint, isprime). Deterministic. Running time: about a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: the output file is written to the path given, relative to the current folder.
# License: GPL 3, same as the repository.
import sys
from sympy import factorint, isprime

Q0 = 337     # q below Q0 is refuted outright; above it q is "unknown, at least Q0"
XS = 1225    # slots below XS are refuted when q is unknown

def phi3(t): return t * t + t + 1

PR = set()   # every forced prime used in a tree

def build(qk, sl, o2):
    # First source with an unlisted prime factor d; its three roles become the children.
    srcs = [(p, phi3(p)) for p in sorted(set(sl) | set(o2))]
    if qk:
        srcs.append((0, qk + 1))
    for p, n in srcs:
        for d in sorted(factorint(n)):
            if d in (2, 3, 13) or d == qk or d in sl or d in o2:
                continue
            PR.add(d)
            slotC = d % 3 == 1 and len(sl) < 2 and n % d ** 3 != 0
            o2C = d % 3 == 2 and n % d ** 3 != 0
            qC = qk == 0 and d % 12 == 1 and Q0 <= d
            cs = build(qk, [d] + sl, o2) if slotC else None
            co = build(qk, sl, [d] + o2) if o2C else None
            cq = build(d, sl, o2) if qC else None
            return ('step', p, d, cs, co, cq)
    raise Exception("state not refuted: %s %s %s" % (qk, sl, o2))

def small(m): return any(2 <= d < m and m % d == 0 for d in range(100))
def size(t): return 0 if t is None else 1 + size(t[3]) + size(t[4]) + size(t[5])

def flat(n):
    out = []
    for f, e in sorted(factorint(n).items()):
        out += [f] * e
    return out

def pratt(primes):
    # Entries (p, a, prime factors of p - 1 with multiplicity); factors from 1000 up get
    # their own entry first, smaller ones are left to trial division in the Lean checker.
    entries, done = [], set()
    def add(p):
        if p in done:
            return
        fs = flat(p - 1)
        for f in set(fs):
            if f >= 1000:
                add(f)
        a = 2
        while not (pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // f, p) != 1 for f in set(fs))):
            a += 1
        entries.append((p, a, fs))
        done.add(p)
    for d in sorted(primes):
        if d >= 100:
            add(d)
    return entries

def lean_tree(t):
    if t is None:
        return ".dead"
    _, p, d, cs, co, cq = t
    return "(.step %d %d %s %s %s)" % (p, d, lean_tree(cs), lean_tree(co), lean_tree(cq))

def main():
    out = sys.argv[1] if len(sys.argv) > 1 else "data13.lean"
    qroots = [(q, build(q, [], [])) for q in range(Q0)
              if q % 12 == 1 and q > 1 and not small(q) and q != 13]
    zroots = [(z, build(0, [z], [])) for z in range(XS)
              if z % 3 == 1 and z > 1 and not small(z) and z != 13]
    assert all(isprime(q) for q, _ in qroots) and all(isprime(z) for z, _ in zroots)
    assert all(isprime(d) for d in PR)
    entries = pratt(PR)
    print("q roots", len(qroots), "nodes", sum(size(t) for _, t in qroots))
    print("z roots", len(zroots), "nodes", sum(size(t) for _, t in zroots))
    print("forced primes", len(PR), "largest", max(PR), "Pratt entries", len(entries))
    with open(out, "w") as f:
        f.write("private def prattCert : List (ℕ × ℕ × List ℕ) :=\n  [%s]\n\n" % (",\n   ".join(
            "(%d, %d, [%s])" % (p, a, ", ".join(map(str, fs))) for p, a, fs in entries)))
        f.write("private def qRoots : List (ℕ × KT) :=\n  [%s]\n\n" % (",\n   ".join(
            "(%d, %s)" % (q, lean_tree(t)) for q, t in qroots)))
        f.write("private def zRoots : List (ℕ × KT) :=\n  [%s]\n" % (",\n   ".join(
            "(%d, %s)" % (z, lean_tree(t)) for z, t in zroots)))
    ds = [p for p in range(10 ** 6, 10 ** 6 + 500) if p % 12 == 11 and isprime(p)][:3]
    print("dummies", ds)
    print("wrote", out)

if __name__ == "__main__":
    main()
