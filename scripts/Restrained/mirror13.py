# Untrusted helper script for the OddPerfect Lean library.
# Exact mirror of the certificates and inequalities of OddPerfect/RestrainedFive.lean (leaf
# r = 13). It reads prattCert, qRoots and zRoots from the Lean file itself (or from the output
# of gen13.py) and replays, with the semantics of the Lean functions: Pratt.check (pratt_ok),
# check (cert_q, cert_z), coverQ and coverZ over range 337 and range 1225 (cover_q, cover_z),
# rootIn (box_13, box_A), the weight conditions of rankin_tail3 and the two closing inequalities
# in exact rational arithmetic. It imports nothing from gen13.py. See SPEC.md.
# Used by: OddPerfect/RestrainedFive.lean.
# Run: python3 -I mirror13.py RestrainedFive.lean   (or the data13.lean written by gen13.py)
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: the input file is read from the path given, relative to the current folder.
# License: GPL 3, same as the repository.
import re, sys
from fractions import Fraction as F

def phi3(t): return t * t + t + 1

# ---- reading the Lean literals ----
def decl(text, name):
    i = text.index("private def %s " % name)
    i = text.index(":=", i) + 2
    j = text.find("\nprivate ", i)
    return text[i:] if j < 0 else text[i:j]

def tokens(s): return re.findall(r"\.step|\.dead|\d+|[()\[\],]", s)

class P:
    def __init__(self, s): self.t, self.i = tokens(s), 0
    def peek(self): return self.t[self.i]
    def eat(self, x=None):
        v = self.t[self.i]
        assert x is None or v == x, (v, x)
        self.i += 1
        return v
    def num(self): return int(self.eat())
    def tree(self):
        if self.peek() == ".dead":
            self.eat(); return None
        self.eat("("); self.eat(".step")
        p, d = self.num(), self.num()
        cs, co, cq = self.tree(), self.tree(), self.tree()
        self.eat(")")
        return (p, d, cs, co, cq)
    def lst(self, item):
        self.eat("["); out = []
        while self.peek() != "]":
            out.append(item())
            if self.peek() == ",": self.eat(",")
        self.eat("]")
        return out

def pratt_entry(p):
    p.eat("("); a = p.num(); p.eat(","); b = p.num(); p.eat(",")
    fs = p.lst(p.num); p.eat(")")
    return (a, b, fs)

def root_entry(p):
    p.eat("("); a = p.num(); p.eat(","); t = p.tree(); p.eat(")")
    return (a, t)

# ---- Lean functions ----
def trialPrime(q): return 2 <= q and all(q % d != 0 for d in range(2, q))   # Pratt.trialPrime

def pratt_check(c):                                                         # Pratt.check
    known = []
    for p, a, fs in c:
        prod = 1
        for f in fs: prod *= f
        if not (prod == p - 1 and all(f in known or trialPrime(f) for f in fs)
                and pow(a, p - 1, p) == 1 and all(pow(a, (p - 1) // f, p) != 1 for f in fs)):
            return False
        known.append(p)
    return True

def make_check(PL, Q0):
    def isPr(d): return (d < 100 and trialPrime(d)) or d in PL
    def check(qk, sl, o2, t):
        if t is None: return False
        p, d, cs, co, cq = t
        n = qk + 1 if p == 0 else phi3(p)                                  # srcVal
        src = (qk != 0) if p == 0 else (p in sl or p in o2)                 # srcOK
        if not (src and isPr(d) and n % d == 0 and d not in (2, 3, 13) and d != qk
                and d not in sl and d not in o2):
            return False
        if d % 3 == 1 and len(sl) < 2 and n % d ** 3 != 0 and not check(qk, [d] + sl, o2, cs):
            return False
        if d % 3 == 2 and n % d ** 3 != 0 and not check(qk, sl, [d] + o2, co):
            return False
        if qk == 0 and d % 12 == 1 and Q0 <= d and not check(d, sl, o2, cq):
            return False
        return True
    return check

def hasSmallFactor(m): return any(2 <= d and d < m and m % d == 0 for d in range(100))

def lowRoot(V, f, lo, hi):
    while f > 0:
        m = (lo + hi) // 2
        if phi3(m) <= V: lo = m
        else: hi = m
        f -= 1
    return lo

def rootIn(L, V):
    m = lowRoot(V, 64, 0, 2 ** 40)
    return (phi3(m) < V and V < phi3(m + 1)) or (phi3(m) == V and m in L)

def tail3(b1, beta, a1, a2, a3, a4):                     # conclusion of rankin_tail3
    return F(121, 100) * (beta * (1 / (1 - b1) * (1 * (1 * 1))) +
        (a2 + a3 + a4) * (1 / (1 - a1) * (1 / (1 - a2) * (1 / (1 - a3) * (1 / (1 - a4))))))

def main():
    text = open(sys.argv[1], encoding="utf-8").read()
    PP = P(decl(text, "prattCert")); cert = PP.lst(lambda: pratt_entry(PP))
    PQ = P(decl(text, "qRoots")); qroots = PQ.lst(lambda: root_entry(PQ))
    PZ = P(decl(text, "zRoots")); zroots = PZ.lst(lambda: root_entry(PZ))
    res = {}
    res["pratt_ok"] = pratt_check(cert)
    PL = [e[0] for e in cert]
    check = make_check(PL, 337)
    res["cert_q"] = all(check(q, [], [], t) for q, t in qroots)
    res["cert_z"] = all(check(0, [z], [], t) for z, t in zroots)
    qs = [q for q, _ in qroots]; zs = [z for z, _ in zroots]
    res["cover_q"] = all(q % 12 != 1 or q <= 1 or hasSmallFactor(q) or q == 13 or q in qs
                         for q in range(337))
    res["cover_z"] = all(z % 3 != 1 or z <= 1 or hasSmallFactor(z) or z == 13 or z in zs
                         for z in range(1225))
    res["box_13"] = all(not 13 ** a < 10 ** 16 or rootIn([0, 3], 13 ** a) for a in range(15))
    res["box_A"] = all(not 3 * 13 ** a < phi3(10 ** 6) or rootIn([1, 22], 3 * 13 ** a)
                       for a in range(12))
    # side facts used with the boxes: 10^16 <= 13^15 and phi3(10^6) <= 13^12
    res["box bounds"] = 10 ** 16 <= 13 ** 15 and phi3(10 ** 6) <= 13 ** 12
    a1, b1, beta = F(2774, 10000), F(527, 1000), F(1, 10 ** 4)
    res["weights"] = (a1 ** 2 * 13 >= 1 and b1 ** 4 * 13 >= 1 and beta ** 4 * 10 ** 16 >= 1
                      and F(1, 18) ** 2 * 337 >= 1 and F(1, 35) ** 2 * 1225 >= 1
                      and F(1, 1000) ** 2 * 10 ** 6 >= 1)
    # the dummy primes (norm_num in Lean): trial division up to 1000 > sqrt(1000199)
    res["dummies"] = all(all(p % d for d in range(2, 1001)) and p % 12 == 11
                         for p in (1000151, 1000187, 1000199))
    # branch q = 1 (mod 12): q >= 337, at most two slots, each >= 1225
    SB = 2 * (F(121, 100) * (1 / F(1225 + 1))) + tail3(b1, beta, a1, F(1, 18), F(1, 35), F(1, 35))
    LB = F(13, 9) * (F(13, 12) * (F(337) / (F(337) - 1)))
    res["close q = 1 mod 12"] = LB < 2 * (1 - SB)
    # branch q = 2 (mod 3): q >= 5, at most one slot, which is >= 10^6
    SA = 1 * (F(121, 100) * (1 / F(10 ** 6 + 1))) + tail3(b1, beta, a1, F(1, 1000), F(1, 1000),
                                                          F(1, 1000))
    LA = F(13, 9) * (F(13, 12) * (F(5) / (F(5) - 1)))
    res["close q = 2 mod 3"] = LA < 2 * (1 - SA)
    print("Pratt entries", len(cert), "largest", max(PL))
    print("q roots", len(qroots), "z roots", len(zroots))
    print("q = 1 mod 12: %.7f < %.7f" % (LB, 2 * (1 - SB)))
    print("q = 2 mod 3:  %.7f < %.7f" % (LA, 2 * (1 - SA)))
    for k, v in res.items():
        print(k, v)
    ok = all(res.values())
    print("all checks pass" if ok else "FAILED")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
