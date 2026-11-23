"""Untrusted helper script for the OddPerfect Lean library.

Independent recheck of the two exception certificate of search.py. It was written from a text of
the certificate format alone (an earlier version of FORMAT.md), without the code of search.py,
engine.py or the Lean checker, and it imports no other script. Nothing in the
library depends on it: the Lean kernel checks the certificate through
OddPerfect/TwoExceptionTwo*.lean.

What it checks: every record is reached from the root exactly once (a tree) and every record is
reached; the root state is x = 5, S = {3}, F empty, q undecided. Every core state (x, q, exq, S,
F) is derived from the parent's: the children of a force or decide record are exactly the
admissible roles of the prime, a decide record has its absent child, no unlisted prime is skipped
by a closed, decide or absent step, the receipt and split children change only the entry of
their prime and as allowed. Every leaf is recomputed from its core state: budgets from exact
valuations of sigma of every listed component (not from the stored contribution lists), absent
forced primes, abundant divisors, rule L, receipt leaves without a feasible sender, and every
deficient leaf with exact rational arithmetic (its own a, b, c, d, K, u, H, its own enumeration
of the hits, its own Rankin witnesses, S < 1 and U < 2). The values and factor lists of every
record are recomputed; the stored contribution lists, slots, hits and bounds are compared as
hints, and a stored value that would weaken the argument is an error.

What it does not check: the tail bound statement itself (TAIL_BOUND.md; its Lean counterpart is
in OddPerfect/RankinTailGeneral.lean) and the rules of FORMAT.md, which it takes as given; the
landed theorems behind rule L and the q rules; the fields `generated` and `nonhits` with their
composite witnesses (it enumerates the hits itself instead); the header values DMAX and KCAP (it
does not need them). It also does not follow the bookkeeping of section 3.1 of FORMAT.md that
soundness does not need: the order of the items, the order in which the outcomes are tested,
and that the forced prime is the least pending one (it checks that the forced prime is an odd
prime at least x, unlisted, and dividing a guaranteed component value).
Primality is by a Miller Rabin test with the first thirteen prime bases, exact below
3.3 * 10^24 (larger numbers raise an error); the certificate needs it only below 2^64.

Run: python3 -I check.py CERT   (CERT is cert.jsonl.xz or the decompressed file)
Prints the counts, the errors and warnings and a final line VERDICT PASS or VERDICT FAIL.
Exit status: 0 for PASS, 1 for FAIL, 2 for a usage error or an unreadable file.
Requires: Python 3 standard library only. Running time: a few seconds.
License: GPL 3, same as the repository.
"""
import json
import lzma
import sys
import time
from fractions import Fraction as Fr
from functools import lru_cache
from math import gcd, isqrt
from collections import Counter, defaultdict

LIST_L = (7, 13, 19, 31, 61, 97, 127, 331)

# ---------------------------------------------------------------- arithmetic


def is_prime(n):
    """Deterministic Miller Rabin; valid for n < 3.3e24 (first 13 prime bases)."""
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
    for p in small:
        if n % p == 0:
            return n == p
    if n >= 3317044064679887385961981:
        raise ValueError("primality out of deterministic range: %d" % n)
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def iroot(n, k):
    """floor(n ** (1/k)) exactly."""
    if n < 2:
        return n
    r = 1 << ((n.bit_length() + k - 1) // k)
    while True:
        s = ((k - 1) * r + n // r ** (k - 1)) // k
        if s >= r:
            break
        r = s
    while r ** k > n:
        r -= 1
    while (r + 1) ** k <= n:
        r += 1
    return r


def vp(n, p):
    if n == 0:
        raise ValueError("v_p(0)")
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


@lru_cache(maxsize=None)
def sigma_pow(c, m):
    """sigma(c^m) = 1 + c + ... + c^m."""
    return (c ** (m + 1) - 1) // (c - 1)


def mobius(n):
    res, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            res = -res
        p += 1
    return -res if n > 1 else res


@lru_cache(maxsize=None)
def cyclo(d, x):
    num, den = 1, 1
    for e in range(1, d + 1):
        if d % e == 0:
            mu = mobius(d // e)
            if mu == 1:
                num *= x ** e - 1
            elif mu == -1:
                den *= x ** e - 1
    if num % den:
        raise ValueError("cyclotomic division failed")
    return num // den


def mult_order(g, p):
    """d = ord_p(g) if g != 1 mod p, d = p if g = 1 mod p (so p | sigma(g^k) iff d | k+1)."""
    if g % p == 1:
        return p
    n = p - 1
    d = n
    q = 2
    m = n
    fac = []
    while q * q <= m:
        if m % q == 0:
            fac.append(q)
            while m % q == 0:
                m //= q
        q += 1
    if m > 1:
        fac.append(m)
    for q in fac:
        while d % q == 0 and pow(g, d // q, p) == 1:
            d //= q
    return d


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------- state

class Core:
    __slots__ = ("x", "q", "exq", "S", "F")

    def __init__(self, x, q, exq, S, F):
        self.x, self.q, self.exq, self.S, self.F = x, q, exq, S, F

    def key(self):
        return (self.x, self.q, self.exq, self.S, tuple(sorted(self.F.items())))

    def copy(self, **kw):
        c = Core(self.x, self.q, self.exq, self.S, dict(self.F))
        for k, v in kw.items():
            setattr(c, k, v)
        return c

    def listed(self, p):
        return p in self.S or p in self.F

    def nexc(self):
        return len(self.F) - (1 if self.q is not None else 0)

    def __repr__(self):
        return "Core(x=%s q=%s exq=%s S=%s F=%s)" % (self.x, self.q, sorted(self.exq),
                                                     sorted(self.S), dict(sorted(self.F.items())))


def core_of(st):
    return Core(st["x"], st["q"], frozenset(st["exq"]), frozenset(int(k) for k in st["S"]),
                {int(k): tuple(v) for k, v in st["F"].items()})


def comp_value(c, core):
    """A divisor of sigma(c^{v_c(N)}) guaranteed by the core state."""
    if c in core.S:
        return 13 if c == 3 else c * c + c + 1
    D, no3, kmin, exact = core.F[c]
    return sigma_pow(c, kmin if exact else D - 1)


def w_lb(p, core):
    """Lower bound of w(p) = v_p(sigma(N)) from all listed components other than p."""
    tot = 0
    for c in list(core.S) + list(core.F):
        if c != p:
            v = comp_value(c, core)
            if v % p == 0:
                tot += vp(v, p)
    return tot


def is_q(p, core):
    return core.q == p


def allowed(p, entry, core, k, D=None):
    Dd, no3, kmin, exact = entry
    if D is None:
        D = Dd
    if k < kmin or (k + 1) % D:
        return False
    if exact and k != kmin:
        return False
    if no3 and (k + 1) % 3 == 0:
        return False
    if is_q(p, core):
        return (k + 1) % 4 == 2
    return k % 2 == 0 and k >= 4


def least_allowed(p, entry, core, D, start):
    span = 12 * D + 24
    for k in range(start, start + span + 1):
        if allowed(p, entry, core, k, D):
            return k
    return None


# ---------------------------------------------------------------- checker

class Checker:
    def __init__(self, path=None, recs=None):
        if recs is not None:
            self.recs = recs
        else:
            self.recs = {}
            with (lzma.open(path, "rt") if path.endswith(".xz") else open(path)) as f:
                for line in f:
                    r = json.loads(line)
                    if r["id"] in self.recs:
                        raise ValueError("duplicate id %s" % r["id"])
                    self.recs[r["id"]] = r
        h = self.recs.get(0)
        if h is None or h.get("kind") != "header":
            raise ValueError("record 0 is not a header")
        self.h = h
        self.EMAX = h["EMAX"]
        self.landed = "nolanded" not in h["flags"]
        self.flags = h["flags"]
        self.MHIT = h["MHIT"]
        self.errors = []
        self.warnings = Counter()
        self.warn_examples = {}
        self.leaves = Counter()
        self.kinds = Counter()
        self.hint_mismatch = Counter()
        self.core_cache = {}
        self.incoming = Counter()
        self.max_x = 0

    def err(self, rid, msg):
        self.errors.append((rid, msg))

    def warn(self, tag, rid, msg=""):
        self.warnings[tag] += 1
        self.warn_examples.setdefault(tag, (rid, msg))

    # state of a record (explicit, or prev with x advanced)
    def core(self, rid):
        if rid in self.core_cache:
            return self.core_cache[rid]
        r = self.recs[rid]
        if r.get("state") is not None:
            c = core_of(r["state"])
            if r["kind"] in ("decide", "check") and r["state"]["x"] != r["x"]:
                # format: decide x is the smallest prime >= state.x not listed
                gap = self.primes_between_listed(c, r["state"]["x"], r["x"])
                if gap is not None or r["x"] < r["state"]["x"]:
                    self.err(rid, "record x %s skips unlisted prime %s above state x %s"
                             % (r["x"], gap, r["state"]["x"]))
            if r["kind"] in ("decide", "check"):
                c = c.copy(x=r["x"])
        else:
            prev = r.get("prev")
            if prev is None or prev not in self.recs:
                raise ValueError("record %s: no state and no prev" % rid)
            c = self.core(prev).copy(x=r["x"])
        self.core_cache[rid] = c
        return c

    def primes_between_listed(self, core, lo, hi):
        """every prime p with lo <= p < hi is listed"""
        for p in range(max(lo, 2), hi):
            if is_prime(p) and not core.listed(p):
                return p
        return None

    # admissible roles of a prime f that divides N, as expected F entries
    def roles(self, f, core):
        out = {"square": None}
        if core.q is None and f % 4 == 1 and f not in core.exq and \
                not (self.landed and (f == 5 or f % 9 == 8)):
            if f % 3 == 1:
                out["q0"] = (2, True, 1, False)
                out["q3"] = (6, False, 5, False)
            elif f % 3 == 2:
                out["q"] = (2, bool(self.landed), 1, False)
        if core.nexc() < self.EMAX:
            if f % 3 == 1:
                out["e"] = (1, True, 4, False)
                out["e3"] = (3, False, 8, False)
            elif f % 3 == 2:
                out["e"] = (1, False, 4, False)
        return out

    def add_role(self, core, f, role, entry):
        if role == "square":
            return core.copy(S=core.S | {f})
        F = dict(core.F)
        F[f] = entry
        q = f if role in ("q0", "q3", "q") else core.q
        return core.copy(F=F, q=q)

    def same(self, a, b):
        return a.key() == b.key()

    def check_role_children(self, rid, f, pcore, children):
        exp = self.roles(f, pcore)
        seen = set()
        for cid in children:
            c = self.recs.get(cid)
            if c is None:
                self.err(rid, "missing child %s" % cid)
                continue
            if c["kind"] != "apply":
                self.err(rid, "role child %s is not apply" % cid)
                continue
            a = c["action"]
            role = a.get("role")
            if a.get("prime") != f:
                self.err(cid, "role child for wrong prime %s != %s" % (a.get("prime"), f))
                continue
            if role not in exp:
                self.err(cid, "role %s of %d is not admissible here" % (role, f))
                continue
            want = self.add_role(pcore, f, role, exp[role])
            got = self.core(cid)
            if not self.same(want, got):
                self.err(cid, "role child core mismatch\n want %r\n got  %r" % (want, got))
            seen.add(role)
        for role in exp:
            if role not in seen:
                self.err(rid, "admissible role %s of %d has no child" % (role, f))

    # ---------------------------------------------------------- per record

    def check_values_items(self, rid, r, core):
        """Hint level checks of values and items (closure bookkeeping)."""
        vals = {}
        for v in r.get("values", []):
            src = v["src"]
            if src[0] == "row":
                p = src[1]
                val = 13 if p == 3 else p * p + p + 1
            elif src[0] == "cyc":
                d, p = src[1], src[2]
                val = cyclo(d, p)
            else:
                self.err(rid, "unknown value src %r" % (src,))
                continue
            if "value" in v and int(v["value"]) != val:
                self.err(rid, "value mismatch for %r" % (src,))
            prod = 1
            for p, e in v["factors"]:
                if not is_prime(p):
                    self.err(rid, "factor %d of %r not prime" % (p, src))
                if vp(val, p) != e:
                    self.err(rid, "factor %d^%d not exact in %r" % (p, e, src))
                prod *= p ** e
            odd = val
            while odd % 2 == 0:
                odd //= 2
            if v["complete"] and prod != odd:
                self.err(rid, "complete factorization of %r wrong" % (src,))
            vals[tuple(src)] = val
        for it in r.get("items", []):
            p, w, src = it
            if src[0] == "row":
                c = src[1]
                if c not in core.S:
                    self.err(rid, "item from row of unlisted square %s" % c)
                    continue
                val = 13 if c == 3 else c * c + c + 1
                if w > vp(val, p):
                    self.err(rid, "item weight too big %r" % (it,))
            elif src[0] == "cyc":
                d, c = src[1], src[2]
                if c not in core.F:
                    self.err(rid, "item from cyc of unlisted %s" % c)
                    continue
                D = core.F[c][0]
                if D % d:
                    self.err(rid, "item cyc %d of %d but D=%d" % (d, c, D))
                if w > vp(cyclo(d, c), p):
                    self.err(rid, "item weight too big %r" % (it,))
            elif src[0] == "receipt":
                _, pp, d, g = src
                if pp != p or w != 1:
                    self.err(rid, "receipt item shape %r" % (it,))
                if g not in core.F or core.F[g][0] % d or mult_order(g, p) != d:
                    self.err(rid, "receipt item not justified %r" % (it,))
            else:
                self.warn("item src kind " + src[0], rid)

    def contribution_lists(self, rid, core, st):
        """Double count check: per receiver and per component, stored weights must be at most
        v_p of the guaranteed divisor of that component."""
        for key in ("S", "R"):
            for ps, lst in st[key].items():
                p = int(ps)
                per = defaultdict(int)
                for src, w in lst:
                    if src[0] in ("row",):
                        c = src[1]
                    elif src[0] == "cyc":
                        c = src[2]
                    elif src[0] == "receipt":
                        c = src[3]
                    else:
                        continue
                    per[c] += w
                for c, w in per.items():
                    if not core.listed(c) or c == p:
                        self.err(rid, "contribution to %d from unlisted/self %d" % (p, c))
                        continue
                    if w > vp(comp_value(c, core), p):
                        self.err(rid, "double count: %d receives %d from %d, only %d possible"
                                 % (p, w, c, vp(comp_value(c, core), p)))

    def run(self):
        root = self.h["root"]
        self.incoming[root] += 1
        # the root state is the only one not derived from a parent: check it against the family
        rc = self.core(root)
        want = Core(5, None, frozenset(), frozenset({3}), {})
        if self.recs[root]["kind"] != "apply" or not self.same(rc, want):
            self.err(root, "root state %r is not x=5, S={3}, F empty, q undecided" % rc)
        if self.EMAX not in (1, 2) or self.MHIT < 1:
            self.err(0, "unexpected header %r" % self.h)
        stack = [(root, None)]
        visited = set()
        while stack:
            rid, parent = stack.pop()
            if rid not in self.recs:
                self.err(parent, "missing record %s" % rid)
                continue
            if rid in visited:
                self.err(parent, "record %s reached twice" % rid)
                continue
            visited.add(rid)
            r = self.recs[rid]
            self.kinds[r["kind"]] += 1
            try:
                kids = self.check_record(rid, r)
            except Exception as ex:  # report and continue
                self.err(rid, "exception %r" % (ex,))
                kids = []
            for k in kids:
                self.incoming[k] += 1
                stack.append((k, rid))
        unreached = set(self.recs) - visited - {0}
        if unreached:
            self.err(None, "%d records not reachable from root" % len(unreached))
        shared = sum(1 for k, v in self.incoming.items() if v > 1)
        if shared:
            self.err(None, "%d records have several parents (not a tree)" % shared)
        return visited

    def check_record(self, rid, r):
        kind = r["kind"]
        core = self.core(rid)
        self.max_x = max(self.max_x, core.x)
        if kind == "apply":
            return self.check_apply(rid, r, core)
        if kind == "decide":
            return self.check_decide(rid, r, core)
        if kind == "check":
            self.leaves[("check", r.get("reason"))] += 1
            self.check_leaf(rid, r, core, r.get("reason"))
            return []
        if kind == "split":
            return self.check_split(rid, r, core)
        self.err(rid, "unknown kind %s" % kind)
        return []

    def check_apply(self, rid, r, core):
        self.check_values_items(rid, r, core)
        self.contribution_lists(rid, core, r["state"])
        out = r["outcome"]
        if out == "leaf":
            self.leaves[("apply", r["reason"])] += 1
            self.check_leaf(rid, r, core, r["reason"])
            return []
        if out == "force":
            f = r["forced"]
            if not is_prime(f) or f < core.x or core.listed(f):
                self.err(rid, "forced %d not a pending prime" % f)
            if not any(comp_value(c, core) % f == 0 for c in list(core.S) + list(core.F)
                       if c != f):
                self.err(rid, "forced %d divides no guaranteed component value" % f)
            self.check_role_children(rid, f, core, r["children"])
            return r["children"]
        if out == "closed":
            if len(r["children"]) != 1:
                self.err(rid, "closed with %d children" % len(r["children"]))
            nx = r["next_x"]
            if nx < core.x:
                self.err(rid, "next_x below x")
            gap = self.primes_between_listed(core, core.x, nx)
            if gap is not None:
                self.err(rid, "closed skips unlisted prime %d" % gap)
            for cid in r["children"]:
                c = self.recs[cid]
                if c["kind"] not in ("decide", "split", "check"):
                    self.err(cid, "closed child kind %s" % c["kind"])
                cx = self.core(cid).x
                st = c.get("state")
                if st is not None and st["x"] != nx:
                    self.err(cid, "closed child state x %s != next_x %s" % (st["x"], nx))
                gap = self.primes_between_listed(core, core.x, cx)
                if gap is not None:
                    self.err(cid, "closed child skips unlisted prime %d" % gap)
                want = core.copy(x=cx)
                if not self.same(want, self.core(cid)):
                    self.err(cid, "closed child core mismatch\n want %r\n got  %r"
                             % (want, self.core(cid)))
            return r["children"]
        if out == "receipt":
            return self.check_receipt(rid, r, core)
        self.err(rid, "unknown outcome %s" % out)
        return []

    def check_receipt(self, rid, r, core):
        p = r["receiver"]
        if not (core.listed(p) and p % 3 == 2 and is_prime(p)):
            self.err(rid, "receiver %d not a listed prime = 2 mod 3" % p)
        if core.q is None or core.nexc() != self.EMAX:
            self.err(rid, "receipt applied while a free prime may be unlisted")
        feasible = {}
        for g, entry in core.F.items():
            if g == p:
                continue
            d = mult_order(g, p)
            Dn = lcm(entry[0], d)
            k = least_allowed(g, entry, core, Dn, entry[2])
            if k is not None:
                feasible[g] = (d, Dn, k)
            else:
                si = r.get("senders_infeasible", {}).get(str(g))
                if si is None or si["d"] != d:
                    self.hint_mismatch["receipt infeasible list"] += 1
        seen = set()
        for cid in r["children"]:
            c = self.recs[cid]
            a = c["action"]
            g = a.get("sender")
            if c["kind"] != "apply" or a.get("role") != "sender" or a.get("receiver") != p:
                self.err(cid, "receipt child shape")
                continue
            if g not in feasible:
                self.warn("receipt child for infeasible sender", cid)
                continue
            d, Dn, k = feasible[g]
            if a.get("d") != d:
                self.err(cid, "receipt d %s != %d" % (a.get("d"), d))
            got = self.core(cid)
            old = core.F[g]
            ge = got.F.get(g)
            other_ok = self.same(core.copy(F={**core.F, g: ge}), got) if ge else False
            if not other_ok:
                self.err(cid, "receipt child changes more than F[%d]" % g)
            elif not (Dn % ge[0] == 0 and ge[1] == old[1] and ge[3] == old[3]
                      and old[2] <= ge[2] <= k):
                self.err(cid, "receipt child entry %r not justified (D=%d, least k=%d)"
                         % (ge, Dn, k))
            elif ge[0] != Dn or ge[2] != k:
                self.warn("receipt child weaker than possible", cid)
            seen.add(g)
        for g in feasible:
            if g not in seen:
                self.err(rid, "feasible sender %d of %d has no child" % (g, p))
        if not r["children"]:
            self.err(rid, "receipt with no children but outcome receipt")
        return r["children"]

    def check_decide(self, rid, r, core):
        x = r["x"]
        if not is_prime(x) or core.listed(x):
            self.err(rid, "decide x=%d not an unlisted prime" % x)
        self.check_role_children(rid, x, core, r["children"])
        a = r.get("absent")
        if a is None or a not in self.recs:
            self.err(rid, "decide without absent child")
            return r["children"]
        ac = self.core(a)
        if self.recs[a]["kind"] not in ("decide", "check"):
            self.err(a, "absent child kind")
        if ac.x <= x:
            self.err(a, "absent child x not above decided prime")
        gap = self.primes_between_listed(core, x + 1, ac.x)
        if gap is not None:
            self.err(a, "absent child skips unlisted prime %d" % gap)
        if not self.same(core.copy(x=ac.x), ac):
            self.err(a, "absent child core mismatch\n want %r\n got  %r" % (core.copy(x=ac.x), ac))
        return list(r["children"]) + [a]

    def check_split(self, rid, r, core):
        p = r["prime"]
        if p not in core.F or core.F[p][3]:
            self.err(rid, "split on non free or exact prime")
            return r["children"]
        D, no3, kmin, exact = core.F[p]
        if r["kmin"] != kmin:
            self.err(rid, "split kmin mismatch")
        nxt = least_allowed(p, core.F[p], core, D, kmin + 1)
        kinds = Counter()
        for cid in r["children"]:
            c = self.recs[cid]
            a = c["action"]
            got = self.core(cid)
            ge = got.F.get(p)
            if ge is None or not self.same(core.copy(F={**core.F, p: ge}), got):
                self.err(cid, "split child changes more than F[p]")
                continue
            if a["role"] == "exact":
                kinds["exact"] += 1
                # exact branch: any D' with D | D' | kmin+1 is implied (or branch empty)
                if not (ge[2] == kmin and ge[3] and ge[1] == no3 and (kmin + 1) % ge[0] == 0
                        and ge[0] % D == 0):
                    self.err(cid, "exact child entry %r" % (ge,))
            elif a["role"] == "atleast":
                kinds["atleast"] += 1
                if not (ge[0] == D and ge[1] == no3 and not ge[3] and kmin < ge[2] <= nxt):
                    self.err(cid, "atleast child entry %r, next allowed %s" % (ge, nxt))
            else:
                self.err(cid, "split child role")
        if kinds != Counter({"exact": 1, "atleast": 1}):
            self.err(rid, "split children %r" % kinds)
        return r["children"]

    # ---------------------------------------------------------- leaves

    def check_leaf(self, rid, r, core, reason):
        pf = r.get("proof", {})
        if reason in ("cap", "cap3", "capexact"):
            p = pf["prime"]
            if p in core.S:
                budget = 2
            elif p in core.F and core.F[p][3]:
                budget = core.F[p][2]
            else:
                self.err(rid, "cap on prime without budget")
                return
            w = w_lb(p, core)
            if w <= budget:
                self.err(rid, "cap not reached: w_lb(%d)=%d budget %d" % (p, w, budget))
            # the stored proof must itself be a valid argument
            if pf.get("budget") != budget:
                self.err(rid, "proof budget %s != true budget %d" % (pf.get("budget"), budget))
            per = defaultdict(int)
            for src, wt in pf.get("contributions", []):
                c = {"row": lambda s: s[1], "cyc": lambda s: s[2],
                     "receipt": lambda s: s[3]}.get(src[0], lambda s: None)(src)
                if c is None or c == p or not core.listed(c):
                    self.err(rid, "proof contribution from %r invalid" % (src,))
                    continue
                per[c] += wt
            for c, wt in per.items():
                if wt > vp(comp_value(c, core), p):
                    self.err(rid, "proof claims %d from %d to %d, only %d"
                             % (wt, c, p, vp(comp_value(c, core), p)))
            if sum(per.values()) <= budget:
                self.err(rid, "proof contributions sum %d not above budget" % sum(per.values()))
            if (reason == "cap3") != (p == 3):
                self.warn("cap3 label", rid)
        elif reason == "absentforced":
            p = pf["prime"]
            if not (p % 2 == 1 and is_prime(p) and p < core.x and not core.listed(p)):
                self.err(rid, "absentforced prime %d not an absent odd prime" % p)
            elif not any(comp_value(c, core) % p == 0 for c in list(core.S) + list(core.F)):
                self.err(rid, "absentforced prime %d divides no component" % p)
        elif reason == "abundant":
            ratio = Fr(1)
            seen = set()
            for p, e in pf["divisor"]:
                if p in seen:
                    self.err(rid, "repeated divisor prime")
                seen.add(p)
                if p in core.S:
                    ok = 0 <= e <= 2
                elif p in core.F:
                    ok = 0 <= e <= core.F[p][2]
                else:
                    ok = False
                if not ok:
                    self.err(rid, "divisor exponent %d^%d not allowed" % (p, e))
                ratio *= Fr(sigma_pow(p, e), p ** e)
            if not ratio > 2:
                self.err(rid, "abundant ratio %s not > 2" % ratio)
            if Fr(pf["ratio"]) != ratio:
                self.hint_mismatch["abundant ratio"] += 1
                self.warn("abundant ratio differs", rid, "%s vs mine %s" % (pf["ratio"], ratio))
        elif reason == "landedL":
            if not self.landed:
                self.err(rid, "landedL without landed facts")
                return
            for p in LIST_L:
                if p in core.F and p != core.q:
                    D, no3, kmin, exact = core.F[p]
                    three_divides = D % 3 == 0 or (exact and (kmin + 1) % 3 == 0)
                    if not three_divides:
                        self.err(rid, "landedL but listed exception %d may have 3 not | k+1" % p)
            if core.nexc() < self.EMAX:
                for p in LIST_L:
                    if not core.listed(p) and p >= core.x and p != core.q:
                        self.err(rid, "landedL but %d can still become an exception" % p)
        elif reason == "receipt":
            # receipt leaf: no feasible sender at all
            p = pf.get("receiver", r.get("receiver"))
            if p is None:
                self.err(rid, "receipt leaf without receiver")
                return
            if not (core.listed(p) and p % 3 == 2 and is_prime(p)):
                self.err(rid, "receipt leaf receiver %s invalid" % p)
            if core.q is None or core.nexc() != self.EMAX:
                self.err(rid, "receipt leaf while a free prime may be unlisted")
            for g, entry in core.F.items():
                if g == p:
                    continue
                d = mult_order(g, p)
                if least_allowed(g, entry, core, lcm(entry[0], d), entry[2]) is not None:
                    self.err(rid, "receipt leaf but %d can send %d" % (g, p))
        elif reason == "deficient":
            self.check_deficient(rid, r, core, pf)
        else:
            self.err(rid, "leaf reason %s not accepted" % reason)

    def check_deficient(self, rid, r, core, pf):
        x = core.x
        if pf.get("x") != x:
            self.err(rid, "proof x mismatch")
        EMAX = self.EMAX
        H = Fr(1)
        for p in core.S:
            H *= Fr(13, 9) if p == 3 else Fr(p * p + p + 1, p * p)
        for p, (D, no3, kmin, exact) in core.F.items():
            H *= Fr(sigma_pow(p, kmin), p ** kmin) if exact else Fr(p, p - 1)
        a = 1 if core.q is None else 0
        b = EMAX - core.nexc()
        if b < 0:
            self.err(rid, "more exceptions than EMAX")
        c = max(0, 2 - w_lb(3, core))
        dA = {p: max(0, 2 - w_lb(p, core)) for p in core.S if p % 3 == 1}
        dE = {g: max(0, e[2] - w_lb(g, core)) for g, e in core.F.items() if e[3] and g % 3 == 1}
        d = sum(dA.values()) + 2 * c + sum(dE.values())
        K = sorted(g for g, e in core.F.items() if not e[3] and g % 3 == 1)
        u = a + b
        # hint comparison
        for name, mine in (("a", a), ("b", b), ("c", c), ("d", d), ("u", u)):
            if pf.get(name) != mine:
                self.hint_mismatch["deficient " + name] += 1
                self.warn("deficient %s differs" % name, rid, "%s vs %s" % (pf.get(name), mine))
                if not isinstance(pf.get(name), int) or pf.get(name) < mine:
                    self.err(rid, "certificate slot %s=%s below justified %d"
                             % (name, pf.get(name), mine))
        if sorted(pf.get("K", [])) != K:
            self.hint_mismatch["deficient K"] += 1
            if not set(K) <= set(pf.get("K", [])):
                self.err(rid, "certificate K %s misses generators of %s" % (pf.get("K"), K))
        if Fr(pf["H"]) != H:
            self.hint_mismatch["deficient H"] += 1
        L = x * x + x + 1
        MHIT = self.MHIT
        # hits: n in <K>, L <= n < MHIT, n = t^2+t+1, t = 2 mod 3, t >= x, t unlisted
        hits = []
        stack = [(1, 0)]
        while stack:
            n, i = stack.pop()
            if n >= L:
                s2 = 4 * n - 3
                s = isqrt(s2)
                if s * s == s2:
                    t = (s - 1) // 2
                    # a hit is a prime factor t of N, so t must be prime
                    if t >= x and t % 3 == 2 and not core.listed(t) and is_prime(t):
                        hits.append((n, t))
            for j in range(i, len(K)):
                m = n * K[j]
                if m < MHIT:
                    stack.append((m, j))
        hitfac = Fr(1)
        for n, t in hits:
            hitfac *= Fr(n, t * t)
        if sorted(t for n, t in hits) != sorted(h[0] for h in pf.get("hits", [])):
            self.hint_mismatch["deficient hits"] += 1
            self.warn("deficient hits differ", rid, "%s vs %s" % (hits, pf.get("hits")))
            if not {t for n, t in hits} <= {h[0] for h in pf.get("hits", [])}:
                self.err(rid, "certificate hits %s miss %s" % (pf.get("hits"), hits))
        rk = pf["rankin"]
        if rk.get("mode") != "theta":
            self.err(rid, "rankin mode %s not implemented" % rk.get("mode"))
            return
        k = rk["k"]
        if not (isinstance(k, int) and k >= 2):
            self.err(rid, "bad Rankin k")
            return

        def alpha(g):
            rr = iroot(g * 10 ** (6 * k), k)
            if rr <= 10 ** 6:
                return None
            al = Fr(10 ** 6, rr)
            if al ** k * g < 1:
                raise ValueError("alpha witness fails for %d" % g)
            return al
        G = Fr(1)
        for g in K:
            al = alpha(g)
            if al is None:
                self.err(rid, "alpha >= 1 for %d" % g)
                return
            G *= 1 / (1 - al)
        ax = alpha(x)
        if ax is None:
            self.err(rid, "alpha_x >= 1")
            return
        if ax ** k * x < 1:
            raise ValueError("alpha_x witness fails")
        mL = Fr(iroot(L, k) + 1, isqrt(L))
        M = max(L, MHIT)
        mM = Fr(iroot(M, k) + 1, isqrt(M))
        R = mL * G * ((1 / (1 - ax)) ** u - 1) + mM * G
        Sb = Fr((x + 1) ** 2, x * x) * R
        if not Sb < 1:
            self.err(rid, "S >= 1")
            return
        U = H * Fr(x, x - 1) ** (a + b) * Fr(L, x * x) ** (c + d) * hitfac / (1 - Sb)
        if not U < 2:
            self.err(rid, "U = %s >= 2 (cert U %s)" % (float(U), pf.get("U")))
        if "U" in pf and Fr(pf["U"]) != U:
            self.hint_mismatch["deficient U"] += 1
            if Fr(pf["U"]) < U:
                self.err(rid, "certificate U %s below my justified bound %s"
                         % (float(Fr(pf['U'])), float(U)))
        if U > getattr(self, "max_U", Fr(0)):
            self.max_U, self.max_U_rid, self.max_U_info = U, rid, (x, a, b, c, d, K, u, k, float(Sb))


def main():
    if len(sys.argv) != 2:
        print("usage: python3 -I check.py CERT")
        sys.exit(2)
    path = sys.argv[1]
    t0 = time.time()
    try:
        rp = Checker(path)
    except (OSError, ValueError, KeyError, lzma.LZMAError) as ex:
        print("unreadable certificate:", ex)
        sys.exit(2)
    rp.run()
    dt = time.time() - t0
    nrec = len(rp.recs)
    nleaf = sum(rp.leaves.values())
    print("file", path)
    print("header", {k: rp.h[k] for k in rp.h if k != "id"})
    print("records", nrec, "(including header)", "reached kinds", dict(rp.kinds))
    print("leaves", nleaf, dict(sorted(rp.leaves.items(), key=str)))
    print("errors", len(rp.errors))
    for e in rp.errors[:30]:
        print("  ERR", e)
    print("warnings", dict(rp.warnings))
    for k, v in rp.warn_examples.items():
        print("  example", k, v)
    print("hint mismatches", dict(rp.hint_mismatch))
    if hasattr(rp, "max_U"):
        print("max U over deficient leaves", float(rp.max_U), "at record", rp.max_U_rid,
              "(x, a, b, c, d, K, u, k, S) =", rp.max_U_info)
    print("max x", rp.max_x)
    print("time %.1f s" % dt)
    print("VERDICT", "PASS" if not rp.errors else "FAIL")
    sys.exit(0 if not rp.errors else 1)


if __name__ == "__main__":
    main()
