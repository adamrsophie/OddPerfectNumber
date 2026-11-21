# Untrusted helper script for the OddPerfect Lean library.
# Certificate search for OddPerfect/EqualExponentChain.lean: for an odd prime l, a tree of
# ord / spec / branch / expo / overflow / mod4 steps showing that the exponents other than
# the special prime cannot all equal l - 1, plus the Pratt certificates it needs.
# Used by: OddPerfect/EqualExponentChain.lean (pc5 .. pc29, ord5 .. ord29, spec5 .. spec29).
# Build the helper first: cc -O2 -o osearch osearch.c (or set OSEARCH to its path).
# Run: python3 gen2.py L                 writes cert_L.json
#      python3 gen2.py L ord|spec        writes tree_L_ord.json or tree_L_spec.json
#      python3 gen2.py L merge           joins the two trees into cert_L.json
# The environment variable DEEPB sets the deeper osearch bound (default 2 * 10^9).
# Then emit.py or assemble.py turn cert_L.json into Lean, and checker.py rechecks it.
# Requires: Python 3 standard library and a C compiler. Running time: seconds for
# l = 5, 7; minutes to about half an hour per part for l = 17 to 29.
# This script does not reproduce the certificates in the Lean file: for l = 5, 7 and the
# ordinary part of l = 17 it finds different certificates (checker.py accepts the ones for
# l = 5 and 7; repeated runs for l = 5 give the same output). The certificates used in the
# Lean file are stored in certs/. How the search was configured when they were found was
# not recorded.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Certificate search for OddPerfect/EqualExponentChain.lean (see checker.py for the rules)."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
import math
import time
import subprocess
OSEARCH = os.environ.get('OSEARCH', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'osearch'))
from nt import factor, is_probable_prime, pratt, rho
from pm1 import PR

sys.setrecursionlimit(100000)

TRIAL = 2 * 10 ** 6       # trial bound for factors of Phi_l(p) (candidates r = 2lk + 1)
SPEC_TRIAL = 10 ** 5      # trial bound for factors of sigma(Q^(m-1))
EXPO_MAX = 5000
MMAX = 1000               # largest m used in spec / over steps
MAXP = 10 ** 50           # largest chain prime accepted
RHO_ITERS = 30000

FORD = {}
CERT_OK = {}


def certifiable(p):
    if p < 10 ** 12:
        return True
    if p not in CERT_OK:
        try:
            pratt(p, {})
            CERT_OK[p] = True
        except Exception:
            CERT_OK[p] = False
    return CERT_OK[p]
FSPEC = {}


def phi(p, n):
    return (p ** n - 1) // (p - 1)


def cofactor_primes(n, found):
    """Remove found primes from n, then try rho on the rest."""
    for r in found:
        while n % r == 0:
            n //= r
    out = set()
    stack = [n] if n > 1 else []
    tries = 0
    while stack and tries < 8:
        m = stack.pop()
        if m == 1:
            continue
        if is_probable_prime(m):
            if m <= MAXP and certifiable(m):
                out.add(m)
            continue
        if m.bit_length() > 400:
            continue
        f = rho(m, RHO_ITERS)
        tries += 1
        if f:
            stack += [f, m // f]
    return out


def osearch(p, l, B):
    out = subprocess.run([OSEARCH, str(p), str(l), str(2 * l), str(2 * l + 1), str(B)],
                         capture_output=True, text=True, check=True).stdout.split()
    return {int(x) for x in out if is_probable_prime(int(x))}


DEEP = set()


def deepen(known, l):
    for p in sorted(known):
        if p not in DEEP:
            DEEP.add(p)
            new = osearch(p, l, int(os.environ.get("DEEPB", 2 * 10 ** 9))) - set(FORD[p])
            if new:
                FORD[p] = sorted(set(FORD[p]) | new)
                return True
    return False


def facs_ord(p, l):
    if p not in FORD:
        found = set()
        pm = p
        if p % l == 1:
            found.add(l)
        found |= osearch(p, l, 2 * 10 ** 7)
        found |= cofactor_primes(phi(p, l), found)
        FORD[p] = sorted(x for x in found if x != 2)
    return FORD[p]


def facs_spec(Q, m):
    key = (Q, m)
    if key not in FSPEC:
        found = set()
        for r in PR:
            if r > SPEC_TRIAL:
                break
            if r == 2 or r == Q:
                continue
            if (Q - 1) % r == 0:
                if m % r == 0:
                    found.add(r)
            elif pow(Q, m, r) == 1:
                found.add(r)
        n = phi(Q, m)
        if n.bit_length() < 300:
            found |= cofactor_primes(n, found)
        FSPEC[key] = sorted(x for x in found if x != 2 and x != Q)
    return FSPEC[key]


def vs(n, s, cap):
    k = 0
    while k < cap and n % s == 0:
        n //= s
        k += 1
    return k


def divisors_small(M, bound):
    ds = [1]
    n = M
    p = 2
    fac = {}
    while p * p <= n and p < 10 ** 6:
        while n % p == 0:
            fac[p] = fac.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        fac[n] = fac.get(n, 0) + 1
    for p, e in fac.items():
        ds = [d * p ** i for d in ds for i in range(e + 1) if d * p ** i <= bound]
    return sorted(d for d in ds if d >= 2)


def try_close(l, known, qs, M):
    best = None
    for s in known:
        if s == 2:
            continue
        cs = []
        for p in known:
            k = vs(phi(p, l), s, l)
            if k:
                cs.append((k, p))
        cs.sort(reverse=True)
        sk, sm = 0, 0
        if qs is not None:
            for m in divisors_small(M, MMAX):
                k = vs(phi(qs, m), s, l)
                if k > sk:
                    sk, sm = k, m
        tot, ps = sk, []
        for k, p in cs:
            if tot > l - 1:
                break
            ps.append((p, k))
            tot += k
        if tot > l - 1:
            cand = ('over', s, ps, sm, sk)
            if best is None or len(ps) < len(best[2]):
                best = cand
    return best


def order(Q, s):
    d, x = 1, Q % s
    while x != 1:
        x = x * Q % s
        d += 1
    return d


def expo_factor(l, s, d, v):
    return s ** (l - 1) if d == 1 else d * s ** max(l - 1 - v, 0)


def do_expo(l, known, qs, M, done_expo, steps):
    progressed = False
    for s in known:
        if s in done_expo or s == 2 or s == l or s % l == 1 or s > EXPO_MAX:
            continue
        done_expo.add(s)
        d = order(qs, s)
        v = vs(pow(qs, d, s ** l) - 1, s, l) if d > 1 else 0
        f = expo_factor(l, s, d, v)
        if M % f != 0:
            M = M * f // math.gcd(M, f)
            steps.append(('expo', s, d, v))
            progressed = True
    return M, progressed


def solve(l, known, qs, ex, M, maxknown, done_expo=(), depth=0, eager=False):
    known = list(known)
    done_expo = set(done_expo)
    steps = []
    while True:
        c = try_close(l, known, qs, M)
        if c is not None:
            return build(steps, c)
        if len(known) > maxknown:
            raise RuntimeError(f'too many primes l={l} depth={depth}')
        if qs is not None and eager:
            M, prog = do_expo(l, known, qs, M, done_expo, steps)
            if prog:
                continue
        cands = []
        ms = divisors_small(M, MMAX) if qs is not None else []
        if qs is not None and not eager:
            ms = [m for m in ms if m == 2]
        for m in ms:
            for r in facs_spec(qs, m):
                if r not in known:
                    cands.append((r, ('spec', m, r)))
        for p in known:
            for r in facs_ord(p, l):
                if r != 2 and r not in known and r != qs:
                    cands.append((r, ('ord', p, r)))
        safe = [x for x in cands if qs is not None or x[0] % 4 == 3 or x[0] in ex]
        if not safe and qs is not None and not eager:
            eager = True
            continue
        if not cands and deepen(known, l):
            continue
        if not cands:
            raise RuntimeError(f'stuck l={l} depth={depth} known={len(known)} qs={qs}')
        if safe:
            r, st = min(safe)
            steps.append(st)
            known.append(r)
            continue
        r = min(x[0] for x in cands)
        yes = solve(l, known, r, ex, M, maxknown, (), depth + 1)
        no = solve(l, known, None, ex + [r], M, maxknown, done_expo, depth + 1)
        return build(steps, ('branch', r, yes, no))


def build(steps, tail):
    t = tail
    for st in reversed(steps):
        t = st + (t,)
    return t


def annotate_prune(t, M, l):
    """Bottom-up prune. Returns (tree, needed primes, ex used, m values used)."""
    kind = t[0]
    if kind == 'over':
        _, s, ps, m, k = t
        return t, {s} | {p for p, _ in ps}, set(), ({m} if k else set())
    if kind == 'mod4':
        return t, set(), set(), set()
    if kind == 'ord':
        _, p, r, nxt = t
        n, need, exu, mu = annotate_prune(nxt, M, l)
        if r in need:
            return ('ord', p, r, n), (need - {r}) | {p}, exu | {r}, mu
        return n, need, exu, mu
    if kind == 'spec':
        _, m, r, nxt = t
        n, need, exu, mu = annotate_prune(nxt, M, l)
        if r in need:
            return ('spec', m, r, n), need - {r}, exu, mu | {m}
        return n, need, exu, mu
    if kind == 'expo':
        _, s, d, v, nxt = t
        f = expo_factor(l, s, d, v)
        M2 = M * f // math.gcd(M, f)
        n, need, exu, mu = annotate_prune(nxt, M2, l)
        if any(M % m != 0 for m in mu):
            return ('expo', s, d, v, n), need | {s}, exu, mu
        return n, need, exu, mu
    if kind == 'branch':
        _, r, yes, no = t
        ny, needy, exy, muy = annotate_prune(yes, M, l)
        nn, needn, exn, mun = annotate_prune(no, M, l)
        if r not in exn:
            return nn, needn, exn, mun
        return ('branch', r, ny, nn), needy | needn, exy | (exn - {r}), muy | mun
    raise ValueError(kind)


def size(t):
    if t[0] in ('over', 'mod4'):
        return 1
    if t[0] == 'branch':
        return 1 + size(t[2]) + size(t[3])
    return 1 + size(t[-1])


def primes_of(t, acc):
    k = t[0]
    if k == 'ord':
        acc.add(t[2]); primes_of(t[3], acc)
    elif k == 'spec':
        acc.add(t[2]); primes_of(t[3], acc)
    elif k == 'expo':
        primes_of(t[4], acc)
    elif k == 'branch':
        primes_of(t[2], acc); primes_of(t[3], acc)
    return acc


def main(l, maxknown=400):
    t0 = time.time()
    ordt = solve(l, [l], None, [l], 2, maxknown)
    ordt = annotate_prune(ordt, 2, l)[0]
    t1 = time.time()
    print(f'l={l}: ord done {t1 - t0:.1f}s nodes {size(ordt)}', file=sys.stderr)
    if l % 4 == 1:
        spect = solve(l, [], l, [], 2, maxknown, eager=True)
        spect = annotate_prune(spect, 2, l)[0]
    else:
        spect = ('mod4',)
    print(f'l={l}: spec done {time.time() - t1:.1f}s nodes {size(spect)}', file=sys.stderr)
    ps = primes_of(ordt, set()) | primes_of(spect, set())
    cache = {}
    for p in sorted(ps):
        pratt(p, cache)
    cert = {'l': l, 'pratt': list(cache.values()), 'ord': ordt, 'spec': spect}
    print(f'l={l}: primes {len(ps)}, pratt entries {len(cache)}, max prime {max(ps)}',
          file=sys.stderr)
    return cert


def part(l, which, maxknown=600):
    t0 = time.time()
    if which == 'ord':
        t = annotate_prune(solve(l, [l], None, [l], 2, maxknown), 2, l)[0]
    elif l % 4 == 1:
        t = annotate_prune(solve(l, [], l, [], 2, maxknown, eager=True), 2, l)[0]
    else:
        t = ('mod4',)
    print(f'l={l} {which}: {time.time() - t0:.1f}s nodes {size(t)}', file=sys.stderr)
    json.dump(t, open(f'tree_{l}_{which}.json', 'w'))


def merge(l):
    ordt = json.load(open(f'tree_{l}_ord.json'))
    spect = json.load(open(f'tree_{l}_spec.json'))
    ps = primes_of(ordt, set()) | primes_of(spect, set())
    cache = {}
    for p in sorted(ps):
        pratt(p, cache)
    json.dump({'l': l, 'pratt': list(cache.values()), 'ord': ordt, 'spec': spect},
              open(f'cert_{l}.json', 'w'))
    print(f'l={l}: primes {len(ps)}, pratt entries {len(cache)}, max prime {max(ps)}',
          file=sys.stderr)


if __name__ == '__main__':
    l = int(sys.argv[1])
    if len(sys.argv) > 2 and sys.argv[2] in ('ord', 'spec'):
        part(l, sys.argv[2])
    elif len(sys.argv) > 2 and sys.argv[2] == 'merge':
        merge(l)
    else:
        cert = main(l)
        with open(f'cert_{l}.json', 'w') as f:
            json.dump(cert, f)
