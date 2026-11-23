"""Untrusted helper script for the OddPerfect Lean library.

Translator from the JSON certificate of search.py (format in FORMAT.md) to a term of the Lean type
`OddPerfect.TwoExcEngine.Cert`, and an exact Python mirror of the Lean checker
`TwoExcEngine.check` (OddPerfect/TwoExcEngineCheck.lean, OddPerfect/TwoExcEngineTail.lean). The
mirror computes every state itself from the root state and reads from the certificate only what
the Lean term holds: the items of each record, the outcome kinds, the receivers and senders, the
split primes and the witnesses of the deficient leaves. Helper of gen.py, which writes the Lean
modules from the term; the mirror run gives the subtree costs and the primes the Lean checker
asks its primality oracle about (here a Miller Rabin test with the first twelve prime bases,
exact below 3.1 * 10^23; the Lean oracle is a Pratt certificate written by gen.py).

The mirror also follows `TwoExcEngine.checkV` for the fixed exponent families (a header with a
field V3: exponent V3 at 3, every further exception of exponent exactly 4, landed facts off).
For V3 != 2 the prime 3 is a key with an exact exponent and counts as one exception.

Run: python3 -I engine.py CERT   (CERT is cert.jsonl.xz or the decompressed file; prints
`accepted True`, the leaf counts, the operation counts and the number of oracle primes)
Requires: Python 3 standard library only. Running time: a few seconds.
Untrusted: the term is checked again by the Lean kernel.
License: GPL 3, same as the repository.
"""
import json, sys, math, collections, lzma, threading

sys.setrecursionlimit(100000)

# ---------------------------------------------------------------- JSON

def read_lines(fn):
    """The lines of a certificate file, read through lzma when the name ends in .xz."""
    fh = lzma.open(fn, 'rt') if fn.endswith('.xz') else open(fn)
    with fh:
        return fh.read().splitlines(keepends=True)

def load(fn):
    recs = {}
    for l in read_lines(fn):
        r = json.loads(l)
        req(isinstance(r, dict), 'record must be an object')
        req(type(r.get('id')) is int and r['id'] >= 0, 'record id must be a natural number')
        req(r['id'] not in recs, 'duplicate record id')
        recs[r['id']] = r
    return recs

def comp_of(src):
    if src[0] == 'row': return src[1]
    if src[0] == 'sig': return src[1]
    if src[0] == 'cyc': return src[2]
    if src[0] == 'receipt': return src[3]
    raise ValueError(src)

# ---------------------------------------------------------------- roles

def role_of_class(cls, f, landed):
    # role tuple: ('sq',) or ('fr', isQ, D, no3, kmin, exact)
    if cls == 'square': return ('sq',)
    if cls == 'q0': return ('fr', True, 2, True, 1, False)
    if cls == 'q3': return ('fr', True, 6, False, 5, False)
    if cls == 'q': return ('fr', True, 2, landed, 1, False)
    if cls == 'e':
        return ('fr', False, 1, True, 4, False) if f % 3 == 1 else ('fr', False, 1, False, 4, False)
    if cls == 'e3': return ('fr', False, 3, False, 8, False)
    raise ValueError(cls)

# ---------------------------------------------------------------- translator

def defdata_trivial(pr):
    """Leaf data for a deficient leaf without generators and without undecided free primes
    (K empty, u = 0), where the search writes no Rankin data: the Rankin part of the bound is
    zero, and the checks on the witnesses are met by k = 24, B = 10^6, the least admissible
    r_x, m_L = 1 and m_M = 10^-13 (S is then below 10^-12)."""
    req(pr['K'] == [] and pr['u'] == 0 and pr['a'] == 0 and pr['b'] == 0, 'trivial tail slots')
    req(pr['extra_ab'] == 0 and pr['extra_cd'] == 0 and pr['hits'] == [], 'trivial tail extras')
    k, B, x = 24, 10 ** 6, pr['x']
    rx = B + 1
    req(rx ** k <= B ** k * x, 'trivial tail alpha_x')
    return ('dd', k, B, [], rx, (1, 1), (1, 10 ** 13), [])

class Translator:
    def __init__(self, recs):
        self.recs = recs
        self.hdr = recs[0]
        # the fixed exponent families: factor lists sorted, so the term does not depend on the
        # order in which the factoring library lists the factors
        self.sort_items = 'V3' in self.hdr

    def apply_node(self, rid, comp):
        r = self.recs[rid]
        req(r['kind'] == 'apply', 'expected apply record')
        items = [(p, e) for p, e, src in r['items'] if comp_of(src) == comp]
        # positional check: the own items are a suffix of the record's items
        own = [(p, e) for p, e, src in r['items']]
        req(own[len(own) - len(items):] == items, 'own items must be a suffix')
        if self.sort_items:
            items = sorted(items)
        return ('apply', items, self.out(r))

    def out(self, r):
        oc = r['outcome']
        if oc == 'leaf':
            rs = r['reason']
            if rs in ('cap', 'cap3', 'capexact', 'absentforced'): return ('leaf',)
            if rs == 'abundant': return ('abundant',)
            if rs == 'landedL': return ('landedL',)
            if rs == 'receipt':
                p = r['proof']['receiver']
                inf = r['proof']['senders']
                ss = [('inf', int(g), v['d']) for g, v in sorted(inf.items(), key=lambda kv: int(kv[0]))]
                return ('receipt', p, ss)
            if rs == 'noroles': return ('leaf',)  # the checker finds the empty role list
            raise ValueError(rs)
        if oc == 'force':
            f = r['forced']
            return ('force', [self.apply_node(c, f) for c in r['children']])
        if oc == 'receipt':
            p = r['receiver']
            ent = {}
            for g, v in r['senders_infeasible'].items():
                ent[int(g)] = ('inf', int(g), v['d'])
            for c in r['children']:
                a = self.recs[c]['action']
                g = a['sender']
                ent[g] = ('snd', g, a['d'], self.apply_node(c, g))
            return ('receipt', p, [ent[g] for g in sorted(ent)])
        if oc == 'closed':
            req(len(r['children']) == 1, 'closed record must have one child')
            return ('closed', self.step(r['children'][0]))
        raise ValueError(oc)

    def step(self, rid):
        r = self.recs[rid]
        k = r['kind']
        if k == 'decide':
            x = r['x']
            ch = [self.apply_node(c, x) for c in r['children']]
            return ('decide', ch, self.step(r['absent']))
        if k == 'check':
            if r['reason'] == 'landedL': return ('checkL',)
            req(r['reason'] == 'deficient', 'expected deficient leaf')
            return ('check', self.defdata(r['proof']))
        if k == 'split':
            p = r['prime']
            ex = at = None
            for c in r['children']:
                a = self.recs[c]['action']
                if a['role'] == 'exact': ex = self.apply_node(c, p)
                elif a['role'] == 'atleast': at = self.apply_node(c, p)
            return ('split', p, ex, at)
        raise ValueError(k)

    def defdata(self, pr):
        if 'rankin' not in pr:
            return defdata_trivial(pr)
        rk = pr['rankin']
        req(rk['mode'] == 'theta', 'unsupported Rankin mode')
        req(pr['extra_ab'] == 0 and pr['extra_cd'] == 0, 'unsupported extra slots')
        base = rk['alpha_x'][2]
        rs = []
        for g in pr['K']:
            a = rk['alpha'][str(g)]
            req(a[2] == base, 'Rankin bases differ')
            rs.append(a[1])
        def frac(s):
            n, d = s.split('/') if '/' in s else (s, '1')
            return (int(n), int(d))
        comps = sorted((t, w) for n, t, reason, *wit in pr['nonhits'] if reason == 'composite'
                       for w in wit)
        return ('dd', rk['k'], base, rs, rk['alpha_x'][1], frac(rk['mL']), frac(rk['mM']), comps)

    def root(self):
        r = self.recs[self.hdr['root']]
        term = self.apply_node(r['id'], 3)
        natural_term(term)
        return term

# ---------------------------------------------------------------- mirror checker

class Reject(Exception):
    pass

def req(b, msg='reject'):
    if not b:
        raise Reject(msg)

def natural_term(term):
    """Lean certificate terms have only constructor tags and natural-number fields.
    In particular the numerators of mL and mM are Nat, not signed integers.
    Reject values Python arithmetic would accept but Lean's input type cannot express.
    """
    tags = {'apply', 'leaf', 'abundant', 'landedL', 'checkL', 'ext', 'force', 'receipt',
            'inf', 'snd', 'closed', 'decide', 'check', 'split', 'dd'}
    pending = [term]
    while pending:
        value = pending.pop()
        if isinstance(value, (tuple, list)):
            pending.extend(value)
        elif isinstance(value, str):
            req(value in tags, 'unexpected string in certificate term')
        else:
            req(type(value) is int and value >= 0,
                'certificate field must be a natural number: %r' % (value,))


COUNT = collections.Counter()

def is_prime_small(n):
    """Trial division up to the square root (mirror of minFacB)."""
    if n < 2: return False
    d = 2
    while d * d <= n:
        COUNT['tdiv'] += 1
        if n % d == 0: return False
        d += 1
    return True

def miller(n):
    req(type(n) is int, 'primality candidate must be an integer')
    # Enforce the conservative exactness range stated in the module docstring.
    req(n < 310000000000000000000000, 'primality candidate exceeds deterministic range')
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

ORACLE = set()   # primes the oracle was asked about

def pr(p):
    ORACLE.add(p)
    return miller(p)

def geom(p, e):
    return sum(p ** i for i in range(e + 1))

def key_find(st, p):
    for k in st['keys']:
        if k[0] == p: return k
    return None

def m_of(role):
    if role[0] == 'sq': return 2
    _, isQ, D, no3, kmin, ex = role
    return kmin if ex else D - 1

def gdiv(st, c, n):
    k = key_find(st, c)
    req(k is not None, 'component not a key')
    m = m_of(k[1])
    M = n * (c - 1)
    COUNT['gdiv'] += 1
    return pow(c, m + 1, M) == 1 % M

def csum(cs):
    return sum(w for c, w in cs)

def is_q(role): return role[0] == 'fr' and role[1]
def is_exc(role): return role[0] == 'fr' and not role[1]

def q_decided(st): return any(is_q(k[1]) for k in st['keys'])
def nexc(st): return sum(1 for k in st['keys'] if is_exc(k[1]))

def insert_key(st, p, role, cs):
    req(key_find(st, p) is None, 'already a key')
    keys = list(st['keys'])
    i = 0
    while i < len(keys) and keys[i][0] < p: i += 1
    keys.insert(i, [p, role, cs])
    return {'x': st['x'], 'keys': keys}

def set_role(st, p, role):
    keys = [[k[0], role if k[0] == p else k[1], k[2]] for k in st['keys']]
    return {'x': st['x'], 'keys': keys}

def apply_items(P, st, pend, comp, items):
    """Returns ('contra',) or ('ok', st, pend)."""
    keys = [[k[0], k[1], [list(e) for e in k[2]]] for k in st['keys']]
    st = {'x': st['x'], 'keys': keys}
    pend = [list(e) for e in pend]
    for p, e in items:
        COUNT['item'] += 1
        req(e >= 1 and p % 2 == 1)
        k = key_find(st, p)
        if k is not None:
            cs = k[2]
            old = 0
            for ent in cs:
                if ent[0] == comp: old = ent[1]
            w = old + e
            req(gdiv(st, comp, p ** w), ('gdiv key', p, comp, w, key_find(st, comp)[1], cs))
            found = False
            for ent in cs:
                if ent[0] == comp: ent[1] = w; found = True
            if not found: cs.append([comp, w])
            tot = csum(cs)
            role = k[1]
            if role[0] == 'sq' and tot > 2: return ('contra',)
            if role[0] == 'fr' and role[5] and tot > role[4]: return ('contra',)
        else:
            old = 0
            for ent in pend:
                if ent[0] == p and ent[1] == comp: old = ent[2]
            w = old + e
            req(gdiv(st, comp, p ** w), 'gdiv pend')
            if p < st['x']:
                req(pr(p), 'absent prime')
                return ('contra',)
            found = False
            for ent in pend:
                if ent[0] == p and ent[1] == comp: ent[2] = w; found = True
            if not found: pend.append([p, comp, w])
    return ('ok', st, pend)

def lan(P):
    """Params.lan: the landed facts are used only with exponent 2 at 3."""
    return P['landed'] and P['V3'] == 2

def roles_of(P, st, f):
    rs = [('sq',)]
    if not q_decided(st) and f % 4 == 1 and (not lan(P) or (f != 5 and f % 9 != 8)):
        if f % 3 == 1:
            rs += [('fr', True, 2, True, 1, False), ('fr', True, 6, False, 5, False)]
        else:
            rs += [('fr', True, 2, lan(P), 1, False)]
    if nexc(st) < P['E']:
        if P['e4'] and f != 3:
            rs += [('fr', False, 5, True, 4, True)]
        elif f % 3 == 1:
            rs += [('fr', False, 1, True, 4, False), ('fr', False, 3, False, 8, False)]
        else:
            rs += [('fr', False, 1, False, 4, False)]
    return rs

def allowed(role, n):
    _, isQ, D, no3, kmin, ex = role
    return (n % D == 0 and (not no3 or n % 3 != 0) and
            ((n % 4 == 2) if isQ else (n % 2 == 1 and n >= 5)))

def next_allowed(isQ, D, no3, s):
    """Least n >= s with D | n and n allowed; fuel 64 multiples."""
    j = (s + D - 1) // D
    for _ in range(64):
        n = D * j
        if allowed(('fr', isQ, D, no3, 0, False), n): return n
        j += 1
    raise Reject('no allowed exponent')

def pfacs(d):
    fs = []
    m = d
    r = 2
    while r * r <= m:
        while m % r == 0:
            fs.append(r); m //= r
        r += 1
    if m > 1: fs.append(m)
    return fs

def ord_ok(d, g, p):
    if g % p == 1: return d == p
    if d < 1 or pow(g, d, p) != 1: return False
    fs = pfacs(d)
    req(math.prod(fs) == d and all(is_prime_small(r) for r in fs))
    return all(pow(g, d // r, p) != 1 for r in fs)

def infeasible(role, d):
    _, isQ, D, no3, kmin, ex = role
    L = D * d // math.gcd(D, d)
    return ((ex and (kmin + 1) % L != 0) or (isQ and L % 4 == 0) or
            ((not isQ) and L % 2 == 0) or (no3 and L % 3 == 0))

def abundant(P, st):
    num = 1; den = 1
    for p, role, cs in st['keys']:
        e = 2 if role[0] == 'sq' else min(role[4], P['KCAP'])
        num *= geom(p, e); den *= p ** e
    return 2 * den < num

LSET = [7, 13, 19, 31, 61, 97, 127, 331]

def landedL(P, st):
    if not lan(P) or P['E'] > 2: return False
    for p in LSET:
        k = key_find(st, p)
        if k is not None and is_exc(k[1]) and k[1][2] % 3 != 0: return False
    if nexc(st) == P['E']: return True
    return all(p < st['x'] or key_find(st, p) is not None for p in LSET)

def scan_next(st):
    # 1000 positions, the fuel of `scanNext` in TwoExcEngineCode.lean; exhaustion rejects.
    y = st['x']
    for _ in range(1000):
        if key_find(st, y) is None and is_prime_small(y): return y
        COUNT['scan'] += 1
        y += 1
    raise Reject('scan')

# quadratic residue filter moduli
QR_MODS = [64, 63, 65, 11, 17, 19, 23, 29, 31, 37, 41, 43, 47]
QR_SETS = {m: {(s * s) % m for s in range(m)} for m in QR_MODS}

def isqrt_newton(z):
    x = z
    while True:
        COUNT['newton'] += 1
        y = (x + z // x) // 2
        if y >= x: return x
        x = y

def square_root_if_square(z):
    """Mirror of the filtered square test. Returns s with s*s == z, or None."""
    for m in QR_MODS:
        COUNT['qr'] += 1
        if (z % m) not in QR_SETS[m]: return None
    COUNT['qr_survive'] += 1
    s = isqrt_newton(z)
    return s if s * s == z else None

def budget3(role):
    """Mirror of budget3: 2 for a square, kmin for an exact exception, None otherwise."""
    if role[0] == 'sq': return 2
    _, isQ, D, no3, kmin, ex = role
    return kmin if (not isQ and ex) else None

def deficient(P, st, dd):
    _, k, B, rs, rx, mL, mM, comps = dd
    x = st['x']
    req(x >= 2 and k >= 3)
    keys = st['keys']
    a = 0 if q_decided(st) else 1
    b = P['E'] - nexc(st); req(b >= 0)
    k3 = key_find(st, 3); req(k3 is not None, 'no key 3')
    b3 = budget3(k3[1]); req(b3 is not None, 'budget of 3')
    c = max(0, b3 - csum(k3[2]))
    d = 2 * c
    for p, role, cs in keys:
        if role[0] == 'sq' and p % 3 == 1: d += max(0, 2 - csum(cs))
        if role[0] == 'fr' and role[5] and p % 3 == 1: d += max(0, role[4] - csum(cs))
    K = [p for p, role, cs in keys if role[0] == 'fr' and not role[5] and p % 3 == 1]
    u = a + b
    req(len(rs) == len(K))
    for g, r in zip(K, rs):
        req(r > B and B ** k * g >= r ** k, 'alpha')
    req(rx > B and B ** k * x >= rx ** k, 'alpha_x')
    L = x * x + x + 1
    M = max(L, P['MHIT'])
    req(mL[1] > 0 and mM[1] > 0)
    req(mL[0] ** (2 * k) * L ** (k - 2) >= mL[1] ** (2 * k), 'mL')
    req(mM[0] ** (2 * k) * M ** (k - 2) >= mM[1] ** (2 * k), 'mM')
    # G = prod r/(r-B); Gx = rx/(rx-B)
    Gn = 1; Gd = 1
    for r in rs: Gn *= r; Gd *= r - B
    # R = mL*G*(Gx^u - 1) + mM*G
    gxn = rx ** u; gxd = (rx - B) ** u
    # term1 = mL0*Gn*(gxn-gxd) / (mL1*Gd*gxd); term2 = mM0*Gn/(mM1*Gd)
    t1n = mL[0] * Gn * (gxn - gxd); t1d = mL[1] * Gd * gxd
    t2n = mM[0] * Gn; t2d = mM[1] * Gd
    Rn = t1n * t2d + t2n * t1d; Rd = t1d * t2d
    Sn = (x + 1) ** 2 * Rn; Sd = x * x * Rd
    req(Sn < Sd, 'S<1')
    # hits by enumeration
    hn, hd = 1, 1
    compd = dict(comps)
    def visit(n):
        nonlocal hn, hd
        COUNT['gen'] += 1
        z = 4 * n - 3
        s = square_root_if_square(z)
        if s is None: return
        COUNT['square'] += 1
        t = (s - 1) // 2
        if t % 2 == 0 or t % 3 != 2 or t < x or key_find(st, t) is not None: return
        w = compd.get(t)
        if w is not None:
            req(1 < w < t and t % w == 0, 'composite witness')
            return
        COUNT['hit'] += 1
        hn *= n; hd *= t * t
    def enum(gs, acc):
        if not gs:
            visit(acc); return
        g = gs[0]
        v = acc
        for _ in range(200):
            if v >= P['MHIT']: return
            enum(gs[1:], v)
            v *= g
        raise Reject('enum fuel')
    enum(K, 1)
    # H
    Hn, Hd = 1, 1
    for p, role, cs in keys:
        if role[0] == 'sq':
            Hn *= p * p + p + 1; Hd *= p * p
        elif role[5] and role[4] <= P['KCAP']:
            Hn *= geom(p, role[4]); Hd *= p ** role[4]
        else:
            Hn *= p; Hd *= p - 1
    cd = c + d
    Un = Hn * x ** u * L ** cd * hn * Sd
    Ud = Hd * (x - 1) ** u * x ** (2 * cd) * hd * (Sd - Sn)
    req(Un < 2 * Ud, 'U<2')
    return True

class Mirror:
    def __init__(self, P):
        self.P = P
        self.leaves = collections.Counter()

    def go_apply(self, st, pend, comp, node):
        req(node[0] == 'apply')
        _, items, out = node
        res = apply_items(self.P, st, pend, comp, items)
        if res[0] == 'contra':
            self.leaves['contra'] += 1
            return True
        _, st2, pend2 = res
        return self.go_out(st2, pend2, out)

    def go_out(self, st, pend, out):
        P = self.P
        t = out[0]
        if t == 'abundant':
            self.leaves['abundant'] += 1
            return req(abundant(P, st), 'abundant') or True
        if t == 'landedL':
            self.leaves['landedL'] += 1
            return req(landedL(P, st), 'landedL') or True
        if t == 'leaf':
            # a contradiction leaf whose contradiction was not found, or noroles
            if pend:
                f = min(e[0] for e in pend)
                req(pr(f) and f % 2 == 1)
                if not roles_of(P, st, f): return True
            raise Reject('leaf without contradiction')
        if t == 'force':
            req(pend, 'force without pending')
            f = min(e[0] for e in pend)
            req(pr(f) and f % 2 == 1, 'forced prime')
            cs = [[c, w] for p, c, w in pend if p == f]
            rest = [e for e in pend if e[0] != f]
            roles = roles_of(P, st, f)
            ch = out[1]
            req(len(roles) == len(ch), 'roles mismatch')
            for role, c in zip(roles, ch):
                st2 = insert_key(st, f, role, [list(e) for e in cs])
                req(self.go_apply(st2, rest, f, c))
            return True
        if t == 'receipt':
            _, p, ss = out
            req(q_decided(st) and nexc(st) == P['E'], 'receipt precondition')
            kp = key_find(st, p)
            req(kp is not None and p % 3 == 2, 'receiver')
            frees = [k[0] for k in st['keys'] if k[1][0] == 'fr' and k[0] != p]
            req([s[1] for s in ss] == frees, 'senders mismatch')
            if not ss: self.leaves['receipt_leaf'] += 0
            if all(s[0] == 'inf' for s in ss): self.leaves['receipt_leaf'] += 1
            else: self.leaves['receipt_node'] += 1
            for s in ss:
                g, d = s[1], s[2]
                role = key_find(st, g)[1]
                req(ord_ok(d, g, p), 'order')
                if s[0] == 'inf':
                    req(infeasible(role, d), 'infeasible')
                else:
                    _, isQ, D, no3, kmin, ex = role
                    L = D * d // math.gcd(D, d)
                    if ex:
                        req((kmin + 1) % L == 0)
                        st2 = st
                    else:
                        n = next_allowed(isQ, L, no3, kmin + 1)
                        st2 = set_role(st, g, ('fr', isQ, L, no3, n - 1, False))
                    req(self.go_apply(st2, [], g, s[3]))
            return True
        if t == 'closed':
            return self.go_step(st, out[1])
        raise Reject('bad out ' + t)

    def go_step(self, st, node):
        P = self.P
        t = node[0]
        if t == 'decide':
            y = scan_next(st)
            roles = roles_of(P, st, y)
            req(len(roles) == len(node[1]), 'decide roles')
            for role, c in zip(roles, node[1]):
                st2 = insert_key(st, y, role, [])
                st2['x'] = y
                req(self.go_apply(st2, [], y, c))
            st3 = {'x': y + 1, 'keys': st['keys']}
            return self.go_step(st3, node[2])
        if t == 'check':
            y = scan_next(st)
            self.leaves['deficient'] += 1
            return req(deficient(P, {'x': y, 'keys': st['keys']}, node[1]), 'deficient') or True
        if t == 'checkL':
            y = scan_next(st)
            self.leaves['checkL'] += 1
            return req(landedL(P, {'x': y, 'keys': st['keys']}), 'checkL') or True
        if t == 'split':
            _, p, ex, at = node
            k = key_find(st, p)
            req(k is not None and k[1][0] == 'fr' and not k[1][5], 'split prime')
            _, isQ, D, no3, kmin, _e = k[1]
            req(self.go_apply(set_role(st, p, ('fr', isQ, kmin + 1, no3, kmin, True)), [], p, ex))
            n = next_allowed(isQ, D, no3, kmin + 2)
            req(self.go_apply(set_role(st, p, ('fr', isQ, D, no3, n - 1, False)), [], p, at))
            return True
        raise Reject('bad step ' + t)

def params(hdr):
    for key in ('EMAX', 'MHIT', 'KCAP') + (('V3',) if 'V3' in hdr else ()):
        req(type(hdr.get(key)) is int and hdr[key] >= 0,
            'header %s must be a natural number' % key)
    if hdr.get('kind') != 'header':
        raise ValueError('not a header: %r' % (hdr,))
    if 'V3' in hdr:
        # search_ex.py: exponent V3 at 3, at most EMAX further exceptions, each of exponent 4.
        # For V3 != 2 the prime 3 is an exception key too, so E = EMAX + 1.
        flags = set(hdr['flags'])
        if not flags <= {'cert', 'nojump', 'nolanded', 'ruleL'} or 'nolanded' not in flags:
            raise ValueError('unexpected flags %r' % (hdr['flags'],))
        V3 = hdr['V3']
        return {'E': hdr['EMAX'] + (0 if V3 == 2 else 1), 'MHIT': hdr['MHIT'], 'KCAP': hdr['KCAP'],
                'landed': False, 'V3': V3, 'e4': True}
    if hdr.get('flags') != ['cert']:
        raise ValueError('not a header of search.py: %r' % (hdr,))
    return {'E': hdr['EMAX'], 'MHIT': hdr['MHIT'], 'KCAP': hdr['KCAP'], 'landed': True,
            'V3': 2, 'e4': False}

ROOT_STATE = {'x': 5, 'keys': [[3, ('sq',), []]]}

def root3(P):
    """Mirror of root3."""
    return ('sq',) if P['V3'] == 2 else ('fr', False, P['V3'] + 1, False, P['V3'], True)

def params_ok(P):
    return P['V3'] == 2 or (P['V3'] % 2 == 0 and P['V3'] >= 4)

def check(P, M, term):
    """Mirror of check: the guard, then the root record with 3 a square key."""
    req(P['V3'] == 2 and not P['e4'], 'check guard')
    return M.go_apply(ROOT_STATE, [], 3, term)

def checkV(P, M, term):
    """Mirror of checkV: the guard, then the root record with 3 of role root3 P."""
    req(params_ok(P), 'paramsOK')
    return M.go_apply({'x': 5, 'keys': [[3, root3(P), []]]}, [], 3, term)

def run(fn):
    recs = load(fn)
    T = Translator(recs)
    term = T.root()
    P = params(recs[0])
    M = Mirror(P)
    ok = (checkV if 'V3' in recs[0] else check)(P, M, term)
    return recs, term, P, M, ok

# ---------------------------------------------------------------- serializers

def lean_term(node):
    """Lean syntax for a term (for small subtrees)."""
    t = node[0]
    if t == 'leaf': return '.leaf'
    if t == 'abundant': return '.abundant'
    if t == 'landedL': return '.landedL'
    if t == 'checkL': return '.checkL'
    if t == 'ext': return '.ext'
    if t == 'apply':
        return '(.apply [%s] %s)' % (', '.join('(%d, %d)' % pe for pe in node[1]), lean_term(node[2]))
    if t == 'force': return '(.force %s)' % lean_chain(node[1])
    if t == 'receipt': return '(.receipt %d %s)' % (node[1], lean_chain(node[2]))
    if t == 'inf': return '(.inf %d %d)' % (node[1], node[2])
    if t == 'snd': return '(.snd %d %d %s)' % (node[1], node[2], lean_term(node[3]))
    if t == 'closed': return '(.closed %s)' % lean_term(node[1])
    if t == 'decide': return '(.decide %s %s)' % (lean_chain(node[1]), lean_term(node[2]))
    if t == 'check':
        _, k, B, rs, rx, mL, mM, comps = node[1]
        return ('(.check { k := %d, B := %d, rs := [%s], rx := %d, mL := (%d, %d), mM := (%d, %d), '
                'comps := [%s] })' % (k, B, ', '.join(map(str, rs)), rx, mL[0], mL[1], mM[0], mM[1],
                                      ', '.join('(%d, %d)' % c for c in comps)))
    if t == 'split': return '(.split %d %s %s)' % (node[1], lean_term(node[2]), lean_term(node[3]))
    raise ValueError(t)

def lean_chain(lst):
    s = '.nil'
    for x in reversed(lst):
        s = '(.cons %s %s)' % (lean_term(x), s)
    return s

def lean_role(r):
    if r[0] == 'sq': return '.sq'
    b = lambda v: 'true' if v else 'false'
    return '(.fr %s %d %s %d %s)' % (b(r[1]), r[2], b(r[3]), r[4], b(r[5]))

def lean_keys(keys):
    return '[%s]' % ', '.join('⟨%d, %s, [%s]⟩' % (p, lean_role(r), ', '.join('(%d, %d)' % tuple(e) for e in cs))
                              for p, r, cs in keys)

def lean_params(P):
    s = '{ E := %d, MHIT := %d, KCAP := %d, landed := %s' % (
        P['E'], P['MHIT'], P['KCAP'], 'true' if P['landed'] else 'false')
    if P.get('V3', 2) != 2 or P.get('e4', False):
        s += ', V3 := %d, e4 := %s' % (P['V3'], 'true' if P['e4'] else 'false')
    return s + ' }'



def main():
    import time
    if len(sys.argv) != 2:
        print('usage: python3 -I engine.py CERT'); return 2
    t0 = time.time()
    try:
        recs, term, P, M, ok = run(sys.argv[1])
    except Reject as e:
        print('REJECTED', e); return 1
    except (OSError, ValueError, KeyError, TypeError, IndexError, lzma.LZMAError) as e:
        print('MALFORMED', e); return 2
    print('accepted', ok, 'params', P, 'time %.1fs' % (time.time() - t0))
    print('leaves', dict(M.leaves))
    print('counts', dict(COUNT))
    print('oracle primes', len(ORACLE), 'max', max(ORACLE) if ORACLE else None,
          '>1e6', sum(p > 10**6 for p in ORACLE))
    return 0


if __name__ == '__main__':
    sys.setrecursionlimit(1000000)
    threading.stack_size(512 * 1024 * 1024)
    status = []
    th = threading.Thread(target=lambda: status.append(main()))
    th.start()
    th.join()
    sys.exit(status[0] if status else 1)
