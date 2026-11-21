# Untrusted helper script for the OddPerfect Lean library.
# Independent checker: parses the emitted Lean definitions and replays run as the Lean
# checker defines it, sharing no code with the generator.
# Used by: a recheck of OddPerfect/LowerBound.lean (prime table and the three trees).
# Run: python3 check.py LowerBound.lean 79 3: 5:3 7:3,5
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Independent checker: parses the emitted Lean definitions and replays `run` exactly as the
Lean checker defines it.  Shares no code with the generator.
Usage: python3 -I check.py file.lean B root_state_spec...
root spec: p0:excl,excl  meaning the state [pw p0 1, nd excl...] run against tree<p0>."""
import re, sys, math

def is_prime_exact(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True

def td_prime(n):  # mirrors tdPrime (trial division up to the square root)
    return is_prime_exact(n)

def trial_prime(q):  # mirrors Pratt.trialPrime (linear)
    return q >= 2 and all(q % d for d in range(2, q))

def check_entry(known, p, a, fs):  # mirrors Pratt.checkEntry
    prod = 1
    for f in fs: prod *= f
    if prod != nat_sub(p, 1): return False
    if not all(f in known or trial_prime(f) for f in fs): return False
    assert p >= 2
    if pow(a, p - 1, p) != 1: return False
    if not all(f != 0 and pow(a, (p - 1) // f, p) != 1 for f in fs): return False
    return True

def entry_ok(tab, p, a, fs):  # mirrors entryOK (pm with fuel p computes a ^ e % p for e < p)
    if not p > 1: return False
    prod = 1
    for f, k in fs: prod *= f ** k
    if prod != p - 1: return False
    if pow(a, p - 1, p) != 1: return False
    for f, k in fs:
        if not f < p: return False
        if not (f in tab or td_prime(f)): return False
        if f == 0 or pow(a, (p - 1) // f, p) == 1: return False
    return True

def table_ok(tab):
    return all(entry_ok(tab, p, a, fs) for p, (a, fs) in tab.items())

def pratt_check_prime(p, cert):
    known = []
    for (q, a, fs) in cert:
        prod = 1
        for f in fs: prod *= f
        if q < 1 or prod != q - 1: return False
        if not all(f in known or trial_prime(f) for f in fs): return False
        if pow(a, q - 1, q) != 1: return False
        if not all(f != 0 and pow(a, (q - 1) // f, q) != 1 for f in fs): return False
        known.append(q)
    return p in [e[0] for e in cert]

def gs(p, a):
    return (p ** (a + 1) - 1) // (p - 1) if p >= 2 else None

def nat_sub(a, b): return max(a - b, 0)

def low_ok(f, p, e):
    k = f[0]
    if k == 'pw': return f[1] == p and e <= f[2]
    if k == 'dv': return f[1] == p and e + 1 <= f[2]
    if k == 'ex': return f[1] == p and e <= f[2]
    return False

def has_pow(s, p, e): return any(low_ok(f, p, e) for f in s)

def comp_ok(f, p, a):
    if f[0] == 'ex': return f[1] == p and (f[2] + 1) % (a + 1) == 0
    if f[0] == 'dv': return f[1] == p and f[2] % (a + 1) == 0
    return False

def odd_fact(f):
    if f[0] == 'ex': return f[2] % 2 == 1
    if f[0] == 'dv': return f[2] % 2 == 0
    return False

def bad4(f, p):
    if f[0] == 'ex': return f[1] == p and f[2] % 4 != 1
    if f[0] == 'dv': return f[1] == p and f[2] % 4 == 0
    return False

def Dv(cs):
    D = 1
    for p, a in cs:
        # Lean: (p^(a+1) - 1) / (p - 1) with truncated subtraction and division by zero = 0
        num = nat_sub(p ** (a + 1), 1); den = nat_sub(p, 1)
        D *= (num // den if den else 0)
    return D

def comps_ok(s, cs):
    ps = [c[0] for c in cs]
    if len(set(ps)) != len(ps): return False
    return all(any(comp_ok(f, p, a) for f in s) for p, a in cs)

def half(D): return D // 2 if D % 2 == 0 else D

def base(f):
    if f[0] == 'pw': return f[1] ** f[2]
    if f[0] == 'dv': return f[1] ** nat_sub(f[2], 1)
    if f[0] == 'ex': return f[1] ** f[2]
    return 1

def Av(s):
    A = 1
    for f in s:
        b = base(f); A = A * b // math.gcd(A, b) if A and b else 0
    return A

def lcm(a, b): return a * b // math.gcd(a, b) if a and b else 0

def primes_below(R): return [r for r in range(R) if td_prime(r)]

def step(L, ins, s, pcs):
    k = ins[0]
    if k == 'rs':
        _, p, d, R = ins
        if (d == 1 and has_pow(s, p, 1)) or (d >= 2 and any(f == ('dv', p, d) for f in s)):
            out = [[('ex', p, d - 1)] + s] if d >= 2 else []
            out += [[('dv', p, d * r)] + s for r in primes_below(R)]
            out += [[('pw', p, nat_sub(d * R, 1))] + s]
            return out
        return None
    if k == 'force':
        _, q, kk, cs = ins
        okp = q in pcs
        if comps_ok(s, cs) and q != 2 and okp and Dv(cs) % q ** kk == 0:
            return [[('pw', q, kk)] + s]
        return None
    if k == 'up':
        _, p, e = ins
        if has_pow(s, p, e) and e % 2 == 1 and (e % 4 == 3 or p % 4 != 1 or
                any(f[1] != p and odd_fact(f) for f in s)):
            return [[('pw', p, e + 1)] + s]
        return None
    if k == 'big':
        cs = ins[1]
        return [] if comps_ok(s, cs) and L < lcm(Av(s), half(Dv(cs))) else None
    if k == 'ndc':
        p = ins[1]
        return [] if has_pow(s, p, 1) and ('nd', p) in s else None
    if k == 'ovf':
        _, q, f, cs = ins
        return [] if comps_ok(s, cs) and ('ex', q, f) in s and q != 2 and Dv(cs) % q ** (f + 1) == 0 else None
    if k == 'par2':
        _, p, q = ins
        return [] if p != q and any(f[1] == p and odd_fact(f) for f in s) and any(f[1] == q and odd_fact(f) for f in s) else None
    if k == 'parS':
        p = ins[1]
        return [] if any(f[1] == p and odd_fact(f) for f in s) and (p % 4 != 1 or any(bad4(f, p) for f in s)) else None
    if k == 'abund':
        l = ins[1]
        ps = [c[0] for c in l]
        if len(set(ps)) != len(ps): return None
        if not all(has_pow(s, p, e) for p, e in l): return None
        dp, sp = 1, 1
        for p, e in l: dp *= p ** e; sp *= gs(p, e)
        return [] if 2 * dp < sp else None
    return None

def run(L, ins, stk, pcs):
    for n, i in enumerate(ins):
        if not stk: return False, n
        s = stk.pop(0)
        cs = step(L, i, s, pcs)
        if cs is None: return False, n
        stk = cs + stk
    return len(stk) == 0, len(ins)

def parse_pairs(t):
    return [tuple(int(x) for x in m) for m in re.findall(r'\((\d+), (\d+)\)', t)]

def parse(text):
    pcs = {}
    tdefs = dict(re.findall(r'def (tab\d+|table) : PT :=\n(.*?)\n\n', text, re.S))
    def parse_def(name):
        toks = re.findall(r'\[(?:\(\d+, \d+\)(?:, )?)*\]|\(|\)|PT\.node|PT\.leaf|tab\d+|\d+', tdefs[name])
        pos = [0]
        def term():
            t = toks[pos[0]]; pos[0] += 1
            if t == '(':
                r = term(); assert toks[pos[0]] == ')'; pos[0] += 1; return r
            if t == 'PT.leaf': return []
            if re.fullmatch(r'tab\d+', t): return parse_def(t)
            assert t == 'PT.node', t
            l = term()
            p = int(toks[pos[0]]); a = int(toks[pos[0] + 1]); fs = toks[pos[0] + 2]; pos[0] += 3
            assert fs.startswith('[')
            r = term()
            assert p not in pcs
            pcs[p] = (a, [(int(x), int(y)) for x, y in re.findall(r'\((\d+), (\d+)\)', fs)])
            return l + [p] + r
        ks = term(); assert pos[0] == len(toks), name
        return ks
    keys = parse_def('table')
    assert keys == sorted(keys) and len(set(keys)) == len(keys)
    assert table_ok(pcs), 'table rejected'
    print('table ok', len(pcs))
    defs = {}
    for m in re.finditer(r'def (\w+) : List Ins := \[\n(.*?)\]\n', text, re.S):
        out = []
        for line in m.group(2).split(',\n'):
            line = line.strip().rstrip(',')
            w = line.split()
            k = w[0][1:]
            if k == 'rs': out.append(('rs', int(w[1]), int(w[2]), int(w[3])))
            elif k == 'force':
                out.append(('force', int(w[1]), int(w[2]), parse_pairs(line)))
            elif k == 'up': out.append(('up', int(w[1]), int(w[2])))
            elif k == 'big': out.append(('big', parse_pairs(line)))
            elif k == 'ndc': out.append(('ndc', int(w[1])))
            elif k == 'ovf': out.append(('ovf', int(w[1]), int(w[2]), parse_pairs(line)))
            elif k == 'par2': out.append(('par2', int(w[1]), int(w[2])))
            elif k == 'parS': out.append(('parS', int(w[1])))
            elif k == 'abund': out.append(('abund', parse_pairs(line)))
            else: raise ValueError(line)
        defs[m.group(1)] = out
    trees = {}
    for m in re.finditer(r'def (tree\d+) : List Ins := ([\w +]+)\n', text):
        ins = []
        for nm in m.group(2).split(' ++ '): ins += defs[nm.strip()]
        trees[m.group(1)] = ins
    return pcs, trees

if __name__ == '__main__':
    text = open(sys.argv[1]).read()
    L = 10 ** int(sys.argv[2])
    pcs, trees = parse(text)
    for spec in sys.argv[3:]:
        p0, _, ex = spec.partition(':')
        s = [('pw', int(p0), 1)] + [('nd', int(x)) for x in ex.split(',') if x]
        ok, n = run(L, trees['tree' + p0], [s], pcs)
        print('tree', p0, 'OK' if ok else 'REJECTED at %d' % n, len(trees['tree' + p0]))
