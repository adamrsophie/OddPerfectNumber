# Untrusted helper script for the OddPerfect Lean library.
# Prunes (optionally) a family certificate, orders its nodes (seeds, the other sources in
# breadth first order, then the sink targets), rechecks everything exactly with mirrors of the
# Lean checkers FamInst.reach and FamInst.abOK2, finds the number of passes, builds Pratt
# certificates for the nodes above a threshold, and writes <name>.lean.txt (the literals
# nodes, rows, vals, tm, P, G, the src and nd parts and pc) and <name>.meta.json.
# Used by: OddPerfect/CommonFiveSeven.lean (name 57), CommonSixtyFive.lean (65),
# CommonFiftyFive.lean (55), CommonEightyFive.lean (85), CommonOneFifteenData.lean (115),
# CommonNinetyFiveData.lean (95, after ndflat.py and asm_split.py).
# Run: python3 gen2.py cert.json name seeds prattThr chunkSize prune variant ...
# with variant = ns:cand and cand one of m12 (b % 12 == 1), m12x13 (and b != 13), eq13
# (b == 13); the commands used are listed in the README.
# Requires: Python 3 and sympy. Deterministic. Running time: under two seconds,
# about five seconds for 95.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json
sys.set_int_max_str_digits(0)
from sympy import isprime, factorint

cert = json.load(open(sys.argv[1])); name = sys.argv[2]
seeds = [int(x) for x in sys.argv[3].split(',')]; thr = int(sys.argv[4])
chunk = int(sys.argv[5]); prune = sys.argv[6] == '1'
variants = [(int(v.split(':')[0]), v.split(':')[1]) for v in sys.argv[7:]]
d = cert['d']; T = set(cert['targets'])
CANDS = {'m12': lambda b: b % 12 == 1, 'm12x13': lambda b: b % 12 == 1 and b != 13,
         'eq13': lambda b: b == 13}
rowd = {}
for s, r in cert['rows']:
    for t in r:
        assert sum(pow(s, k, t) for k in range(d)) % t == 0 and isprime(t) and t != 2
        rowd.setdefault(s, set()).add(t)

def cases(rowd):
    out = []
    for ns, cs in variants:
        sd = seeds[:ns]
        for b in [0] + [s for s in rowd if CANDS[cs](s)]:
            out.append((sd, b))
    return out

def closure(rowd, sd, b):
    R = set(sd); st = list(sd)
    while st:
        x = st.pop()
        if x == b: continue
        for t in rowd.get(x, ()):
            if t not in R: R.add(t); st.append(t)
    return R

def ok(rowd, cs=None):
    for sd, b in (cs or cases(rowd)):
        if not T <= closure(rowd, sd, b): return False
    return True

assert ok(rowd)
if prune:
    # drop receivers that are neither sources nor targets, then try to drop whole rows
    for s in rowd: rowd[s] = {t for t in rowd[s] if t in rowd or t in T or t in seeds}
    assert ok(rowd)
    changed = True
    while changed:
        changed = False
        for s in sorted(rowd, reverse=True):
            if s in seeds and s not in rowd: continue
            trial = {k: v for k, v in rowd.items() if k != s}
            if ok(trial):
                rowd = trial; changed = True
        for s in sorted(rowd, reverse=True):
            for t in sorted(rowd[s], reverse=True):
                trial = dict(rowd); trial[s] = rowd[s] - {t}
                if ok(trial): rowd = trial; changed = True
        rowd = {k: v for k, v in rowd.items() if v}
# order: BFS over sources from the seeds
order = list(seeds); seen = set(order); i = 0
while i < len(order):
    x = order[i]
    if x in rowd:
        for t in sorted(rowd[x]):
            if t not in seen and t in rowd: seen.add(t); order.append(t)
    i += 1
for s in sorted(rowd):
    if s not in seen: seen.add(s); order.append(s)
# seeds without rows stay in front (they must be the first ns nodes)
nsrc = len(order)
while nsrc > 0 and order[nsrc - 1] not in rowd and order[nsrc - 1] not in seeds: nsrc -= 1
sinks = sorted({t for v in rowd.values() for t in v} - set(order))
order = order + sinks
assert set(T) <= set(order), set(T) - set(order)
idx = {t: k for k, t in enumerate(order)}
rows = [sorted(idx[t] for t in rowd.get(x, ())) for x in order[:nsrc]]
assert len(set(order)) == len(order) and all(isprime(t) and t != 2 for t in order)
tidx = sorted(idx[t] for t in T); vals = [order[j] for j in tidx]
tm = 0
for j in tidx: tm |= 1 << j

def fiter(b, passes, M):
    for _ in range(passes):
        if M & tm == tm: break
        for k, (x, r) in enumerate(zip(order, rows)):
            if (M >> k) & 1 and x != b:
                for j in r: M |= 1 << j
    return M

src = order[:len(rows)]
passes = 1
allcases = []
for ns, cs in variants:
    allcases += [(ns, cs, b) for b in [0] + [x for x in src if CANDS[cs](x)]]
for ns, cs, b in allcases:
    while fiter(b, passes, (1 << ns) - 1) & tm != tm:
        passes += 1; assert passes < 50
for ns, cs, b in allcases:
    assert fiter(b, passes, (1 << ns) - 1) & tm == tm

# abundance, as abOK2
def geomS(p, a): return sum(p ** i for i in range(a + 1))
P = 1; G = 1
for t in vals: P *= t ** 4; G *= geomS(t, 4)
assert 2 * P < G
for b in vals:
    if CANDS['m12'](b): assert 2 * P * geomS(b, 4) < G * (b + 1) * b ** 3
assert len(set(vals)) == len(vals)

pc = []; done = set()
def cert_of(p):
    if p in done or p <= 1000: return
    fs = factorint(p - 1)
    for f in fs: cert_of(f)
    flist = [f for f in sorted(fs) for _ in range(fs[f])]
    a = 2
    while not all(pow(a, (p - 1) // f, p) != 1 for f in fs): a += 1
    assert pow(a, p - 1, p) == 1
    pc.append((p, a, flist)); done.add(p)
for t in order:
    if t > thr: cert_of(t)

def L(xs): return '[' + ', '.join(str(x) for x in xs) + ']'
def parts(xs): return [xs[i:i + chunk] for i in range(0, len(xs), chunk)]
out = []
D = f'`d = {d}`'
out.append(f'/-- The nodes of the {D} table: seeds, other sources, then sinks. -/')
out.append(f'def nodes{name} : List ℕ :=\n  ' + L(order))
out.append(f'\n/-- The rows of the {D} table: receiver indices for each source node. -/')
out.append(f'def rows{name} : List (List ℕ) :=\n  [' + ',\n   '.join(L(r) for r in rows) + ']')
out.append(f'\n/-- The target primes of the {D} table, in node order. -/')
out.append(f'def vals{name} : List ℕ :=\n  ' + L(vals))
out.append(f'\n/-- The target mask: bit `j` is set when node `j` is a target. -/')
out.append(f'def tm{name} : ℕ :=\n  {tm}')
out.append(f'\n/-- The product of `t ^ 4` over the target primes. -/')
out.append(f'def P{name} : ℕ :=\n  {P}')
out.append(f'\n/-- The product of `1 + t + ... + t ^ 4` over the target primes. -/')
out.append(f'def G{name} : ℕ :=\n  {G}')
for k, c in enumerate(parts(src)):
    out.append(f'\n/-- Source nodes, part {k}. -/')
    out.append(f'def src{name}_{k} : List ℕ :=\n  ' + L(c))
for k, c in enumerate(parts(order)):
    out.append(f'\n/-- Nodes, part {k}. -/')
    out.append(f'def nd{name}_{k} : List ℕ :=\n  ' + L(c))
if pc:
    out.append(f'\n/-- Pratt certificates for the large nodes of the {D} table. -/')
    out.append(f'def pc{name} : List (ℕ × ℕ × List ℕ) :=\n  [' +
               ',\n   '.join(f'({p}, {a}, {L(f)})' for p, a, f in pc) + ']')
open(f'{name}.lean.txt', 'w').write('\n'.join(out) + '\n')
json.dump({'passes': passes, 'nsrc': len(rows), 'nsrcparts': len(parts(src)), 'nndparts': len(parts(order))},
          open(f'{name}.meta.json', 'w'))
print('nodes', len(order), 'sources', len(rows), 'edges', sum(map(len, rows)), 'targets',
      len(tidx), 'passes', passes, 'pc', len(pc), 'max node', max(order),
      'cases', {(ns, cs): sum(1 for a in allcases if a[:2] == (ns, cs)) for ns, cs in variants},
      'srcparts', len(parts(src)), 'ndparts', len(parts(order)),
      'min ratio', min([G / (2 * P)] + [G * (b + 1) * b ** 3 / (2 * P * geomS(b, 4))
                                        for b in vals if b % 12 == 1]))
