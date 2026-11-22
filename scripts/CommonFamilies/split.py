# Untrusted helper script for the OddPerfect Lean library.
# Splits the lemmas of <name>.tail.txt (written by mktail.py) over several modules: <Prefix>Data
# (definitions), <Prefix>Facts (cheap lemmas), <Prefix>Rows1 .. (row checks), <Prefix>Prime1 ..
# (primality checks), <Prefix>Reach1 .. (reach checks) and the final module <Prefix> (hrows,
# hcand, nodes_prime, ab). Parts are grouped greedily in order so that the estimate of
# est.py for each module stays below its cap. Writes the bodies mod_<Module>.txt and the
# module list <name>.mods.json in import order, and prints the groups.
# Used by: OddPerfect/CommonNinetyFive.lean and its 18 companion modules (through asm_split.py).
# Run: python3 split.py name Prefix d rowsCap primeCap reachCap, for example
# python3 split.py 95 CommonNinetyFive 95 2500000 550000 450000.
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, re, json
n, pre, d = sys.argv[1], sys.argv[2], int(sys.argv[3])
caps = {'rows': float(sys.argv[4]), 'prime': float(sys.argv[5]), 'reach': float(sys.argv[6])}
est = json.load(open(f'{n}.est.json'))
t = open(f'{n}.tail.txt').read()
blocks = [b for b in re.split(r'\n(?=/--)', t) if b.strip()]
def name(b):
    m = re.search(r'^(?:theorem|def) (\S+)', b, re.M); return m.group(1)
cat = {'data': [], 'final': []}; parts = {'rows': {}, 'prime': {}, 'reach': {}}
for b in blocks:
    nm = name(b)
    m = re.fullmatch(rf'rows{n}_(\d+)', nm)
    if m: parts['rows'][int(m.group(1))] = b; continue
    m = re.fullmatch(rf'nd{n}_(\d+)_isPS', nm)
    if m: parts['prime'][int(m.group(1))] = b; continue
    m = re.fullmatch(rf'reach{n}_(\d+)', nm)
    if m: parts['reach'][int(m.group(1))] = b; continue
    if nm in (f'reach{n}_none',): parts['reach'][-1] = b; continue
    if nm in (f'hrows{n}', f'hcand{n}', f'nodes{n}_prime', f'ab{n}'): cat['final'].append(b)
    else: cat['data'].append(b)
dd = [b for b in cat['data'] if re.search(r'^def ', b, re.M)]
ff = [b for b in cat['data'] if not re.search(r'^def ', b, re.M)]
mods = [(pre + 'Data', dd), (pre + 'Facts', ff)]
for kind, label in (('rows', 'Rows'), ('prime', 'Prime'), ('reach', 'Reach')):
    keys = sorted(k for k in parts[kind] if k >= 0)
    groups = [[]]; acc = 0
    for k in keys:
        c = est[kind][k]
        if groups[-1] and acc + c > caps[kind]: groups.append([]); acc = 0
        groups[-1].append(k); acc += c
    if -1 in parts[kind]: groups[-1].append(-1)
    for g_i, g in enumerate(groups):
        mods.append((f'{pre}{label}{g_i + 1}', [parts[kind][k] for k in g]))
        print(f'{pre}{label}{g_i + 1}', kind, 'parts', g[0], g[-1] if g[-1] >= 0 else g[-2],
              'est', sum(est[kind][k] for k in g if k >= 0))
mods.append((pre, cat['final']))
for m, bs in mods:
    open(f'mod_{m}.txt', 'w').write('\n'.join(bs) + '\n')
json.dump([m for m, _ in mods], open(f'{n}.mods.json', 'w'))
