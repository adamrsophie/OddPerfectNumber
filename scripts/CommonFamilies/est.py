# Untrusted helper script for the OddPerfect Lean library.
# Per part cost estimates for a table written by gen2.py (after ndflat.py or not): rows (sum
# of receiver indices plus d per edge, in parts of "zc" rows from <name>.meta.json), primality
# (sum of sqrt(x)/2 over the nodes, in parts of partSize) and reach (blocked candidates times
# rows times passes needed, in parts of partSize sources). Writes <name>.est.json, the input
# of split.py, and prints the totals. The reach estimate assumes two seeds (initial mask 3)
# and the candidates b % 12 == 1.
# Used by: split.py, for the module split of OddPerfect/CommonNinetyFive*.lean; the
# estimates themselves occur in no Lean file.
# Run: python3 est.py name d [partSize] (partSize defaults to 100; the 95 run used 50).
# Exit status: 0 on success; 1, before anything is written, when some target cannot be
# reached with a candidate blocked (no pass adds a node).
# Requires: Python 3 standard library. Deterministic. Running time: about two seconds for 95.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, re, math, json
n = sys.argv[1]; d = int(sys.argv[2]); ch = int(sys.argv[3]) if len(sys.argv) > 3 else 100; s = open(f'{n}.lean.txt').read()
meta = json.load(open(f'{n}.meta.json')); zc = meta.get('zc', 100)
def grab(nm):
    m = re.search(r'def ' + nm + r' : [^\n]*:=\n  (\[.*?\])\n', s, re.S); return eval(m.group(1))
try:
    nodes = grab('nodes' + n)
except Exception:  # node list given as the flattening of its parts (ndflat.py)
    nodes = [x for k in range(len(re.findall(rf'def nd{n}_\d+ :', s))) for x in grab(f'nd{n}_{k}')]
rows = grab('rows' + n); vals = grab('vals' + n)
tm = int(re.search(r'def tm' + n + r' : ℕ :=\n  (\d+)', s).group(1))
R = [sum(j + d for j in r) for r in rows]
rowp = [sum(R[i:i + zc]) for i in range(0, len(R), zc)]
ndp = [sum(math.isqrt(x) // 2 for x in nodes[i:i + ch]) for i in range(0, len(nodes), ch)]
def need(b):
    M = 3; p = 0
    while M & tm != tm:
        M0 = M
        for k, (x, r) in enumerate(zip(nodes, rows)):
            if (M >> k) & 1 and x != b:
                for j in r: M |= 1 << j
        if M == M0:  # a whole pass added nothing: the remaining targets are unreachable
            sys.exit(f'est.py: targets unreachable when {b} is blocked: mask {tm & ~M:#x} '
                     f'still missing after {p} passes')
        p += 1
    return p
src = nodes[:len(rows)]
rp = [sum(need(b) * len(rows) for b in src[i:i + ch] if b % 12 == 1) for i in range(0, len(src), ch)]
json.dump({'rows': rowp, 'prime': ndp, 'reach': rp}, open(f'{n}.est.json', 'w'))
print(n, 'rows', sum(rowp), 'prime', sum(ndp), 'reach', sum(rp))
