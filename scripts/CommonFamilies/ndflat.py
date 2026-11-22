# Untrusted helper script for the OddPerfect Lean library.
# Post-processes the output of gen2.py and mktail.py: removes the node list literal and the
# node parts from <name>.lean.txt and puts the parts first, then defines the node list as the
# flattening of its parts, so that the parts equation holds by rfl and the kernel never
# compares two long lists; in <name>.tail.txt the proof of nd<name>_eq becomes rfl. Edits both
# files in place. A line "set_option maxRecDepth ... in" before the node list is dropped.
# The new docstring says "The nodes of the `d` table"; for 95 the run then replaced `d` by
# `d = 95` with sed (see the README).
# Used by: OddPerfect/CommonNinetyFiveData.lean (nodes95, nd95_0 .. nd95_89) and
# CommonNinetyFiveFacts.lean (nd95_eq).
# Run: python3 ndflat.py name (after gen2.py and mktail.py).
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, re
n = sys.argv[1]
s = open(f'{n}.lean.txt').read()
parts = re.findall(rf'\n/-- Nodes, part \d+\. -/\ndef nd{n}_\d+ : List ℕ :=\n  \[[^\]]*\]\n', s)
for p in parts: s = s.replace(p, '\n', 1)
m = re.search(rf'(set_option maxRecDepth \d+ in\n)?/-- The nodes of the [^\n]*-/\ndef nodes{n} : List ℕ :=\n  \[[^\]]*\]\n', s)
names = [re.search(rf'def (nd{n}_\d+)', p).group(1) for p in parts]
lines = []; cur = '  ['
for i, x in enumerate(names):
    piece = x + (', ' if i < len(names) - 1 else '].flatten')
    if len(cur) + len(piece) > 99: lines.append(cur.rstrip()); cur = '    '
    cur += piece
lines.append(cur)
new = (''.join(p.lstrip('\n') for p in parts) + '\n' +
       f'/-- The nodes of the `d` table: seeds, other sources, then sinks, as the parts above. -/\n'
       f'def nodes{n} : List ℕ :=\n' + '\n'.join(lines) + '\n')
s = s[:m.start()] + new + s[m.end():]
open(f'{n}.lean.txt', 'w').write(s)
t = open(f'{n}.tail.txt').read()
t2 = re.sub(rf'(theorem nd{n}_eq : nodes{n} =\n.*?\]\.flatten := by)\n  decide \+kernel', r'\1\n  rfl', t, flags=re.S)
assert t2 != t
open(f'{n}.tail.txt', 'w').write(t2)
