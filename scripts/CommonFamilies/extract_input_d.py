# Untrusted helper script for the OddPerfect Lean library.
# Reconstructs the input of gen2.py for a common family module (d = 55 or 85) from the landed
# Lean module alone: the nodes are the node parts nd<d>_0, nd<d>_1, ... joined in order, each
# row of rows<d> is turned back into the pair [source, receivers] with the receiver indices
# replaced by the node values, and the targets are the literal vals<d>. The output has exactly
# the fields that gen2.py reads (d, rows, targets). It is not the certificate of the original
# search: it is the table of the published module, from which gen2.py, mktail.py and axioms.py
# reproduce that module byte for byte (see rebuild_d.sh).
# Run: python3 -I extract_input_d.py <d> CommonEightyFive.lean out.json
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# License: GPL 3, same as the repository.

import sys, re, json

d, src, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
s = open(src).read()


def lit(name):
    m = re.search(rf'\ndef {name} : [^\n]*:=\n  (\[[\[\]0-9, \n]*\])\n', s)
    assert m, name
    return json.loads(m.group(1))


parts = sorted(((int(k), k) for k in re.findall(rf'\ndef nd{d}_(\d+) : List ℕ :=', s)))
assert [i for i, _ in parts] == list(range(len(parts)))
nodes = [x for _, k in parts for x in lit(f'nd{d}_{k}')]
assert nodes == lit(f'nodes{d}')
rows = lit(f'rows{d}')
vals = lit(f'vals{d}')
assert len(nodes) == len(set(nodes)) and set(vals) <= set(nodes)
cert = {'d': d,
        'rows': [[nodes[k], [nodes[j] for j in r]] for k, r in enumerate(rows) if r],
        'targets': vals}
open(out, 'w').write(json.dumps(cert, separators=(',', ':')) + '\n')
print('nodes', len(nodes), 'rows', len(rows), 'nonempty rows', len(cert['rows']),
      'targets', len(vals))
