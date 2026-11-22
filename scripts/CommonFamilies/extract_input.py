# Untrusted helper script for the OddPerfect Lean library.
# Reconstructs the input of gen2.py for the common 95 family from the landed Lean module
# OddPerfect/CommonNinetyFiveData.lean alone: the nodes are the node parts nd95_0, nd95_1, ...
# joined in order, each row of rows95 is turned back into the pair [source, receivers] with
# the receiver indices replaced by the node values, and the targets are the literal vals95.
# The output has exactly the fields that gen2.py reads (d, rows, targets) and is written as
# compact JSON. This is not the certificate cert_d95.json of the original search (which also
# carried seeds, the special test and other keys): it is the table of the published modules,
# from which the chain in rebuild95.sh reproduces those modules byte for byte.
# Used by: rebuild95.sh, for OddPerfect/CommonNinetyFive.lean and its 12 companion modules.
# Run: python3 -I extract_input.py CommonNinetyFiveData.lean out.json
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: both files are given on the command line.
# License: GPL 3, same as the repository.

import sys, re, json

src, out = sys.argv[1], sys.argv[2]
s = open(src).read()


def lit(name):
    m = re.search(rf'\ndef {name} : [^\n]*:=\n  (\[[\[\]0-9, \n]*\])\n', s)
    assert m, name
    return json.loads(m.group(1))


parts = sorted(((int(k), k) for k in re.findall(r'\ndef nd95_(\d+) : List ℕ :=', s)))
assert [i for i, _ in parts] == list(range(len(parts)))
nodes = [x for _, k in parts for x in lit(f'nd95_{k}')]
rows = lit('rows95')
vals = lit('vals95')
assert len(nodes) == len(set(nodes)) == 4480 and len(rows) == 3200 and len(vals) == 2700
assert set(vals) <= set(nodes)
cert = {'d': 95,
        'rows': [[nodes[k], [nodes[j] for j in r]] for k, r in enumerate(rows) if r],
        'targets': vals}
open(out, 'w').write(json.dumps(cert, separators=(',', ':')) + '\n')
print('nodes', len(nodes), 'rows', len(rows), 'nonempty rows', len(cert['rows']),
      'targets', len(vals))
