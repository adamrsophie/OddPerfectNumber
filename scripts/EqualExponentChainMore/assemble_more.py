# Untrusted helper script for the OddPerfect Lean library.
# Writes the text of OddPerfect/EqualExponentChainMore.lean from certificate JSON files, with
# emit.py of EqualExponentChain: module header, the certificate bodies, the theorems and the
# final #print axioms lines.
# Used by: OddPerfect/EqualExponentChainMore.lean (the whole file).
# Run: python3 assemble_more.py cert_31.json cert_37.json cert_41.json cert_43.json
# > EqualExponentChainMore.lean (with the files from certs/ in the current folder)
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script, and the helpers shared with
# EqualExponentChain (pm1.py, emit.py, osearch) in the sibling folder EqualExponentChain.
# License: GPL 3, same as the repository.

import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(1, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'EqualExponentChain'))
from emit import emit, theorem

HEAD = '''import OddPerfect.EqualExponentChain

/-!
# Equal exponent chains: further instances

Kernel checked certificates, for the checker `OddPerfect.EqChain.checkAll` of
`OddPerfect.EqualExponentChain`, showing that the exponents other than the special prime of an
odd perfect number cannot all equal `l - 1` for `l = 31, 37, 41, 43`.
The certificates were found by an untrusted search and are checked by `decide +kernel`.
-/

'''
bodies, thms, names = [], [], []
for fn in sys.argv[1:]:
    b, (l, name) = emit(json.load(open(fn)))
    bodies.append(b); thms.append(theorem(l, name)); names.append((l, name))
out = HEAD + 'namespace OddPerfect.EqChain\n\n' + '\n'.join(bodies) + \
    '\nend OddPerfect.EqChain\n\nnamespace OddPerfect\n\n' + '\n'.join(thms) + '\nend OddPerfect\n\n'
for l, name in names:
    out += f'#print axioms OddPerfect.EqChain.check{l}\n'
for l, name in names:
    out += f'#print axioms OddPerfect.not_all_exponents_eq_{name}\n'
sys.stdout.write(out)
