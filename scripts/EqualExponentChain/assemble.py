# Untrusted helper script for the OddPerfect Lean library.
# Joins several certificate JSON files into the whole instances section (definitions,
# theorems and #print axioms lines) of OddPerfect/EqualExponentChain.lean.
# Run: python3 assemble.py cert_5.json cert_7.json ...   writes instances.lean to the
# current folder. Requires emit.py next to this file.
# Requires: Python 3 standard library. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

"""Assemble the instances section for the given certificate files."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from emit import emit, theorem
bodies, thms, names = [], [], []
for fn in sys.argv[1:]:
    b, (l, name) = emit(json.load(open(fn)))
    bodies.append(b); thms.append(theorem(l, name)); names.append((l, name))
out = '/-! ## Instances -/\n\nnamespace OddPerfect.EqChain\n\n' + '\n'.join(bodies) + \
    '\nend OddPerfect.EqChain\n\nnamespace OddPerfect\n\n' + '\n'.join(thms) + '\nend OddPerfect\n\n'
for t in ['gm_eq', 'dvd_sigma_of_gm', 'isP_sound', 'allNe_sound', 'neq_sound', 'over_sum',
          'expo_dvd', 'run_sound', 'checkAll_sound']:
    out += f'#print axioms OddPerfect.EqChain.{t}\n'
for l, name in names:
    out += f'#print axioms OddPerfect.EqChain.check{l}\n'
for l, name in names:
    out += f'#print axioms OddPerfect.not_all_exponents_eq_{name}\n'
open('instances.lean', 'w').write(out)
