# Untrusted helper script for the OddPerfect Lean library.
# Appends one "#print axioms" line per theorem of a Lean file (with its namespace), as at the
# end of the assembled family files.
# Used by: OddPerfect/CommonFiveSeven.lean, CommonSixtyFive.lean, CommonFiftyFive.lean,
# CommonEightyFive.lean, CommonOneFifteen.lean, CommonOneFifteenData.lean,
# CommonOneFifteenPrime.lean, and the 19 modules CommonNinetyFive*.lean (the final lines).
# Run: python3 axioms.py file.lean (edits the file in place).
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, re
p = sys.argv[1]; s = open(p).read()
names = []; ns = []
for line in s.splitlines():
    m = re.match(r'namespace (\S+)', line)
    if m: ns.append(m.group(1)); continue
    m = re.match(r'end (\S+)', line)
    if m and ns and ns[-1] == m.group(1): ns.pop(); continue
    m = re.match(r'theorem (\S+)', line)
    if m: names.append('.'.join(ns + [m.group(1)]))
open(p, 'a').write('\n' + '\n'.join(f'#print axioms {n}' for n in names) + '\n')
