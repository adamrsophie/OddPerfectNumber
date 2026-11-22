# Untrusted helper script for the OddPerfect Lean library.
# Splits the output 115.tail.txt of mktail.py over the three modules of the 115 family:
# the blocks cand115, blk115_*, reach115_*, hcand115, hrows115 and ab115 go to
# 115main.tail.txt (for CommonOneFifteen.lean), the blocks nd115_*_isPS and nodes115_prime
# to 115prime.tail.txt (for CommonOneFifteenPrime.lean), and all other blocks to
# 115data.tail.txt (for CommonOneFifteenData.lean). A block is a run of lines between blank
# lines; the order of the blocks is kept. hrows115 goes to the final module because, with the
# key "fast" of mktail.py, its proof uses nd115_eq, which comes after it in the tail.
# Used by: OddPerfect/CommonOneFifteenData.lean, CommonOneFifteenPrime.lean,
# CommonOneFifteen.lean (see the run record of the 115 family in the README).
# Run: python3 split115.py (in the folder that holds 115.tail.txt)
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import re

MAIN = re.compile(r'(cand115|blk115_\w+|reach115_\w+|hcand115|hrows115|ab115)$')
PRIME = re.compile(r'(nd115_\d+_isPS|nodes115_prime)$')


def name(block):
    m = re.search(r'^(?:private )?(?:theorem|def|lemma|abbrev) (\S+)', block, re.M)
    return m.group(1) if m else ''


tail = open('115.tail.txt').read()
assert tail.endswith('\n') and not tail.endswith('\n\n')
parts = {'data': [], 'prime': [], 'main': []}
for block in tail[:-1].split('\n\n'):
    n = name(block)
    key = 'main' if MAIN.match(n) else 'prime' if PRIME.match(n) else 'data'
    parts[key].append(block)
for key, blocks in parts.items():
    end = '\n' if key == 'main' else '\n\n'
    with open(f'115{key}.tail.txt', 'w') as f:
        f.write('\n\n'.join(blocks) + end)
    print(key, len(blocks), 'blocks')
