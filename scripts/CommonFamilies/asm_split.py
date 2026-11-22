# Untrusted helper script for the OddPerfect Lean library.
# Assembles the module files from the output of split.py: each module gets its imports, a
# module docstring, the opening lines (written in this script; there is no head fragment), its
# body and the closing lines; the Data module also gets <name>.lean.txt before its body, and
# the final module gets the fragment finFile at its end. Writes <outDir>/<Module>.lean for
# every module of <name>.mods.json and prints the module list. Then run axioms.py once on
# each written file.
# Used by: OddPerfect/CommonNinetyFive.lean and its 18 companion modules.
# Run: python3 asm_split.py name d seedText finFile [outDir], for example
# python3 asm_split.py 95 95 '`5, 19`' fragments/fin95.lean out; outDir defaults to OddPerfect
# in the current folder and is created if missing. (The original run wrote straight into the
# folder OddPerfect of the repository.)
# Requires: Python 3 standard library. Deterministic. Running time: under a second.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: input and output files are read from and written to the current folder;
# sibling helper files are found next to this script.
# License: GPL 3, same as the repository.

import sys, json, os
n, d, seeds, fin = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
mods = json.load(open(f'{n}.mods.json')); data, facts, final = mods[0], mods[1], mods[-1]
R = os.path.join(sys.argv[5] if len(sys.argv) > 5 else 'OddPerfect', '')
os.makedirs(R, exist_ok=True)
OPEN = '''open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OddPerfect

namespace FamInst

open OddPerfect.CommonChain (maskOf)
open OddPerfect.CommonFam (pPow pSig expL)

'''
END = '\nend FamInst\n\nend OddPerfect\n'
def doc(m):
    if m == data:
        return (f'the forcing table of the common `{d}` family (seeds {seeds}), the parts of its\n'
                'rows and nodes, the blocked candidates, its target primes and their products')
    if m == facts:
        return (f'facts about the common `{d}` table: its parts, its nodes are not `2`, its\n'
                'target primes are selected and distinct, and their full products')
    for k, w in (('Rows', 'the row divisibility checks'), ('Prime', 'the primality checks'),
                 ('Reach', 'the reach checks')):
        if m.startswith(final + k):
            return f'{w} of the common `{d}` table, part {m[len(final + k):]}'
for m in mods[:-1]:
    imp = 'OddPerfect.CommonFiveSeven' if m == data else 'OddPerfect.' + data
    body = open(f'mod_{m}.txt').read()
    if m == data: body = open(f'{n}.lean.txt').read() + '\n' + body
    txt = (f'import {imp}\n\n/-!\n# Common exponent families: {doc(m)}\n\n'
           f'Part of the proof that the common `{d}` family is impossible; the final theorem is in\n'
           f'`OddPerfect.{final}`.\n-/\n\n' + OPEN + body + END)
    open(R + m + '.lean', 'w').write(txt)
imps = '\n'.join(f'import OddPerfect.{m}' for m in mods[1:-1])
txt = (imps + f'''

/-!
# Common exponent families: the common `{d}` family

Let `N` be an odd perfect number with special prime `q`. A common `d` family means that `d`
divides `v_p(N) + 1` for every ordinary prime `p`. This file proves that the common `{d}`
family is impossible, from the table and checks of the modules `OddPerfect.{data}` and
`OddPerfect.{final}Rows1` onward, with the reach and abundance checkers of
`OddPerfect.CommonFiveSeven`. Known: the statement follows from the Main Theorem of Fletcher,
Nielsen and Ochem (Math. Comp. 81, 2012) together with Kanold's theorem
(`OddPerfect.dvd_of_dvd_succ`); the proof here is an independent certificate checked by the kernel.
-/

''' + OPEN + open(f'mod_{final}.txt').read() + open(fin).read())
open(R + final + '.lean', 'w').write(txt)
print(' '.join(mods))
