#!/usr/bin/env bash
# Untrusted helper script for the OddPerfect Lean library.
# Regenerates the 13 modules OddPerfect/CommonNinetyFive*.lean of the common 95 family from a
# clean checkout and compares them byte for byte with the landed files.
# The input inputs/family95_input.json is reconstructed from the published modules by
# extract_input.py (the nodes, rows and targets of CommonNinetyFiveData.lean), and the chain
# below reproduces those modules from it. It does not document how the original search found
# this table: the original certificate cert_d95.json, the row cache of the search and the
# search settings are not archived (see the README).
# Steps (those of the run record in the README, with the manual steps done here in Python):
# check the SHA-256 of the input; gen2.py; insert "set_option maxRecDepth 100000 in" before
# the docstrings of nodes95, rows95, vals95, set "zc": 25 and "fast": {"P": 4099} in
# 95.meta.json (the cheaper checks of OddPerfect/CommonFastChecks.lean); mktail.py;
# ndflat.py, then the docstring of nodes95 says `d = 95`; est.py; split.py; asm_split.py;
# axioms.py on each written module; compare the file list and every file with the checkout.
# The caps of the rows and primality splits are those of the original run (they keep the
# number of proofs per module, and with it the peak memory, as before); the reach cap is large,
# so that the four blocked set checks share one module.
# Used by: OddPerfect/CommonNinetyFive.lean and its 12 companion modules.
# Run: bash rebuild95.sh <checkout> <outDir>; outDir must not exist or be empty. Exits nonzero
# on any difference. Every intermediate file stays in outDir.
# Requires: bash, Python 3 and sympy (the recorded run used Python 3.12.14 and sympy 1.14.0).
# Interpreter: the environment variable PYTHON if set (for example a virtual environment
# interpreter), otherwise python3 from PATH; every step runs it in isolated mode (-I).
# Deterministic. Running time: about ten seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: all paths come from the two arguments.
# License: GPL 3, same as the repository.

set -euo pipefail
[ $# -eq 2 ] || { echo "usage: rebuild95.sh <checkout> <outDir>" >&2; exit 2; }
C=$(cd "$1" && pwd)
mkdir -p "$2"
O=$(cd "$2" && pwd)
[ -z "$(ls -A "$O")" ] || { echo "output folder $O is not empty" >&2; exit 2; }
S="$C/scripts/CommonFamilies"
PY=${PYTHON:-python3}
IN="$S/inputs/family95_input.json"
cd "$O"

"$PY" -I - "$IN" "$S/inputs/family95_input.json.sha256" <<'EOF'
import sys, hashlib
want = open(sys.argv[2]).read().split()[0]
got = hashlib.sha256(open(sys.argv[1], 'rb').read()).hexdigest()
if got != want: sys.exit(f'SHA-256 mismatch: {got} != {want}')
EOF

"$PY" -I "$S/gen2.py" "$IN" 95 5,19 1000000000 50 0 2:m12

"$PY" -I - <<'EOF'
import json
s = open('95.lean.txt').read()
for name in ('nodes95', 'rows95', 'vals95'):
    i = s.index(f'\ndef {name} :')
    j = s.rfind('\n/-- ', 0, i) + 1  # 0 when the docstring opens the file
    s = s[:j] + 'set_option maxRecDepth 100000 in\n' + s[j:]
open('95.lean.txt', 'w').write(s)
m = json.load(open('95.meta.json')); m['zc'] = 25; m['fast'] = {'P': 4099}
json.dump(m, open('95.meta.json', 'w'))
EOF

"$PY" -I "$S/mktail.py" 95 95 ':2:b % 12 == 1'
"$PY" -I "$S/ndflat.py" 95

"$PY" -I - <<'EOF'
s = open('95.lean.txt').read()
old, new = 'The nodes of the `d` table', 'The nodes of the `d = 95` table'
assert s.count(old) == 1
open('95.lean.txt', 'w').write(s.replace(old, new))
EOF

"$PY" -I "$S/est.py" 95 95 50
"$PY" -I "$S/split.py" 95 CommonNinetyFive 95 2500000 550000 1e18
"$PY" -I "$S/asm_split.py" 95 95 '`5, 19`' "$S/fragments/fin95.lean" mods OddPerfect.CommonFastChecks
for f in mods/*.lean; do "$PY" -I "$S/axioms.py" "$f"; done

status=0
got=$(cd mods && ls CommonNinetyFive*.lean)
want=$(cd "$C/OddPerfect" && ls CommonNinetyFive*.lean)
if [ "$got" != "$want" ]; then echo "module lists differ" >&2; status=1; fi
n=0
for f in $want; do
  if cmp -s "mods/$f" "$C/OddPerfect/$f"; then
    n=$((n + 1))
  else
    echo "differs: $f" >&2; status=1
  fi
done
echo "byte equal: $n of $(echo "$want" | wc -w | tr -d ' ') modules"
exit $status
