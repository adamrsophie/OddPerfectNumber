#!/usr/bin/env bash
# Untrusted helper script for the OddPerfect Lean library.
# Regenerates the three modules OddPerfect/CommonOneFifteenData.lean,
# CommonOneFifteenPrime.lean and CommonOneFifteen.lean of the common 115 family from the
# certificate certs/cert_d115.json.xz and compares them byte for byte with the checkout.
# Steps (the manual steps of the original run done here in Python): decompress the
# certificate; gen2.py; insert "set_option maxRecDepth 20000 in" before the docstrings of
# nodes115 and rows115 and set "zc": 50 in 115.meta.json; mktail.py; split115.py; join each
# part with its fragments head115*.lean and fin115*.lean; axioms.py on each module; cmp.
# Used by: OddPerfect/CommonOneFifteenData.lean, CommonOneFifteenPrime.lean,
# CommonOneFifteen.lean.
# Run: bash rebuild115.sh <checkout> <outDir>; outDir must not exist or be empty. Exits
# nonzero on any difference. Every intermediate file stays in outDir.
# Requires: bash, xz, Python 3 and sympy. Interpreter: the environment variable PYTHON if
# set, otherwise python3 from PATH; every step runs it in isolated mode (-I).
# Deterministic. Running time: about ten seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: all paths come from the two arguments.
# License: GPL 3, same as the repository.

set -euo pipefail
[ $# -eq 2 ] || { echo "usage: rebuild115.sh <checkout> <outDir>" >&2; exit 2; }
C=$(cd "$1" && pwd)
mkdir -p "$2"
O=$(cd "$2" && pwd)
[ -z "$(ls -A "$O")" ] || { echo "output folder $O is not empty" >&2; exit 2; }
S="$C/scripts/CommonFamilies"
F="$S/fragments"
PY=${PYTHON:-python3}
cd "$O"

xz -dc "$S/certs/cert_d115.json.xz" > cert_d115.json
"$PY" -I "$S/gen2.py" cert_d115.json 115 5,23 1000000000 100 0 2:m12

"$PY" -I - <<'EOF'
import json
s = open('115.lean.txt').read()
for name in ('nodes115', 'rows115'):
    i = s.index(f'\ndef {name} :')
    j = s.rfind('\n/-- ', 0, i) + 1  # 0 when the docstring opens the file
    s = s[:j] + 'set_option maxRecDepth 20000 in\n' + s[j:]
open('115.lean.txt', 'w').write(s)
m = json.load(open('115.meta.json')); m['zc'] = 50
json.dump(m, open('115.meta.json', 'w'))
EOF

"$PY" -I "$S/mktail.py" 115 115 ':2:b % 12 == 1'
"$PY" -I "$S/split115.py"
cat "$F/head115data.lean" 115.lean.txt 115data.tail.txt "$F/fin115data.lean" > CommonOneFifteenData.lean
cat "$F/head115prime.lean" 115prime.tail.txt "$F/fin115prime.lean" > CommonOneFifteenPrime.lean
cat "$F/head115.lean" 115main.tail.txt "$F/fin115.lean" > CommonOneFifteen.lean

status=0
n=0
for f in CommonOneFifteenData.lean CommonOneFifteenPrime.lean CommonOneFifteen.lean; do
  "$PY" -I "$S/axioms.py" "$f"
  if cmp -s "$f" "$C/OddPerfect/$f"; then
    n=$((n + 1))
  else
    echo "differs: $f" >&2; status=1
  fi
done
echo "byte equal: $n of 3 modules"
exit $status
