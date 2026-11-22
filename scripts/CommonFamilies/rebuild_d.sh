#!/usr/bin/env bash
# Untrusted helper script for the OddPerfect Lean library.
# Regenerates OddPerfect/CommonFiftyFive.lean (d = 55) or OddPerfect/CommonEightyFive.lean
# (d = 85) with the cheaper checks of OddPerfect/CommonFastChecks.lean, from the module itself.
# Steps: extract_input_d.py reads the table (nodes, rows, targets) back from the module; gen2.py
# with the arguments of the original run (see the README) writes the literals; first the old
# chain (mktail.py without the key "fast", head, literals, tail, fin, axioms.py) is run and its
# output is compared with the module, then the key "fast": {"P": 4099} is set in the meta file,
# mktail.py runs again, the theorem nd<d>_eq is moved in front of the row checks (the fast row
# lemma hrows<d> uses it), the first line of the head becomes the import of
# OddPerfect.CommonFastChecks, and the module is assembled the same way.
# Used by: OddPerfect/CommonFiftyFive.lean and OddPerfect/CommonEightyFive.lean.
# Run: bash rebuild_d.sh <checkout> <d> <outDir>; outDir must not exist or be empty. The new
# module is written to outDir/new/. With a checkout that already holds the new module, the first
# comparison is skipped and the new output is compared with the module instead.
# Requires: bash, Python 3 and sympy (the recorded run used Python 3.12.14 and sympy 1.14.0).
# Interpreter: the environment variable PYTHON if set, otherwise python3 from PATH, run in
# isolated mode (-I).
# Deterministic. Running time: a few seconds.
# Untrusted: every result is checked again by the Lean kernel.
# Paths: all paths come from the arguments.
# License: GPL 3, same as the repository.

set -euo pipefail
[ $# -eq 3 ] || { echo "usage: rebuild_d.sh <checkout> <d> <outDir>" >&2; exit 2; }
C=$(cd "$1" && pwd)
d=$2
case "$d" in
  55) M=CommonFiftyFive; SEEDS=5,11 ;;
  85) M=CommonEightyFive; SEEDS=5,17 ;;
  *) echo "d must be 55 or 85" >&2; exit 2 ;;
esac
mkdir -p "$3"
O=$(cd "$3" && pwd)
[ -z "$(ls -A "$O")" ] || { echo "output folder $O is not empty" >&2; exit 2; }
S="$C/scripts/CommonFamilies"
F="$S/fragments"
PY=${PYTHON:-python3}
LAND="$C/OddPerfect/$M.lean"
cd "$O"

"$PY" -I "$S/extract_input_d.py" "$d" "$LAND" in.json
"$PY" -I "$S/gen2.py" in.json "$d" "$SEEDS" 10000000 100 0 2:m12

status=0
if head -1 "$LAND" | grep -q CommonFastChecks; then
  echo "the checkout holds the new module; old chain skipped"
else
  mkdir old
  cp "$d.lean.txt" "$d.meta.json" old/
  (cd old && "$PY" -I "$S/mktail.py" "$d" "$d" ':2:b % 12 == 1' &&
    cat "$F/head$d.lean" "$d.lean.txt" "$d.tail.txt" "$F/fin$d.lean" > "$M.lean" &&
    "$PY" -I "$S/axioms.py" "$M.lean")
  if cmp -s "old/$M.lean" "$LAND"; then echo "old chain: byte equal to $M.lean"
  else echo "old chain differs from $M.lean" >&2; status=1; fi
fi

mkdir new
cp "$d.lean.txt" new/
"$PY" -I - "$d" <<'EOF'
import json, sys
d = sys.argv[1]
m = json.load(open(f'{d}.meta.json')); m['fast'] = {'P': 4099}
json.dump(m, open(f'new/{d}.meta.json', 'w'))
EOF
cd new
"$PY" -I "$S/mktail.py" "$d" "$d" ':2:b % 12 == 1'
"$PY" -I - "$d" "$F/head$d.lean" <<'EOF'
import sys
d, head = sys.argv[1], sys.argv[2]
t = open(f'{d}.tail.txt').read()
blk = f'/-- The nodes in parts. -/\ntheorem nd{d}_eq : nodes{d} ='
i = t.index(blk); j = t.index('\n\n', i) + 2
nd = t[i:j]; t = t[:i] + t[j:]
k = t.index('/-- The node parts as one list. -/')
open(f'{d}.tail.txt', 'w').write(t[:k] + nd + t[k:])
h = open(head).read().split('\n', 1)
assert h[0] == 'import OddPerfect.CommonFiveSeven'
open('head.lean', 'w').write('import OddPerfect.CommonFastChecks\n' + h[1])
EOF
cat head.lean "$d.lean.txt" "$d.tail.txt" "$F/fin$d.lean" > "$M.lean"
"$PY" -I "$S/axioms.py" "$M.lean"
if head -1 "$LAND" | grep -q CommonFastChecks; then
  if cmp -s "$M.lean" "$LAND"; then echo "new chain: byte equal to $M.lean"
  else echo "new chain differs from $M.lean" >&2; status=1; fi
fi
echo "written: $O/new/$M.lean"
exit $status
