#!/bin/sh
# Untrusted helper script for the OddPerfect Lean library.
# Regenerates the five kernel checks of `python3 gen4.py 10000 test` and compares them as text
# with the generated part of CheckerControls/LargestPrimeControls.lean: every line from the line
# `set_option profiler true` to the end of the file. That Lean file is compiled by
# `sh CheckerControls/run.sh`, so together the two commands regenerate the five statements and
# have Lean check exactly them.
# Used by: CheckerControls/LargestPrimeControls.lean.
# Run: sh scripts/LargestPrimeFactor/check_controls.sh [<checkout>] (default: the checkout that
# holds this script). Exits 0 when the texts are equal, 1 on a difference (a diff is printed),
# 2 on a usage or generator error. Nothing is written inside the repository.
# Interpreter: the environment variable PYTHON if set, otherwise python3 from PATH; run in
# isolated mode (-I).
# Requires: sh, diff and Python 3 standard library. Deterministic. Running time: about three and
# a half minutes.
# License: GPL 3, same as the repository.

set -u
[ $# -le 1 ] || { echo "usage: check_controls.sh [<checkout>]" >&2; exit 2; }
C=$(cd "${1:-$(dirname "$0")/../..}" && pwd) || exit 2
PY=${PYTHON:-python3}
lean="$C/CheckerControls/LargestPrimeControls.lean"
[ -r "$lean" ] || { echo "missing $lean" >&2; exit 2; }

tmp=$(mktemp -d) || exit 2
trap 'rm -f "$tmp/gen.lean" "$tmp/file.lean"; rmdir "$tmp"' EXIT INT TERM

"$PY" -I "$C/scripts/LargestPrimeFactor/gen4.py" 10000 test > "$tmp/gen.lean" ||
  { echo "gen4.py failed" >&2; exit 2; }
awk 'found || $0 == "set_option profiler true" { found = 1; print }' "$lean" > "$tmp/file.lean"
[ -s "$tmp/file.lean" ] || { echo "no generated part in $lean" >&2; exit 1; }

if diff "$tmp/gen.lean" "$tmp/file.lean" > /dev/null; then
  echo "largest prime controls: generated text equal ($(grep -c '^example' "$tmp/gen.lean") examples)"
  exit 0
fi
echo "largest prime controls: generated text differs from $lean" >&2
diff "$tmp/gen.lean" "$tmp/file.lean" | cut -c1-200 | head -n 20 >&2
exit 1
