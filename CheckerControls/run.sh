#!/bin/sh
# Runs the checker controls. From the repository root, after `lake build`:
#
#     sh CheckerControls/run.sh          (the light controls)
#     sh CheckerControls/run.sh full     (also the generated checks, about 15 GB of memory)
#
# Checks CheckerControls/Controls.lean, whose examples fix the value of each certificate
# checker on tiny well formed and malformed inputs, CheckerControls/PairedControls.lean, the
# output of scripts/TwoExceptionTwo/paired.py (the helpers of the two exception engine on fixed
# input vectors, with the values of its Python mirror; compare the file with the generator by
# `python3 -I scripts/TwoExceptionTwo/paired.py check CheckerControls/PairedControls.lean`), and
# CheckerControls/LargestPrimeControls.lean, the five generated checks of
# scripts/LargestPrimeFactor/gen4.py (compare them with the generator by
# scripts/LargestPrimeFactor/check_controls.sh). First compares the examples of the three files
# with the inventory CheckerControls/manifest.txt (required groups and least example counts),
# then has Lean check Controls.lean and PairedControls.lean and, with the argument `full`, also
# LargestPrimeControls.lean. That file repeats on the same literals what the library module
# OddPerfect/LargestPrimeFactor.lean already checks in every build, and costs as much, so it is
# compiled only on request. Nothing is written inside the repository or under .lake. Passes only
# if the inventory is met, Lean exits 0 and prints no error, warning or panic for each file.

set -u

dir=$(dirname "$0")
controls="$dir/Controls.lean"
lpc="$dir/LargestPrimeControls.lean"
paired="$dir/PairedControls.lean"
manifest="$dir/manifest.txt"

if [ ! -r "$controls" ] || [ ! -r "$paired" ] || [ ! -r "$lpc" ] || [ ! -r "$manifest" ]; then
  echo "FAIL: $controls, $paired, $lpc or $manifest is missing"
  echo "checker controls FAILED"
  exit 1
fi

# Prints one line per problem, then "total <n>"; exits 1 if there is a problem.
inventory=$(awk '
  FILENAME == ARGV[1] {
    if ($0 ~ /^[ \t]*(#|$)/) next
    t = substr($0, index($0, " ") + 1)
    if ($1 !~ /^[0-9]+$/ || index($0, " ") == 0 || t == "") {
      print "bad manifest line: " $0; bad = 1; next
    }
    need[t] = $1 + 0; order[++k] = t; sum += $1; next
  }
  FNR == 1 { g = "" }
  /^\/-! ## .* -\/$/ { g = substr($0, 8, length($0) - 10); seen[g] = 1; next }
  /^example/ { all++; if (g != "") cnt[g]++; if (FILENAME == ARGV[3]) heavy++ }
  END {
    if (k == 0) { print "manifest lists no control group"; bad = 1 }
    for (i = 1; i <= k; i++) {
      t = order[i]
      if (!(t in seen)) { print "missing control group: " t; bad = 1 }
      else if (cnt[t] < need[t]) {
        print "control group " t ": " cnt[t] + 0 " examples, at least " need[t] " required"; bad = 1
      }
    }
    if (all < sum) { print "only " all + 0 " examples, at least " sum " required"; bad = 1 }
    print "heavy " heavy + 0
    print "total " all + 0
    exit bad
  }' "$manifest" "$controls" "$lpc" "$paired")
istatus=$?
if [ "$istatus" -ne 0 ]; then
  echo "FAIL: the control files do not meet CheckerControls/manifest.txt"
  echo "$inventory" | sed 's/^/     | /'
  echo "checker controls FAILED"
  exit 1
fi
count=${inventory##*total }
heavy=${inventory##*heavy }
heavy=${heavy%%[!0-9]*}
if [ "${1:-}" = full ]; then
  files="$controls $paired $lpc"
  note=""
else
  files="$controls $paired"
  count=$((count - heavy))
  note="; $heavy generated examples of LargestPrimeControls.lean not compiled (run with the argument full)"
fi

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
log="$tmp/controls.log"

for f in $files; do
  lake env lean "$f" > "$log" 2>&1
  status=$?
  if [ "$status" -ne 0 ] || grep -qE 'error|warning|PANIC|sorry' "$log"; then
    echo "FAIL: $f (exit $status)"
    sed 's/^/     | /' "$log" | cut -c1-300 | head -n 80
    echo "checker controls FAILED"
    exit 1
  fi
done
echo "checker controls OK: $count examples$note"
