#!/bin/sh
# Runs the checker controls. From the repository root, after `lake build`:
#
#     sh CheckerControls/run.sh
#
# Checks CheckerControls/Controls.lean, whose examples fix the value of each certificate
# checker on tiny well formed and malformed inputs. First compares the examples with the
# inventory CheckerControls/manifest.txt (required groups and least example counts), then has
# Lean check the file. Nothing is written inside the repository or under .lake. Passes only if
# the inventory is met, Lean exits 0 and prints no error, warning or panic.

set -u

dir=$(dirname "$0")
controls="$dir/Controls.lean"
manifest="$dir/manifest.txt"

if [ ! -r "$controls" ] || [ ! -r "$manifest" ]; then
  echo "FAIL: $controls or $manifest is missing"
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
  /^\/-! ## .* -\/$/ { g = substr($0, 8, length($0) - 10); seen[g] = 1; next }
  /^example/ { all++; if (g != "") cnt[g]++ }
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
    print "total " all + 0
    exit bad
  }' "$manifest" "$controls")
istatus=$?
if [ "$istatus" -ne 0 ]; then
  echo "FAIL: CheckerControls/Controls.lean does not meet CheckerControls/manifest.txt"
  echo "$inventory" | sed 's/^/     | /'
  echo "checker controls FAILED"
  exit 1
fi
count=${inventory##*total }

tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
log="$tmp/controls.log"

lake env lean "$controls" > "$log" 2>&1
status=$?

if [ "$status" -ne 0 ] || grep -qE 'error|warning|PANIC|sorry' "$log"; then
  echo "FAIL: CheckerControls/Controls.lean (exit $status)"
  sed 's/^/     | /' "$log" | head -n 80
  echo "checker controls FAILED"
  exit 1
fi
echo "checker controls OK: $count examples"
