#!/bin/sh
# Runs the checker controls. From the repository root, after `lake build`:
#
#     sh CheckerControls/run.sh
#
# Checks CheckerControls/Controls.lean, whose examples fix the value of each certificate
# checker on tiny well formed and malformed inputs. Nothing is written inside the repository
# or under .lake. Passes only if Lean exits 0 and prints no error, warning or panic.

set -u

dir=$(dirname "$0")
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
log="$tmp/controls.log"

lake env lean "$dir/Controls.lean" > "$log" 2>&1
status=$?

if [ "$status" -ne 0 ] || grep -qE 'error|warning|PANIC|sorry' "$log"; then
  echo "FAIL: CheckerControls/Controls.lean (exit $status)"
  sed 's/^/     | /' "$log" | head -n 80
  echo "checker controls FAILED"
  exit 1
fi
count=$(grep -c '^example' "$dir/Controls.lean")
echo "checker controls OK: $count examples"
