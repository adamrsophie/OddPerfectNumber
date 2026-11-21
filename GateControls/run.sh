#!/bin/sh
# Runs the axiom gate controls. From the repository root, after `lake build`:
#
#     sh GateControls/run.sh [gate file]
#
# The gate file defaults to AxiomGate.lean. It is copied to a temporary directory and compiled
# there as the module AxiomGateLib (compiling it also runs the gate on the library), so the
# controls can import it; nothing is written inside the repository or under .lake.
# The controls mention the words axiom and unsafe on purpose; scans exclude GateControls/.
#
# Passes only if the clean control exits 0 with the summary line, and each rejecting control
# exits with status 1 (a normal Lean error exit), reports the expected number of problems,
# and prints its intended diagnostic line. Any other status (a crash or a signal), a panic,
# or a missing diagnostic fails the runner.

set -u

gate=${1:-AxiomGate.lean}
dir=$(dirname "$0")
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
mkdir "$tmp/src" "$tmp/lib"
cp "$gate" "$tmp/src/AxiomGateLib.lean" || exit 2

if ! lake env lean -R "$tmp/src" -o "$tmp/lib/AxiomGateLib.olean" \
    "$tmp/src/AxiomGateLib.lean" > "$tmp/gate.log" 2>&1; then
  echo "FAIL: $gate does not compile as a module"
  cat "$tmp/gate.log"
  exit 1
fi
lean_path=$(lake env printenv LEAN_PATH) || exit 2

failures=0

# check NAME STATUS PROBLEMS DIAGNOSTIC...
# PROBLEMS is the expected problem count of a rejection, or "-" for the clean control.
check() {
  name=$1; want=$2; problems=$3; shift 3
  log="$tmp/$name.log"
  lake env env LEAN_PATH="$tmp/lib:$lean_path" lean "$dir/$name.lean" > "$log" 2>&1
  status=$?
  ok=1
  if [ "$status" -ne "$want" ]; then
    echo "FAIL $name: exit status $status, expected $want"; ok=0
  fi
  if grep -q 'PANIC' "$log"; then echo "FAIL $name: panic"; ok=0; fi
  if [ "$problems" = "-" ]; then
    grep -q '^axiom gate OK: ' "$log" || { echo "FAIL $name: no summary line"; ok=0; }
  else
    grep -qF "axiom gate FAILED ($problems problems):" "$log" ||
      { echo "FAIL $name: no rejection with $problems problems"; ok=0; }
  fi
  for line in "$@"; do
    grep -qF -- "$line" "$log" || { echo "FAIL $name: missing line: $line"; ok=0; }
  done
  if [ "$ok" -eq 1 ]; then
    echo "ok   $name (exit $status)"
  else
    sed 's/^/     | /' "$log" | head -n 40
    failures=$((failures + 1))
  fi
}

check Clean 0 - \
  'GateControls.sumTo._unsafe_rec (base GateControls.sumTo' \
  'GateControls.halve._unsafe_rec (base GateControls.halve'
check PrivateAxiom 1 2 \
  'GateControls.unusedAxiom: is an axiom'
check ForbiddenAxiom 1 3 \
  'GateControls.usesBadAxiom: depends on [GateControls.badAxiom]'
check DisguisedHelper 1 1 \
  'GateControls.disguised._unsafe_rec: is partial (not a compiler helper: base is not a recursive definition, types differ)'
check RenamedConjecture 1 7 \
  'GateControls.restated: states OddPerfectConjecture but is not named oddPerfectConjecture' \
  'GateControls.restatedNeg: states the negation of OddPerfectConjecture but is not named oddPerfectConjecture' \
  '!!! RESOLUTION: GateControls.oddPerfectConjecture proves OddPerfectConjecture; axioms:'

if [ "$failures" -ne 0 ]; then
  echo "gate controls FAILED: $failures of 5"
  exit 1
fi
echo "gate controls OK: 5 of 5"
