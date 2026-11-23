#!/bin/sh
# Contribution gate runner. Run from the repository root after the library is built:
#
#     sh scripts/Controls/contribution_gate.sh            checks Contributions/*.lean
#     sh scripts/Controls/contribution_gate.sh DIR        checks DIR/*.lean instead
#     sh scripts/Controls/contribution_gate.sh controls   runs the gate on small forged
#                                                         contributions; each must be rejected
#
# Every contributed file is compiled outside the library (lake env lean -o) into a temporary
# folder, then ContributionGate.lean is run on the compiled files. Read a contributed file in
# full, and run scripts/Controls/contribution_scan.py on it, before compiling it on a machine
# you care about: elaborating a Lean file can run code.
set -eu
[ -f ContributionGate.lean ] && [ -f OddPerfect/Steps.lean ] || { echo "run from the repository root"; exit 2; }
tmp=$(mktemp -d)
made=""
cleanup() {
  for n in $made; do
    rm -f "$tmp/path/ContributionCheck/$n.olean" "$tmp/path/ContributionCheck/$n.lean" "$tmp/$n.log"
  done
  rm -f "$tmp/Gate.lean" "$tmp/src/Example.lean" "$tmp/src/NoSuchStep.lean"
  rmdir "$tmp/path/ContributionCheck" "$tmp/path" "$tmp/src" "$tmp" 2>/dev/null || true
}
trap cleanup EXIT
mkdir -p "$tmp/path/ContributionCheck" "$tmp/src"

# gate DIR: compiles DIR/*.lean and runs the gate; prints the gate's output; status of the gate
gate() {
  for n in $made; do
    rm -f "$tmp/path/ContributionCheck/$n.olean" "$tmp/path/ContributionCheck/$n.lean"
  done
  imports=""
  for f in "$1"/*.lean; do
    [ -e "$f" ] || continue
    n=$(basename "$f" .lean)
    case "$n" in
      *[!A-Za-z0-9]*|[!A-Z]*) echo "contribution gate FAILED: $f: the file name must be a step name"; return 1 ;;
    esac
    # Lean takes the module name from the path below --root, so the file is compiled from a
    # copy at the place it is imported from.
    cp "$f" "$tmp/path/ContributionCheck/$n.lean"
    if ! lake env lean --root="$tmp/path" -o "$tmp/path/ContributionCheck/$n.olean" \
        "$tmp/path/ContributionCheck/$n.lean" > "$tmp/$n.log" 2>&1; then
      head -20 "$tmp/$n.log"
      echo "contribution gate FAILED: $f does not compile"; return 1
    fi
    made="$made $n"
    imports="$imports
import ContributionCheck.$n"
  done
  { echo "import OddPerfect.Steps$imports"; cat ContributionGate.lean; } > "$tmp/Gate.lean"
  lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean "$2"' sh "$tmp/path" "$tmp/Gate.lean"
}

if [ "${1:-}" != controls ]; then
  gate "${1:-Contributions}"
  exit $?
fi

# Controls: the format example must pass, and each forged variant of it must be rejected with
# the expected message.
pass=0; total=0
control() { # name, expected text, expected status (0 or 1); the file is $tmp/src/Example.lean
  total=$((total + 1))
  if out=$(gate "$tmp/src" 2>&1); then st=0; else st=1; fi
  if [ "$st" = "$3" ] && printf '%s\n' "$out" | grep -q "$2"; then
    pass=$((pass + 1)); echo "PASS $1"
  else
    echo "FAIL $1 (status $st)"; printf '%s\n' "$out" | head -8
  fi
}
cp Contributions/Example.lean "$tmp/src/Example.lean"
control "the format example is accepted" "contribution gate OK: 1 proofs checked" 0
cat > "$tmp/src/Example.lean" <<'LEAN'
import OddPerfect.Steps
namespace OddPerfect.Proofs
theorem Example : OddPerfect.Steps.Example := sorry
end OddPerfect.Proofs
LEAN
control "sorry is rejected" "sorryAx" 1
cat > "$tmp/src/Example.lean" <<'LEAN'
import OddPerfect.Steps
namespace OddPerfect.Proofs
axiom assumed : OddPerfect.Steps.Example
theorem Example : OddPerfect.Steps.Example := assumed
end OddPerfect.Proofs
LEAN
control "an added axiom is rejected" "is an axiom" 1
cat > "$tmp/src/Example.lean" <<'LEAN'
import OddPerfect.Steps
namespace OddPerfect.Proofs
theorem Example : True := trivial
end OddPerfect.Proofs
LEAN
control "a different statement is rejected" "is not exactly" 1
cat > "$tmp/src/Example.lean" <<'LEAN'
import OddPerfect.Steps
namespace OddPerfect.Proofs
def Example : Prop := OddPerfect.Steps.Example
end OddPerfect.Proofs
LEAN
control "a definition in place of the theorem is rejected" "has no theorem" 1
cat > "$tmp/src/Example.lean" <<'LEAN'
import OddPerfect.Steps
namespace OddPerfect.Proofs
theorem Example : OddPerfect.Steps.Example := by
  intro N h h2
  have h1 := Nat.odd_iff.mp h.odd
  omega
theorem byNative : (2 : Nat) + 2 = 4 := by native_decide
end OddPerfect.Proofs
LEAN
control "native_decide in a helper is rejected" "depends on the axioms" 1
mv "$tmp/src/Example.lean" "$tmp/src/NoSuchStep.lean"
control "a file that names no step is rejected" "has no step of this name" 1
rm -f "$tmp/src/NoSuchStep.lean"
echo "contribution gate controls: $pass of $total"
[ "$pass" = "$total" ]
