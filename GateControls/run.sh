#!/bin/sh
# Runs the axiom gate controls. From the repository root, after `lake build`:
#
#     sh GateControls/run.sh [gate file] [statement gate file]
#
# The gate file defaults to AxiomGate.lean and the statement gate file to StatementGate.lean.
# Both are copied to a temporary directory and compiled there as the modules AxiomGateLib and
# StatementGateLib (compiling them also runs both gates on the library), together with
# GateControls/GateSecondLib.lean as the module GateSecondLib, so the controls can import
# them; nothing is written inside the repository or under .lake.
# The controls mention the words axiom and unsafe on purpose; scans exclude GateControls/.
#
# Passes only if the clean controls exit 0 with the summary line, and each rejecting control
# exits with status 1 (a normal Lean error exit), reports the expected number of problems,
# and prints its intended diagnostic line. Three controls of the statement gate change its
# inventory: an entry without a restatement, a restatement without an entry, and an entry
# paired with another library theorem. Any other status (a crash or a signal), a panic,
# or a missing diagnostic fails the runner. Also runs the source scan on its control
# GateControls/SourceScan.lean (every construct reported, nothing else), checks its import
# check on the real tree and on a copy with one file missing from the root file, and replays
# the module compiled from GateControls/SkipKernel.lean with leanchecker, which must reject it.

set -u

gate=${1:-AxiomGate.lean}
sgate=${2:-StatementGate.lean}
dir=$(dirname "$0")
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT INT TERM
mkdir "$tmp/src" "$tmp/lib"
cp "$gate" "$tmp/src/AxiomGateLib.lean" || exit 2
cp "$sgate" "$tmp/src/StatementGateLib.lean" || exit 2
cp "$dir/GateSecondLib.lean" "$tmp/src/GateSecondLib.lean" || exit 2

for m in AxiomGateLib StatementGateLib GateSecondLib; do
  if ! lake env lean -R "$tmp/src" -o "$tmp/lib/$m.olean" \
      "$tmp/src/$m.lean" > "$tmp/$m.log" 2>&1; then
    echo "FAIL: $tmp/src/$m.lean (copy of the gate or control library) does not compile as a module"
    cat "$tmp/$m.log"
    exit 1
  fi
done
lean_path=$(lake env printenv LEAN_PATH) || exit 2
checker="$(lake env lean --print-prefix)/bin/leanchecker"

failures=0
total=0

# report NAME OK LOG: prints the verdict and counts a failure
report() {
  total=$((total + 1))
  if [ "$2" -eq 1 ]; then
    echo "ok   $1"
  else
    grep -vF -e '_unsafe_rec (base ' -e 'ctorIdx._impl (module ' "$3" |
      sed 's/^/     | /' | head -n 40
    failures=$((failures + 1))
  fi
}

# expect NAME STATUS LINE...: compiles GateControls/NAME.lean against the temporary modules
# and checks the exit status, the absence of a panic, and each line.
expect() {
  name=$1; want=$2; shift 2
  log="$tmp/$name.log"
  lake env env LEAN_PATH="$tmp/lib:$lean_path" lean "$dir/$name.lean" > "$log" 2>&1
  status=$?
  ok=1
  if [ "$status" -ne "$want" ]; then
    echo "FAIL $name: exit status $status, expected $want"; ok=0
  fi
  if grep -q 'PANIC' "$log"; then echo "FAIL $name: panic"; ok=0; fi
  for line in "$@"; do
    grep -qF -- "$line" "$log" || { echo "FAIL $name: missing line: $line"; ok=0; }
  done
  report "$name (exit $status)" "$ok" "$log"
}

# check NAME STATUS PROBLEMS DIAGNOSTIC...
# PROBLEMS is the expected problem count of an axiom gate rejection, or "-" for a clean control.
check() {
  name=$1; want=$2; problems=$3; shift 3
  if [ "$problems" = "-" ]; then
    expect "$name" "$want" 'axiom gate OK: ' "$@"
  else
    expect "$name" "$want" "axiom gate FAILED ($problems problems):" "$@"
  fi
}

check Clean 0 - \
  'GateControls.sumTo._unsafe_rec (base GateControls.sumTo' \
  'GateControls.halve._unsafe_rec (base GateControls.halve' \
  'exempted generated ctorIdx pairs (2):' \
  'GateControls.Shade.ctorIdx with GateControls.Shade.ctorIdx._impl (module ' \
  'GateControls.Tagged.ctorIdx with GateControls.Tagged.ctorIdx._impl (module '
check PrivateAxiom 1 2 \
  'GateControls.unusedAxiom: is an axiom'
check ForbiddenAxiom 1 3 \
  'GateControls.usesBadAxiom: depends on [GateControls.badAxiom]'
check DisguisedHelper 1 1 \
  'GateControls.disguised._unsafe_rec: is partial (not a compiler helper: base is not a recursive definition, types differ)'
check ImplementedBy 1 2 \
  'GateControls.slowId: has @[implemented_by]' \
  'GateControls.fastId: is unsafe'
check CtorIdxTarget 1 3 \
  'Foo.ctorIdx: has @[implemented_by] (not a generated ctorIdx: target is not ctorIdx._impl)' \
  'Foo.ctorIdx._impl: is unsafe (not a generated ctorIdx: target is not ctorIdx._impl)' \
  'GateControls.Foo.otherImpl: is unsafe'
check CtorIdxBody 1 2 \
  'Baz.ctorIdx: has @[implemented_by] (not a generated ctorIdx: _impl body is not getObjTagNat)' \
  'Baz.ctorIdx._impl: is unsafe (not a generated ctorIdx: _impl body is not getObjTagNat)'
check CtorIdxOrphan 1 1 \
  'GateControls.Bar.ctorIdx._impl: is unsafe (not a generated ctorIdx: target is not ctorIdx._impl)'
# The reasons of the new ctorIdx controls, in the form the gate prints them.
why='(not a generated ctorIdx: safe body is not the generated casesOn)'
check CtorIdxConst 1 2 \
  "Qux.ctorIdx: has @[implemented_by] $why" "Qux.ctorIdx._impl: is unsafe $why"
why='(not a generated ctorIdx: argument type is not T applied to its parameters and indices)'
check CtorIdxArg 1 2 \
  "Arg.ctorIdx: has @[implemented_by] $why" "Arg.ctorIdx._impl: is unsafe $why"
why='(not a generated ctorIdx: T has one constructor)'
check CtorIdxOne 1 2 \
  "Single.ctorIdx: has @[implemented_by] $why" "Single.ctorIdx._impl: is unsafe $why"
why='(not a generated ctorIdx: T is defined in another module)'
check CtorIdxModule 1 2 \
  "Far.ctorIdx: has @[implemented_by] $why" "Far.ctorIdx._impl: is unsafe $why"
check RenamedConjecture 1 7 \
  'GateControls.restated: states OddPerfectConjecture but is not named oddPerfectConjecture' \
  'GateControls.restatedNeg: states the negation of OddPerfectConjecture but is not named oddPerfectConjecture' \
  '!!! RESOLUTION: GateControls.oddPerfectConjecture proves OddPerfectConjecture; axioms:'
check ReformulatedConjecture 1 8 \
  'GateControls.viaFalse: states OddPerfectConjecture but' \
  'GateControls.viaNotExists: states OddPerfectConjecture but' \
  'GateControls.viaImplicit: states OddPerfectConjecture but' \
  'GateControls.viaAlias: states OddPerfectConjecture but' \
  'GateControls.viaCurried: states OddPerfectConjecture but' \
  'GateControls.viaUnfolded: states OddPerfectConjecture but' \
  'GateControls.viaExists: states the negation of OddPerfectConjecture but' \
  'GateControls.viaNegation: states the negation of OddPerfectConjecture but'
check ConjectureLimits 0 - \
  'statements compared up to unfolding with 7 forms, 0 matches, 0 undecided'
check SecondLibrary 1 1 \
  'module GateSecondLib is not checked and comes neither from the toolchain nor from a package'
expect ShadowedStatement 1 \
  'axiom gate OK: ' \
  'Type mismatch'
expect StatementGuard 1 \
  'statement gate FAILED (1 problems):' \
  'StatementGate.shadowed: mentions GateControls.OddPerfect, a project definition outside the allowed list'
expect StatementMissing 1 \
  'statement gate FAILED (1 problems):' \
  'StatementGate.lower_bound_79: expected restatement of OddPerfect.LowerBound.lower_bound is missing'
expect StatementExtra 1 \
  'statement gate FAILED (1 problems):' \
  'StatementGate.extra: restated but not in the expected list'
expect StatementRebound 1 \
  'statement gate FAILED (1 problems):' \
  'StatementGate.lower_bound: proved by OddPerfect.LowerBoundTwo.lower_bound, expected OddPerfect.LowerBound.lower_bound'
check SkipKernel 0 -

# The kernel replay must reject the declaration that the axiom gate accepted above.
log="$tmp/replay.log"
cp "$dir/SkipKernel.lean" "$tmp/src/GateSkipKernel.lean" || exit 2
ok=1
if lake env env LEAN_PATH="$tmp/lib:$lean_path" lean -R "$tmp/src" \
    -o "$tmp/lib/GateSkipKernel.olean" "$tmp/src/GateSkipKernel.lean" > "$log" 2>&1; then
  lake env env LEAN_PATH="$tmp/lib:$lean_path" "$checker" GateSkipKernel >> "$log" 2>&1
  status=$?
  [ "$status" -eq 1 ] || { echo "FAIL replay: exit status $status, expected 1"; ok=0; }
  grep -qF 'leanchecker found a problem in GateSkipKernel' "$log" ||
    { echo "FAIL replay: no problem reported"; ok=0; }
else
  echo "FAIL replay: GateControls/SkipKernel.lean does not compile as a module"; ok=0
fi
report "replay of GateSkipKernel" "$ok" "$log"

# The source scan must report each construct of its controls and nothing else.
log="$tmp/scan.log"
python3 -I scripts/Controls/source_scan.py "$dir/SourceScan.lean" "$dir/SourceScanLakefile.toml" \
  > "$log" 2>&1
status=$?
ok=1
[ "$status" -eq 1 ] || { echo "FAIL source scan: exit status $status, expected 1"; ok=0; }
for line in \
  'SourceScan.lean:12: debug option debug.skipKernelTC' \
  'SourceScan.lean:12: set_option debug.skipKernelTC' 'SourceScan.lean:15: set_option pp.all' \
  'SourceScan.lean:17: run_cmd' 'SourceScan.lean:19: run_meta' 'SourceScan.lean:21: run_elab' \
  'SourceScan.lean:23: #eval' 'SourceScan.lean:25: initialize' 'SourceScan.lean:27: syntax' \
  'SourceScan.lean:29: declare_syntax_cat' 'SourceScan.lean:31: macro' \
  'SourceScan.lean:33: macro_rules' 'SourceScan.lean:35: elab' 'SourceScan.lean:37: elab_rules' \
  'SourceScan.lean:39: notation' 'SourceScan.lean:41: infix' 'SourceScan.lean:43: local instance' \
  'SourceScan.lean:45: local instance' 'SourceScan.lean:47: attribute that runs code' \
  'SourceScan.lean:50: run_tac' 'SourceScan.lean:52: by_elab' 'SourceScan.lean:54: simproc' \
  'SourceScan.lean:56: attribute that runs code' 'SourceScan.lean:58: notation3' \
  'SourceScan.lean:60: prefix' 'SourceScan.lean:62: postfix' 'SourceScan.lean:64: infixl' \
  'SourceScan.lean:66: infixr' 'SourceScan.lean:68: dsimproc' \
  'SourceScan.lean:70: builtin_initialize' 'SourceScan.lean:72: local instance' \
  'SourceScan.lean:75: run_meta' 'SourceScan.lean:78: run_elab' 'SourceScan.lean:80: run_cmd' \
  'SourceScanLakefile.toml:4: lakefile option moreLeanArgs' \
  'SourceScanLakefile.toml:6: lakefile option leanOptions' \
  'source scan FAILED: 36 findings in 2 files'; do
  grep -qF -- "$line" "$log" || { echo "FAIL source scan: missing line: $line"; ok=0; }
done
report "source scan of its controls (exit $status)" "$ok" "$log"

# The import check of the source scan: the real tree must pass, and a copy of the tree with one
# library file that the root file does not import must fail and name that file.
log="$tmp/imports.log"
scan=$(pwd)/scripts/Controls/source_scan.py
ok=1
python3 -I "$scan" > "$log" 2>&1 || { echo "FAIL import check: the real tree fails"; ok=0; }
mkdir "$tmp/tree" && cp -R OddPerfect OddPerfect.lean lakefile.toml "$tmp/tree/" || exit 2
printf 'theorem gateExtra : True := trivial\n' > "$tmp/tree/OddPerfect/GateExtra.lean"
(cd "$tmp/tree" && python3 -I "$scan") >> "$log" 2>&1
status=$?
[ "$status" -eq 1 ] || { echo "FAIL import check: exit status $status on the copy, expected 1"; ok=0; }
grep -qxF 'OddPerfect/GateExtra.lean: not imported by OddPerfect.lean' "$log" ||
  { echo "FAIL import check: the extra file is not named"; ok=0; }
grep -qF 'source scan FAILED: 1 findings' "$log" ||
  { echo "FAIL import check: other findings on the copy"; ok=0; }
report "import check of the root file (exit $status on the copy)" "$ok" "$log"

if [ "$failures" -ne 0 ]; then
  echo "gate controls FAILED: $failures of $total"
  exit 1
fi
echo "gate controls OK: $total of $total"
