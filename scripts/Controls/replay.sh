#!/bin/sh
# Untrusted helper script for the OddPerfect Lean library.
# Kernel replay of the compiled library: replays the declarations of every library module (the
# modules that OddPerfect.lean imports from OddPerfect.*, directly or through each other) with
# leanchecker, the checker shipped with the toolchain, one module at a time. Each module's
# declarations go through the kernel again on top of the environment of its imports, so a
# declaration that was added without a kernel check (for example under debug.skipKernelTC) is
# rejected here although AxiomGate.lean cannot see it.
# Run from the repository root after lake build:
#     sh scripts/Controls/replay.sh                 (every library module)
#     sh scripts/Controls/replay.sh MODULE ...      (the given modules only)
# Never pass the umbrella module OddPerfect: leanchecker replays every module whose name starts
# with the given one, all at once, which needed more than 50 GB of memory on the build server.
# One module at a time needs at most about 10 GB (OddPerfect.OmegaSevenRootsA).
# Prints one line per module with the seconds it took, then a summary line.
# Requires: the toolchain (lake, leanchecker) and Python 3 for the module list.
# Exit status: 0 when every module replays, 1 when one fails, 2 for a usage error.
# License: GPL 3, same as the repository.

set -u

if [ ! -f OddPerfect.lean ]; then
  echo "run from the repository root"
  exit 2
fi
if [ "$#" -gt 0 ]; then
  mods=$*
else
  mods=$(python3 -I -c '
import re
seen, todo = set(), ["OddPerfect"]
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    with open(m.replace(".", "/") + ".lean") as f:
        todo += re.findall(r"^import (OddPerfect[A-Za-z0-9_.]*)\s*$", f.read(), re.M)
print("\n".join(sorted(seen - {"OddPerfect"})))
') || exit 2
fi
for m in $mods; do
  [ "$m" = OddPerfect ] && { echo "the umbrella module OddPerfect cannot be replayed alone"; exit 2; }
done

checker="$(lake env lean --print-prefix)/bin/leanchecker"
[ -x "$checker" ] || { echo "no leanchecker in the toolchain: $checker"; exit 2; }
tmp=$(mktemp) || exit 2
trap 'rm -f "$tmp"' EXIT INT TERM
count=0
failures=0
start=$(date +%s)
for m in $mods; do
  t0=$(date +%s)
  if lake env "$checker" "$m" > "$tmp" 2>&1; then
    echo "ok   $m ($(( $(date +%s) - t0 )) s)"
  else
    echo "FAIL $m"
    sed 's/^/     | /' "$tmp" | head -n 20
    failures=$((failures + 1))
  fi
  count=$((count + 1))
done
if [ "$failures" -ne 0 ]; then
  echo "kernel replay FAILED: $failures of $count modules"
  exit 1
fi
echo "kernel replay OK: $count modules, $(( $(date +%s) - start )) s"
