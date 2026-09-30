#!/bin/bash
# OS-spec trace validation of the Lua image's c/src/htif.c (its in-image
# file system, compiled natively), with ship-your-ocaml's driver and checker
# (tcb/validation/, copied verbatim). Also re-runs the Linux host traces as
# a control.
#   experiments/os/run.sh [--quick]
# Outputs in experiments/os/out/ (not committed); results in
# experiments/os/RESULTS.md.
set -eu
cd "$(dirname "$0")/../.."
Q=${1:-}
O=experiments/os/out${Q:+-quick}
mkdir -p "$O/sandbox"
gcc -O1 -Wall -o "$O/driver-linux" tcb/validation/driver.c
gcc -O1 -w -DMEMFS -include experiments/os/htif_shim.h -o "$O/driver-htif" tcb/validation/driver.c
python3 tcb/validation/gen.py "$O/all.scripts" ${Q:+--quick}
"$O/driver-linux" "$O/all.scripts" "$O/linux.trace" "$(realpath "$O/sandbox")" < /dev/null > /dev/null
# console.scripts only on htif.c: the Linux driver does not reset fds 0-2
# between scripts, so there they are not independent
"$O/driver-htif" "$O/all.scripts" "$O/htif.trace" < /dev/null > /dev/null
"$O/driver-htif" experiments/os/console.scripts "$O/console-htif.trace" < /dev/null > /dev/null
lake build tcbcheck 2>&1 | tail -1
for b in linux htif console-htif; do
  echo "== $b"
  .lake/build/bin/tcbcheck "$O/$b.trace" > "$O/$b.verdicts" 2> "$O/$b.summary" || true
  cat "$O/$b.summary"
done
for b in htif console-htif; do python3 tcb/validation/classify.py "$O/$b.verdicts" > "$O/$b.classes"; done
