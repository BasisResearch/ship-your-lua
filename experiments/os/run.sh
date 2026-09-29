#!/bin/bash
# OS-spec trace validation of the Lua image's console-only c/src/htif.c
# (unchanged), with ship-your-ocaml's driver and checker (tcb/validation/,
# copied verbatim). Also re-runs the Linux host traces as a control.
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
for s in all console; do
  src=$O/all.scripts p=
  [ $s = console ] && { src=experiments/os/console.scripts; p=console-; }
  "$O/driver-htif" "$src" "$O/${p}htif.raw" < /dev/null > /dev/null
  # the Lua ELF has no clock (_gettimeofday is not linked)
  sed 's/^clock => .*/clock => unsupported/' "$O/${p}htif.raw" > "$O/${p}htif.trace"
done
lake build tcbcheck 2>&1 | tail -1
for b in linux htif console-htif; do
  echo "== $b"
  .lake/build/bin/tcbcheck "$O/$b.trace" > "$O/$b.verdicts" 2> "$O/$b.summary" || true
  cat "$O/$b.summary"
done
for b in htif console-htif; do python3 tcb/validation/classify.py "$O/$b.verdicts" > "$O/$b.classes"; done
