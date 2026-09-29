#!/bin/bash
# Full OS-spec validation: generate scripts, run them on the Linux host and
# on the in-image file system, check both trace sets with tcbcheck.
#   tcb/validation/run.sh [--quick]
# Outputs go to tcb/validation/out/ (not committed); results summarised in
# tcb/validation/RESULTS.md.
set -eu
cd "$(dirname "$0")/../.."
Q=${1:-}
O=tcb/validation/out${Q:+-quick}
mkdir -p $O/sandbox
gcc -O1 -Wall -o $O/driver-linux tcb/validation/driver.c
gcc -O1 -w -DMEMFS -Ic/src/config -o $O/driver-memfs tcb/validation/driver.c
python3 tcb/validation/gen.py $O/all.scripts ${Q:+--quick}
$O/driver-linux $O/all.scripts $O/linux.trace $(realpath $O/sandbox) < /dev/null > /dev/null
$O/driver-memfs $O/all.scripts $O/memfs.trace < /dev/null > /dev/null
lake build tcbcheck 2>&1 | tail -1
for b in linux memfs; do
  echo "== $b"
  .lake/build/bin/tcbcheck $O/$b.trace > $O/$b.verdicts 2> $O/$b.summary || true
  cat $O/$b.summary
done
