#!/usr/bin/env bash
# Round 5: compile ONE Lean file under the shared machine's rules
# (8 GB cap; refuse if fewer than 25 GB are available), recording user CPU
# and peak RSS. Usage: run_lean.sh <file.lean> <out-file>
set -u
root="$(cd "$(dirname "$0")/../../.." && pwd)"
avail=$(grep "Mem:" ~/syi-mem.log | tail -1 | awk '{print $NF}')
if [ "${avail:-0}" -lt 25 ]; then echo "only ${avail} GB available; wait" >&2; exit 2; fi
cd "$root"
/usr/bin/time -f "USER %U s  SYS %S s  WALL %e s  PEAK %M KB" \
  systemd-run --user --scope -p MemoryMax=8G -q lake env lean "$1" > "$2" 2>&1
echo "exit $?" >> "$2"
