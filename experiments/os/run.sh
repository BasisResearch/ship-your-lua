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
# driver.c's MEMFS branch answers mkdir/rmdir with `unsupported` and puts
# absolute paths under "/sb" (ship-your-ocaml's htif.c has no directories
# and no path resolution); ours has both, so the copy compiled here calls
# htif.c's mkdir/rmdir and passes paths unchanged (its root is the
# script's "/", as the fresh sandbox directory is on Linux). These three
# lines are the only change.
sed -e 's|^static const char \*ROOT = "/sb";|static const char *ROOT = "";|' \
    -e '/"mkdir")) {/,/^#endif/ s|fprintf(out, "unsupported\\n");|if (mkdir(mapp(\&t[1]), 0777) < 0) ret_err(); else fprintf(out, "none\\n");|' \
    -e '/"rmdir")) {/,/^#endif/ s|fprintf(out, "unsupported\\n");|if (rmdir(mapp(\&t[1])) < 0) ret_err(); else fprintf(out, "none\\n");|' \
    tcb/validation/driver.c > "$O/driver-htif.c"
[ "$(diff tcb/validation/driver.c "$O/driver-htif.c" | grep -c '^>')" = 3 ] || { echo "driver patch failed"; exit 1; }
sed -i 's|"../../c/src/htif.c"|"'"$(pwd)"'/c/src/htif.c"|' "$O/driver-htif.c"
gcc -O1 -w -DMEMFS -include experiments/os/htif_shim.h -o "$O/driver-htif" "$O/driver-htif.c"
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
