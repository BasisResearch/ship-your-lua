#!/bin/bash
# L-C4 / L-C6: trace every program (lc4_trace.py), then run the real Lean
# `step?` over the decoded dispatch-head states (LC4Check.lean.in).
#   abstractions/checks/round3/lc4_run.sh [prog ...]
# Lean runs in the MAIN checkout's built environment (SYL_MAIN, default
# ~/Documents/code/ship-your-lua; same commit), under a 30 GB memory cap.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
MAIN=${SYL_MAIN:-$HOME/Documents/code/ship-your-lua}
WORK=${WORK:-$HERE/lc4_work}
progs=("$@")
[ ${#progs[@]} -eq 0 ] && progs=(while f1_ops f1b_bits print_print f1_src f4_strlite \
  difftest/f1_arith difftest/f1_cond difftest/f1_for difftest/f1_while)
python3 "$HERE/lc4_trace.py" --work "$WORK" "${progs[@]}" | tee "$WORK/trace.out"
: > "$WORK/lean.out"
for p in "${progs[@]}"; do
  s=${p#difftest/}
  f=$WORK/LC4_$s.lean
  { echo "import Lua.Vm.Host"; echo "import Lua.Fragment"; echo "import Lua.Bytecode.Exec"
    cat "$WORK/$s.proto.lean"; cat "$HERE/LC4Check.lean.in"
    echo "#eval LC4.main Lua.Programs.lc4Proto \"$WORK/$s.heads\""; } > "$f"
  echo "== $s" | tee -a "$WORK/lean.out"
  (cd "$MAIN" && systemd-run --user --scope -q -p MemoryMax=30G lake env lean "$f") 2>&1 | tee -a "$WORK/lean.out"
done
# beyond F1: f4_strlite past its first non-F1 instruction (the F4-lite kernels)
if [ -f "$WORK/f4_strlite.heads" ]; then
  f=$WORK/LC4_f4_strlite_all.lean
  sed 's/#eval LC4.main Lua.Programs.lc4Proto \(.*\)$/#eval LC4.main Lua.Programs.lc4Proto \1 false/' "$WORK/LC4_f4_strlite.lean" > "$f"
  echo "== f4_strlite (not stopping at non-F1)" | tee -a "$WORK/lean.out"
  (cd "$MAIN" && systemd-run --user --scope -q -p MemoryMax=30G lake env lean "$f") 2>&1 | tee -a "$WORK/lean.out"
fi
