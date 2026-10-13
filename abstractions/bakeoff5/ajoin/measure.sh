#!/usr/bin/env bash
# Round 5 bake-off, A-JOIN: user CPU and peak RSS of a single-file compile
# (`lake env lean`, imports prebuilt) of each new or changed module, one at a
# time under a 12 GB cap, each started only with >= 25 GB available; then the
# per-declaration heartbeats of the arms (`Measure.lean`).
#   bash abstractions/bakeoff5/ajoin/measure.sh > abstractions/bakeoff5/ajoin/measure.out
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
cd "$root"
tmp="$here/.cpu"
mkdir -p "$tmp"
for f in Lua/Vm/Sim/Kit/AtJoinRow.lean Lua/Vm/Sim/Kit/AtJoin.lean \
         Lua/Vm/At/Forloop.lean Lua/Vm/At/Sub.lean Lua/Vm/At/ForprepF.lean Lua/Vm/At/LtF.lean \
         Lua/Vm/Sim/Kit/AtFltForloop.lean Lua/Vm/Sim/Kit/AtFltSub.lean \
         Lua/Vm/Sim/Kit/AtFltForprep.lean Lua/Vm/Sim/Kit/AtFltLt.lean; do
  until [ "$(grep 'Mem:' ~/syi-mem.log | tail -1 | awk '{print $NF}')" -ge 25 ]; do sleep 10; done
  out="$tmp/$(echo "$f" | tr / _).out"
  /usr/bin/time -f "USER %U s  WALL %e s  PEAK %M KB" \
    systemd-run --user --scope -p MemoryMax=12G -q lake env lean "$f" > "$out" 2>&1
  echo -e "$f\t$(grep -c '' "$f") lines\t$(grep -E '^USER' "$out")\terrors $(grep -c 'error' "$out")"
done
until [ "$(grep 'Mem:' ~/syi-mem.log | tail -1 | awk '{print $NF}')" -ge 25 ]; do sleep 10; done
systemd-run --user --scope -p MemoryMax=12G -q lake env lean "$here/Measure.lean" 2>&1 | grep "HB"
