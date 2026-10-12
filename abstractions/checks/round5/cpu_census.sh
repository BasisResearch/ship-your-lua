#!/usr/bin/env bash
# Round 5 census, the CPU axis: user CPU and peak RSS of a single-file
# compile (`lake env lean`, imports prebuilt) of each float-arm module, its
# generated at-lemmas, and the soft-float summaries small enough to rerun.
# One file at a time, each under run_lean.sh's 8 GB cap and 25 GB check.
#   bash abstractions/checks/round5/cpu_census.sh > abstractions/checks/round5/cpu_census.out
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
tmp="$here/.cpu"
mkdir -p "$tmp"
for f in Lua/Vm/Sim/Kit/AtFltLoadf.lean Lua/Vm/Sim/Kit/AtFltLti.lean Lua/Vm/Sim/Kit/AtFltEqi.lean \
         Lua/Vm/Sim/Kit/AtFltGei.lean Lua/Vm/Sim/Kit/AtFltAddi.lean Lua/Vm/Sim/Kit/AtFltForloop.lean \
         Lua/Vm/Sim/Kit/AtFlt.lean Lua/Vm/Sim/Kit/FltVal.lean \
         Lua/Vm/At/Loadf.lean Lua/Vm/At/Lti.lean Lua/Vm/At/Gei.lean Lua/Vm/At/Addi.lean Lua/Vm/At/Forloop.lean \
         Lua/Vm/Fn/Floatsidf.lean Lua/Vm/Fn/Fixdfdi.lean Lua/Vm/Fn/Eqdf2.lean Lua/Vm/Fn/Ledf2.lean \
         Lua/Vm/Fn/Floatdidf.lean Lua/Vm/Fn/Adddf3/Defs.lean; do
  out="$tmp/$(echo "$f" | tr / _).out"
  bash "$here/run_lean.sh" "$f" "$out"
  echo -e "$f\t$(grep -c '' "$root/$f") lines\t$(grep -E '^USER' "$out")\t$(tail -1 "$out")"
done
