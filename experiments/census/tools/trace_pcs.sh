#!/bin/bash
# usage: trace_pcs.sh ELF OUTPREFIX
#   -> OUTPREFIX.pcs.tsv  rows: pc  count  count_before_luaV_execute_entry  count_after
#   -> OUTPREFIX.meta     steps / last step index / step of first luaV_execute entry
# EMU (default: the repository's riscv-lean/lean_emulator build), NM default xPack riscv-none-elf-nm.
elf=$1; out=$2
EMU=${EMU:-$(cd "$(dirname "$0")/../../.." && pwd)/riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
NM=${NM:-$HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-nm}
entry=$($NM "$elf" | awk '$3=="luaV_execute"{sub(/^0+/,"",$1); print $1}')
"$EMU" "$elf" --trace-all --max-steps 20000000 2>&1 >"$out.stdout" | awk -F'\t' -v E="$entry" -v OUT="$out" '
$1=="T"{ n++; if($3==E && !ent){ent=1; entstep=$2}
  if(ent) a[$3]++; else b[$3]++; last=$2 }
END{ for(p in b) seen[p]=1; for(p in a) seen[p]=1;
  for(p in seen) print p"\t"(a[p]+b[p])"\t"(b[p]+0)"\t"(a[p]+0) > (OUT ".pcs.tsv");
  print "steps\t"n"\tlast\t"last"\tluaV_execute_entry_step\t"entstep"\tentry_pc\t"E > (OUT ".meta") }'
