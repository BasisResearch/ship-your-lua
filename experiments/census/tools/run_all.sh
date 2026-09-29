#!/bin/bash
# Re-run the whole Lua-vs-WHILE disassembly census from scratch.
#   cd <census dir> && tools/run_all.sh
# Env overrides: LUA_ELF, DIFFTEST_DIR, SYI (read-only syi checkout), LUA_SRC, OBJDUMP, EMU, JOBS.
set -euo pipefail
cd "$(dirname "$0")/.."
T=${TC:-$HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf}
OBJDUMP=${OBJDUMP:-$T-objdump}
export LUA_ELF=${LUA_ELF:-$(cd "$(dirname "$0")/../../.." && pwd)/c/lua-riscv-htif.elf}
DIFFTEST_DIR=${DIFFTEST_DIR:-$(dirname "$LUA_ELF")/build/difftest}
export SYI=${SYI:-$HOME/Documents/code/syi}
# 1. disassembly (same flags as syi experiments/disasm.txt: plain objdump -d)
"$OBJDUMP" -d "$LUA_ELF" > lua_disasm.txt
"$OBJDUMP" -d "$SYI/c/while-riscv-htif.elf" > while_disasm.txt
# 2. census (syi disasm_census.py, output path from argv)
python3 tools/disasm_census.py lua_disasm.txt lua_census.json > lua_census.out
python3 tools/disasm_census.py while_disasm.txt while_census.json > while_census.out
# 3. static reachability (jump tables + address-flow closure for indirect calls)
python3 tools/reach.py lua_disasm.txt "$LUA_ELF" _start lua_reach.json
python3 tools/reach.py while_disasm.txt "$SYI/c/while-riscv-htif.elf" _start while_reach.json
# 4. traces -> unique PCs (streamed; ~100 KB per ELF)
mkdir -p traces; rm -f traces/*
( echo "$LUA_ELF"; ls "$DIFFTEST_DIR"/*.elf ) | xargs -P "${JOBS:-9}" -I{} sh -c 'tools/trace_pcs.sh "$1" "traces/$(basename "$1" .elf)"' _ {}
rm -f traces/*.stdout
python3 tools/dyn.py > dyn.out
# 5. template match, luaV_execute arms, construct counts, derived tables
python3 tools/match.py > match.out
python3 tools/arms.py > arms.out
python3 tools/constructs.py > constructs.tsv
python3 tools/tables.py
