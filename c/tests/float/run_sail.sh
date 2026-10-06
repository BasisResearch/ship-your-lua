#!/bin/bash
# Run one Lua program on the bare-metal ELF under the Sail Lean emulator and
# print its console output (the HTIF noise lines removed).
#   c/tests/float/run_sail.sh c/tests/float/nan_probe.lua
set -eu
abs=$(realpath "$1")
cd "$(dirname "$0")/../.."
src=$(realpath --relative-to=. "$abs")
n=$(basename "$src" .lua)
EMU=${EMU:-$(pwd)/../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
mkdir -p build/float
make -s host >/dev/null
make -s riscv-htif CHUNK_SRC="$src" CHUNK=build/float/$n.luac ELF=build/float/$n.elf >/dev/null
"$EMU" build/float/$n.elf 2>/dev/null \
  | grep -vE '^(TODO: cancel_reservation|PC = 0x|htif_tohost = 0x|SUCCESS$|FAILURE|lua: )'
