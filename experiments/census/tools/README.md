Lua-vs-WHILE disassembly census tools. Rerun everything from the census directory
(the parent of tools/) with `tools/run_all.sh`. Requirements: python3, xPack riscv-none-elf
binutils, and the lean_riscv_emulator; no Lean or lake. Overrides: LUA_ELF,
DIFFTEST_DIR, SYI, LUA_SRC, OBJDUMP/TC, EMU, JOBS. See ../CENSUS.md for what each
output means.
