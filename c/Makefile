# Lua 5.4.7 for bare-metal RV64 (HTIF), and a host lua/luac from the same
# vendored source.
#
#   make            host ./lua and ./luac, then ./lua-riscv-htif.elf
#   make host       host ./lua and ./luac only
#   make riscv-htif [CHUNK_SRC=tests/while.lua]  cross-compile the ELF with
#                   the luac-compiled chunk embedded (chunk.S)
#   make run        run the ELF on the Sail Lean emulator (EMU=...)
#   make difftest   native lua vs the ELF on tests/difftest/*.lua
#   make clean

LUA_DIR  := ../vendor/lua-5.4.7/src
CC       ?= cc
# The host build force-includes the same baremetal.h (fixed hash seed), so
# `next` order agrees with the ELF's and difftests can compare pairs().
HOST_CFLAGS ?= -std=gnu99 -O2 -Wall -DLUA_USE_POSIX -include src/baremetal.h

# Cross toolchain: the xPack riscv-none-elf-gcc 15.2.0 (GCC 15.2.0 +
# newlib 4.5.0.20241231), the same release that built
# ship-your-interpreter's proof ELF.
XPACK_GCC    := $(firstword $(wildcard $(HOME)/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin/riscv-none-elf-gcc))
RISCV_CC     ?= $(if $(XPACK_GCC),$(XPACK_GCC),riscv-none-elf-gcc)
# Same ISA/ABI/code model as the WHILE HTIF build: plain rv64i (the Lean
# emulator's model has no M/F/D; mul/div and doubles come from libgcc's soft
# routines), lp64, medany. LUA_USE_JUMPTABLE=0: luaV_execute dispatches
# through one C switch (one shared fetch/dispatch site) instead of
# computed gotos duplicated into every opcode arm.
RISCV_CFLAGS ?= -std=gnu11 -O2 -Wall -march=rv64i -mabi=lp64 \
                -mcmodel=medany -DLUA_HTIF -DLUA_USE_JUMPTABLE=0 \
                -include src/baremetal.h -I$(LUA_DIR)

CHUNK_SRC ?= tests/while.lua
CHUNK     := build/chunk.luac
ELF       ?= lua-riscv-htif.elf
EMU       ?= ../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator

CORE := lapi lcode lctype ldebug ldo ldump lfunc lgc llex lmem lobject \
        lopcodes lparser lstate lstring ltable ltm lundump lvm lzio
LIBS := lauxlib lbaselib lstrlib ltablib lcorolib liolib loslib
TARGET_SRC := $(patsubst %,$(LUA_DIR)/%.c,$(CORE) $(LIBS))
HOST_ALL   := $(CORE) $(LIBS) ldblib lmathlib loadlib \
              lutf8lib linit
HOST_SRC   := $(patsubst %,$(LUA_DIR)/%.c,$(HOST_ALL))

all: host riscv-htif

host: lua luac

lua: $(HOST_SRC) $(LUA_DIR)/lua.c src/baremetal.h
	$(CC) $(HOST_CFLAGS) -o $@ $(filter %.c,$^) -lm

luac: $(HOST_SRC) $(LUA_DIR)/luac.c src/baremetal.h
	$(CC) $(HOST_CFLAGS) -o $@ $(filter %.c,$^) -lm

# -s: strip debug info (smaller chunk, no line info in the undumped Proto)
$(CHUNK): $(CHUNK_SRC) luac
	@mkdir -p build
	./luac -s -o $@ $(CHUNK_SRC)

riscv-htif: $(ELF)

$(ELF): $(TARGET_SRC) src/main.c src/crt0.S src/htif.c src/chunk.S src/link.ld src/baremetal.h $(CHUNK)
	$(RISCV_CC) $(RISCV_CFLAGS) -DCHUNK_PATH='"$(CHUNK)"' \
	    -nostartfiles -T src/link.ld -o $@ \
	    src/crt0.S src/htif.c src/chunk.S src/main.c $(TARGET_SRC) -lm

run: $(ELF)
	$(EMU) $(ELF)

difftest: host
	./tests/difftest.sh

clean:
	rm -rf build lua luac lua-riscv-htif.elf

.PHONY: all host riscv-htif run difftest clean
