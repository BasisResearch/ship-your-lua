# Attribution

This repository reuses the language-agnostic machinery of
[ship-your-interpreter](https://github.com/BasisResearch/ship-your-interpreter)
(BasisResearch), copied at commit `46b1eb8e`. Both projects are Basis
Research's. ship-your-interpreter carries no licence file; this repository
keeps that consistent and adds none of its own. Third-party components keep
their own licences, listed below.

## Copied from ship-your-interpreter

| here | there | changes |
|---|---|---|
| `riscv-lean/` | `riscv-lean/` | none (added `README.md`, `LICENCE-sail-riscv`) |
| `Vsa/` (663 modules) | `Vsa/` | none; `Vsa.lean` imports only the copied modules |
| `VsaIris/` (19 modules) | `VsaIris/` | none; `VsaIris.lean` likewise |
| `Vsa/Meta/SimpNF.lean`, `Vsa/Sim/DecodeNF.lean` | same (branch `exponentiate`, uncommitted there at `182e80d1`) | none: the generic decoder `#simp_nf` / `Vsa.Sim.decodeW` |
| `scripts/syi/` | `scripts/` | none (generators, checks, boot-witness generator, difftest library), except the two below |
| `scripts/syi/disasm_to_sites.py` | `scripts/disasm_to_sites.py` | classifies the classes the `luaV_execute` arms need (`andi`/`ori`/`xori`/`slti`/`sltiu`, the immediate and register shifts, `and`/`or`/`xor`/`slt`/`sltu`, `addw`/`sllw`/`srlw`/`sraw`, `lui`/`auipc`, `lb`/`lh`/`lhu`/`lwu`, `sh`, general `jalr`); defaults to the Lua ELF and the xPack objdump; `ROOT` is the repository root |
| `scripts/syi/disasm_to_segment.py` | `scripts/disasm_to_segment.py` | fails on `#UNSUPPORTED` rows and on addresses without a row instead of dropping them (`--allow-unsupported` drafts explicit `UNSUPPORTED` steps); drafts the new classes, marking steps gen_sites.py/gen_segment.py cannot emit with a blocking `TODO`; `--from-elf` |
| `experiments/syi/` | `experiments/` | none (`gen_decode_table.py`, `gen_code_lemmas.py`, `disasm_census.py`, `disasm_reachable.py`) |
| `scripts/gen_lua_code.py` | `experiments/gen_code_lemmas.py`, `scripts/gen_fixed_image.py --projection` | retargeted to the Lua ELF and `Lua/Vm/Image.lean`; a function over 16 chunks is split into parts of the original shape |
| `scripts/lua_decode_ast_dump.lean` | `experiments/M2_decode_ast_dump.lean` | ELF and word list as arguments |
| `c/src/crt0.S`, `c/src/htif.c`, `c/src/link.ld` | `c/src/` | `WHILE_HTIF` → `LUA_HTIF`; link.ld adds the `.lua_chunk` region |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | same | new package name, new `Lua` library |
| `CLAUDE.md` (the discipline) | `CLAUDE.md` | rows for WHILE-specific abstractions dropped; availability column added |
| `Lua/Refinement.lean` | `Vsa/Refinement.lean` | generalised over the specification |

**What "copied" covers.** The 682 copied Lean modules are the import closure
of these roots (plus the two later copies `Vsa.Meta.SimpNF`, `Vsa.Sim.DecodeNF`):

* the machine relation (`Vsa.Machine`, `Vsa.Elf`, `Vsa.Triple`);
* densification (`Vsa.Densify.*`);
* the instruction-level simulation layer (`Vsa.Sim.{Decode,Fetch,Execute*,Step*,MemLoad*,RamRead*,RegAccess,GoodState,Htif*,Pmp,FnSummary,DeriveLoop,DeriveCallSeg,TripleCat,…}`);
* the decode table (`Vsa.Sim.DecodeTable.*`);
* the libgcc/newlib site proofs (`Muldi3*`, `Div*`, `Memcpy*`, `Strlen*`,
  `Strcmp*`, `Strcpy*`, `Snprintf*`, `Ssprint*`, `Ssputs*`);
* the Iris machine logic (`VsaIris.{Machine,MachWP,Step,Ptsto,PartialWP,Adequacy,Lag,Loop,Call,CallAbort,Stack,LocalRun,LocalRunO,DlHeap,MallocRun,MallocChg}`).

**What was left out.** The closure contains none of ship-your-interpreter's
WHILE semantics or representation (`Vsa.While.*`, `Vsa.MemRepr*`,
`Vsa.RuntimeRepr`, `Vsa.ElfBytes`). `experiments/port/port_census.py
--copyset` checks this, and `scripts/check.sh` runs it. The closure does
include code pins of a few WHILE interpreter functions (`Vsa.Sim.Code.Value_*`),
because the site proofs import them. Those are byte facts about the WHILE
ELF, not WHILE semantics.

**Proof instances are about the WHILE ELF.** The copied proofs (decode
lemmas aside, which are per instruction word) are about the WHILE ELF's
addresses. PHASES.md A0 retargets them to the Lua ELF.

## Copied from ship-your-ocaml

[ship-your-ocaml](https://github.com/BasisResearch/ship-your-ocaml)
(BasisResearch), at commit `b6ffcf9`.

| here | there | changes |
|---|---|---|
| `tcb/` (Lean library `TCB`, `tcbcheck`, `Audit.lean`, `validation/`, `upstream/`, `LICENSE-*`) | `tcb/` | `b6ffcf9` plus ship-your-ocaml's diff of `tcb/` from `main` to branch `f5-htif` at `39e79b2` (spec DEVIATION 10 in `osReaddir`; `driver.c`'s MEMFS back end calls `mkdir`/`rmdir` and passes paths unchanged; RESULTS.md), so `tcb/` equals ship-your-ocaml's at `39e79b2`. Its `README.md` and `validation/RESULTS.md` describe ship-your-ocaml (its theorems, its `htif.c`); this repository's results are in `experiments/os/RESULTS.md` |
| `lakefile.toml`: the `TCB` library and `tcbcheck` executable | same | none |
| `Lua/Os/HtifFs.lean` | `OCaml/Os.lean` (the part over `Vsa.Machine` + `TCB`) | namespace `Lua.Os`; `retOf` takes the entry configuration too; `OsSpecial` calls allowed (the file's header says why) |

`experiments/os/htif_shim.h` and `experiments/os/run.sh` are new: they run
the copied `tcb/validation/driver.c` against this repository's `htif.c`.

`c/src/htif.c`'s in-image file system was written here and adopted by
ship-your-ocaml (`f5-htif` `39e79b2`, its OCaml-only parts marked `OCAML`);
the shared parts are kept identical in both.

`tcb/` contains third-party material, under its own licences:

* **SibylFS** (`tcb/upstream/sibylfs/`, ported in `tcb/TCB/Os/Fs.lean`,
  `Syscall.lean`): `sibylfs/sibylfs_src` at `30675bc3`, ISC licence
  (`tcb/LICENSE-sibylfs`).
* **CakeML** basis FFI model (`tcb/upstream/cakeml/fsFFIScript.sml`, ported in
  `tcb/TCB/Os/Streams.lean`): `CakeML/cakeml` at `530c7dee`, BSD-3-Clause
  (`tcb/LICENSE-cakeml`).

## Third party

* **Lua 5.4.7** (`vendor/lua-5.4.7/`): Lua.org, PUC-Rio, MIT licence
  (`vendor/lua-5.4.7/LICENSE`). Vendored unmodified.
* **Sail RISC-V model** (`riscv-lean/Lean_RV64D*`, `riscv-lean/lean_emulator`):
  BSD-2-Clause (`riscv-lean/LICENCE-sail-riscv`).
* **lean-sail** (`riscv-lean/lean-sail/`): rems-project/lean-sail at
  `0794631`, patched by ship-your-interpreter.
* **Lean dependencies** (`iris-lean`, `batteries`, `Qq`, `ELFSage`, `Cli`):
  fetched by Lake under their own licences.
