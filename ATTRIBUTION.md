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
| `Vsa/` (663 modules) | `Vsa/` | none, except the rows below; `Vsa.lean` imports only the copied modules |
| `Vsa/Sim/InitValues.lean` | same | `tohostAddr` is the Lua ELF's `0x80048400` (was the WHILE ELF's `0x8001ad00`); `Lua.Vm.tohostAddr_eq_symTohost` ties it to the generated layout |
| `Vsa/Sim/{Hooks,MemLoad,RamReadData,MemcpySpec}.lean` | same | the literal `tohost` bounds in their proofs follow `tohostAddr`; the `maxHeartbeats`/`maxRecDepth` raises are dropped (the proofs build without them) |
| `VsaIris/` (19 modules) | `VsaIris/` | none; `VsaIris.lean` likewise |
| `scripts/syi/` | `scripts/` | none (generators, checks, boot-witness generator, difftest library) |
| `experiments/syi/` | `experiments/` | none (`gen_decode_table.py`, `gen_code_lemmas.py`, `disasm_census.py`, `disasm_reachable.py`) |
| `c/src/crt0.S`, `c/src/htif.c`, `c/src/link.ld` | `c/src/` | `WHILE_HTIF` → `LUA_HTIF`; link.ld adds the `.lua_chunk` region |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | same | new package name, new `Lua` library |
| `CLAUDE.md` (the discipline) | `CLAUDE.md` | rows for WHILE-specific abstractions dropped; availability column added |
| `Lua/Refinement.lean` | `Vsa/Refinement.lean` | generalised over the specification |

**What "copied" covers.** The 682 copied Lean modules are the import closure
of these roots:

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

## Third party

* **Lua 5.4.7** (`vendor/lua-5.4.7/`): Lua.org, PUC-Rio, MIT licence
  (`vendor/lua-5.4.7/LICENSE`). Vendored unmodified.
* **Sail RISC-V model** (`riscv-lean/Lean_RV64D*`, `riscv-lean/lean_emulator`):
  BSD-2-Clause (`riscv-lean/LICENCE-sail-riscv`).
* **lean-sail** (`riscv-lean/lean-sail/`): rems-project/lean-sail at
  `0794631`, patched by ship-your-interpreter.
* **Lean dependencies** (`iris-lean`, `batteries`, `Qq`, `ELFSage`, `Cli`):
  fetched by Lake under their own licences.
