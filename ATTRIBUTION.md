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
| `Vsa/` (663 modules at first copy) | `Vsa/` | none, except the rows below; `Vsa.lean` imports only the copied modules |
| `Vsa/Sim/InitValues.lean` | same | `tohostAddr` is the Lua ELF's `0x80048400` (was the WHILE ELF's `0x8001ad00`); `Lua.Vm.tohostAddr_eq_symTohost` ties it to the generated layout |
| `Vsa/Sim/{Hooks,MemLoad,RamReadData,MemcpySpec}.lean` | same | the literal `tohost` bounds in their proofs follow `tohostAddr`; the `maxHeartbeats`/`maxRecDepth` raises are dropped (the proofs build without them) |
| `Vsa/Sim/{SegToTripleFramed,BridgeSegFull,FrameMeta,SegEval,SegEvalSound,BlockMem,BlockTerm,BlockDecode,BlockTactics,ChainFactsTac,ExecLoadTotal,NegBlockProto,NegTailSites}.lean`, `Vsa/Sim/Code/{Eval_expr,Memmove}.lean` | same | none (the segment layer, PHASES A0.2a) |
| `Vsa/Sim/{DeriveCase,DeriveCaseRow,BridgeSeg,WriteLogNF,FrameOn,Mfr,CodeRangeInsert,ObsAvoid,BlockTactics2,BlockTermDemo}.lean` | same | import lines only: the WHILE-reaching imports are replaced by `Vsa/Sim/Generic/*` (below); heartbeat raises dropped; `ObsAvoid`/`BlockTermDemo` destructure their conjunction hypotheses with `obtain` instead of `.2.2.2.2…` projections |
| `Vsa/Sim/Generic/{Abi,MapReads,ObsOther,BvArith,Pins}.lean` (new) | declarations of `Vsa/Alloc.lean`, `Vsa/Sim/{InterpEntry,ValueSpec,ValueTruthySpec,EnvNewSpec,StrlenSpec,SnprintfSpec5,SnprintfSpec18,SnprintfSpec19,SnprintfSpec25}.lean` | the WHILE-free declarations the segment layer uses, copied verbatim (same names) out of modules that import the WHILE representation; `Pin8_frame` destructures instead of projecting |
| `VsaIris/Vsa/{SymRun,Instance,Tools,AllocRun,AllocCode}.lean`, `VsaIris/Vsa/AllocSteps/Part{01,03,04,05,06,07,09,11}.lean`, `Vsa/Sim/{StepCount,BridgeSegFramed,EnvNewSites}.lean`, `Vsa/Sim/rows/DriveSpillGen.lean`, `Vsa/Sim/Code/{Env_new,Exec_stmt}.lean` | same | none (the allocator Iris route, PHASES A0.2b; the step tables are at WHILE addresses) |
| `VsaIris/Vsa/RunBase.lean`, `Vsa/Sim/{ExecRetEpilogue,InterpSpillReads,SegEffect}.lean` | same | import lines only, as above |
| `Vsa/Sim/Generic/{MemRead,GRegs}.lean`, `VsaIris/Vsa/Generic/FastWords.lean` (new) | declarations of `Vsa/MemRepr.lean` (`Mem`, `readLE`, `read64`), `Vsa/Sim/{ValueSpec,ValueTruthySpec,ReprSurvival,EnvGetSpec3,SegFrameFactsAuto,SegReadback}.lean`, `VsaIris/Vsa/MallocFastSegs.lean` | copied verbatim, same names; the `Vsa.MemRepr` module itself is not copied |
| `VsaIris/Vsa/AllocStepsTohost.lean` (new) | — | why `AllocSteps/Part{00,02,08,10}.lean` are not copied (machine-checked) |
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
