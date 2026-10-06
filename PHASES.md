# Phases

The goal is `endToEnd_lua`: for every supported Lua chunk `s` and the
bare-metal ELF running its compiled `Proto`, the machine halts cleanly
printing `out` iff `LuaSem s out`. We get there compositionally:

```
LuaSem s out  ↔  BcSem (compile s) out  ↔  Halts c out 0
   Layer B: compile_refinement      Layer A: vm_refinement
```

This file is the plan and the obligation ledger. The three headline
statements are `def …_Statement : Prop`s in `Lua/Theorems.lean`. None is an
axiom or a `sorry`. Their compositions are proved:

* `vm_refinement_of_sim` gives Layer A from `VmSim`;
* `compile_refinement_of_tv` gives Layer B from `CompileTV`;
* `endToEnd_of_layers` and `endToEnd_of_obligations` give the composition.

## Obligations

Every row is currently unassigned.

| statement / obligation | file | discharged in | status |
|---|---|---|---|
| `VmLayout.runtimeReady` concrete instance `luaLayout` | `Lua/Vm/Runtime.lean` | A0 | **defined** (`luaRuntimeReady`); every field holds at both traced entries (checked natively by `gen_lua_boot_witness.py`) |
| `VmLoaded luaLayout p (fillZero c)` at real entry states (boot witness) | `Lua/Vm/Boot/` | A0 | **proved** for `while.lua` and `f1_ops.lua` (`vmLoaded_while_entry`, `vmLoaded_f1Ops_entry`, `Lua/Vm/Boot/Witness/`), for every state with the traced registers (`EntryRegs`) and the boot memory; the register file itself is a hypothesis (A0.6) |
| `VmSim luaLayout` (F1: `term_sim`, `stuck_sim`) | `Lua/Vm/Sim/` | A1 | open, **reduced to named premises**: `vm_refinement_of_open : OpenArms → FinalSim → StuckSim → vm_refinement_Statement luaLayout` (`Lua/Vm/Sim/Fold.lean`, lane F1-3). Discharged inside it: the entry (`entrySim`), `VARARGPREP` (`Kit.varargSim`) and the 34 proved arms (`armTable`: the 25 generated `sim_<OP>`, `Kit.sim_{MUL,MULK,MOD,LOADNIL,EQ,LT}`, `At.sim_{MODK,IDIV,FORPREP}`). Left: the 18 fields of `OpenArms` (GETTABUP, SHL, SHR, SHRI, SHLI, IDIVK, BANDK, BORK, BXORK, MMBIN, MMBINI, MMBINK, UNM, LEN, CONCAT, CALL, and the open paths of EQK (two long strings) and LE (two strings)), `FinalSim` and `StuckSim` (rows below) |
| `vmRel_final_Statement` / `FinalSim` (the `RETURN*` arms: from `VmRel` at a reachable `Final` state the machine halts with code 0 and console `s.out`) | `Lua/Vm/Sim/Rel.lean`, `Lua/Vm/Sim/Fold.lean` | A1 | open, **not provable from `VmRel` as it stands**: the return runs `luaV_execute`'s epilogue (`ld ra,168(sp)`, `ld s0…s11`), but `VmRel` leaves its C frame free (it is in `Win`), and its `Complement` states nothing about the caller frames above `sp` (`CStackAt.callers` at the entry) that `ccall`, `luaD_rawrunprotected`, `lua_pcallk` and `main` return through; then newlib `exit` (`__call_exitprocs`, the stdio cleanup) and `_exit`'s `tohost` store. Needed first: `Core` keeping the 13 saved words of the C frame (no arm writes `72…175(sp)`; only the prologue does) and `Complement` keeping `RuntimeData.callerFrames`; then summaries of `luaF_close` (no open upvalues, `tbclist` below `base`), `luaD_poscall` (`wanted = 0`), the C returns and `exit` (A1 bullet) |
| `vmRel_entry_Statement` (the prologue run from `VmLoaded luaLayout` to `VmRel … State.init`) | `Lua/Vm/Sim/Rel.lean` | A1 | **proved** (`vmRel_entry`, `Lua/Vm/Sim/Entry.lean`) |
| `StuckSim` (`stuck_sim`'s error paths: from `VmRel` at a reachable state that is neither final nor stepping, the machine diverges or halts nonzero) | `Lua/Vm/Sim/Fold.lean` | A1 | open: `luaG_opinterror`/`luaG_forerror`/`luaG_typeerror`/`luaG_ordererror`/the `MMBIN*` miss/a non-`print` call → `luaD_throw` → `longjmp` (`ErrorJmpAt`) → `lua_pcallk` → `main` returns 2 → `exit` |
| `sim_{MOD,MODK,IDIV,IDIVK,EQ,EQK}_Statement` (`SimArm o`, `sim_ADD`'s shape; the round-3 bake-off targets) | `Lua/Vm/Sim/Rel.lean` | A1 | `sim_MOD_Statement` proved on the KIT branch (`Lua.Vm.Sim.Kit.sim_MOD`, with `sim_MUL`); `sim_MODK_Statement` proved (`Kit.sim_MODK`, with `Kit.sim_MULK`; kit lane 1, `abstractions/ledger/kit-arms-1.md`); `sim_EQ_Statement` proved (`Kit.sim_EQ`: `Kit.eq_long` closes `Kit.sim_EQ_of_long` through `luaS_eqlngstr`/`memcmp` summaries on BASE-S's owned strings; round-4 S-SCAN, `abstractions/bakeoff4/S-SCAN.md`); `sim_EQK_Statement` proved (`At.sim_EQK`, `Lua/Vm/Sim/Kit/AtStr.lean`: `Kit.eqk_short`, and the two-long-string path on the location-list route through the call node `At.lngeq_sum` over `Kit.eqo_long_ex`, `luaV_equalobj`'s exact return memory; lane F1-2, `abstractions/ledger/f1-lane-2.md`); the others open |
| `SimArm .LT`, `SimArm .LE` on two strings (the premise of `Kit.sim_LT_of_str`, `Kit.sim_LE_of_str`; integers and the stuck cases proved: `lt_int`, `lt_stuck`, `le_int`, `le_stuck`) | `Lua/Vm/Sim/Kit/{Lt,Le,AtStr}.lean` | A1 | **proved** on the location-list route (`At.sim_LT`, `At.sim_LE`; lane F1-2): the call node `At.lstr_sum` (`Kit.lstrcmp_sum`, now with the observation `Kit.LsObs`: zero iff equal, a sign-extended answer, `LsObs.le` for `slti 1`) fused with its observing instruction (`At.obs_lt`, `At.obs_le`), `docondjump` in the generated at-lemmas (`Lua/Vm/At/{Lt,Le}.lean`); `lt_str_take` costs 14k heartbeats (the kit's 200.3k; the kit's `LtStr` is retired) |
| `SimArm .LEN` (a string `R[B]`; `δ .len` has no other F1 value) | `Lua/Vm/Sim/Kit/{Objlen,AtStr}.lean` | A1 | **proved** (`At.sim_LEN`; lane F1-2): `luaV_objlen`'s string summary `Kit.objlen_sum` (exact memory `olMem`), the call node `At.len_sum`, the arm's segments emitted apart (`gen_lua_arms.py` `EXTRA_ARMS`), `Lua/Vm/At/Len.lean` |
| `SimArm .GETTABUP` (`_ENV.print` only) | — | A1 | open, **obstruction** (lane F1-2, `abstractions/ledger/f1-lane-2.md`): (1) `VmEntryData.env_print_ptr` gives `TableHasShortKeyPtr` (some node of `_ENV` holds the key pointer), not that `luaH_getshortstr`'s walk from the key's main position `hash & (2^lsizenode - 1)` along `gnext` reaches that node past nodes with other keys; the boot check (`printPtrCheck`) and `VmEntryData` need that walk; (2) the relation holds no closure: the arm reads `cl` at `8(sp)` (`RelPtrs` and `Core` have no `cl`), `cl->upvals[0]->v` and the table header and nodes (not in `Complement`); (3) a `luaH_getshortstr` summary (`seg_loop` over the chain) |
| `SimArm .FORPREP` | — | A1 | open (lane KIT-2 stopped at the gate): `luaV_tointeger`'s integer summary `Kit.toint_sum` and the C-frame close `Core.bleachF` are proved; the arm's run (8 segments, two call nodes) exceeds the default heartbeat budget in one declaration and needs a split at the call with an abstract mid-state memory (`abstractions/ledger/kit-arms-2.md`) |
| `SimArm .IDIVK` (`sim_IDIVK_Statement`) | `Lua/Vm/Sim/Kit/AtIdivk.lean` | A1 | **proved** (`At.sim_IDIVK`, the at-lemma route; lane F1-1, `abstractions/ledger/f1-lane-1.md`) |
| `SimArm` of SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK | `Lua/Vm/Sim/Kit/At{Shl,Shr,Shli,Shri,Bandk,Bork,Bxork}.lean` | A1 | **proved** (`At.sim_SHL`, …, `At.sim_BXORK`; `luaV_shiftl` per machine branch in `Kit/Shift.lean`; lane F1-1) |
| `UnmStr_Statement` (`OP_UNM` on a string: `luaT_trybinTM` and the string library's `__unm`; the premise of `At.sim_UNM_of_str`) | `Lua/Vm/Sim/Kit/AtUnm.lean` | A1 (with the `MMBIN`/`CALL` runtime summaries) | open; the integer path (`At.unm_int`) and the stuck values (`At.unm_stuck`) proved |
| **`vm_refinement_Statement luaLayout`** | `Lua/Theorems.lean` | A1 (by `vm_refinement_of_sim`) | open |
| `CompileTV CorpusCompiles` (translation validation of the host `luac -s` on the corpus) | `Lua/Compile/Corpus.lean` | B1 | **proved** (`corpus_compileTV`) |
| `CompileTV (fun s p => compile s = some p)` for a Lean `compile` | new `Lua/Compile/` | B2 | open |
| the ELF's `lparser`/`lcode` refine `compile` | — | B3 | open |
| **`compile_refinement_Statement`** | `Lua/Theorems.lean` | B1/B2 (by `compile_refinement_of_tv`) | **proved for `CorpusCompiles`** (`compile_refinement_corpus`); open for B2's `compile` |
| **`endToEnd_lua_Statement luaLayout Compiles`** | `Lua/Theorems.lean` | E (by `endToEnd_of_layers`) | open |
| `HtifPrint_Statement`: `htif.c`'s `write` to fds 1-2, `read` from fd 0 and `fstat` of fds 0-2 implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open (traces accept it) |
| `HtifFs_Statement`: all twelve system-call functions implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open; plausibly true within `htif.c`'s resource limits (no trace rejected, `experiments/os/RESULTS.md`); needs a resource bound and the `OsState` frame obligation (OS bullet) |

## P0: validation and scaffold (done)

* **Result.** Recorded in `VALIDATION.md`:
  * The ELF runs on Sail, and 16 difftests pass.
  * The census is written up.
  * F1's `BcSem` reproduces the binary's output on three programs by kernel
    evaluation.
* **Scaffold.**
  * Bytecode syntax and decoding.
  * The F1 semantics.
  * The fragment predicate and ledger.
  * The VM representation skeleton and `VmLoaded`.
  * The Lua 5.4 source syntax and `LuaSem` for F1.
  * The statements.
* **Exit.** `scripts/check.sh` passes. That covers generator drift, the ELF
  hash, forbidden tokens, the copied layer being WHILE-free, `lake build`,
  and the axioms of 14 theorems.

## A0: retarget the machine layer to the Lua image

The copied layer (`Vsa/`, `VsaIris/`) is language-agnostic. Its proof
instances, however, are at the WHILE ELF's addresses.

1. **`tohost` (done).**
   * `Vsa.Sim.tohostAddr` (`Vsa/Sim/InitValues.lean`) is the Lua ELF's
     `tohost`. It is the only place the number is written: the copied proofs
     that used the WHILE literal go through `tohostAddr`, and
     `Lua.Vm.tohostAddr_eq_symTohost : Vsa.Sim.tohostAddr = Layout.symTohost`
     (`rfl`) fails the build when a regenerated ELF moves `tohost`.
   * Changing the value was cheaper than generalising: the whole copied layer
     rebuilt unchanged apart from four literal bounds.
   * `LuaGoodState` is retired; `MachineAt.good` and `Lua/Os/Htif.lean` use
     `Vsa.Sim.GoodState`.
2. **Cut the WHILE import edges (partly done).** `experiments/port/CUTS.txt`
   (`python3 experiments/port/port_census.py`) lists what is left.
   * **Method.** `experiments/port/term/` follows, over a built syi checkout,
     every constant a module set uses (theorem bodies included). The import
     edges into the WHILE layer mostly carried no WHILE constant. The generic
     declarations they did carry are copied verbatim, under their own names,
     into `Vsa/Sim/Generic/*` and `VsaIris/Vsa/Generic/*`. The importing
     modules get rewritten import lines. `port_census.py --copyset` follows
     this repository's import lines, and must stay WHILE-free and complete.
   * **Ported (here):**
     * the segment layer: `SegToTripleFramed` (`segRowFramed`), `DeriveCase`
       (`#derive_case`), `DeriveCaseRow`, `BridgeSeg`, `BridgeSegFull`,
       `BridgeSegFramed`, `FrameMeta`, `SegEffect`, `ExecRetEpilogue`,
       `InterpSpillReads`;
     * the dlmalloc Iris route: `VsaIris.Vsa.{SymRun,Instance,Tools,RunBase,AllocRun}`
       (its code bytes and step table are regenerated at Lua addresses, A0.5);
     * the output/exit machinery of the stdio route: `SymRunO` (`SWPO`),
       `SymObs`, `SymJalr`, `SymLeaf`, `SymBridge`, `SymData`, `SymHavoc`,
       `SymCompact`, `SegRun`, `AllocSltu`, `Console` (`TohostSite`,
       `putc_runFact`, `exit_haltFact`, `vsa_adequacy_exit`), `HtifStepObs`,
       and `Vsa.Sim.Generic.ExitStep`;
     * `SeparationLogic`, `MemPresence`.
   * **Not ported, with the obstruction:**
     * ship-your-interpreter's `_write`/`_exit` `TohostSite` instances: their
       stores miss the Lua mailbox (`VsaIris.Inst.whileSites_not_tohost`). The
       Lua ELF's sites are instantiated in A0.5.
     * `Stdout.*`, `Fprintf.*`, `ExitH.*` (the stdio chain). The step tables
       are WHILE-address instances, and they also need about 27 helper
       declarations and the `ITac`/`AllocTac` tactic layer. The top-level specs
       (`fwrite_out`, `fprintf_out`, …) are stated in the WHILE interpreter's
       Iris world (`VsaIris.Interp.Repr`: `InterpGS`, `Newlib.binImg`,
       `FrameReads`). Following constructors, the census reaches
       `Vsa.MemRepr.CString`, `Vsa.RuntimeRepr.NativeAddrs` and `Vsa.While.*`
       (`experiments/port/term/CtorRoots.lean`). Seventy constants over 24
       modules depend on the WHILE HTIF sites (`RevDeps.lean`). Porting means
       restating that world for Lua. It is done together with A0.5's
       regeneration.
     * `DlHeap`, `AllocLedger`: the ledger is the WHILE runtime's ownership
       (`RuntimeOwnership*`, `Vsa.While.{Ast,Semantics}`; 29 + 26 WHILE-root
       constants reached).
3. **Decode (done).** The generic decoder replaces per-word tables.
   * `Vsa.Sim.decodeW σ hmisa hpriv hsec : (ext_decode w).run σ = .ok i σ`
     (`Vsa/Sim/DecodeNF.lean`, from ship-your-interpreter's `#simp_nf`,
     `Vsa/Meta/SimpNF.lean`). The instruction `i` is found by an autoParam
     `rfl` for any concrete word, so no per-word lemma is generated.
   * Drop-in rule: `DecodeTable.decode_<hex> σ h1 h2 h3` becomes
     `Vsa.Sim.decodeW (w := 0x<hex>#32) σ h1 h2 h3`. A `DecodeFactM`/`DecodeFactT`
     leaf is `fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3`.
   * Coverage: `Lua/Vm/DecodeCheck/*` (`scripts/gen_lua_decode_check.py`)
     kernel-checks one `example` per unique word of `luaV_execute` (1,641
     words, 4,020 instructions), each stating the instruction the Lean
     evaluator decodes the word to. It builds in 13 modules of 128 words:
     6 s wall, 54 s CPU, about 1.7 GB per module. check.sh stage 1 checks drift.
4. **Code pins (done).** `scripts/gen_lua_code.py` emits `Lua/Vm/Code/*`
   (index module `Lua.Vm.Code`). It retargets `gen_code_lemmas.py` and
   `gen_fixed_image.py --projection`.
   * Functions: `luaV_execute`, the non-float callees of the F1 arms read from
     `experiments/census/luaV_execute_arms.tsv`, and `luaB_print`,
     `luaL_tolstring`, `fwrite` (`lua_writestring`) and `luaG_opinterror`.
     That is 25 functions. `__udivdi3` is pinned as `__hidden___udivdi3`,
     the same code.
   * Per function `F`: `<F>Loaded` and fetch lemmas `<f>_at_<addr>`, plus
     `textLoaded_<F>Loaded : FixedBytesLoaded textBase textSize textByte m →
     <F>Loaded m`. Each pinned byte is `h off (by decide)` against
     `Lua/Vm/Image.lean`.
   * `luaV_execute` (252 chunks) is split into 16 parts `LuaV_execute_p<k>Loaded`,
     each of the syi shape. Its fetch lemmas take the part, via
     `luaV_execute_part<k>`.
   * Build: 83 modules, 21 s wall, 5m47 CPU.
5. **Library proofs at Lua addresses.**
   * **Allocator step table (done).** `scripts/syi/gen_alloc_steps.py` reads
     the Lua ELF (`objdump`/`nm`; `gp` = `__global_pointer$`, which is
     `VsaIris.MallocFast.gpV` (`alloc_gp` ties the two), the
     `_impure_ptr` word). `FUNCS` is the call closure of `malloc`, `free`,
     `realloc`, `_malloc_r`, `_free_r`, `_realloc_r`: 15 functions, 1,366
     instructions, one `st_<pc>` each, in `VsaIris/Vsa/AllocSteps/Part{00..11}`
     (aggregator `VsaIris.Vsa.AllocSteps`) over `allocText`
     (`VsaIris/Vsa/AllocCode.lean`). The WHILE-address tables are gone. The
     dlmalloc globals lie at or above `tohost + 16` in the Lua ELF
     (`__malloc_av_` = `0x8005c6d0`), so every `StOK` closes by `decide`.
     Decode is `decodeW` (`jalx_<pc>`, and `chain_facts`' decode leaves). The
     one instruction outside `MKind`, `_realloc_r`'s `sltu a4,a5,a4`
     (`0x80030360`), goes through `AllocSltu.sltuAluStepAt` (any address).
     `check.sh` stage 1 checks drift (`--check`).
   * Regenerate the other reused functions' step tables and specs with the
     generators (`gen_str_steps.py`, `gen_memcpy_steps.py`, `gen_fn.py`).
   * They are identical code at new addresses: `__udivdi3` (`FORPREP`),
     `__moddi3`/`__divdi3` (`MOD`/`IDIV`), the stdio chain behind `print`,
     `setjmp`/`longjmp`.
6. **`luaLayout` (defined; kernel witness done).**
   * **`luaRuntimeReady`** (`Lua/Vm/Runtime.lean`) is `∃ w : RtPtrs,
     RuntimeReadyAt c L ci w`, eight named structures. Each field's doc
     comment names the callee that reads it:
     * `HarnessAt`: the platform loop's `tick < 2` and the empty console
       (read by A1's `vmRel_entry`);
     * `CStackAt`: `sp`, `ra` (into `ccall`, `retCcall_after_call`), `gp`, the
       saved registers `s0 … s11`, the caller frames' bytes above `sp`, and
       every RAM byte present (true of the zero fill);
     * `ErrorJmpAt`: `L->errorJmp`, `previous = NULL`, and the `jmp_buf`'s
       `ra`/`sp`/`s*` slots (`setjmpRet_after_call`);
     * `StdioBoot`: newlib before its lazy `__sinit` (`__stdio_exit_handler =
       NULL`, the `_reent` stream pointers, `__sglue`, the three `FILE`s zero);
     * `MemfsBoot`: htif.c before its lazy `fs_init` (`fs_ready = 0`, both
       tables zero);
     * `DlHeap.HeapAt` (`Lua/Vm/DlHeap.lean`): ship-your-interpreter's heap
       shape without the WHILE ledger fields;
     * `LuaStateAt`: `hookmask`, `trap`, `errfunc`, `nCcalls`, `openupval`,
       `tbclist`, the stack bounds, `ci->top`,
       `CIST_FRESH`, `nresults = 0`, `ci->previous`/`ci->next`, the `mt` of
       nil/booleans/numbers, the string table (`StrtAt`, chains by
       `StrChain`) and the string cache;
     * `VmRegionsAt`: `L`, `ci`, the Lua stack, the main closure, its `Proto`
       and code array lie in the heap `[_end, __heap_end)`, and `ci` and the
       code array lie apart from the Lua stack (read by `vmRel_entry`: the
       prologue's loads and `VmRel`'s `Ranges`). `RtPtrs` names the closure,
       the `Proto`, `code` and `sizecode`. `L`, `ci`, the code array and the
       constant array are pairwise apart (`L_sep_ci`, `code_sep_*`,
       `k_sep_*`: the scratch words miss them); `L` is apart from the Lua
       stack (`L_sep_stack`: `L->top`'s store misses every slot) and `L`, `ci`
       are 8-aligned (`L_al`, `ci_al`: `savestate`'s `sd`s);
     * `RuntimeReadyAt.top`: `L->top = func + 1`, an entry-only fact
       (`OP_VARARGPREP` → `luaT_adjustvarargs`), not a fetch-head invariant;
     * `RuntimeReadyAt.interned` (`KInterned`): the short-string constants
       are interned (`loadStringN` → `luaS_newlstr`), so `vmRel_entry` builds
       `VmRel`'s intern map `ι.ptr`;
     * `RuntimeReadyAt.kowned` (`KOwned`, round-4 BASE-S): every string
       constant's object (header, contents, terminator) lies in the user range
       of an in-use chunk of `HeapAt`'s walk, in the heap and apart from the
       Lua stack, `L` and `ci` (`StrChunkAt`). `vmRel_entry` turns it into
       `VmRel`'s `Complement.own` (`chunkOwns_of_strChunkAt`): every string a
       register or constant points to (`Strs.own`, carried by `ValRepr.str`)
       is owned by a chunk apart from `Win ∪ Scratch` (`StrOwned`,
       `Core.reg_owned`, `Core.k_owned`, `Core.str_frame`);
     * `TStringRepr.long` (round-4 BASE-S) carries `shrlen = 0xFF` (`+11`,
       `luaS_createlngstrobj`; `l_strcmp` branches on it at `0x8001a720`),
       checked by `tstrCheck` and the generator's `check_tstring`.
     * `RuntimeReadyAt.vararg` and `VmEntryData.vararg_room`/`vararg_proto`
       (lane F1-3): the runtime after `OP_VARARGPREP`'s stores
       (`varargMem`, `RtPtrs.vmoved`), the stack room `luaD_checkstack` needs,
       and the prototype apart from the `CallInfo` and the copied slot
       (`VarargDirty`); checked in the kernel only (`RtPostChecks` over
       `postView`, `entryCheck` over `View.minus`), not by the generator's
       native evaluation.
   * `luaLayout : VmLayout := ⟨luaRuntimeReady⟩`. The boot-invariant values it
     pins (entry `sp`/`ra`, the `jmp_buf`, the caller frames, the return
     chain, `nCcalls`) are `Lua/Vm/RuntimeData.lean`. The offsets are
     `Lua/Vm/LayoutRt.lean`, a second output of `gen_lua_layout.py`, which
     probes `struct lua_longjmp` by including ldo.c.
   * **Generator** `scripts/gen_lua_boot_witness.py` (from
     `scripts/syi/gen_boot_witness.py`):
     * It writes each program's chunk into the committed ELF's `.lua_chunk`
       region; the committed ELF is reproduced from `c/tests/while.luac`.
     * It traces to the first `luaV_execute` step, tracking the open call
       chain.
     * It rebuilds the entry memory: the PT_LOAD `p_filesz` bytes plus the
       store log.
     * It evaluates every field of `VmEntryData` and `luaRuntimeReady`, and
       requires the boot-invariant values to agree across programs. For
       `HarnessAt` it checks `plat_insns_per_tick ≤ 2` and that no boot store
       touches `tohost`.
     * It emits `RuntimeData.lean`, `Boot/ImageData.lean` and
       `Boot/Gen/{While,F1Ops}.lean`: the chunk region, the `PackedLog`, the
       `RunTree`, the registers and the witnesses `e`, `w`, `printSlot`, as
       data.
     * check.sh stage 1 runs `--check`, which re-traces (about 25 s).
     * Measured: `while.lua` enters at step 181,166 (18,137 stores);
       `f1_ops.lua` enters at step 181,079 (18,125 stores). Both have 178 heap
       chunks (one free), 141 interned strings in 256 buckets, and `nCcalls =
       0x20001`. Nothing touched stdio or the file system before the entry.
   * **Kernel side (landed):**
     * `Lua/Vm/Boot/Log.lean`: syi's `PackedLog`/`RunTree`/`LogOk`, with the
       cell check chunked (`runsIn`).
     * `Lua/Vm/Boot/Image.lean`: `bootMem chunk log` (loader plus log) and
       `bootMem_get : LogOk log runs → ViewOf (bootMem chunk log) (bootView
       chunk runs)`.
     * `Lua/Vm/Boot/View.lean`: `PartialView`, reads transported from a view
       (`PartialView.rdLE`), `zeroOk`/`bytesOk`/`segsOk`.
     * `Lua/Vm/Boot/Heap.lean`: `heapCheck`, `heapAt_of_check`.
   * **The kernel witness (done).** For each traced program,
     `Lua/Vm/Boot/Witness/<Prog>.lean` (generated by the same script) proves
     `vmLoaded_<prog>_entry : EntryRegs σ gprs → σ.mem = bootMem chunk log →
     output σ = "" → tick < 2 → VmLoaded luaLayout proto (fillZero ⟨σ, tick,
     steps⟩)`, `vmLoaded_<prog>_view` (any memory extending the boot view) and
     `runtimeReady_<prog>_entry` (`RuntimeReadyAt … w`, the witnessed
     `luaRuntimeReady`). Every check is a `decide +kernel` at default budgets
     over the byte view `bootView chunk runs`; no memory image is reduced.
     * `Lua/Vm/Boot/Check.lean`: one Bool checker per structure with its
       soundness lemma under `PartialView m v`: `entryCheck` (`VmEntryData`,
       with `protoCheck`/`constCheck`/`tstrCheck` for `ProtoRepr` against
       `gen_proto.py`'s `Proto`), `errorJmpCheck`, `stdioCheck`,
       `memfsCheck`, `luaStateCheck` (with `strtCheck`, `strcacheCheck`),
       `regionsCheck` (every round-3 `VmRegionsAt` field), `internedCheck`
       (`KInterned`, by `strDiff`: distinct pointers must differ in bytes),
       `kownedCheck` (`KOwned`, by `strLenV` and a search of the chunk walk),
       `heapCheck`, `runsAvoid` (no store in `.text`/`.rodata`), and
       `logOk_of_chunks`.
     * `Lua/Vm/Boot/Assemble.lean`: `EntryRegs` (`GoodState`, `pc`, the HTIF
       mailbox, the traced GPRs), `gprsCheck`, `runtimeReadyAt_of_checks`,
       `vmLoaded_of_checks`, `vmLoaded_of_boot`.
     * Per program: 18 store chunks of 1024 and 10 run chunks of 64
       (`LogOk`), `regsOk`, `imageOk`, `entryOk`, `rtOk` (10 structure
       checks), each one line.
     * Cost: each witness module ≈ 4–5 min wall, 236 s CPU, 3.0 GB peak
       (a 1024-store chunk ≈ 8 s, a 64-run chunk ≈ 7 s, `rtOk` ≈ 25 s,
       `entryOk` < 1 s); the data modules are unchanged.
     * Not built: the Sail register file. `EntryRegs` is a hypothesis
       (this repository has no copy of syi's `physicalAssignments`), so the
       theorem is over the family of states with the traced registers, not a
       closed `Config`. The step count and tick are free (`tick < 2`).
   * **Found by the witness: a `VmEntryData` bug.** `TStringRepr` required
     the string's header tag `GCObject.tt = vShrStr` (68, the `TValue` tag
     with `BIT_ISCOLLECTABLE`). `luaC_newobj` stores `LUA_VSHRSTR` (4), so
     `VmEntryData` (its `_ENV.print` key and every string constant) held at
     no real entry state, and `VmLoaded` was vacuous. It now uses `gcShrStr`
     and `gcLngStr` (`LayoutRt.lean`), and the traced entries satisfy it.
   * **`VmEntryData.env_print_ptr` (closes the pointer gap).**
     `TableHasShortKey` compares string contents, but `luaH_getshortstr`
     compares pointers. The new field says every short-string constant with
     bytes `"print"` is the key pointer of `_ENV`'s `print` node
     (`TableHasShortKeyPtr`). The generator checks it natively and
     `printPtrCheck` in the kernel.
7. **`disasm_to_segment.py` (done).**
   * It no longer drops rows. An `#UNSUPPORTED` row in the range, or an
     address with no row, is an error; `--allow-unsupported` drafts an
     explicit `UNSUPPORTED` step instead.
   * `disasm_to_sites.py` classifies every instruction of `luaV_execute`
     (4,396 rows, 0 unsupported). The added classes are the immediate and
     register shifts and logic ops, `addw`, `lui`/`auipc`,
     `lb`/`lh`/`lhu`/`lwu`, `sh` and general `jalr`.
   * `scripts/draft_f1_arms.py` drafts all 34 F1 arms: 2,050 instructions in
     496 segments (`experiments/census/demo/f1_arm_drafts.tsv`).
   * Every step has a site class (`draft_f1_arms.py`: 0 steps without one;
     check.sh stage 1). `scripts/syi/gen_sites.py` gained the classes
     `andi`/`ori`/`xori`/`slti`/`sltiu`, `slli`/`srli`/`srai`,
     `slliw`/`srliw`/`sraiw`, `and`/`or`/`xor`/`slt`/`sltu`/`sll`/`srl`/`sra`,
     `addw`/`sllw`/`srlw`/`sraw`, `lui`/`auipc` and the total loads
     `lh`/`lhu`/`lwu`. Each goes through an existing execute characterisation
     (`ExecuteAlu`, `ExecLoadTotal`); decode is `decodeW`.
8. **F1 arm segments (done).** `scripts/gen_lua_arms.py` emits, for every F1
   arm, the site batteries and one theorem per straight-line segment
   (`Lua/Vm/Arms/{Sites,Segs}/*`, index `Lua.Vm.Arms`, per-arm list
   `Lua/Vm/Arms/arms.tsv`).
   * Segments are `draft_f1_arms.py`'s, also cut after every `jal`; a
     segment ending in a conditional branch has a theorem per polarity
     (`_t`/`_n`). 788 segment theorems over 2,111 site lemmas, all built.
   * Each is `Triple (SegSt entry L (TextLoaded ∧ mem = m0)) (SegSt exit L' …)`
     (`Vsa.Sim.SegSt`, `gen_segment.py` `"boundary": "segst"`). `L` pins the
     registers read before written; `L'` gives every written register as the
     exact machine term and the memory as the store expression over `m0`.
     Loads are total (`bytesT*`). The address side conditions, branch guards
     and `jr` alignments are named hypotheses `h*_<step>` over the entry
     values: the arm proof discharges them from the A1 invariant.
   * `.text` (`Lua.Vm.Arms.TextLoaded`, the image's exact bytes) survives each
     store above `tohost + 16` (`TextLoaded.{writeMap8,writeMap4,insert}`).
   * Build: 119 modules; about 1.9 GB and 5–60 s each; built in batches of
     8 modules on this machine.

**Exit:** `VmLoaded luaLayout p (fillZero c)` is kernel-checked for
`while.lua` and `f1_ops.lua` at their real entry states, and check.sh
covers the new stages.

## A1: Layer A for F1

* **Target.** Prove `VmSim luaLayout`, then `vm_refinement_Statement luaLayout`
  by `vm_refinement_of_sim`.
* **Invariant.** The machine state represents a `BcSem` `State`:
  * `L->ci`, `savedpc` = `code + 4·pc`;
  * `FrameRepr` for the registers `Supported` says are definitely
    initialised;
  * output = `s.out`;
  * image, heap and stdio unchanged.
* **Arms.** One simulation lemma per F1 `Step` rule.
  * Each goes from the shared fetch site (`0x8001bfe4`, 10 instructions)
    through one of the 43 arms (2,239 instructions of per-arm reach; 613 on
    the integer fast paths) back to the fetch site.
  * Arms are generated with `gen_fn.py`/`genseg.py`. Integers-only
    `Supported` prunes the float/string slow paths of `LT`/`LE`/`FORPREP`/`MOD`.
* **Calls.** `CALL print` runs `luaD_precall` → `luaB_print` →
  `luaL_tolstring` → `lua_writestring`/`fwrite` → newlib stdout → HTIF. It
  reuses the stdio proofs from A0.5.
* **Errors.** The error paths (`luaG_opinterror`, `luaG_forerror`,
  `luaG_runerror` → `luaD_throw` → `longjmp` → `lua_pcallk` returns →
  `main` exits 2) give `stuck_sim`.
* **Definite initialisation (proved, `Lua/FragmentSound.lean`).** The
  fixpoint `supportedB` computes is a certificate (`Supported.defInit :
  DefInit p (defMask p)`).
  * `DefInit.step` is the invariant to use: two states agreeing on
    `defMask p pc` step to states agreeing on the successor's mask, and a
    `CALL` clobbers nothing in it. So `FrameRepr` is needed only for the
    registers in `defMask p s.pc`; the rest of the frame may hold anything.
  * `bcSemFrom_iff`: `BcSem` from any entry register file equals `BcSem`
    from all-`nil`. `cbcSem_iff`: the same with every register at or above a
    `CALL`'s results clobbered after each call (`CStep`).
  * `reachable_defInit`: at every reached state the pc is in range, the
    reads are in the mask, and the masked registers do not depend on the
    entry registers. `condJump_ne_none`/`condJump_lt`: test targets exist
    and are in range.
  * `Step.deterministic`, `BcSem.deterministic` (`Lua/Bytecode/Exec.lean`,
    via `step?_complete`).
* **Status (pilot, incumbent tooling; `abstractions/pilot/A1-incumbent.md`).**
  * **The relation** (`Lua/Vm/Sim/Rel.lean`). `VmRel p c s := ∃ w, VmRelAt p c s w`,
    all named fields:
    * the machine is at the fetch head `Lua.Vm.Arms.headPc` (`0x8001bfe4`, from
      the census JSON);
    * `Pins` fixes s0 = `L`, s7 = `ci`, s8 = the jump table, s1 = 81, s2 = 3,
      s5 = `trap` = 0, s9 = `base`, s11 = `code + 4·pc` (the cached pc; the
      memory `savedpc` is only written by `savepc`), `sp` and `gp`;
    * `Core.stack`: every defined register `j < maxstacksize` is represented
      (`ValRepr`) by its slot's tag and payload. The kernel's ⊥ already
      encodes the definite-initialisation mask. Nil is exactly `LUA_VNIL`, a
      string's tag is `strTag s`, and a short string's pointer is the intern
      map's `w.ι s` (`luaV_equalobj` decides `δ .eq`);
    * `Core.out`: the HTIF console is `s.out`;
    * `Core.frame`: outside the window (register slots, `luaV_execute`'s C
      frame, and `Scratch`: `ci->u.l.savedpc`, `L->top`, the callee frames
      `[spEntry - cStackBudget, sp)`) memory is a complement `w.mo`. `Complement` holds the image,
      `ProtoRepr`, the code words, `ci->func`, `ci->u.l.trap = 0`,
      `LuaStateAt`, `HeapAt` and `ErrorJmpAt`. `Ranges` holds the address
      bounds and separations.
  * **Relocation.** Registers are decoded from `ci->func` as the complement
    holds it (`base = func + 16`), not from a fixed address. Two operations
    move it; both re-establish `VmRel` with a new `func`, so no rewrite is
    needed:
    * `VARARGPREP` moves `ci->func` in every main chunk;
    * `CALL print` can reallocate the stack at ≥ 15 locals
      (`experiments/a1-falsifiers/REPORT.md`).

    The alternative, recorded but not taken, is a frame bound in `Supported`
    that rules out the reallocation.
  * **Dispatch, proved once** (`Lua/Vm/Sim/Dispatch.lean`, `dispatch`). It
    runs from `VmRelAt` with the instruction `ins` (opcode < 82) to
    `armTarget ins.opNum`, the table entry in `.rodata`
    (`jtWord_eq`, `armTarget_aligned`). It goes through the generated head
    segment `seg_8001bfe4_8001c00c` (`Lua/Vm/Arms/Head.lean`).
  * **Arms** (`scripts/gen_lua_arm.py`, `Lua/Vm/Sim/Arms/`). Each
    `sim_<OP> : Supported p → VmRel p c s → fetch → op → Step binaryHost p s s' →
    ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'` is proved for the 25 arms
    listed below. The proof composes:
    * `dispatch`;
    * the arm's generated segments (one chain per exit, picked by branch
      polarity), whose side conditions are closed by `arm_arith`/`slot_arith`;
    * the kernel combinator's inversion (`step_setR`, `step_jump`,
      `step_opArith`, `step_condjump`, `step_testset`, `step_forloop`);
    * a close: `Core.write`, `Core.jump`, `Core.update` or `Core.forloop`.

    The segments of `SIM_OPS` arms carry the fetch-head registers,
    `sailOutput` and `RegsOk` (`gen_lua_arms.py` `KEEP`, `OK`).
  * **Entry lemma (proved,** `Lua/Vm/Sim/Entry.lean`, `vmRel_entry :
    vmRel_entry_Statement`**).** From `VmLoaded luaLayout p c`, the prologue
    runs to the fetch head in `VmRel p c' State.init`. It composes the two
    generated prologue segments (`Lua/Vm/Arms/Prologue.lean`,
    `gen_lua_arms.py`, cut at `startfunc`):
    * `seg_8001bf68_8001bfb0` (the C frame, `L`/`ci`, the jump table): 52 ground
      side conditions, one `decide` each;
    * `seg_8001bfb0_8001bfe4` (`startfunc`'s loads, s1/s2, the `trap` check,
      `base`): 27 side conditions, one normalising `simp` plus `omega` over
      `VmRegionsAt`.

    The relation's pointers are `VmEntryData`'s and `w.mo` is the entry
    memory; `rdLE_spec` turns `rd32`/`rd64` into the total reads. It needed
    two new `luaRuntimeReady` structures, `VmRegionsAt` and `HarnessAt`
    (A0.6). Costs: `abstractions/pilot/A1-incumbent.md`.
  * **Arms proved (25):** MOVE, LOADI, JMP, ADD, SUB, ADDI, ADDK, SUBK, BAND, BOR, BXOR, EQI, LTI, GTI, LEI, GEI, TEST, TESTSET, NOT, BNOT, LOADK, LOADTRUE, LOADFALSE, LFALSESKIP, FORLOOP (`scripts/gen_lua_arm.py` kinds `copy`,
    `imm`, `jump`, `arith` (register, `sC` and `K` operands, the `op_arith`
    and `op_bitwise` layouts), `condjump`, `cmpI`, `truth`, `bnot`, `settag`,
    `loadk`, `forloop`; costs in `abstractions/pilot/A1-incumbent.md`, "More
    arms"). The relation now also carries:
    * `Core.frame` on total reads (`bytesT1`), `.text` presence separately
      (`Core.text`, the segments' fetches);
    * `Core.ok : RegsOk` (every GPR present, HTIF mailbox idle;
      `MachineAt.regs`, checked on the boot traces; threaded by every
      segment through `gen_segment.py`'s `"ok"` option);
    * the constant array: `Core.kptr` (`0(sp) = k`), `Complement.kconst`,
      `Ranges.k_*`/`frame_sep` (`VmRegionsAt.k*`, checked natively).
  * **The fold (lane F1-3, `Lua/Vm/Sim/Fold.lean`).** `fold_sim` is `Refine.Sim`
    from a relation and four clauses at reachable states (`FoldSim`: a step is a
    non-empty run, a final state halts with 0, a stuck state diverges or halts
    nonzero), by induction on the bytecode run; divergence of an unending run is
    by strong induction on the step count. Its instance `vmSim_of_arms` takes the
    arm table `∀ o ∈ armOps, SimArm o` (`armOps` = every opcode `opKernel` gives a
    kernel, `kernelOps`, but `VARARGPREP`), `EntrySim`, `VarargSim`, `FinalSim`,
    `StuckSim`; `armTable` discharges the 34 proved arms from `OpenArms`, so
    `vm_refinement_of_open : OpenArms → FinalSim → StuckSim →
    vm_refinement_Statement luaLayout`. `fillZero` enters only in
    `vm_refinement_of_sim`; `Supported` through `VmLoadedSupported`.
  * **`VARARGPREP` (proved, `Kit.varargSim`).** `SimArm .VARARGPREP` is not the
    obligation: `luaT_adjustvarargs` reads `L->top`, which `VmRel` leaves free
    (`Scratch`), so from a general `VmRel` state the move of `ci->func` is
    unknown, and an `A > 0` copies uninitialised parameters. So:
    * the kernel admits `VARARGPREP` only at pc 0 with `A = 0` (`lparser.c`
      `mainfunc`: `setvararg(fs, 0)`), and `supportedB` rejects every edge into
      pc 0 (`edges`; `DefInit.pc_pos`), so the one reachable state at a
      `VARARGPREP` is the entry state (`reach_pc_zero`); the corpus stays
      `Supported`;
    * the entry-only facts are `FreshAt` (`Lua/Vm/Sim/Vararg.lean`), proved at the
      fetch head by `entry_fresh` (from `entry_at`, `vmRel_entry` factored, and
      `relParts`, the complement and ranges from `ProtoAt` and `RtPostAt`);
    * the relation after the move: the entry contract now says the runtime is
      ready also at the memory the stores leave (`RuntimeReadyAt.vararg` at
      `varargMem`, for `RtPtrs.vmoved`; `VmEntryData.vararg_room` (no
      `luaD_growstack`) and `vararg_proto` (the prototype framed away from the
      `CallInfo` and the copied slot, `VarargDirty`)). The boot witness checks
      both at `postView`/`View.minus` (`RtPostChecks`, `entryCheck`); the two
      traced entries pass (each witness ≈ 5 min, 3.3 GB);
    * the run: `dispatchM` (dispatch, memory unchanged), the segment-local
      lemmas `vp1` (to the call), the call node `Kit.adjvar_sum` (three
      segment-local lemmas over the generated `HluaT_adjustvarargs` segments,
      `av_guard` for `luaD_checkstack`), `vp2` (`trap`), `vp3` (`updatebase`),
      and the close `vclose` at `w.vmoved ι`, its memory frame `vmem_frame`.
    The at-lemma generator does not express this arm: its close `AtFin.close`
    keeps `w`, `ld a3,24(a5)` loads through a loaded pointer (`gen_lua_at.py`
    `addr_of` stops), and `lw`/`sw` have no `Loc`/`Ent`.
  * **Open, with what each needs:**
    * callee contracts at Lua addresses: `MUL`/`MULK`/`MOD`/`MODK` are
      proved on the kit (`Kit/{Mul,Mulk,Mod,Modk}.lean`). `IDIV`/`IDIVK`
      need a `__divdi3` summary: its helper segments are generated
      (`Lua/Vm/Arms/Segs/{Hdivdi3,Humoddi3}.lean`; the sign fix-ups lie in
      `__umoddi3`'s symbol, and the unsigned case falls through into
      `__hidden___udivdi3`), the summary is open. `FORPREP` (`__udivdi3`
      whenever the step is not 1);
    * callee contracts in `luaV_execute`'s callees: `UNM` (a numeric
      string: `luaT_trybinTM` → the string library's `__unm`), `VARARGPREP`
      (`luaT_adjustvarargs`, which moves `ci->func`: `VmRel` is
      re-established with a new `func`). (`EQ`, `EQK`, `LT`, `LE` on
      strings and `LEN` are proved: `Kit.sim_EQ`, `At.sim_EQK`, `At.sim_LT`,
      `At.sim_LE`, `At.sim_LEN`; lane F1-2 put `docondjump`, observed call
      nodes and calls that store `R[A]` on the location-list route,
      `Kit/AtCond.lean`);
    * `BANDK`/`BORK`/`BXORK`: the arm reads `K[C]`'s payload without a tag
      test (`lvm.c` `op_bitwiseK`: `ivalue(KC(i))`; `lcode.c` `codebitwise`
      emits a `K` operand only for a `VKINT` constant), so their kernel is
      `bitwiseRK`, defined only for an integer `K[C]`
      (`Lua/Bytecode/Semantics.lean`; the corpus stays `Supported`). The arm
      proofs are open;
    * the shifts (`SHL`/`SHR`/`SHLI`/`SHRI`): inline, but a new kind (the
      shift-amount branches against `shiftl`); (`LOADNIL` is proved on the
      kit: `Kit.sim_LOADNIL`, its loop by `Kit.loadnil_loop`);
    * `RETURN*`: `vmRel_final_Statement` (above);
    * `CALL` (print): callee contracts `luaD_precall` → `luaB_print` →
      `luaL_tolstring` → `lua_writestring` = `fwrite` → newlib stdout → HTIF
      (the A0.2 stdio tables at Lua addresses), `checkstackGCp` (possible
      stack reallocation at ≥ 15 locals: `VmRel` with a new `func`), the
      heap, string interning (`luaS_newlstr`) and `StdioBoot`/`MemfsBoot`
      evolving in the complement, the `trap` reload; `GETTABUP` (the
      `_ENV.print` lookup) is its companion, blocked as its obligation row
      says (the walk to the `print` node, the closure in the relation);
    * the error paths (`StuckSim`, Obligations).
* **Exit.** `vm_refinement : vm_refinement_Statement luaLayout` has only
  standard axioms and is listed in check.sh stage 6.

## A2–A8: later fragments (Layer A)

Each fragment extends `Value`, `Step`, `Supported` and the representation,
and removes its opcodes from `ledger` (`Lua/Fragment.lean`;
`ledger_exact` keeps the ledger honest).

* **A2 (F1b): integer bitwise (done).** `BAND`/`BOR`/`BXOR`/`SHL`/`SHR`,
  the `K` forms and `SHRI`/`SHLI` are integer binary operations
  (`intArith`, with `luaV_shiftl` as `shiftl`); `BNOT` is its own rule. The
  opcodes are F1 and left the ledger (29 entries). `c/tests/f1b_bits.lua`
  passes the difftest; `f1b_bcSem` and `f1b_supported` are kernel-checked.
  Layer A's F1 arms now include these 11.
* **A3 (F2): tables.**
  * Semantics: a heap of tables in `State`, and `next` order as the binary's
    order. The array part, and the hash part in node order with
    `lsizenode`/`lastfree`/rehash (`luaH_resize`), are specified exactly,
    since F2's difftest shows `pairs` order is observable.
  * Heap: allocation through the dlmalloc proofs, GC stopped.
  * Address-revealing `tostring` (`table: 0x…`) needs an allocation model in
    the semantics or an exclusion in `Supported`. Decide at the start of A3.
* **A4 (F3): multi-frame semantics.**
  * Closures, upvalues (open/closed, `luaF_close`), Lua calls and returns,
    varargs, multret, tail calls.
  * `BcSem` becomes multi-frame over a `CallInfo` stack; `luaD_precall`
    and `luaD_poscall` are simulated.
* **A5 (F4): strings and metatables.**
  * String interning (`luaS_newlstr`, the short-string table) and
    concatenation.
  * Metatables and metamethods (`luaT_trybinTM`, `__index` chains), and
    to-be-closed variables.
* **A6 (Float): floats.** Soft-float `__adddf3` and the rest (15 routines in
  the census) and `%.14g` via `vfprintf`/`_dtoa_r`. The WHILE ELF has the
  same code; retarget it.
* **A7 (Coroutine): coroutines.** `lua_resume`/`lua_yield`, a separate
  `lua_State`, and `longjmp` across resumes.
* **OS (io/os libraries).** The shared syscall spec of ship-your-ocaml
  (`tcb/`, Lean library `TCB`): SibylFS for the file system, the CakeML
  basis FFI for console streams, `OsStep`/`next`, and the checker `allowed`.
  * **Landed.**
    * `tcb/` is ship-your-ocaml's at `f5-htif` `39e79b2` (ATTRIBUTION.md),
      including spec DEVIATION 10 (`osReaddir`). It builds, and
      `TCB.Os.allowed_sound`/`checkTrace_sound` are in check.sh stage 6.
      Its Linux trace validation reproduces here (6,398 accepted, 0
      rejected, 92 special).
    * `Lua/Os/HtifFs.lean`: `HtifFsImplements`, adapted from
      ship-your-ocaml's `OCaml/Os.lean`. `retOf` also sees the entry, and
      calls the spec leaves unconstrained are allowed.
    * **The ELF opens `io` and `os`** (steps 1-2 of the old plan).
      * `c/src/htif.c` has an in-image file system written against the
        spec: files and directories, the spec's path resolution, one
        descriptor table with `EBADF` outside it, `st_nlink` 1 for the
        console, `_stat`/`_unlink`/`rename`/`mkdir`/`rmdir`, and a clock
        frozen at 0. Its memory comes from `malloc`, so the dlmalloc
        proofs apply.
      * ship-your-ocaml adopted the same file.
      * `experiments/os/run.sh` rejects none of its traces: 5,275
        accepted, 79 special, and 1,136 that stop at `opendir`, which the
        ELF lacks; all 26 console scripts are accepted. check.sh 5b pins
        these verdicts.
      * Difftests `f7_io`/`f7_os`: 18/18 on Sail (VALIDATION.md §6).
    * `Lua/Os/Htif.lean`: the instance for the Lua ELF.
      * `HtifCallAt` decodes the twelve functions `_open`, `_close`,
        `_read`, `_write`, `_lseek`, `_fstat`, `_stat`, `_unlink`,
        `rename`, `mkdir`, `rmdir` and `_gettimeofday` (the clock) at their
        entry. Addresses and newlib's flag, errno, `struct stat` and
        `struct timeval` layout come from `Lua/Vm/Layout.lean`.
      * `HtifRetAt` reads `a0`, `errno` and the out-buffer at the return.
      * Also `LuaCallConv` and `HtifRepr`.
      * Two statements: `HtifPrint_Statement` (now including newlib's
        `_fstat` of the console) and `HtifFs_Statement` (Obligations).
    * `Lua/Os/HtifTraces.lean`: the console verdicts as kernel-checked
      facts about `next`, both the old `htif.c`'s rejected returns and the
      current one's accepted returns.
  * **`HtifFs_Statement` is now plausibly true** (every trace is accepted,
    special or unsupported), with two caveats.
    * **Resources.** Past 64 files and directories, 32 descriptors or the
      heap, `htif.c` returns `EMFILE`/`ENOSPC`, which `next` never allows.
      The proved form needs a resource bound in its scope, like `Fits`.
    * **Vacuity.** `HtifRepr` lets `R` hold at boot only, which satisfies
      the statement vacuously. The frame obligation below is what makes it
      meaningful.
  * **Next.**
    1. **`OsState` in `BcSem`.** The plan:
       * The World gets an `OsState` next to its output: the console
         stream replaces the output string (`st.streams.console`), and the
         initial world is `OsState.init`.
       * The C functions of `io`/`os` (a new `Builtin` per function) are
         specified through `OsStep`: each is a sequence of `TCB.Os.Call`s
         as newlib issues them (buffering made explicit, or an abstract
         `FILE` layer over `OsStep` for `io`), and a Lua-level result
         built from the returns. `os.time`/`os.clock` are `Call.clock`,
         `os.getenv` is `Call.getenv`, and `os.exit` is `Call.exit`.
       * `BcSem` then quantifies over the allowed returns, since `next` is
         nondeterministic. The ELF's are the frozen clock and full writes;
         `Host` records these choices, as it does for function addresses.
       * The frame obligation: every step outside `htif.c` preserves the
         representation relation `R`. This is what makes `HtifFs_Statement`
         non-vacuous.
    2. Prove `HtifPrint_Statement`, then `HtifFs_Statement` (with the
       resource bound), with the whole-function machinery (`gen_fn.py`,
       `FnSummary`).
    3. Optionally, directory streams (`opendir`/`readdir`/`closedir`,
       ship-your-ocaml's `OCAML` part of `htif.c`), so the remaining 1,136
       traces are checked too. Lua does not need them.
  * The ELF must stay free of `ecall` (check.sh stage 2).
* **A8: GC.**
  * Stop calling `lua_gc(L, LUA_GCSTOP)`.
  * Prove the semantics GC-invariant (unreachable objects unobservable);
    handle weak tables and finalizers, or exclude them from `Supported`.

## B: Layer B, source to bytecode

* **B1: translation validation (done for the corpus).** For concrete F1
  chunks and the host `luac -s`'s output, both directions of `CompileTV`.
  * Source syntax: `Lua/Ast/Syntax.lean` is the complete Lua 5.4 syntax
    (manual §9: every `stat`, `retstat`, vars, prefix expressions, method
    calls, the three `args` forms, every `exp` including functions, tables
    and all operators; numerals as integers or float bits, strings as
    bytes).
  * Parser: `scripts/gen_ast.py` parses all of Lua 5.4 following
    `llex.c`/`lparser.c`, including lparser's static errors (`goto`/label
    visibility, `<const>`/`<close>`, `...` outside a vararg function, `break`
    outside a loop, 200 locals). Not enforced: code-generation limits
    (registers, upvalues, C levels, jump length); the parser accepts a
    superset there. It never enforces F1.
    * `--roundtrip`: parse, pretty-print, re-parse to the same AST, and
      `luac -l -l` of the original and the printed text agree. check.sh
      runs it on every `.lua` file in the repo. It also passes on all 33
      files of the Lua 5.4.7 test suite (`lua-5.4.7-tests.tar.gz` from
      lua.org, not committed).
    * `--differential N`: token-level mutants are accepted exactly when
      `luac -p` accepts them (8,100 mutants of the test suite and
      `c/tests`, 0 mismatches).
  * F1 on source: `AstSupported` (`Lua/Ast/Semantics.lean`) is decidable.
    `print(…)` is a call of the free name `print`; other globals, calls,
    floats, strings, tables, functions, `return` and `<close>` are outside.
    `goto`/labels follow the manual's visibility rules (a visible label in
    an enclosing block, not jumping into a local's scope unless the label
    ends its block, no label visible twice).
  * `LuaSem` over the full syntax, with rules for F1: names resolve to
    locals or `_ENV.x`; the call rule evaluates the function and arguments
    and calls the builtin `print`; blocks catch `goto`s to their own labels
    (`ExecBF`, `findLabel`, `jumpEnv`); loops catch `break`; multiple
    assignment stores in `restassign`'s order.
  * `LuaSem` side: the fuel-bounded interpreter `luaRun`
    (`Lua/Ast/Exec.lean`) with `luaRun_sound` (`execSound`), by
    `decide +kernel`.
  * `BcSem` side: `bcSem_of_run`, by `decide +kernel`.
  * Determinism: `LuaSem.deterministic` (`Lua/Ast/Determinism.lean`),
    `Step.deterministic`, `Final.not_step`, `BcSem.deterministic`
    (`Lua/Bytecode/Exec.lean`); `agree_of_outputs` turns one common
    output into `∀ out, LuaSem s out ↔ BcSem p out`.
  * Per program: `ProgramTV s p` (`AstSupported s`, `Supported p`, the `↔`)
    and `CompileTV.of_programTV` (`Lua/Compile/TV.lean`).
  * Corpus (`Lua/Compile/Corpus.lean`): `while.lua` (`goto continue`),
    `f1_ops.lua`, `f1_src.lua` (`if`/`elseif`, `repeat` over body locals,
    `break` from `while`/`for`/`repeat`, shadowing, padded/extra `local`
    values) and `f1b_bits.lua` (bitwise operators); expected outputs are the
    ELF's on the Sail model (`c/tests/*.expected`). `print_print.lua` passes
    `print` as a value, outside `AstSupported`.
  * Exit (met): `compile_refinement_corpus :
    compile_refinement_Statement CorpusCompiles`, standard axioms only.
  * Adding a program: write `c/tests/x.lua`, commit `luac -s` output and
    the ELF's output, run `gen_ast.py`/`gen_proto.py`, add both to check.sh's
    drift lists, and add a `ProgramTV` plus a `CorpusCompiles` constructor.
* **B2: a Lean compiler.** Write `compile : Chunk → Option Proto`, a model of
  `lparser.c`/`lcode.c` on the F1 part of the full syntax (register
  allocation, jump patching including `goto`/label resolution, the
  `RK`/immediate/constant selection that `luac` does).
  * Check it against `luac` on the corpus (`compile s = luac s`).
  * Prove `CompileTV` for it.
  * Exit: `compile_refinement_Statement (fun s p => compile s = some p)`.
* **B3: the binary compiler.** `luaY_parser` and `luaK_*` in the ELF (about
  9.4k instructions, statically reachable via `load`) refine `compile` on
  source text. This needs a lexer/parser relation between text and `Chunk`.
  * Until then, the bytecode chunk is the trusted input (the program is
    `luac`'s output).

## E: composition

`endToEnd_lua_Statement luaLayout Compiles` follows from A1 and B1/B2 by
`endToEnd_of_layers`.

* **Extending to boot.** The statement can start from the ELF's `_start`
  instead of `luaV_execute`'s entry. Use A0.6's boot witness generalised
  over programs (as ship-your-interpreter's `loadedEntry_fill`): boot and
  undump reach a `VmLoaded` state for every chunk in the `.lua_chunk`
  region.
* **Exit.** The composed theorem has no hypotheses beyond `Supported` /
  `AstSupported`, and only standard axioms.

## Abstraction discovery (process; `abstractions/`)

`abstractions/gate.py` (check.sh stage 3c) fails when a proof cluster reaches
8 hand proofs without its per-case cost falling by a third. The only allowed
next task is then a round of `/abstraction-discovery`.

Round 1 (`abstractions/ROUND-1.md`) adopted two abstractions by bake-off:

- **bytecode:** per-opcode kernel terms with read/def/kill ports and a shared
  δ;
- **source:** `LuaSem` as the graph of a generic rulebook.

The round changed the plan in three ways:

- **Strings land with floats, not before them.** Lua coerces numeric strings
  in arithmetic (`"1.5"+1` gives `2.5`), so an F4 strings fragment without
  floats is not closed. Merge F4 and Float into one phase.
- **F2 constraints.**
  - `next` order and printed addresses are `Host` fields (functions of the
    history), not a nondeterministic choice.
  - Kernels keep static register ports and add adaptive heap queries for
    data-dependent table reads.
- **A1 prerequisites.** Before any A1 abstraction is built, run the recorded
  falsifiers (ROUND-1 §3 C7–C9):
  - a dependence-graph orbit canonicaliser over the ELF;
  - the exit count of the `ADD` arm (fast path plus fall-through to `MMBIN`);
  - `L->stack` logged at every dispatch head, which tests whether registers
    must be decoded relative to the stack base.
