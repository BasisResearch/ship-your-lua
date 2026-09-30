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
| `VmLayout.runtimeReady` concrete instance `luaLayout` | `Lua/Vm/Loaded.lean` | A0 | to define |
| `VmLoaded luaLayout p (fillZero c)` at real entry states (boot witness) | new `Lua/Vm/Boot/` | A0 | open |
| `VmSim luaLayout` (F1: `term_sim`, `stuck_sim`) | new `Lua/Vm/Sim/` | A1 | open |
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
6. **`luaLayout`.**
   * Define `VmLayout.runtimeReady` concretely, the analogue of
     `InterpRunReadyFacts`: the C stack below `sp`, the return address into
     `ccall`, `L->errorJmp` (the `lua_longjmp` chain), newlib's stdout
     `FILE`, and the dlmalloc heap `[_end, __heap_end)` in canonical shape.
   * Also every byte the run may touch must be present, checked on the dense
     view (`fillZero`).
   * Retarget `scripts/syi/gen_boot_witness.py` to stop at `luaV_execute`
     (step 181,166 for `while.lua`). It should emit the kernel witness
     `VmLoaded luaLayout whileProto (fillZero c)` at the traced entry state.
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
