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
| `HtifPrint_Statement`: `htif.c`'s `write` to fds 1-2 and `read` from fd 0 implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open (traces accept it) |
| `HtifFs_Statement`: all six system-call functions implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open; **false of the current `htif.c`** (`experiments/os/RESULTS.md` H1-H6) |

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
  * The AST and `LuaSem` for F1.
  * The statements.
* **Exit.** `scripts/check.sh` passes. That covers generator drift, the ELF
  hash, forbidden tokens, the copied layer being WHILE-free, `lake build`,
  and the axioms of 14 theorems.

## A0: retarget the machine layer to the Lua image

The copied layer (`Vsa/`, `VsaIris/`) is language-agnostic. Its proof
instances, however, are at the WHILE ELF's addresses.

1. **`tohost`.**
   * The problem: `Vsa.Sim.tohostAddr` (`0x8001ad00`) is baked into
     `GoodState` and the `RamRead*` lemmas.
   * Fix: make it the Lua image's `0x80048400` (`Layout.symTohost`), or
     generalise it to a parameter.
   * Then retire `LuaGoodState`, which is a field-for-field copy.
2. **Cut the 40 WHILE import edges.** `experiments/port/CUTS.txt` lists them,
   from `python3 experiments/port/port_census.py`.
   * They tie the segment bridges (`SegToTripleFramed`, `BridgeSeg*`,
     `FrameMeta`, `DeriveCase`) to WHILE representation modules.
   * They do the same to the allocator ledger (`AllocLedger`, `DlHeap`) and
     to the newlib/dlmalloc Iris proofs (`VsaIris/Vsa/{SymRun,AllocSteps,Stdout,Fprintf,ExitH}`).
   * Most of those edges supply shared geometry lemmas. Move those lemmas
     below the WHILE modules, then copy the targets.
   * Exit: `port_census.py --copyset` is clean with the targets included.
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
   * Regenerate the 74 reused functions' step tables and specs with the
     generators (`gen_alloc_steps.py`, `gen_str_steps.py`,
     `gen_memcpy_steps.py`, `gen_fn.py`).
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
     (step 124,808 for `while.lua`). It should emit the kernel witness
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
   * 376 of those steps need a site class that `gen_sites.py` or
     `gen_segment.py` lacks (`slli`, `andi`, `srliw`, `sh`, `jalr`, …). Each
     carries a blocking `TODO` marker. Those batteries are open.

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
  * Each goes from the shared fetch site (`0x8001aa7c`, 10 instructions)
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
    * `tcb/` copied verbatim (ship-your-ocaml `b6ffcf9`, ATTRIBUTION.md); it
      builds, and `TCB.Os.allowed_sound`/`checkTrace_sound` are in check.sh
      stage 6. Its Linux trace validation reproduces here (6,398 accepted,
      0 rejected, 92 special).
    * `Lua/Os/HtifFs.lean`: `HtifFsImplements`, adapted from
      ship-your-ocaml's `OCaml/Os.lean` (`retOf` also sees the entry; calls
      the spec leaves unconstrained are allowed).
    * `Lua/Os/Htif.lean`: the instance for the Lua ELF. `HtifCallAt` decodes
      `_open`/`_close`/`_read`/`_write`/`_lseek`/`_fstat` at their entry
      (addresses and newlib's flag, errno and `struct stat` layout from
      `Lua/Vm/Layout.lean`); `HtifRetAt` reads `a0`, `errno` and the
      out-buffer at the return; `LuaCallConv`, `HtifRepr`. Two statements:
      `HtifPrint_Statement` and `HtifFs_Statement` (Obligations).
    * `experiments/os/run.sh`: ship-your-ocaml's trace driver run on our
      unchanged `htif.c` (check.sh stage 5b). Our `htif.c` conforms on
      `write` to fds 1-2 and `read` from fd 0, and deviates on `fstat` of the
      console (`st_nlink` 0, not 1), unknown or closed descriptors (the
      console, not `EBADF`), `read` of stdout / `write` of stdin, a bad
      `whence`, and `open` with `O_CREAT` (`experiments/os/RESULTS.md`;
      the console deviations are also kernel-checked facts about `next`,
      `Lua/Os/HtifTraces.lean`).
  * **Next.**
    1. Add `io`/`os` to the Lua build (needs the go-ahead: it changes the
       ELF, `.text`, the image, the code pins and the validation outputs).
    2. A conforming in-image file system in `htif.c`: a descriptor table
       (`EBADF` for descriptors it did not issue, `close` that closes),
       `st_nlink = 1` for the console, files for `open`, and the functions
       `io`/`os` need (`_stat`, `_unlink`, `rename`, a clock). Rerun
       `experiments/os/run.sh` until the flat family and the console
       scripts are accepted.
    3. An `OsState` in the semantics (`BcSem`/`LuaSem` over the OS), with
       the frame obligation that the rest of the ELF preserves the
       representation relation `R` (`HtifRepr` alone does not make `R`
       hold at a call entry).
    4. Prove `HtifPrint_Statement`, then `HtifFs_Statement`, with the
       whole-function machinery (`gen_fn.py`, `FnSummary`).
  * The ELF must stay free of `ecall` (check.sh stage 2).
* **A8: GC.**
  * Stop calling `lua_gc(L, LUA_GCSTOP)`.
  * Prove the semantics GC-invariant (unreachable objects unobservable);
    handle weak tables and finalizers, or exclude them from `Supported`.

## B: Layer B, source to bytecode

* **B1: translation validation (done for the corpus).** For concrete F1
  chunks and the host `luac -s`'s output, both directions of `CompileTV`.
  * Source side: `scripts/gen_ast.py` parses an F1 `.lua` file into a Lean
    `Chunk` (check.sh stage 1 checks drift, and that the committed `.luac`
    is `luac -s` of the `.lua`). The F1 AST has multi-name `local`
    (`Stat.locals`, `adjust_assign`: missing values `nil`, extras dropped).
  * `LuaSem` side: the fuel-bounded interpreter `luaRun`
    (`Lua/Ast/Exec.lean`) with `luaRun_sound`, by `decide +kernel`.
  * `BcSem` side: `bcSem_of_run`, by `decide +kernel`.
  * Determinism: `LuaSem.deterministic` (`Lua/Ast/Determinism.lean`),
    `Step.deterministic`, `Final.not_step`, `BcSem.deterministic`
    (`Lua/Bytecode/Exec.lean`); `agree_of_outputs` turns one common
    output into `∀ out, LuaSem s out ↔ BcSem p out`.
  * Per program: `ProgramTV s p` (`AstSupported s`, `Supported p`, the `↔`)
    and `CompileTV.of_programTV` (`Lua/Compile/TV.lean`).
  * Corpus (`Lua/Compile/Corpus.lean`): `f1_ops.lua` and `f1_src.lua`
    (`if`/`elseif`, `repeat` over body locals, `break` from
    `while`/`for`/`repeat`, shadowing, padded/extra `local` values); expected
    outputs are the ELF's on the Sail model (`c/tests/*.expected`).
    `while.lua` needs `goto` and `print_print.lua` reads `print` as a value:
    both outside the F1 AST.
  * Exit (met): `compile_refinement_corpus :
    compile_refinement_Statement CorpusCompiles`, standard axioms only.
  * Adding a program: write `c/tests/x.lua`, commit `luac -s` output and
    the ELF's output, run `gen_ast.py`/`gen_proto.py`, add both to check.sh's
    drift lists, and add a `ProgramTV` plus a `CorpusCompiles` constructor.
* **B2: a Lean compiler.** Write `compile : Chunk → Option Proto`, a model of
  `lparser.c`/`lcode.c` for F1 (register allocation, jump patching, the
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
