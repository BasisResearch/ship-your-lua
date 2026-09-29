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
| `CompileTV (LuacOutput)` per program (translation validation) | new `Lua/Compile/TV.lean` | B1 | open |
| `CompileTV (fun s p => compile s = some p)` for a Lean `compile` | new `Lua/Compile/` | B2 | open |
| the ELF's `lparser`/`lcode` refine `compile` | — | B3 | open |
| **`compile_refinement_Statement`** | `Lua/Theorems.lean` | B1/B2 (by `compile_refinement_of_tv`) | open |
| **`endToEnd_lua_Statement luaLayout Compiles`** | `Lua/Theorems.lean` | E (by `endToEnd_of_layers`) | open |

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
3. **Decode table.**
   * Run `experiments/syi/gen_decode_table.py` on the Lua ELF's reached
     words.
   * 43% of the difftest union's 8,346 words are already covered by the
     copied lemmas.
4. **Code pins.**
   * `Lua/Vm/Image.lean` pins `.text`/`.rodata` already.
   * Generate per-function projections (`scripts/syi/gen_fixed_image.py`
     retargeted, `experiments/syi/gen_code_lemmas.py`) for `luaV_execute`
     and its F1 callees.
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
7. Fix `scripts/syi/disasm_to_segment.py`, which silently drops unsupported
   rows (VALIDATION.md §4).

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
* **Definite initialisation.** Soundness of `Supported`'s check: a register
  read on an executed path was written by the semantics, so its
  `FrameRepr` holds.
* **Exit.** `vm_refinement : vm_refinement_Statement luaLayout` has only
  standard axioms and is listed in check.sh stage 6.

## A2–A8: later fragments (Layer A)

Each fragment extends `Value`, `Step`, `Supported` and the representation,
and removes its opcodes from `ledger` (`Lua/Fragment.lean`;
`ledger_exact` keeps the ledger honest).

* **A2 (F1b): integer bitwise.** Mechanical. Exit: `.F1b` leaves the ledger.
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
* **A8: GC.**
  * Stop calling `lua_gc(L, LUA_GCSTOP)`.
  * Prove the semantics GC-invariant (unreachable objects unobservable);
    handle weak tables and finalizers, or exclude them from `Supported`.

## B: Layer B, source to bytecode

* **B1: translation validation.** For concrete F1 chunks and the host
  `luac`'s output, prove both directions of `CompileTV`.
  * `BcSem` side: from `run_sound`, as `Lua/Programs/Validation.lean` does.
  * `LuaSem` side: from a derivation tactic like ship-your-interpreter's
    `bigstep_derive`, plus determinism of `LuaSem` and `BcSem`.
  * Exit: `compile_refinement_Statement` for the relation "is the host
    `luac -s` output" restricted to a corpus. `f1_ops.lua` is the first
    target; `while.lua` needs `goto`, which is outside the F1 AST.
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
