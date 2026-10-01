# Ship your Lua

This project will verify **Lua 5.4.7 compiled to bare-metal RV64**
(`c/lua-riscv-htif.elf`) against a formal semantics, on the Sail RISC-V
model, in Lean 4 + iris-lean. It is the successor to
[ship-your-interpreter](https://github.com/BasisResearch/ship-your-interpreter),
which proved a WHILE interpreter's ELF against a big-step semantics
(`endToEnd_refinement`). This repository reuses its machine layer
(ATTRIBUTION.md).

**Status.** Phase 1 (validation) is done: the ELF runs on Sail and agrees
with native Lua (VALIDATION.md). The Lean scaffold builds. The headline
theorems are *stated*, not yet proved: they are `def …_Statement : Prop`,
never `sorry` or axioms. Their composition *is* proved. PHASES.md is the
plan.

## The plan

The proof is compositional, cut at the VM:

```
LuaSem s out  ↔  BcSem (compile s) out  ↔  Halts c out 0
   Layer B: compile_refinement      Layer A: vm_refinement
```

**Layer A (first): the bytecode semantics against the `luaV_execute` binary.**
* `BcSem` (`Lua/Bytecode/Semantics.lean`) is an inductive small-step
  relation transcribed from `lvm.c`.
* The cut point is `VmLoaded` (`Lua/Vm/Loaded.lean`): the machine at
  `luaV_execute(L, ci)` with the chunk's `Proto` in memory. It is the
  analogue of WHILE's `Loaded` at `interp_run`.
* Layer A grows fragment by fragment over opcodes. `Supported`
  (`Lua/Fragment.lean`) is a decidable fragment check: opcodes,
  well-formedness, and definite initialisation. Every excluded opcode is in
  `ledger` with its fragment. There is never a `sorry`.

**Layer B: the bytecode against Lua source.**
* The source is real Lua: `Lua/Ast/Syntax.lean` is the complete Lua 5.4
  syntax (the manual's §9), and `scripts/gen_ast.py` parses all of Lua 5.4
  into it, following `llex.c`/`lparser.c` with lparser's static errors. It
  parses every `.lua` file in the repo and the Lua 5.4.7 test suite, and
  round-trips them through the host `luac` with identical `luac -l -l`
  listings.
* `LuaSem` (`Lua/Ast/Semantics.lean`) is a big-step semantics over the full
  syntax with rules for F1. `print(…)` is a call of the global `print`
  looked up in `_ENV`, and `goto` resumes after its label in the enclosing
  block. `AstSupported` is the decidable F1 predicate on source, including
  the manual's label visibility rules.
* The order: per-program translation validation of `luac`'s output first,
  then a Lean compiler with a correctness proof, then the ELF's own
  `lparser`/`lcode`.

**Fragments.**

| fragment | contents |
|---|---|
| **F1** | bytecode: integers, moves, constants, integer arithmetic and bitwise operators (F1b, merged), compare+jump, `FORPREP`/`FORLOOP`, `RETURN`, calls to `print`. Source (`AstSupported`): integer literals, locals (also `<const>`), assignment to locals (also multiple), arithmetic, bitwise, comparison and logical operators, `print(…)` calls of the global `print`, `do`, `while`, `repeat`, `if`, numeric `for`, `break`, `goto` and labels |
| F2 | tables (the real `next` order) |
| F3 | closures, upvalues, calls, varargs, multret |
| F4 | strings, metatables |
| later | floats and `%.14g`, then coroutines and `longjmp`, and the GC last |

**Statements** (`Lua/Theorems.lean`):

```lean
def vm_refinement_Statement (Lay : VmLayout) : Prop :=
  ∀ p c, Supported p → VmLoaded Lay p (fillZero c) →
    (∀ out, BcSem binaryHost p out ↔ Halts c out 0) ∧
    (Diverges c → ¬ ∃ out, BcSem binaryHost p out)

def compile_refinement_Statement (Compiles : Chunk → Proto → Prop) : Prop :=
  ∀ s p, Compiles s p → AstSupported s →
    Supported p ∧ ∀ out, LuaSem binaryHost s out ↔ BcSem binaryHost p out

def endToEnd_lua_Statement (Lay : VmLayout) (Compiles : Chunk → Proto → Prop) : Prop :=
  ∀ s p c, Compiles s p → AstSupported s → VmLoaded Lay p (fillZero c) →
    (∀ out, LuaSem binaryHost s out ↔ Halts c out 0) ∧
    (Diverges c → ¬ ∃ out, LuaSem binaryHost s out)
```

**Proved.** Everything below uses only `propext`, `Classical.choice` and
`Quot.sound`, checked by `scripts/check.sh`.

* **Composition.**
  * `endToEnd_of_layers`: A ∧ B → end-to-end.
  * `vm_refinement_of_sim`: Layer A from the forward simulation `VmSim`, by
    the CompCert-style refinement pattern plus densification.
  * `compile_refinement_of_tv`: Layer B from `CompileTV`.
* **Layer B on a corpus** (`Lua/Compile/Corpus.lean`).
  * `compile_refinement_corpus`: `compile_refinement_Statement` for the host
    `luac -s` on `while.lua` (with `goto continue`), `f1_ops.lua`,
    `f1_src.lua` and `f1b_bits.lua`. Each has `AstSupported`, `Supported`,
    and `LuaSem` and `BcSem` of the ELF's output by kernel evaluation.
  * `luaRun_sound`/`execSound`: the source interpreter is sound for
    `LuaSem`; `LuaSem.deterministic`.
* **Semantics validated against the binary.**
  * `while_bcSem`, `f1Ops_bcSem`, `printPrint_bcSem`, `f1b_bcSem`: `BcSem`
    gives exactly the output the ELF prints on Sail.
  * These are kernel evaluation of a stepper proved sound for `Step`
    (`step?_sound`, `run_sound`). It is also complete (`step?_complete`), so
    `Step` and `BcSem` are deterministic (`Step.deterministic`,
    `BcSem.deterministic`).
* **Fragment check.**
  * `while_supported`, `f1Ops_supported` and `f1b_supported` hold.
  * `readsStale_unsupported`: a read of an unwritten register is rejected.
  * `ledger_exact`: the ledger is exactly the non-F1 opcodes.
  * The definite-initialisation check is sound (`Lua/FragmentSound.lean`):
    for a supported program, `BcSem` does not depend on the registers at
    entry (`bcSemFrom_iff`) or on what a call leaves above its results
    (`cbcSem_iff`).

**The runtime boundary** (`Lua/Vm/Runtime.lean`, PHASES.md A0.6).
`luaLayout`'s `luaRuntimeReady` is defined as named structures: the C stack
and return chain, `L->errorJmp`'s `jmp_buf`, newlib stdio and htif.c's file
system before their lazy initialisation, the dlmalloc heap, and the
`lua_State`/`CallInfo`/string-table invariants. `scripts/gen_lua_boot_witness.py`
traces `while.lua` and `f1_ops.lua` to `luaV_execute` (steps 181,166 and
181,079). It rebuilds the entry memory and checks natively that every field of
`VmEntryData` and `luaRuntimeReady` holds. This check found that `VmEntryData`
was unsatisfiable (a string's header tag); that is now fixed. The kernel boot
witness (`Lua/Vm/Boot/Witness/`, `vmLoaded_while_entry`, `vmLoaded_f1Ops_entry`)
proves `VmLoaded luaLayout` at both traced entries, one `decide +kernel` per
structure over the entry memory's byte view; the register file is a
hypothesis (`EntryRegs`).

**OS boundary.** ship-your-ocaml's OS spec (`tcb/`, SibylFS + CakeML) is
copied in; `Lua/Os/Htif.lean` states what `c/src/htif.c` must do to
implement it. Its in-image file system, which backs Lua's `io`/`os`, is
rejected on none of 6,490 generated traces and 26 console scripts
(`experiments/os/RESULTS.md`; PHASES.md, OS).

## Validation numbers (VALIDATION.md)

* **Toolchain.** xPack GCC 15.2.0 with newlib 4.5.0, the release that built
  the WHILE ELF. Flags are `rv64i`, `lp64`, `medany`, `-O2`. The `io`
  and `os` libraries run over an in-image file system in `htif.c` that
  follows the shared OS spec (`tcb/`), with a clock frozen at 0; GC stopped
  before any allocation through the API; a constant hash seed; output over
  HTIF.
* **`while.lua` on Sail.** It prints `55 2500 36` and exits 0 in **215,723
  steps**.
  * `luaV_execute` is entered at step **181,166**; the VM part is 34,557
    steps and 671 dispatched instructions.
  * The emulator runs at about 47k steps/s.
* **Difftest.** **18/18** programs across F1–F4, floats, pcall/error,
  coroutines and `io`/`os` agree with native `lua` built from the same
  source. They take 190k–2.6M Sail steps each.
* **Census of the ELF.**
  * The image is 980 functions and 80,690 instructions, against the WHILE
    ELF's 258 and 25,336.
  * 848 functions are statically reachable, and the difftests together
    execute 502.
  * Shared code: 203 functions are identical to the WHILE ELF modulo
    relocations (newlib, libgcc, dlmalloc, stdio, setjmp/longjmp). 101 of
    them are executed.
  * `luaV_execute` is 4,020 instructions with **one** dispatch `jr` over an
    82-entry jump table.
  * F1's 43 opcode arms total 2,239 instructions, of which 613 are on the
    integer fast paths.
  * New constructs: TValue tag dispatch (438 tag loads), 49 jump tables, 66
    indirect calls, and 575 soft-float call sites.

## Layout

| path | content |
|---|---|
| `vendor/lua-5.4.7/` | Lua 5.4.7, unmodified (MIT, `LICENSE`) |
| `c/` | bare-metal build: `Makefile`, `src/{main.c,baremetal.h,chunk.S,crt0.S,htif.c,link.ld}` |
| `c/lua-riscv-htif.elf` | the ELF, with sha256 in `lua-riscv-htif.elf.sha256` and embedded chunk `c/tests/while.luac` |
| `c/tests/` | `while.lua` (a port of WHILE's `while.wl`), the F1 validation programs (`f1_ops.lua`, `f1b_bits.lua`, `print_print.lua`), and `difftest/` with `difftest.sh` |
| `Lua/Bytecode/` | opcodes (generated from `lopcodes.h`), instruction decoding, `Proto`, **`BcSem`** (F1), and the sound stepper |
| `Lua/Fragment.lean`, `Lua/FragmentSound.lean` | `Supported`, the fragments, the ledger of unsupported opcodes, and the soundness of the definite-initialisation check |
| `Lua/Vm/` | struct layout (generated from the cross compiler), the image (generated from the ELF), representation predicates, `VmLoaded`, `luaLayout` (`Runtime.lean`, `DlHeap.lean`), and the binary's `Host` |
| `Lua/Vm/Boot/` | boot traces to `luaV_execute` (`Gen/`, generated by `gen_lua_boot_witness.py`), the loader-plus-store-log memory (`Image.lean`, `Log.lean`), view checkers (`View.lean`, `Heap.lean`, `Check.lean`), the assembly (`Assemble.lean`) and the generated kernel witnesses (`Witness/`) |
| `Lua/Ast/` | the complete Lua 5.4 syntax, **`LuaSem`** (rules for F1), `AstSupported`, the sound source interpreter, determinism |
| `Lua/Compile/` | translation validation (`ProgramTV`) and the corpus (`CorpusCompiles`, `compile_refinement_corpus`) |
| `Lua/Refinement.lean`, `Lua/Theorems.lean` | the refinement pattern and the three statements with their proved compositions |
| `Lua/Programs/` | generated `Proto`s of the test chunks, the validation theorems, and the `Supported` checks |
| `Vsa/`, `VsaIris/`, `riscv-lean/` | the machine layer copied from ship-your-interpreter: Sail model and ISA relation, densification, instruction-level simulation, decode table, libgcc/newlib sites, Iris machine WP, dlmalloc |
| `scripts/` | this repository's generators (`gen_opcodes.py`, `gen_lua_layout.py`, `gen_lua_image.py`, `gen_proto.py`, and `gen_ast.py`, the Lua 5.4 parser), `check.sh`, the discipline check; `scripts/syi/` holds the copied generator layer |
| `experiments/census/` | the disassembly census and its tools |
| `experiments/port/` | what was copied and the import edges still to cut |

## Building and checking

```sh
# toolchain: xPack riscv-none-elf-gcc 15.2.0-1 unpacked under ~/toolchains/
make -C c                 # host lua/luac, then the ELF with while.lua embedded
make -C c run             # run it on the Sail emulator (EMU=path/to/lean_riscv_emulator)
make -C c difftest        # 16 programs, native lua vs the ELF on Sail
lake build Lua            # the Lean scaffold (the copied layer builds with it)
scripts/check.sh          # drift, ELF hash, forbidden tokens, discipline, build, axioms
```

The emulator is `riscv-lean/lean_emulator` (`lake build lean_riscv_emulator`
in that directory). CLAUDE.md is the proof discipline.
