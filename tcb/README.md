# Trusted computing base

Everything the headline theorems (`OCaml/Theorems.lean`) rely on without
proof, in one place. "Trusted" means: if it is wrong, a proved theorem can
say something false about the real system. Each entry names the Lean
object, where it comes from, how it is validated, and its status.

What is **not** trusted: the C runtime, newlib, libgcc, the cross compiler,
the host OCaml compiler, and every generator in `scripts/` (their outputs are
checked by Lean). The bytecode semantics `BcSem` is an intermediate
specification, with one exception: `EndToEnd` (`OCaml/EndToEnd.lean`)
takes the compile run of `boot/ocamlc` as a `BcSem` run (`BcRun Pc …`), so
there `BcSem` stands for the machine until `EndToEndMachine` replaces it
by Layer A.

## A. The OS interface (this directory)

| object | file | source |
|---|---|---|
| file system: state, path resolution, operations | `TCB/Os/Fs.lean` | SibylFS, `sibylfs/sibylfs_src` `30675bc`, Linux flavour, files and directories (ISC, `LICENSE-sibylfs`; sources in `upstream/sibylfs/`) |
| console streams, short reads and writes | `TCB/Os/Streams.lean` | CakeML basis `fsFFIScript.sml`, `CakeML/cakeml` `530c7de` (BSD-3, `LICENSE-cakeml`; `upstream/cakeml/`) |
| clock (monotone) | `TCB/Os/Clock.lean` | POSIX `CLOCK_MONOTONIC` |
| process: argv, environment, exit | `TCB/Os/Process.lean` | CakeML `clFFIScript.sml` (argv fixed) |
| **the specification** `next`, `OsStep`, `OsSpecial`; errno numbers | `TCB/Os/Syscall.lean`, `TCB/Os/Errno.lean` | SibylFS process level (`os_open` … `os_closedir`) |

`next s c r` is the list of states the OS may be in after call `c`
returned `r` in state `s` (nondeterminism: SibylFS's sets of allowed
errors, partial reads and writes, `readdir` order, whether `opendir` uses
a descriptor). The deviations from the two sources are marked
`DEVIATION 1-9` / `EXTENSION` in the Lean files, each justified by POSIX
or observed Linux behaviour (`validation/RESULTS.md`).

It is used in two ways, and it is **trusted only in the first**:

1. **On Linux**, system calls are `ecall`s into a kernel we do not verify.
   The assumption is that the kernel's behaviour on the calls in scope is
   allowed by `next`. Validated by traces: 6,490 generated scripts
   (101,621 calls) run on the host (Linux 7.0, ext4, glibc 2.43) and all
   accepted by the checker, 92 of them at a point the spec leaves
   unconstrained (`validation/RESULTS.md`). The checker is proved sound
   (`TCB.Os.checkTrace_sound`: every state it keeps is reachable by
   `OsStep`s with exactly the observed returns).
2. **On bare metal**, the "OS" is `c/src/htif.c`'s in-image file system,
   which is code in the ELF: that it implements `next` is a **proof
   obligation**, not trust. The same traces show it does not yet (it
   treats unknown descriptors as the console, has no directories, and
   reports a link count of 1 after `unlink`; `validation/RESULTS.md`
   §In-image), so that obligation needs those fixes first, or a restriction
   of the bare-metal instance to root-level files. The frozen bare-metal
   clock does meet the spec (`TCB.Os.Clock.frozen_ok`).

Scope limits (outside every statement that uses the spec): symlinks, hard
links, permissions and ownership, `truncate`, `pread`/`pwrite`, `chdir`,
`dup`, several processes, signals, sockets.

## B. The machine

| object | file | source | validation | status |
|---|---|---|---|---|
| the RISC-V ISA: `Vsa.Machine.Step` is the graph of one step of the Sail RV64 model (`stepOnce`); `Halts`, `Diverges`, `output` | `Vsa/Machine.lean`, `riscv-lean/Lean_RV64D*` | sail-riscv, generated to Lean (BSD-2, `riscv-lean/LICENCE-sail-riscv`) | ship-your-interpreter's review (the model against its emulator on a program corpus, `REVIEW2.md` §4 there); here: the ELF's output on the Sail emulator equals the host `ocamlrun`'s on 9/9 difftests (`VALIDATION.md`) | trusted |
| lean-sail, the Sail runtime library for Lean, as patched by ship-your-interpreter (`readByte` total, `getD 0`) | `riscv-lean/lean-sail/` | rems-project/lean-sail `0794631` + patches | as above | trusted |
| the HTIF convention: a store of `1<<56 \| 1<<48 \| c` to `tohost` prints `c`; `(e<<1)\|1` exits with `e` | the Sail model's HTIF device; `c/src/htif.c` | Spike / sail-riscv | every Sail run in `VALIDATION.md` | trusted |

## C. Tools

| object | status |
|---|---|
| the Lean 4 kernel (`lean-toolchain`: v4.34.0) and the standard axioms `propext`, `Classical.choice`, `Quot.sound` (checked by `scripts/check_all.sh` stages a3, t1) | trusted |
| iris-lean (`lake-manifest.json` rev `740e2c4`), for Layer B′ | trusted as a Lean library (its proofs are kernel-checked; its definitions of WP and adequacy are what "program logic" means) |
| the executable loader `OCaml/Bytecode/Load.lean` (`runbc`, generated program literals) | not in any statement: used only to validate `BcSem` and to generate `OCaml/Programs/WhileMin.lean`, whose theorem is about that literal |

## D. Hypotheses of the headline theorems

Not trusted facts but assumptions the theorems carry; they say which
programs and machine states a theorem is about, and each is discharged per
program or per phase.

| hypothesis | file | meaning | how it is discharged |
|---|---|---|---|
| `Loaded L P c` (`LoadedAt`) | `OCaml/Refinement.lean:81` | the machine is at `caml_interprete`'s entry with `P` in memory | boot witnesses for small programs (PHASES A0) |
| `Layout.runtimeOk` | `OCaml/Refinement.lean:46` | the collector's and allocator's own invariants at that point | a concrete instance, PHASES A0 (open) |
| `Good P` | `OCaml/Bytecode/Semantics.lean:739` | the run stays in the fragment and never reaches a state whose behaviour depends on what `BcSem` abstracts | per program; `runbc` checks it on runs, typing (Layer C) in general |
| `Fits B P` (`Budget`) | `OCaml/Refinement.lean:55` | the run fits the heap/stack budget (no collection needed: PLAN §GC G1) | per program, measured on Sail and by `runbc` |
| `parse` (trusted front end) | `OCaml/EndToEnd.lean` (parameter of every Layer C statement) | OCaml's parser and typechecker, producing the program `SourceSem` gives meaning to | trusted at first; per-program validation later (PLAN §5) |
| `SourceSem` (`OCamlSem`) | `OCaml/EndToEnd.lean:54` | the meaning of OCaml programs: the top-level specification | LLM-written, validated by running it against the host OCaml on the difftests (PHASES C1) |
| `Loader` | `OCaml/EndToEnd.lean:62` | how executable bytes become a loaded `Prog` | to be connected to `Loaded` (what `caml_main` does before the cut point) |
| `Bootstrap` | `OCaml/EndToEnd.lean:84` | the compiler's build command and sources | data, from the 4.14.4 build |
