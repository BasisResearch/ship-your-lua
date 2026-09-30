# L-C4 (value law) and L-C6 (arm store footprint): trace checks

Checking only; no theorem. Input for ROUND-3 §2.

## Laws

- **L-C4.** At every dispatch-head crossing of a real Sail run, decode the VM
  state from memory. That decoded state is the one `step?` predicts from the
  previous head crossing. The head is the step at `0x8001bfe8`
  (`lw s4,0(s11)`, checked against the ELF word `0x000daa03`).
  - Two forms were checked:
    - (i) *VmRel-lite*: iterate the model `S_{i+1} = step? S_i` from
      `State.init`. At every head, `S_i` and the decoded machine state `M_i`
      agree on the pc and the output. They also agree on every register the
      model defines: `S_i.regs j = some v ⇒ slot j decodes to v`.
    - (ii) *per step*: apply `step?` to `M_i` masked to `S_i`'s defined
      registers. The result agrees with `M_{i+1}` on the same observables.
  - Also checked: the word the `lw` loads equals `Proto.fetch pc`.
- **L-C6.** Consider the stores between two head crossings. Each one lands in
  one of two places:
  - the slot of a register in the def/kill ports of the edge the kernel takes
    (`decide? (kernelAt p) S_i`);
  - or `luaV_execute`'s own C frame `[sp, sp+176)`.

  Only callee-making steps may store elsewhere.

## Method

- **`lc4_trace.py`** does the machine side:
  - It patches each chunk into `c/lua-riscv-htif.elf`, reusing
    `gen_lua_boot_witness.patched_elf`.
  - It streams `lean_riscv_emulator --trace-all`. The trace is never stored.
  - It keeps a shadow memory: the PT_LOAD bytes, plus every store's landing
    bytes. As a self-check, every load's `pre` bytes are compared against the
    shadow memory.
  - At each head it decodes the machine state:
    - `func = ci->func` and `base = s9`, checking `base = func + 16`;
    - the closure, then the `Proto`, then `code` and `maxstacksize`;
    - pc = `(s11 − code)/4`;
    - every slot's `TValue`: the tag at +8 and the payload at +0. The
      encodings are: nil is `tag % 16 = 0`; the booleans are 1 and 17; int
      is 3; a string is tag 68/84, with the header variant 4/20, the
      `shrlen`/`lnglen` and the contents; `print` is `LUA_VLCF` at
      `luaB_print`;
    - the console bytes so far, from the rows' `O` suffix.
  - It classifies every store by region against the previous head's frame
    (L-C6). The regions are: slot, cframe, callee C stack, caller C stack,
    `CallInfo`, `lua_State`, other Lua stack, static, heap, `tohost`.
- **`LC4Check.lean.in`** runs the REAL `Lua.Bytecode.step?` with
  `binaryHost`, and `decide?`/`kernelAt` for the ports, over the decoded
  heads. It runs via `lake env lean` in the main checkout's build at the
  same commit, under `systemd-run --user --scope -p MemoryMax=30G`, with
  about 90 GB available. Each program takes 2–3 s.
- **No Python kernel was written.** The real Lean `step?` was used instead
  of option (a).
- **Rerun:** `abstractions/checks/round3/lc4_run.sh [prog …]`. The full
  suite takes about 2.5 min. The outputs are `lc4_trace.out` and
  `lc4_lean.out`.

## Results

**The replay self-check** held on every program: 0 of 372,411 traced loads
mismatched the shadow memory, and `base = ci->func + 16` held at every head
(0 exceptions).

| program | Sail steps | trace wall (s) | heads | L-C4 (i) checked / bad | (ii) checked / bad | fetch words bad | L-C6 slot ports checked / bad | ends at |
|---|---|---|---|---|---|---|---|---|
| while | 215,723 | 10.5 | 671 | 671 / 0 | 670 / 0 | 0 | 670 / 1 (VARARGPREP) | Final (RETURN) |
| f1_ops | 271,860 | 13.2 | 186 | 186 / 0 | 185 / 0 | 0 | 185 / 1 (VARARGPREP) | Final |
| f1b_bits | 320,764 | 15.8 | 220 | 220 / 0 | 219 / 0 | 0 | 219 / 1 (VARARGPREP) | Final |
| print_print | 188,129 | 7.1 | 8 | 8 / 0 | 7 / 0 | 0 | 7 / 1 (VARARGPREP) | Final |
| f1_src | 221,516 | 9.7 | 265 | 265 / 0 | 264 / 0 | 0 | 264 / 2 (VARARGPREP; CALL with stack realloc) | Final |
| f4_strlite, F1 prefix | 236,227 | 10.9 | 110 | 13 / 0 | 12 / 0 | 0 | 12 / 1 (VARARGPREP) | first non-F1: CONCAT, pc 12 |
| difftest/f1_arith | 317,386 | 11.8 | 374 | 16 / 0 | 15 / 0 (+1 boundary) | 0 | 15 / 1 (VARARGPREP) | no kernel: `GETTABUP _ENV.type`, pc 22 |
| difftest/f1_cond | 401,320 | 14.2 | 4,779 | 2 / 0 | 1 / 0 | 0 | 1 / 1 (VARARGPREP) | first non-F1: CLOSURE, pc 1 |
| difftest/f1_for | 210,874 | 10.3 | 119 | 52 / 0 | 51 / 0 | 0 | 51 / 1 (VARARGPREP) | first non-F1: SETTABUP, pc 29 |
| difftest/f1_while | (identical to `while`) | | | | | | | |
| **total within F1** (f1_while not counted) | | | | **1,433 / 0** | **1,424 / 0** | 0 | 1,424 / 10 | |
| f4_strlite, past F1 (the F4-lite kernels) | | | 110 | 110 / 0 | 109 / 0 | 0 | 109 / 1 | Final |

**Opcodes stepped within F1:** 45 of the 55 F1 opcodes, plus `RETURN` as the
final head. `CALL print` (33 steps) and `VARARGPREP` (5 steps) are checked
head to head.

- `CALL print` spans the whole `luaD_precall` → `luaB_print` → `fwrite` →
  HTIF call. Its output line equals `printLine binaryHost`.
- One `CALL` (f1_src, pc 145, 19 slots) reallocates the Lua stack (`func`
  moves from `0x8006f360` to `0x80073680`). (i) and (ii) still hold across
  it, because registers are decoded relative to `s9`/`ci->func`.
- **Not stepped in any F1 run:** ADDK, SUBK, RETURN0, RETURN1. LE and MMBIN,
  MMBINI and MMBINK are stepped only in f4_strlite past F1, with 0 bad there.

**L-C4: 0 counterexamples.** Two apparent failures were not counterexamples
of the law:

1. **A bug in the decoder, now fixed.** The first run gave 11 bad heads on
   f4_strlite. The decoder had compared the string header's `tt` with the
   `TValue` tag (68/84). The header holds the variant without the collectable
   bit (`gcShrStr = 4`, `gcLngStr = 20`), which `Repr.lean`'s
   `TStringRepr` already states correctly.
2. **A boundary, not a violation.** On f1_arith, `step?` is `none` at
   `GETTABUP _ENV.type`: the F1 kernel handles only `_ENV.print`. The
   machine continues. The law holds under its precondition: the pc's kernel
   steps (`Supported`).

**L-C6: store footprint per opcode** (summed over while, f1_ops, f1b_bits,
print_print and f1_src; the columns count stores):

| op | steps | slot | cframe | callee C stack | caller C stack | ci | L | other Lua stack | static | heap | tohost | slot store shapes (`r<j>+<off>/<width>`, in program order) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ADD, ADDI, SUB, BAND, BOR, BXOR, LOADI, UNM | 91 / 160 / 7 / 1 / 10 / 42 / 86 / 4 | 2 per step | | | | | | | | | | `sb` tag, then `sd` payload |
| MOVE, MUL, MULK, SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK, BNOT, LOADK | 32 / 19 / 12 / 3 / 4 / 16 / 46 / 22 / 1 / 1 / 3 / 6 | 2 per step | | | | | | | | | | `sd` payload, then `sb` tag |
| GETTABUP | 34 | 68 | 68 | | | | | | | | | `sb`, then `sd` (plus 2 spills to its own frame) |
| LOADTRUE, LOADFALSE, LFALSESKIP, NOT, LOADNIL | 9 / 4 / 3 / 2 / 5 | 1 per register | | | | | | | | | | `sb` tag only |
| TESTSET | 3 | 2 | | | | | | | | | | `sb`, `sd` (1 of 3 steps stores) |
| FORLOOP | 77 | 280 | | | | | | | | | | `r1+0/8 r3+8/1 r0+0/8 r3+0/8` ×70: payload-only count and index (`chgivalue`), then tag+payload of the control variable |
| MOD, IDIV, MODK, IDIVK | 1 / 1 / 127 / 3 | 2 per step | | | | 1 per step | 1 per step | | | | | `sd`, `sb`; **plus `ci->savedpc` and `L->top` (`Protect`)** |
| FORPREP | 13 | 50 | 38 | 26 | | 13 | 13 | | | | | `r2+8/1 r2+0/8 r0+0/8 r0+8/1` ×12; **plus `ci`/`L` (Protect), spills, a callee frame (`forprep` / `__udivdi3`)** |
| EQ, EQK | 1 / 2 | 0 | | 1 / 2 | | 1 / 0 | 1 / 0 | | | | | **callee frame (`luaV_equalobj`); EQ also `Protect`** |
| EQI, LTI, GTI, LEI, GEI, LT, JMP, TEST | 144 / 18 / 106 / 18 / 19 / 8 / 139 / 4 | 0 | | | | | | | | | | none |
| CALL (print) | 33 | 130 | | 18,108 | | 44 | 329 | 61 | 1,032 | 1,704 | 493 | the result and top slots, `sd`+`sb` pairs; one `r0+8/8 r0+0/8` 16-byte copy |
| VARARGPREP | 5 | 10 | | 5 | | 20 | 5 | | | | | `sd`, `sb`: the closure copied to the new `ci->func` |
| RETURN (final) | 5 | | | 5 | 260 | 10 | 35 | | 80 | 25 | 5 | the exit path |

**L-C6 violations:**

- *Non-callee steps storing outside the slot ports and the C frame:*
  - `Protect`'s `ci->savedpc` and `L->top`: MOD, MODK, IDIV, IDIVK,
    FORPREP and EQ, on every execution;
  - callee C-stack frames: EQ, EQK and FORPREP.

  These opcodes are all ones whose arms call a helper (`luaV_mod`/`idiv`,
  `luaV_equalobj`, `luaV_forprep`/`__udivdi3`). MUL's `__muldi3` is a leaf
  and stores nothing outside the slots.
- *Slot stores outside the edge's ports,* 10 in the Lean check:
  - 9 are VARARGPREP. Its only slot store, counted against the old frame's
    slot 0, is the closure copied to the new `ci->func` (= old `base`; `func`
    moves by +16).
  - 1 is f1_src's reallocating `CALL`. Its store "into old slot 0" is
    `free()`'s bookkeeping in the freed old stack block.

**Refinements (stated so that every observation satisfies them):**

- **L-C4.** Add the precondition "the kernel at pc steps" (`Supported`).
  Decode registers relative to `s9 = ci->func + 16` at each head, not a fixed
  base. This is already `VmRel`'s choice, and the check confirms it across
  `VARARGPREP` and a real stack reallocation.
- **L-C6′.** Between heads, the stores land in the three places below. The
  callee-making set is CALL, VARARGPREP, MOD, MODK, IDIV, IDIVK, FORPREP, EQ
  and EQK, plus by the census LE/LT on strings, UNM on strings and MUL/MULK's
  leaf.
  - (a) the slots of the edge's def/kill ports, taken relative to the frame
    *after* the step (`VARARGPREP`), and only while the old frame is live
    (a realloc frees it);
  - (b) `luaV_execute`'s C frame;
  - (c) only for the callee-making opcodes: `ci->savedpc` and `L->top`
    (`Protect`/`savepc`), plus the callee's C frame below `sp`. For CALL and
    VARARGPREP it can be anything. CALL alone reaches heap, static, stdio and
    `tohost`.
- **Store shapes.** Four shapes cover every non-CALL slot store:
  - `sb`+`sd` in either order;
  - `sb` alone (the tag-only stores);
  - FORLOOP's payload-only `sd`s.

  CALL adds one 16-byte (`sd`+`sd`) copy. Store order is layout data: the
  same kernel combinator (`opArith`) stores `sb`→`sd` for ADD/SUB and
  `sd`→`sb` for MUL/shifts.

## Files

The scripts and outputs are in `abstractions/checks/round3/`:

- `lc4_trace.py`: the trace and decoder, plus the L-C6 classification;
- `LC4Check.lean.in`: the Lean `step?` checker;
- `lc4_run.sh`: the driver;
- `lc4_trace.out`, `lc4_lean.out`: the outputs of the run;
- `lc4_work/` holds the heads and generated Lean files. It is git-ignored.
