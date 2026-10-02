# Abstraction discovery, round 4: the kit's hidden costs (A1)

Trigger: after round 3 adopted the kit, `a1-kit-arm` failed at 20 cases, with a flat ~3.7 hand lines per path (3.6 → 3.8). The line count is cheap, but four costs it does not measure blocked the lanes (`abstractions/ledger/kit-arms-{1,2}.md`). Kiran asked for this round on those four costs (2026-10-02). The shared machine is tight on memory, so builds are capped and agents staggered.

## 1. Census (from main at 3ae6bf6)

| cluster | instances | cost | blocked |
|---|---|---|---|
| **C-loop:** a machine loop over generated segments, proved by a hand-written induction on a measure | `muldi3_loop` (`Kit/Muldi3.lean:37`), `loadnil_loop` (`Kit/Loadnil.lean:51`), `__udivdi3`'s two loops (`Kit/Udivdi3.lean`, `termination_by`) | 20–60 lines each, plus an invariant per loop; Loadnil.lean is 100 lines for a 1-instruction-body loop | the shifts' `luaV_shiftl` loop-free? (check); every later loop (table traversal, `memcmp`, `strlen`) |
| **C-call:** the machine state at a helper's call and return, written out by hand | 14 uses over 6 arms (`AtRet`/`ArmPre`, `SegSt.call` frames). `modk_call` is 6 lines, 4 of them the frame. EQK's lines are mostly the `luaV_equalobj` frame | a frame statement per call site; FORPREP has two calls | FORPREP, IDIV/IDIVK (two helpers) |
| **C-budget:** a path split by hand to fit the default per-declaration heartbeat budget (200k) | MOD (5 paths), MODK (≈205k whole, split via `armBody_split`), FORPREP (does not fit, uncommitted `fp_pre`/`FpMem`). Disjunctive separation facts multiply `omega` cost by about 4 | the arm's structure is dictated by the budget, not the kernel; 557k heartbeats for one segment when a fallback unifies store chains | FORPREP |
| **C-str:** a register's string bytes, and the `'\0'` after them, are outside what `VmRel` relates | `sim_EQ_of_long`, `sim_EQK_of_long` (`memcmp` via `luaS_eqlngstr`), `sim_LT_of_str`, `sim_LE_of_str` (`l_strcmp` → `strcmp`/`strlen`/`strcoll`) | 4 named premises; UNM's numeric-string path is unprovable the same way | EQ, EQK, LT, LE, UNM; later CONCAT, LEN, every string library call |

Note: the copied layer already has `loopFromBody` (`DeriveLoop`, CLAUDE.md's "Loop" row). None of the three kit loops used it. The census must say why (a different state shape: `SegSt` against `Triple`?) before proposing a new loop rule.

## 1b. Census check (2026-10-02, base 3ae6bf6)

Every number here comes from the ELF, the generator or a Lean run, by the
scripts in `abstractions/checks/round4/` (their outputs sit beside them as
`*.out`). No `lake build` was run. Corrections to §1:

- **C-call is smaller than §1 says, and is caused by C-budget.** Only one
  frame in the kit is written by hand: `modk_call`'s 4-line `divFrame`. It is
  needed only because `ArmPre` must name the state at the split. Every other
  call site reads its frame off the pins: `hframe?`, `kframe?` or
  `⟨_, …⟩`. EQK's 16 lines are `EqCtx`: 9 address facts, the callee's
  *precondition*, not its frame.
- **C-loop has 3 inline arm loops, not 0.** They are `LOADNIL`, `RETURN0`
  and `RETURN1`, and all three are the same 3-instruction nil fill. FORPREP,
  IDIV/IDIVK, the shifts and UNM have none (§1b.1).
- **C-budget is a cost per load, not per path.** A segment costs between 6k
  and 42k heartbeats. The cost follows the loads through `savestate`'s
  stores, not the segment's length. It is additive across segments (§1b.3).

### 1b.1 C-loop: why the kit did not use `loopFromBody`

`loopFromBody` is `Triple.loop` itself: `∀ n, Triple (I ∧ B ∧ μ = n) (I ∧ μ < n)`
gives `Triple I (I ∧ ¬B)`. It does not fit the kit's loops in three ways.

1. **The exit is at the head, but the kit's loops test at the bottom.**
   - `muldi3_loop` has its head at `0x8002f6d0` and its latch `bnez a1` at
     `0x8002f6e4`. It exits to `0x8002f6e8`.
   - `loadnil_loop` has its head at `0x8001d2a8` (`addi; sb; bne`) and exits
     to `0x8001d2b4`.
   - `udiv_norm` exits in the middle of its body.
   - With `loopFromBody`, the guard must be stated at the head (`B` = "this
     iteration takes the back edge"), `I` must be `AtHead ∨ AtDone`, and one
     more iteration is run after the loop.
   - ship-your-interpreter's `Vsa/Sim/Muldi3Spec.lean` does exactly this
     (`LoopI`/`LoopB`/`LoopMu`, `loop_body`, `loop_to_done`). It takes about
     110 lines for the loop that `muldi3_loop` proves in 25.
2. **The state is a single `Config` predicate, while the kit's is a family of
   `SegSt`.** Each iteration has new pin *values* (`a0 a1 a2`, `X`) and a new
   memory (`nilMem M X k`). So `I` must be `∃ a0 a1 a2, SegSt … ∧ inv`, packed
   and unpacked on every iteration. The kit's runner (`kit_run`, `pins_of`)
   works on a concrete `SegSt` hypothesis, not under an `∃`.
3. **The measure is read off the machine, while the kit's is a ghost.**
   - `μ : Config → Nat` must read a register through `σ`, as `LoopMu` does
     with `x11`, and each loop needs a pin lemma to evaluate it.
   - The kit's measures are logical: `a1.toNat`, the slots left `k`
     (`X + 16k = E`), and `2^64 − a2`. The last two are not register values.

The kit's direct recursion on a `Nat` (the `| 0 => absurd | n+1 => …`
pattern) was cheaper than adapting the rule. The missing piece is a loop rule
stated over `SegSt` families with an exit anywhere in the body. That is
L4-loop, refined in §2b.

### 1b.2 C-loop: every loop the remaining arms and helpers meet

`loops.py` finds natural loops: back edges by DFS from the entry, with
`noreturn` calls cut. The address order of the code is not used, because
`luaV_execute`'s arms are scattered and a backward jump there is usually
layout, not a loop. The output is in `loops.out`, and `loops_print.out` for
the print chain.

| where | loops | shape (head → latch, exit, loop-carried state, stores) |
|---|---|---|
| arms FORPREP, IDIV, IDIVK, SHL, SHR, SHLI, SHRI, UNM, EQ, EQK, LT, LE, CALL, VARARGPREP, RETURN, BANDK/BORK/BXORK | **0** | `luaV_shiftl` is inlined and has no loop; FORPREP's count is one `__udivdi3` |
| arm LOADNIL `0x8001d2a8` | 1 | `addi a5,16; sb zero,-8(a5); bne a5,a4`: bottom test, pointer `a5`, one nil-tag store per iteration |
| arm RETURN0 `0x8001c2f4` | 1 | the same nil fill (`a3`, `sb zero,-8(a3)`) |
| arm RETURN1 `0x8001ed74` | 1 | the same nil fill, with the store before the bump (`sb zero,0(a4); addi a4,16; bne`) |
| `luaD_precall` `0x8000ab70`, `luaD_poscall` `0x8000a4a4` | 1 + 1 | the same nil fill (`sb zero,0(a5)` / `8(a5)`) |
| `luaD_poscall` `0x8000a464`, `luaT_adjustvarargs` `0x80019874` | 1 + 1 | slot copy: `ld`/`sd` the payload and `lbu`/`sb` the tag, with a bottom test; adjustvarargs also nils the source tag and writes `L->top` |
| `__muldi3` `0x8002f6d0` | 1 | done (`muldi3_loop`): registers `a0`–`a3`, bottom test |
| `__udivdi3` `0x8002f74c`, `0x8002f760` | 2 | done (`udiv_norm`, mid exit; `udiv_div`, bottom test) |
| `memcmp` `0x800361c0`, `0x800361dc` (via `luaS_eqlngstr`) | 2 | read-only. The word loop exits on a mismatch *into* the byte loop. The byte loop is rotated (entered by a `j` into the middle) and has two exits (a mismatch, or the count) |
| `strlen` | 2 | read-only word scan then byte scan, rotated |
| `strcmp` | 2 | read-only: an aligned 8-byte loop with 6 exits, and a byte loop with 2 exits |
| `l_strcmp` `0x8001a790` | 1 | the chunk loop over embedded `'\0'`s; calls `strcoll` (a `j strcmp`) and `strlen` twice per iteration |
| `luaV_tointeger`, `luaV_tonumber_`, `luaV_equalobj`, `luaS_eqlngstr`, `luaT_trybinTM` | 0 | UNM's numeric-string path leaves F1 through the string metatable's `__unm` → `luaO_str2num`, which has 4 loops |
| `luaF_close` (RETURN with `k`) | 2 (+7 in `luaF_closeupval`) | `tbc`/upvalue lists, linked-list walks with calls; outside F1 programs (no upvalues) |
| `CALL print`'s executed chain (81 functions, `round3/callee_groups.out`) | **93** back edges in 27 functions | 33 bottom-tested with a single exit. The bulk: `_svfprintf_r` 20, `luaC_step` 9, `__sfvwrite_r` 8, `_malloc_r` 8, `strchr` 6, `memcpy`/`memmove` 4 each |

Two patterns stand out. **One loop shape, the slot nil fill, occurs 5
times** (LOADNIL, RETURN0, RETURN1, `luaD_precall`, `luaD_poscall`). With the
slot copy (2 more), it covers every loop that the remaining F1 arms and their
runtime callees meet. **The string loops are all read-only scans** with
several exits, rotated, and chained loop to loop (`memcmp`, `strlen`,
`strcmp`).

### 1b.3 C-budget: what dominates

**Measured.** `ProfModk.lean` replays `modk_call` and `modk_rz`'s post half,
with `kit_div_pre`/`kit_div_post` expanded and a heartbeat log at every
segment boundary. Memory allowed it: 75 GB free; peak 2.2 GB under an 8 GB
cap. It also profiles by category (`set_option profiler true`).

| step (MODK general path) | instructions | heartbeats (k) |
|---|---|---|
| setup (`kitk_ints`: `kit_setup`, M1, the `K[C]` facts) | — | 4 |
| seg1 `dad0–db14`: `savestate`'s 2 `sd`, the `R[B]` tag `lbu` after them, `beq` | 17 | 32 |
| seg2 `e46c–e474`: `lbu` of `K[C]`'s tag through the 2 stores, `bne` | 2 | **38** |
| seg3 `e474–e478`: `j` | 1 | 6 |
| seg4 `f7a0–f7b0`: `ld` of `K[C]`'s payload through the 2 stores, `bgeu` on it | 4 | **42** |
| seg5 `f7b0–f7bc`: `ld` of `R[B]`'s payload, `mv`, `jal` | 3 | 10 |
| normalise (`slotVal_wm8`, `ld_slot_gen`) + call node (`moddi3_sum`) | — | 11 + 7 |
| **pre half (`ArmPre`)** | 27 | **151** |
| post: setup 5, two segments 9, to the head 14, close (`bleach_store` + `kit_frame`) **24** | 9 | **52** |

- **Additivity.** One declaration for the whole path (pre and post, one
  setup) logged 5, 135 (to the call), 153, 177 (at the head). The close then
  hit the 200k budget: `(deterministic) timeout at whnf`.
  - Pre + post − one setup = 198k. So the cost is additive in segments, and
    the split itself costs one more setup (≈ 5k).
  - Whole MODK misses the budget by about 1%. That is why the kit's
    structure follows the budget.
- **What a segment costs.** It follows the loads through the store chain and
  the guard on the loaded value, not the instruction count.
  - Two loads (seg2, seg4) are 80k of the 151k pre half.
  - A load with its guard costs about 15–20k. A straight-line `j` costs 6k.
  - So the budget holds about 10 guarded loads through `savestate`.
  - FORPREP's integer path reads `R[A]`, `R[A+1]` and `R[A+2]` (tags and
    payloads) after `savestate`, then calls twice. That is over budget,
    as the KIT-2 ledger found.
- **By category.** Cumulative times for the pre half alone:
  - tactic execution 7.8 s, of which `omega` is 4.7 s (**341 `omega` calls
    of 5 ms or more**, for 27 instructions);
  - type checking 3.7 s;
  - simp 2.1 s.

  Every `omega` comes from `kit_disch`, the runner's side-condition closer.
  That is about 12 slow `omega` runs per instruction: the same address-range
  and separation facts are re-proved for each read and each pin.
- **Answer.** Of the three candidates, **`kit_disch` repetition of
  `omega`** dominates: about 60% of tactic time.
  - The disjunctive separation facts multiply the cost of each run by about
    4. That is the KIT-1 measurement, and the reason `Ranges.k_*_wm8` exist.
  - whnf and type checking of the concrete memory terms come second (about
    a third). They are where the budget actually breaks: every failure seen
    is a `timeout at whnf` in a close or a fallback unification. The 557k
    segment is the extreme case.

### 1b.4 C-call: the hand frame against the generator's liveness

`lcall_frames.py` finds every call segment of the `SIM_OPS` arms in
`gen_lua_arms.py`'s output: a segment that ends in a `jal` to a `SUMMARISED`
helper. For each one it computes:
- `need`: the pins the generated segments at the return address demand
  (their `SegSt` pre-state after the liveness pass), minus the helper's
  results;
- `hand`: the registers of the kit's frame structure for that callee
  (`HFrame`, or `KFrame` + `sp`), parsed from `Kit/Run.lean`.

It also composes the frame *values* along every path from the arm's
jump-table target, by substituting each segment's post pins into the next
segment's pre pins.

| call sites | `hand = need` | `hand ⊋ need` (dead pins carried) | `need ⊄ hand` |
|---|---|---|---|
| 14 in 9 arms: EQ, EQK, MOD, MODK, MUL, MULK, IDIV ×2, IDIVK ×2, FORPREP ×4 | 8 | 6: `s10` at MUL/MULK and at IDIV/IDIVK's `__divdi3`; `s6`, `s10` at FORPREP's two `__udivdi3` | **0** |

What the composed values show:
- **The arm writes most frame registers, so the values are not the fetch-head
  values.**
  - `s6` (`R[A]`'s address) is written by the arm at every soft-int call.
  - `s10` is the divisor loaded through `savestate`'s stores (MOD, MODK).
  - FORPREP writes `s6`, `s10` and `s11`.
  - MUL/MULK write `s11 = pc + 2`, the `MMBIN` skip.
  - IDIV/IDIVK reuse **`s3` and `s4` as operand temporaries**: the payloads
    of `R[B]`/`R[C]`.
- **`divFrame` holds only because it takes `s3`/`s4`/`s10` as parameters.**
  Its doc comment ("the fetch-head registers, … `s3`, `s4`") is MOD-shaped,
  and an IDIV `ArmPre` must state loaded values there.
- **The composed values come out raw.** They are `bytesT8` through the
  `writeMap8` chain of both `savestate` stores. The kit's statements use the
  normalised form (`slotVal c.σ.mem (w.k + 16 * ins.c)`), which is
  `slotVal_wm8` / `Ranges.k_*_wm8` applied to the raw form.

## 2. Laws (to check before the fan-out)

- **L4-loop.** For a machine loop whose body is a chain of generated segments, an invariant `I k` over the segment state and a decreasing measure, the loop's run from `I n` reaches its exit with `I 0`. The rule is proved once over `SegSt`, and each loop supplies only `I` and the body's segment chain.
- **L4-call.** At every summarised call, the machine state is a function of the arm state at the call site: the caller's live pins and the frame. The generator's liveness pass already computes it. A call's frame is therefore *derivable*, never stated by hand.
- **L4-split.** Provability of a path is compositional at segment boundaries. A path splits at any boundary whose state is the segment's own postcondition, at no extra statement cost, so the heartbeat budget dictates nothing about the proof's structure.
- **L4-str.** No F1 arm store lands in a string object's bytes or its terminator. Every arm writes only `Win ∪ Scratch`, and string objects are heap chunks disjoint from both. A string's content in memory is therefore invariant along an F1 run once it is so at entry (boot witness: `TStringRepr` plus the terminator).

## 2b. Law checks (2026-10-02)

### L4-loop: **refined**

As stated (one rule over `SegSt`; each loop supplies `I` and the body's
segment chain), the law holds for every loop in §1b.2. But "`I n` reaches
the exit with `I 0`" assumes a single bottom exit and a numeric index. The
string loops break both: `memcmp`, `strlen` and `strcmp` have 2 to 6 exits
and are entered in the middle, and `memcmp`'s word loop exits into its byte
loop. `udiv_norm` exits mid-body.

**L4-loop′.** Let a loop have a state type `α`, a pin family
`pins : α → List Pin` and a memory `mem : α → Mem` at its DFS head `h` (the
entry; this covers the rotated loops), and an invariant `I : α → Prop` with a
measure `μ : α → Nat`. If one pass of the body satisfies

    ∀ a, I a → Triple (SegSt h (pins a) (P (mem a)))
      (fun c => (∃ a', I a' ∧ μ a' < μ a ∧ SegSt h (pins a') (P (mem a')) c) ∨ X a c)

then `∀ a, I a → Triple (SegSt h (pins a) (P (mem a))) (fun c => ∃ a', X a' c)`.

- The exit post `X` is a disjunction over the exits. A loop that exits into
  another loop composes as `Triple.seq` on `X`.
- This is `Triple.loop` with `I := ∃ a, I a ∧ SegSt …`, proved once. The
  kit's `| 0 => absurd | n+1 => …` recursion (5–6 lines per loop) is gone.
- What is left per loop is `I`, `μ` and the body's arithmetic, about 15 of
  `loadnil_loop`'s 25 lines.

Most of the remaining cost is in the loop shapes, not in the loop rule. **The
slot nil fill occurs 5 times, and the slot copy twice.** So L4-loop′ should
ship with one *parametric* nil-fill summary, over the head pc, the pointer
and end registers, and the store offset (−8 or 0, store before or after the
bump), and one slot-copy summary. They would be instantiated from the
generator's segment names, as `loadnil_loop` is today but once for all.

The read-only scans (`memcmp`, `strlen`, `strcmp`) are a third shape: the
`X` of each exit is a fact about a byte prefix (`BytesAt`), and memory is
unchanged.

### L4-call: **holds for the register set; refined for the values and for where the frame is needed**

- **Registers.** At all 14 call sites, the generator's live set at the return
  address is covered by the kit's frame, so nothing is missing (§1b.4). At 8
  sites it is exactly the frame. At the other 6, `HFrame` carries 1–2 dead
  callee-saved registers. That is harmless: the helper segments keep them,
  because `HELPERS` lists `s6` and `s10` as caller temporaries.
- **Values.** The values are a function of the arm state, as the law says:
  the composition of the path's segment post-pins, which `lcall_frames.py`
  computes mechanically.
  - But they come out raw (`bytesT8 (writeMap8 (writeMap8 m0 …) …)`). They
    are not the fetch-head pins either: IDIV reuses `s3` and `s4`.
  - So a generated frame must pass through the kit's read-through
    normaliser (`slotVal_wm8`, `Ranges.k_*_wm8`) to reach the form the arm
    proofs state.
- **Where a frame is stated at all.** A call site with the frame left as a
  hole (`hframe?`) costs 0 frame lines today. The hand frame appears only
  where a path is split (`ArmPre`/`AtRet`). The call-site cost that remains
  is the callee's *precondition* (`EqCtx`, 9 address facts), not its frame.

**L4-call′.** At a summarised call, the frame register set is the
generator's live set at the return address, and its values are the composed
post-pins of the path, normalised by the kit's read lemmas. A frame must be
written only at a split point, so the generator can emit it as the `AtRet`
state of that boundary. The callee's address preconditions (`EqCtx`) are a
separate cost: `Ranges` facts that one `kit_disch` closes per field.

### L4-split: **refined (cost: holds; statement cost: false as stated)**

- **Cost.** It is additive in segments. One declaration for the whole MODK
  path costs pre + post − one setup (198k against 151k + 52k). A split costs
  one more setup (about 5k heartbeats) and nothing else (§1b.3).
- **Statement.** The split is not free. The boundary state must be stated:
  `AtRet` with `divFrame` (4 lines in `modk_call`). The law's "the segment's
  own postcondition" is the *raw* generated `SegSt`, whose memory is the
  `writeMap8` chain and whose pins are raw loads. The `ArmPost` half cannot
  take that state as it is. It needs the normalised `slotVal` form to apply
  `imodC_eq` and close with `bleach_store`.

**L4-split′.** A path may be split at any segment boundary at about one
setup's heartbeats (≈ 5k). Its statement cost is zero exactly when the
boundary state is emitted: the generated pins and memory, put through the
normaliser of L4-call′. Then the budget dictates where the generator cuts,
not what the proof says.

Per-segment cost is 6–42k heartbeats, set by the loads through the store
chain. So the cut can be placed mechanically: cut before the running sum
passes about 150k.

### L4-str: **holds on every trace, for the bytes and the terminator; refined for the header**

**Method.** `lstr_trace.py` uses the round-3 L-C4 trace tooling with a
shadow memory; every traced load is checked, and there are 0 mismatches.
At each dispatch head it collects the strings reachable from `R[0..maxstacksize)`
and from `K`, and watches:
- each one's header `[ts, ts+24)`;
- its contents plus terminator `[ts+24, ts+24+len]`.

Every store until the next head is checked against both. Strings created
during a step are expected writes. As a control, the script counts them
separately: stores in an interval into strings that become reachable only at
the next head.

| programs | heads | strings watched | stores into bytes or terminator | header stores | terminator ≠ 0 | overlap with Lua stack / C frame / C stack / `L` / `ci` |
|---|---|---|---|---|---|---|
| `f4_strlite`, `print_print`, `f1_src`; difftest `f4_strings`, `f1_arith`, `f4_objects`, `f2_tablelib`, `f4_metatables`, `f1_cond` | 6,254 | 249 | **0** | 0 | 0 | 0 |
| `progs/l4str_fullgc.lua` (two `collectgarbage()`, 2 long strings, long `==`/`<`) | 31 | 15 (2 long) | **0** | 41: CALL (GC) `reallymarkobject`/`sweepstep` at `+9` (`marked`), `sweepstep` at `+0` (`next`) | 0 | 0 |
| `progs/l4str_gc.lua` (3,000 `CONCAT`s, string-table resize) | 21,122 | 6,011 | **0** | 35: CONCAT `tablerehash` at `+16` (`u.hnext` of short strings) | 0 | 0 |

- **Controls.** These fired, so the detector works. Creation stores:
  `internshrstr`, `luaC_newobj` and `memcpy` under CONCAT (e.g. 30,000,
  18,000 and 24,786 in `l4str_gc`) and under CALL (`tostring` of integers in
  `print`). These are the expected CONCAT/`luaS_newlstr` writes. None of
  them hit a string reachable at the step's head.
- **No F1 opcode stored into any byte of a reachable string object**, header
  included. Every header store happens in a CALL or CONCAT step.
- **The terminator.** It was `'\0'` for every one of the 6,275 strings at
  first sight. It is in the boot view:
  - `TStringRepr` (`Lua/Vm/Repr.lean:52`) has the terminator conjunct;
  - `gen_lua_boot_witness.py`'s `check_tstring` checks `rd(c + n, 1) == 0`
    for every boot-reachable string.
- **Disjointness.** No reachable string overlapped the Lua stack, the C
  frame, the C stack, `L` or `ci`. So the relation widening of KIT.md's
  obstruction 1 (a register's string lies outside `Win`) holds on every
  trace.

**L4-str′.** For each step from a dispatch head, no store lands in the
`TStringRepr` footprint of a string reachable at that head. The footprint is
`tt` at +8, `shrlen` at +11 or `lnglen` at +16..23, the contents, and the
terminator. Such strings are disjoint from `Win ∪ Scratch` and from the C
stack.
- For an F1 step, no store lands anywhere in the object.
- CALL (through GC) and CONCAT (through `luaS_resize`) may write header
  bytes outside the footprint: `next` +0, `marked` +9, and a short string's
  `hnext` +16.

So `TStringRepr mo ts s` transfers along any F1 run unchanged, and along
CALL/CONCAT through a footprint-frame lemma.

**Not exercised:**
- a long string used as a table key (`luaS_hashlongstr` writes `hash` +12
  and `extra` +10, which are outside the footprint);
- a GC cycle that frees a string while it is reachable. That cannot happen
  by GC's own invariant, and no trace showed it.

### Verdicts

| law | verdict | the refined law |
|---|---|---|
| L4-loop | refined | L4-loop′: a `SegSt`-family rule with a disjunctive exit post (bottom, middle or rotated loops; loop-to-loop by `seq`), plus two parametric summaries for the shapes that recur (slot nil fill ×5, slot copy ×2) |
| L4-call | holds for registers (14/14 covered, 8/14 exact); refined for values | L4-call′: the frame is generated (live set + composed post-pins), normalised by the kit's read lemmas; it is stated only at split points; callee preconditions are a separate `Ranges` cost |
| L4-split | refined: additive cost holds, free statement does not | L4-split′: splitting costs about 5k heartbeats; the statement is free exactly when the boundary state is generated (L4-call′); cut where the running per-segment sum (6–42k, driven by loads through stores) nears the budget |
| L4-str | holds (bytes and terminator, every trace); refined for headers | L4-str′: `TStringRepr`'s footprint of every head-reachable string is untouched by every step; F1 steps touch no byte of the object; GC and the string table touch only `next`/`marked`/`hnext` |

## 2c. Falsifier: a region-tagged write log for loads through `savestate` (2026-10-02)

**Claim.** If a path's memory is a region-tagged write log, a guarded load
through `savestate`'s two stores costs under 10k heartbeats (likely 1–3k),
against 15–20k on the kit route (§1b.3). Measurement only; nothing adopted.

**Built** (`abstractions/checks/round4/RegionLog.lean`, not imported by `Lua`;
`lake env lean abstractions/checks/round4/RegionLog.lean`, 24 s, under 8 GB):
- `Rgn` (slots, `K`, `ci->u.l.savedpc`, `L->top`, the C frame), `Ent`,
  `applyLog`, the Boolean forwarder `fwd` (region tags first, then offsets)
  and `fwd_sound`, with `rl_load1`/`rl_load8`;
- `rsep_of_ranges`: the regions pairwise disjoint, once, from `Ranges`;
- `saveMem_log`: `savestate`'s memory is the two-entry log `saveLog`, once
  for every path;
- `kslot_addr` (`K[C]`'s address as the arm computes it is
  `k + (16·C + j)`), `kArr_ram` (the `K` region is RAM, apart from
  `tohost`: the segments' bus checks), `ktag_eq`, `kval_eq8`.

A load is then one `rw` of `rl_load*` whose `fwd` premise is `rfl`, with no
`omega` and no `simp`. Axioms of `fwd_sound`, `rsep_of_ranges`, `saveMem_log`,
`pre_rl`, `pre_rlk` and `modk_rz_one` are `[propext, Classical.choice, Quot.sound]`.

**Measured** (thousands of heartbeats, deltas within one declaration, all in
the same file). MODK's general pre half is run four ways, differing only at
seg2 (`lbu` of `K[C]`'s tag and `bne`) and seg4 (`ld` of `K[C]`'s payload and
`bgeu`):

| | seg2 | seg4 | pre half |
|---|---|---|---|
| `pre_kit`: the kit's `kit_run` (= ProfModk) | 38.3 | 42.3 | 150.8 |
| `pre_kitd`: segment applied directly (polarity named), side conditions by `kit_side`, `kit_norm` | 23.3 | 24.0 | 117.4 |
| `pre_rl`: segment applied directly, side conditions by the region log | **6.6** | **6.4** | **83.6** |
| `pre_rlk`: the region log as `kit_side_pre`/`kit_norm` rules inside `kit_run` | 14.3 | 16.5 | 103.2 |

Per load, that is the bus checks `lo`/`hi`/`ht`, the guard and the
normalisation of the loaded pin:

| | `lo` | `hi` | `ht` | guard | normalise | **load** | segment application + `pins_of` |
|---|---|---|---|---|---|---|---|
| kit, tag (seg2) | 1.0 | 1.2 | 0.9 | 8.1 | 5.7 | **16.9** | 6.3 |
| kit, payload (seg4) | 1.0 | 1.3 | 0.9 | 9.1 | 5.9 | **18.2** | 5.7 |
| region log, tag (seg2) | 0.04 | 0.04 | 0.04 | 0.06 | — (dead pin) | **0.18** | 6.4 |
| region log, payload (seg4) | 0.04 | 0.04 | 0.04 | 0.09 | 0.32 | **0.53** | 5.8 |

The one-time costs are: the region facts per arm (`rsep_of_ranges`,
`saveMem_log`, two bounds) 1.0k; the library file elaborates in about 2 s.

**One declaration.** `modk_rz_one` is MODK's general path (`x % y = 0`):
`pre_rl`'s run to `__moddi3`'s return, then `modk_rz`'s post half
(`kit_div_post`: two segments, to the head, `kit_div_close`) in ONE theorem
under the default 200k budget. It builds at **138.8k**:
- setup 4.3, region setup 1.0, seg1 32.8, seg2 6.6, seg3 6.3, seg4 6.4;
- seg5 10.1, normalise 9.7, call node 6.8, `AtRet` repin 5.8;
- post 9.1 + 14.9, close 25.1.

The kit's single declaration hit the budget at its close (≈ 201k, §1b.3).

**Verdict: holds, with the measurement.** A guarded load through `savestate`
drops from 16.9–18.2k to 0.18–0.53k, below the predicted 1–3k. A segment
holding such a load drops from 38–42k to 6.4–6.6k. What is left is the
segment's own application (≈ 6k, independent of loads). MODK's whole general
path then fits one declaration with 61k to spare, so `armBody_split` is no
longer forced for MODK.

Refinements the numbers force:
- **Half of the kit's segment cost is its polarity search, not the load.**
  `kit_run` elaborates the wrong branch polarity's guard and fails slowly
  (38.3 → 23.3 by naming the polarity). With the region log as a
  `kit_side_pre` rule the search stays (14.3 / 16.5). A route should pick
  the polarity by evaluating the guard (here one `decide`), not by trying
  closers.
- **Only cross-region reads were tested.** `fwd` reduces by `rfl` because the
  tags differ, and the offsets (`16·C + j`, symbolic) are never compared. A
  same-region read after a store at a symbolic offset (`R[A]` after a slot
  store) needs `fwd`'s offset test decided over symbolic offsets. That is
  not measured.
- **The address normaliser is the other half of the abstraction.**
  `kslot_addr` maps the arm's `BitVec` address to `region + offset` once;
  without it each read re-proves the field arithmetic.
- **Next loads.** The next costs on the path are also loads through
  `savestate`: seg1's `lbu` of `R[B]`'s tag (32.8k, a `slots`-region read)
  and seg5/normalise's `R[B]` payload (19.8k). Then comes the close (25.1k).
