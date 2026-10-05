# Round-4 A1 bake-off, axis S: contender S-INC (the kit as it is)

S-INC closes the two held-out string cases on the kit of round 3, on top of
BASE-S, with no new abstraction: every loop is a hand induction on a measure,
every string fact is a hand lemma, and the budget is met by hand splits. The
base is `6defac8`; the branch head is the last commit on this worktree.

## Summary row

| setup | callees | held-out hand lines (EQ / LT) | generated | CPU | peak mem | largest decl heartbeats | refactor `sim_LOADNIL` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 94 Lean + 12 Python | 1,997 (EQ 492, LT 1,505) | 21 / 170 | +23,254 (0 by hand) | 215 s (new hand modules) + 142 s (new generated modules) | 2.43 GB | `lt_take` 183.6k | 47 → 47 (kept as is) | 1 `lake build`, ≈ 80 `lake env lean` | ≈ 2 h 20 min |

Lines are non-blank, non-comment lines; `--` lines and `/- … -/` blocks
(docstrings included) are dropped. Heartbeats are in thousands of
`maxHeartbeats` units, measured with `IO.getNumHeartbeats` around each
declaration in scratch copies with `Elab.async false`.

## What is proved

All built (`lake build Lua Vsa VsaIris`, 1576 jobs); axioms
`[propext, Classical.choice, Quot.sound]` for each, and `scripts/check.sh`
stage 6 lists them.

| theorem | file | statement |
|---|---|---|
| `Kit.sim_EQ` | `Kit/Eq.lean` | `SimArm .EQ` = `sim_EQ_of_long eq_long`, no premise |
| `Kit.eq_long` | `Kit/Eq.lean` | round 3's open premise: `OP_EQ` on two long strings |
| `Kit.sim_LT` | `Kit/LtStr.lean` | `SimArm .LT` = `sim_LT_of_str lt_str`, no premise |
| `Kit.lt_str` | `Kit/LtStr.lean` | `OP_LT` on two strings (split: `lt_pre`, `lt_take`, `lt_skip`) |
| `Kit.memcmp_sum` | `Kit/Memcmp.lean` | `a0 = 0` iff the `n` bytes agree (`MemEq`) |
| `Kit.eqlngstr_sum` | `Kit/Eqlngstr.lean` | `luaS_eqlngstr`: `a0 = (s1 = s2)` on two long strings |
| `Kit.equalobj_full` | `Kit/EqLong.lean` | `luaV_equalobj` on all F1 values (round 3's `equalobj_sum` plus the long path `eqo_long`) |
| `Kit.strcmp_sum` | `Kit/Strcmp.lean` | `strcmp`'s first event (`CmpAt`): equal non-`'\0'` prefix, then differing bytes or two `'\0'`s; `z = 0` iff equal there, `z < 0` iff `q1`'s byte is smaller, `|z| < 65536` |
| `Kit.strlen_sum` | `Kit/Strlen.lean` | `a0` is the index of the first `'\0'` (`LenAns`) |
| `Kit.lstrcmp_sum` | `Kit/Lstrcmp.lean` | `l_strcmp`: `z < 0` iff `lexLt s1 s2`, `|z| < 65536`, frame restored |
| `Core.strAt`, `Core.reg_strAt` | `Kit/StrAt.lean` | BASE-S's facts in live memory: a string register's object (`shrlen`, `lnglen`, bytes, terminator) as the callees read it |

Callee behaviour is proved, not assumed: `memcmp`, `luaS_eqlngstr`,
`strlen`, `strcmp` (and `strcoll` = `j strcmp`) and `l_strcmp` run on their
generated segments at the Lua ELF's addresses.

## The route

- **Generators.** `gen_lua_code.py` pins `luaS_eqlngstr`, `memcmp`, `strcoll`,
  `strcmp`, `strlen`; `gen_lua_arms.py` adds them and `l_strcmp` to `HELPERS`,
  and roots `luaV_equalobj`'s long-string arm (`0x8001b8f8`, formerly a stop).
  No generated arm changed (`gen_lua_arm.py --check` passes).
- **String facts (setup).** `StrAt` is BASE-S's `TStringRepr` moved to live
  memory (`Core.strAt`: `Core.str_frame` per byte, `StrOwned.heap` for the
  RAM bounds from `HeapAt`'s chunk walk). `StrAt.congr`/`StrAt.wm8` carry it
  through `savestate` and callee frames; `Core.longPair`, `Core.strAt_of`
  give the two string operands at a call.
- **Loops, by hand.** `memcmp`: the byte loop (rotated entry) and the word
  loop, each a `| 0 => absurd | n + 1 =>` recursion. `strcmp`: the byte loop,
  and the three-word unrolled loop as three step lemmas in
  continuation-passing form (`strcmp_w0` → `w1` → `w2` → the loop at `k + 24`).
  `strlen`: the alignment loop, the word loop. `l_strcmp`: the chunk loop
  (`ls_loop`, measure "bytes of `s1` left") with its body `ls_after`.
- **Word tricks.** The zero test `((x & M) + M) | x | M` is lane-wise:
  `add_append_nc` (no carry out of a byte lane) and one 256-case `decide` per
  association order (`lane_cmp`, `lane_len`). `strcmp`'s halfword exit is
  arithmetic over the eight bytes (`word_toNat`, `sum8_hw`, one `omega`).
- **`lexLt`.** `lexLt_skip` (a common prefix of `i` bytes); `chunk_ne`/`chunk_nul`
  connect `strcmp`'s first event to `lexLt` of the rests at chunk offset `k`.
- **Kit extensions** (`Kit/Run.lean`, +15): `kit_seg h acc seg` (one named
  segment, no polarity search) and `bool_goal` (a syntactic guard test for
  guard closers). The kit's pin matching is unchanged.

## Lines

| row | file | lines |
|---|---|---|
| setup | `Kit/StrAt.lean` | 78 |
| setup | `Kit/Run.lean` (`kit_seg`, `bool_goal`), `Kit.lean` | 16 |
| setup | `gen_lua_arms.py`, `gen_lua_code.py` (Python) | 12 |
| callee, EQ | `Kit/Memcmp.lean` (2 loops, `MemEq`, `memEq_word`) | 245 |
| callee, EQ | `Kit/Eqlngstr.lean` | 115 |
| callee, EQ | `Kit/EqLong.lean` (`eqo_long`, `equalobj_full`, `Core.longPair`) | 132 |
| callee, LT | `Kit/StrBits.lean` (zero test) | 88 |
| callee, LT | `Kit/Strcmp.lean` (byte loop, halfword exit ×4, word loop ×3, entry) | 613 |
| callee, LT | `Kit/Strlen.lean` (alignment loop, word loop, last word ×3) | 296 |
| callee, LT | `Kit/LexLt.lean`, `Kit/LsMath.lean` (`lexLt` math) | 151 |
| callee, LT | `Kit/Lstrcmp.lean` (loop, prologue, epilogue, frame reads) | 357 |
| held-out EQ | `Kit/Eq.lean`: lines touched (net +9) | 21 |
| held-out LT | `Kit/LtStr.lean` (arm-local helpers ≈ 70: `srliw_sign`, `guard_str15`, `Core.strAt_of`, `Core.rodata_of`, `lt_call`; paths ≈ 100) | 170 |

**Generated:** `Lua/Vm/Arms` +19,796 (15 files: sites and segments of the six
callees, the new `luaV_equalobj` root) and `Lua/Vm/Code` +3,458 (11 files).

## CPU, memory, heartbeats

`lake env lean` of each module alone (user CPU / wall / peak RSS) and the
largest declaration:

| module | user s | wall s | peak | largest declarations (k) |
|---|---|---|---|---|
| `StrAt` | 1.6 | 2.1 | 2.0 GB | `Core.strAt` 1.5 |
| `Memcmp` | 26.8 | 14.1 | 2.2 GB | `memcmp_words` 135.4, `memcmp_sum` 80.5 |
| `Eqlngstr` | 8.2 | 8.7 | 2.1 GB | `eqlngstr_sum` 82.3 |
| `EqLong` | 7.3 | 7.3 | 2.1 GB | `eqo_long` 62.7 |
| `Eq` | 26.0 | 15.7 | 2.4 GB | `eq_take` 158.0, `eq_skip` 125.8 |
| `StrBits` | 2.7 | 2.7 | 2.0 GB | `lane_cmp` 3.1 |
| `Strcmp` | 53.5 | 30.0 | 2.4 GB | `strcmp_w2` 89.2, `strcmp_w1` 65.1 |
| `Strlen` | 24.7 | 12.9 | 2.2 GB | `strlen_tail4` 60.5 |
| `LexLt` | 0.6 | 1.0 | 0.8 GB | `lexLt_skip` 0.8 |
| `LsMath` | 1.5 | 2.1 | 2.0 GB | `chunk_nul` 1.1 |
| `Lstrcmp` | 23.5 | 18.4 | 2.3 GB | `lstrcmp_sum` 74.3, `ls_after` 56.2 |
| `LtStr` | 39.0 | 28.3 | 2.4 GB | **`lt_take` 183.6**, `lt_pre` 130.7, `lt_skip` 110.4 |

The new generated modules (14: sites and segments) take 142 s user in all,
peak 2.2 GB (`Segs/Hstrcmp` 31.5 s). `lake build Lua.Vm.Sim.Kit` from the
cache: 1 min 46 s wall; the full `lake build Lua Vsa VsaIris`: 6 min 39 s
wall.

## Failed builds and wall time

- **One failed `lake build`** (`Lua.Vm.Sim.Kit`): an experimental change to
  `pins_of` (keep a load `bytesT8 m a` folded when unifying a pin) broke
  `Kit/Modk.lean`'s post half; reverted, and the string proofs do without it.
- **About 80 `lake env lean` runs with errors**: `strcmp` ≈ 25, `l_strcmp`
  ≈ 18, `strlen` ≈ 10, `luaS_eqlngstr` ≈ 7, `memcmp` ≈ 6, the LT arm ≈ 8,
  the rest ≈ 6.
- **Wall**: ≈ 2 h 20 min (EQ with its callees ≈ 25 min; `strcmp` ≈ 40 min;
  `strlen` ≈ 15 min; `l_strcmp` with its math ≈ 30 min; the LT arm ≈ 15 min;
  measurements, gate and this file ≈ 20 min).

## What the route could not express (or expressed only at a cost)

1. **The budget dictates the structure again (C-budget).** One declaration
   per path does not fit: `strcmp`'s halfword compare is four lemmas plus a
   shared exit (`strcmp_hw`), `strlen`'s last-word scan three, the word loop
   three continuation-passing steps; the LT arm is split by hand at
   `l_strcmp`'s return (`LtRet`, a hand-stated boundary state with the frame
   `headKF` and the memory `lsMem(saveMem …)`), and then its post half by
   exit (`lt_take`, `lt_skip`). Even so `lt_take` is at 183.6k of 200k: any
   widening of the relation or of `kit_cond` will push it over.
2. **The polarity search fails dangerously.** When `kit_run` tries the wrong
   polarity of a branch, the fallback closer (`kit_bv`'s `simp` over every
   fact) or a guard closer's `assumption` unfolds `bytesT8` loads and hits
   `maxRecDepth`, a runtime exception that `first` does not catch, so the
   search aborts instead of trying the other polarity. The cure was to name
   the polarity (`kit_seg`, used 55 times: `strlen` 30, `l_strcmp` 23,
   `strcmp` 2), to guard closers with `bool_goal`, and to use
   `with_reducible assumption`. Round 4's §2c finding (half a segment's
   cost is the search) shows up here as a correctness hazard, not only a
   cost.
3. **Value normal forms are fragile.** `pins_of` unifies through `whnfR`, which
   unfolds the reducible `bytesT8`, so a load can appear folded in one fact and
   unfolded in another; `omega` then sees two atoms (`strcmp_diff*` unfold
   every read uniformly before arithmetic). `simp … at h` also rewrites inside
   the memory term, so a lemma about the frame memory (`lsMem`) stops
   matching: `sign_extend 0#12` artefacts (`v + sext 0`) are carried through
   `lstrcmp_sum`'s post rather than normalised.
4. **Every loop is its own induction.** Seven hand loop inductions (the
   `| 0 => absurd | n + 1 =>` pattern with a hand invariant and measure),
   one per loop shape. None reuses another: `memcmp`'s word loop and
   `strcmp`'s word loop differ in exits and unrolling; the byte loops differ in
   rotation and exits. `strcmp`'s three-word unrolling needs a
   continuation-passing decomposition to fit the budget.
5. **String facts are re-derived at each use.** BASE-S gives ownership in the
   complement; each callee needs the live-memory form (`StrAt`), its transport
   through the arm's and the callee's own stores (`StrAt.congr`, `StrAt.wm8`,
   `StrAt.ls`), and RAM bounds for every load (`RamSpan`, with a word of slack
   for the word scans' reads past the terminator).
6. **Specifications stop at what the arm needed.** `lstrcmp_sum` states only
   `z < 0 ↔ lexLt s1 s2`; `OP_LE` (`slti a0, a0, 1`, i.e. `z ≤ 0`) needs also
   `z = 0 ↔ s1 = s2`. `strcmp_sum` has it per chunk (`CmpAt.zero`), so this is
   a further `lstrcmp` lemma (≈ 40 lines: the exits' `z` against
   `lexLt s2 s1`), not done. `OP_EQK` on two long strings needs only its
   `EqCtx`-style call to `equalobj_full` (≈ 15 lines), not done.

## Forecast (on this route)

- **VARARGPREP.** `luaT_adjustvarargs` (≈ 64 instructions) copies the fixed
  parameters with a slot-copy loop (`ld`/`sd` payload, `lbu`/`sb` tag, nil the
  source tag, `L->top` written) and moves `func`. On S-INC: one more hand
  loop induction over a memory-writing loop (unlike every loop here, which
  only reads), ≈ 120 lines for the summary, plus the re-witness of `w` with a
  new `func` and BASE-S's `Complement.own` re-proved for the moved window
  (chunk disjointness, ≈ 40 lines). Expect at least one hand split for the
  budget. ≈ 250 lines, 3–4 h.
- **CALL print.** Not reachable on this route alone: `luaD_precall` →
  `luaB_print` → `luaL_tolstring` → stdio is ≈ 81 functions with 93 loop back
  edges (§1b.2). S-INC's rate here was about 300 hand lines per string callee
  with one or two loops; at that rate the print chain is several thousand
  lines and weeks, and it also needs the runtime-shape post (heap, `L`,
  `ci`, new strings owned by fresh chunks, BASE-S's "what an arm that creates
  a string must do").
- **RETURN.** RETURN0/RETURN1's nil fill is a slot-store loop (a hand
  induction like `loadnil_loop`, ≈ 30 lines each); RETURN's `luaD_poscall`
  has a slot copy and a nil fill (two more inductions) and leaves through the
  `Final` clause rather than `SimArm`. ≈ 200 lines plus the `Final` statement
  work.

## Measurement notes

- Hand lines come from a comment-aware counter over each file at `HEAD`
  minus its `6defac8` version.
- The gate (`scripts/check.sh` stage 3c, `a1-kit-arm`) still fails (37 cases,
  first-quarter mean 3.3, last-quarter mean 11.2); every other stage passes
  (run with the gate made non-fatal in a scratch copy; `check: all stages OK`).
