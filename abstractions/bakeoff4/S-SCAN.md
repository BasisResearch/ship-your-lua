# Round-4 bake-off, axis S: contender S-SCAN

Base: BASE-S (`6defac8`). Both held-out cases are closed with no premise:

- `Lua.Vm.Sim.Kit.sim_EQ : SimArm .EQ` (`Kit/EqLong.lean`), which closes `sim_EQ_of_long`;
- `Lua.Vm.Sim.Kit.sim_LT : SimArm .LT` (`Kit/LtStr.lean`), which closes `sim_LT_of_str`.

The callee behaviour is proved, not assumed: `memcmp_sum`, `eqlngstr_sum`,
`strcmp_sum`, `strlen_sum` and `lstrcmp_sum`. `strcoll` is a one-segment
`j strcmp`. The refactor case `sim_LOADNIL` now runs on `seg_loop` with a
comprehension log entry.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
`check.sh` stage 6 lists 21 new lines.

## Summary row

| setup | callees | held-out hand lines (per case) | generated | CPU | peak mem | largest decl heartbeats | refactor (before → after) | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 461 | 1,347 | EQ 39 · LT 111 | 23,254 Lean (+14 Python) | 290 s user (13 new modules) | 2.66 GB (`LstrcmpPro`) | `lt_str_take` 200.3k (at the budget); next `eq_long` 175.1k, `lstrcmp_LL` 164.1k | LOADNIL 47 → 47 arm lines; Multi −21 (`nilMem`) | 0 `lake build`; ≈ 90 `lake env lean` iterations with errors | ≈ 2 h 20 min |

**How lines were counted.** A hand line is a line that is not blank and not
a comment; `--` comments and `/- … -/` blocks, docstrings included, are
dropped. Each file's import, `open` and `namespace` lines are counted too.
The per-case counts come from the per-declaration tally.

### Library setup (461)

| file | lines | content |
|---|---|---|
| `Kit/Scan.lean` | 149 | M-loop `seg_loop`; M-scan `scan_loop`, `relay`; comprehension entries `compMem`, `compMem_out`, `compMem_in`; `append_inj'`, `bytesT8_eq_iff`, `zext8_beq`, `subw_bytes_ne`; tactics `guard_assumption`, `bool_goal`, `kit_seg` |
| `Kit/Str.lean` | 145 | M-str: `StrFoot` (the footprint per variant), `StrView`, `TStringRepr.view`, `StrView.frame/wm8/agree`, `StrApart`, `ChunkWalk.bound`, `Complement.own_bounds`, `Ranges.own_apart`, `Core.unseal`, `Core.str_at`, `StrView.eq_iff`, `lnglen_eq` |
| `Kit/Word.lean` | 167 | lanes: `and_app`, `or_app`, `add_app` (no carry), `lane_hz` and `lane_noovf` (each one 256-case `decide`), `hzW_lanes`, `hzW_bytes`; byte atoms `bytesT8_toNat`, `wordAt`; halfword atoms `hw0..3_toNat`, `shl48/32/16_eq`; `CmpObs`, `cmpObs_sub` |

### Callees (1,347)

| callee | file | lines |
|---|---|---|
| `memcmp` (word loop, rotated byte loop, relay) | `Kit/Memcmp.lean` | 221 |
| `luaS_eqlngstr` | `Kit/Lngstr.lean` | 118 |
| `luaV_equalobj`, long-string arm (`eqo_long`, `eq_jump_lng`, `LngPair`, `Core.lng_pair`) | `Kit/EqLong.lean` (callee part) | 78 |
| `strcmp` (byte loop, 3-way unrolled word loop, 4 halfword exits) | `Kit/Strcmp.lean` | 434 |
| `strlen` (byte scan, word scan, 8 lane exits) | `Kit/Strlen.lean` | 245 |
| `l_strcmp` (chunk loop, both call sites, epilogue) | `Kit/Lstrcmp.lean` | 266 |
| `l_strcmp`'s prologue (4 variants) and `lstrcmp_sum` | `Kit/LstrcmpPro.lean` | 104 |
| `lexLt` against the chunks (`Agree`, `lexLt_of_diff`, `lexLt_of_zero`) | `Kit/Lex.lean` | 81 |

### Held-out arms

- **EQ: 39 lines.** `eq_long` 25, `sim_EQ` 1, local runner rules 13 (`kit_bv_norm`, `kit_norm` and `kit_frame` through `luaV_equalobj`'s output memory).
- **LT: 111 lines.**
  - The path prefix (`lt_str_call` macro) is 31.
  - `lt_str_take` 18, `lt_str_skip` 11, `lt_str` 7, `sim_LT` 1.
  - Local rules 20.
  - The string-tag and `srliw 31` lemmas are 22.
  - `kit_cond` could not be used: both exits in one declaration exceed the budget (see "What the route could not express"). So the two `docondjump` exits are written out, about 25 of the 111 lines.

### Generated

- Helper segments and site batteries for `luaS_eqlngstr`, `memcmp`, `l_strcmp`, `strcoll`, `strcmp` and `strlen`: 136 segments.
- Code pins (`Lua/Vm/Code/{LuaS_eqlngstr,Memcmp,Strcoll,Strcmp,Strlen}`).
- `luaV_equalobj`'s new root `0x8001b8f8`.
- Total: +23,254 lines over 26 files.
- Python changes:
  - `gen_lua_arms.py`: 6 `HELPERS` entries, `RESULTS`, `SUMMARISED += l_strcmp`, and the long-string root moved from the stops.
  - `gen_lua_code.py`: 5 `EXTRA` entries.
- `gen_lua_arms.py --check` passes (check.sh stage 1).

### Refactor: `sim_LOADNIL`

| | before | after |
|---|---|---|
| loop | `loadnil_loop` 25 (a hand `\| 0 => absurd \| k+1 =>` recursion) | `nilSt` 4 + `loadnil_loop` 19 (`seg_loop` by the iteration count) |
| close | `sim_LOADNIL` 22 | `sim_LOADNIL` 24 (`compMem_out`/`compMem_in` instead of `nilMem_out`/`nilMem_tag`) |
| library | `nilMem`, `nilMem_out`, `nilMem_tag` (Multi, 21, LOADNIL-specific) | `compMem`, `compMem_out`, `compMem_in` (Scan, 18, generic: any stride, stride 0 allowed) |

- The arm itself stays at 47 lines. The measure recursion is gone.
- The memory is now a reusable comprehension entry. It serves the other nil fills (RETURN0, RETURN1, `luaD_precall`, `luaD_poscall`) unchanged. `nilMem` served only LOADNIL.

## CPU and peak memory per module

Each module was checked with `lake env lean` alone (user CPU s / wall / peak RSS):

| module | user s | wall | peak |
|---|---|---|---|
| Scan | 1.9 | 0:02 | 1.90 GB |
| Str | 1.8 | 0:02 | 1.89 GB |
| Word | 5.5 | 0:04 | 1.96 GB |
| Lex | 1.4 | 0:02 | 1.88 GB |
| Memcmp | 18.5 | 0:15 | 2.05 GB |
| Lngstr | 7.4 | 0:08 | 1.98 GB |
| EqLong | 23.3 | 0:22 | 2.30 GB |
| Strcmp | 56.7 | 0:27 | 2.34 GB |
| Strlen | 53.0 | 0:23 | 2.27 GB |
| Lstrcmp | 15.7 | 0:13 | 2.07 GB |
| LstrcmpPro | 62.1 | 0:33 | 2.66 GB |
| LtStr | 36.8 | 0:22 | 2.51 GB |
| Loadnil | 7.1 | 0:05 | 2.07 GB |

The full `lake build Lua Vsa VsaIris` (1,577 jobs) rebuilt every kit module after the `Multi`/`Arms` changes:

- 930 s user;
- 4 min 9 s wall;
- 3.08 GB peak.

## Heartbeats

**Method.** `IO.getNumHeartbeats` was read around each declaration, with `Elab.async false`, in scratch copies of the files. The figures are in units of `maxHeartbeats`; the budget is 200k.

| declaration | heartbeats (k) |
|---|---|
| `lt_str_take` | 200.3 |
| `eq_long` | 175.1 |
| `lstrcmp_LL` | 164.1 |
| `lt_str_skip` | 148.4 |
| `lstrcmp_LS` / `_SL` / `_SS` | 111.9 / 102.5 / 80.1 |
| `strcmp_w2` / `_w1` / `_w0` | 88.3 / 81.8 / 79.1 |
| `memcmp_words` | 81.7 |
| `eqlngstr_sum` | 70.5 |
| `lstrcmp_mid` | 68.4 |
| the `strlen` lanes | ≤ 65.4 |
| `eqo_long` | 63.6 |
| `sim_LOADNIL` | 33.7 |
| `loadnil_loop` | 26.8 |

- `lt_str_take` sits at the budget. It builds under the default limit in `lake build`; the measurement with `async false` includes the wrapper.
- `eq_long` and `lt_str_*` are heavy because of the arm half, not the callee half. They pay for the path to the call through `savestate` (§1b.3's loads through stores), the call node's context (strings unsealed through the stores), and the `docondjump` exit.

## The route, as built

- **M-str** (`Kit/Str.lean`). `TStringRepr`'s read list per variant gives the footprint `StrFoot`. For a long string, `lnglen` at `+16..23` is in the footprint; for a short string, `+16` is `hnext` and is not.
  - `Core.unseal` moves the complement's partial facts to total reads in any memory that agrees with the machine's outside the window.
  - It uses BASE-S's `StrOwned` and two derived facts:
    - `Complement.own_bounds`: the chunk walk puts the object in `[_end, __heap_end)`;
    - `Ranges.own_apart`: the object lies on one side of the whole C-stack interval `[spEntry − cStackBudget, sp + 176)`.
  - Each callee then carries its strings through its own frame stores with `StrView.wm8`/`agree`.
- **M-scan** (`scan_loop`, `relay`). Every string loop is a `scan_loop` over positions, with the invariant "no event before `i`".
  - `memcmp`'s word loop relays a differing word to the byte loop at that word.
  - `strcmp`'s word loop relays a word holding a zero byte to the byte loop, or to `0` when the two words are equal.
  - `strlen`'s byte scan relays to its word scan. The word scan's 8 lane exits are 8 generated theorems (`sl_lane_thm`).
  - `l_strcmp`'s chunk loop is `seg_loop` over the chunk position.
- **Lanes.**
  - The zero-byte test is lane-wise: `hzW_lanes` is carry-free append distribution plus two 256-case `decide`s.
  - Word compares are byte compares: `bytesT8_eq_iff`.
  - Halfword exits reduce to linear arithmetic over 16 byte atoms (`hw*_toNat`, `shl*_eq`), each proved once.
- **Observation quotient** (`CmpObs`). `strcmp` returns a byte or a halfword difference. The summary states only zero-ness (`bnez` in `l_strcmp`) and bit 31 (`srliw 31` in the arm), at the first event. `memcmp` states only zero-ness (`seqz`). `l_strcmp` states only bit 31 (`LsRet`).
- **Branch choice by the proof** (§2c). The tag guards in the arm and the zero-word tests are not searched:
  - guard facts are stated per polarity (`sc_hz_ok`/`sc_hz_zero`, `bne_of_eq`, …) and matched syntactically (`guard_assumption`);
  - where the runner's pre-check (`guardsHold`) unfolds pin values (`whnfR`), the path is named segment by segment (`kit_seg`, LT's prefix).

## What the route could not express

1. **`guardsHold` unfolds the pins.** The runner's polarity pre-check matches pins after `whnfR`. This unfolds reducible heads in the pins: the `bytesT8` abbrev into byte appends, and `&&&`/`+` instances.
   - A guard fact stated over the folded form then fails the pre-check, and both polarities are rejected.
   - Workarounds:
     - pins hold atoms (`wordAt`, `maskV`, `onesV` are `def`s, not abbrevs);
     - or the path is named (`kit_seg`).
   - A kit fix is to drop the `whnfR` in `guardsHold`. It was not made, because it would change every existing arm.
2. **Defeq-based closers recurse.** A non-syntactic `assumption` tried against a guard can unfold `Nat.sub`/`%` by literal and hit `maxRecDepth`. This happened with `assumption` on `n - i - 8 = 0`, and with `(by assumption)` inside `rw [ret_tgt _ …]`.
   - The fixes are a syntactic `guard_assumption`, a named `hra`, and `bool_goal` (a syntactic `Bool` check).
   - `guard_target =~` also recursed.
3. **The per-declaration budget still shapes the arms.** One declaration with both of LT's `docondjump` exits after the `l_strcmp` call exceeded 200k. `kit_cond` was replaced by two path lemmas (`lt_str_take`/`skip`), and `lt_str_take` still sits at 200k.
   - S-SCAN does not attack the arm-side load cost (§1b.3). That is axis B's region log.
   - Likewise the `strcmp` halfword exit, the `strlen` lanes and `l_strcmp`'s prologue were split per lane or variant (command macros `sl_lane_thm`, `ls_variant`).
4. **Abbrevs in memory facts.** `kit_norm`'s `simp` unfolds `bytesT8` in pins, so later rewrites with `bytesT8` facts need `unfold bytesT8 at …` (`lstrcmp_A`).
5. **`OP_LE` is not closed.** `slti a0, 1` observes `a0 ≤ 0`, so `LsRet` would need zero-ness of the whole answer as well as bit 31. `CmpObs` already carries zero-ness per chunk; what is missing is the `l_strcmp` exits' `a0 = 0` iff the strings are equal. That is estimated at ~30 lines in `Lstrcmp`, plus an `le_str` (~110 lines, mirroring `lt_str`).
6. **The gate.** `a1-kit-arm` stays red (28 cases, last quarter 13.6 lines against 3.3). The held-out arms are 39/111 lines, against the 2–7 of the integer paths.

## Forecast

- **VARARGPREP.**
  - `luaT_adjustvarargs` holds a slot copy loop: 4 stores, 3 bases, stride-0 `L->top`.
  - `seg_loop` and `compMem` cover the loop shape: one comprehension entry per store stream, stride 0 allowed.
  - The close needs a re-witness with a new `func` (window move). It must re-prove `Complement.own`'s `out` for the new window by chunk disjointness (BASE-S).
  - Estimate: loop 40, arm 60, re-witness 80.
- **CALL print.**
  - The stdio chain has 93 loops (§1b.2). The read-only scans (`strchr`, `strlen` in `luaL_tolstring`) reuse `scan_loop` and the lane library directly (`strchr` uses the same `hzW` test).
  - The store loops (`memcpy`, `__sfvwrite_r`) need `compMem` with a data stream, not a constant byte. That is a small generalisation.
  - The dominant cost stays the runtime summary (allocator, GC, stdio). M-scan does not cut it.
  - Estimate: the scans ≈ 100 lines each, as `strlen` (245 with 8 lane exits); the arm ≈ 60 once the summary exists.
- **RETURN.**
  - The nil fills of `RETURN0`/`RETURN1` and `luaD_poscall` are LOADNIL's loop: `compMem` with offset `0` or `−8`. About 20 lines per fill on `seg_loop`.
  - `luaD_poscall`'s slot copy is as VARARGPREP's.
  - The `Final` clause and the exit to HTIF are outside this axis.

## Files

- New:
  - `Lua/Vm/Sim/Kit/{Scan,Str,Word,Lex,Memcmp,Lngstr,EqLong,Strcmp,Strlen,Lstrcmp,LstrcmpPro,LtStr}.lean`
  - generated `Lua/Vm/Arms/{Segs,Sites}/H{luaS_eqlngstr,memcmp,l_strcmp,strcoll,strcmp,strlen}.lean`
  - generated `Lua/Vm/Code/{FixedImage_,}{LuaS_eqlngstr,Memcmp,Strcoll,Strcmp,Strlen}.lean`
- Changed:
  - `Kit/Loadnil.lean` (refactor);
  - `Kit/Multi.lean` (`nilMem` removed);
  - `Kit.lean` (imports);
  - `scripts/gen_lua_{arms,code}.py`;
  - `scripts/check.sh` (stage 6);
  - `PHASES.md` (the EQ/LT obligation rows).

## Gate and checks

- `scripts/check.sh` passes every stage except 3c (`a1-kit-arm`, red as expected). It was run with the gate made non-fatal in a scratch copy, so that stages 4–6 also ran.
- Stage 6: 191 axiom lines, all ⊆ {propext, Classical.choice, Quot.sound}.
