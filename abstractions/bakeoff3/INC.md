# Round-3 A1 bake-off: contender INC (the incumbent route)

Base: `3f9797f`. Branch: `inc-bakeoff3`. The route is the existing one: per-kind
templates in `scripts/gen_lua_arm.py` over generated segments from
`scripts/gen_lua_arms.py`. Callees are handled by generating their bodies as
segments at the Lua ELF's addresses and adding a call node to the arm chain.
No M1–M6 abstraction was introduced.

## Result

| held-out | status | theorem |
|---|---|---|
| `sim_MUL` (`SimArm .MUL`) | **proved** | `Lua/Vm/Sim/Arms/Mul.lean:25` (generated) |
| `sim_MOD` (`sim_MOD_Statement`) | **proved** | `Lua/Vm/Sim/Arms/Mod.lean:879`, with six path lemmas `sim_MOD_{m1,r0,neg,pos,cni,bni}` (generated) |
| `sim_EQ` (`sim_EQ_Statement`) | **proved from one named premise** | `Lua/Vm/Sim/Arms/Eq.lean:24`: `sim_EQ_lng_Statement → sim_EQ_Statement`. Every path is proved except the one where both registers hold long strings (> 40 bytes); that path is `sim_EQ_lng_Statement` (`Lua/Vm/Sim/Callees/Equalobj.lean`). |
| refactor `sim_ADD` | unchanged | `Lua/Vm/Sim/Arms/Add.lean` is byte-identical to the base (245 lines, 233 code lines). For INC it is the route's own output, so there are 0 new lines. |

Callee summaries, all proved at the Lua ELF's addresses:
- `muldi3_sum` (`Lua/Vm/Sim/Callees/Muldi3.lean`): shift-add loop, `a0 = x * y`.
- `udivdi3_sum` (`Callees/Udivdi3.lean`): the normalise and divide loops, `a0 = n / d`, `a1 = n % d` (d ≠ 0).
- `moddi3_sum` (`Callees/Moddi3.lean`): `a0 = x.srem y` (y ≠ 0), through a nested call node to `udivdi3`.
- `equalobj_sum` (`Callees/Equalobj.lean`): `luaV_equalobj` on F1 values that are not two long strings. It covers the tag tests, the `.rodata` jump table (`jr a5`), the payload compare and the `ra` spill below `sp`. It returns `eqRes`, and `eqRes_spec` shows `eqRes` decides `δ .eq` on `ValRepr`ed values.

`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of `sim_MUL`, `sim_MOD`, `sim_EQ`, `callNode`, `muldi3_sum`, `udivdi3_sum`, `moddi3_sum`, `equalobj_sum`, `eqRes_spec`, `Core.write_scr`, `Core.jump_scr` and `smod_srem`. All are in `scripts/check.sh` stage 6, which now expects 143 reports.

Gate: `scripts/check.sh` passes every stage except 3c. Stage 3c is red as expected: the `a1-arm-sim` ledger rows MUL 7, MOD 220 and EQ 102 move its last-quarter mean to 93.6. Stage 5b must run outside `systemd-run --scope`: inside the scope, one Linux trace is rejected because the scope adds an open fd (fd 4 instead of 3). Outside it, 0 traces are rejected.

## What the route needed (setup)

**Helper bodies as generated segments** (`gen_lua_arms.py`, `HELPERS`):
- Each helper's reachable blocks get generated segments, with liveness inside the helper. Its outputs are kept live at its returns. A `jr` through a jump table gets its listed successors.
- A helper's segments pin only its own registers. Every other register rides in a ghost frame `∀ R, FrameW W R → σ.regs.get? R = g R`. `W` is the helper's write set (plus its callees' write sets) and the step bookkeeping registers.
- The per-step frame lemmas are the `gen_segment.py` `"frame"` templates (`Lua/Vm/Arms/HelperFrame.lean`).
- Generated: 7,346 code lines in `Lua/Vm/Arms/Helpers/*` for 4 helpers.

**The call node** (`HelperFrame.callNode`, `callNodeH`):
- It turns any helper summary, stated for all `g`, into a step of an arm's chain. The caller's other pins survive the call.
- The callee may change memory (`m → m'`: `luaV_equalobj`'s spill of `ra`).
- In `gen_lua_arm.py`, `walk` inserts `CALL:` nodes at helper entries. `call_node` emits them from a `CALLEES` row: the summary, its argument registers, its outputs, its post memory and its side conditions.

**`Scratch` closes** (`Lua/Vm/Sim/CloseScratch.lean`):
- `ScrEq`, `scr_savestate`, `scr_stack`.
- `Core.stack_scr`, `fetch_scr`, `trap_scr` and `rodata_scr`: register, code, `trap` and `.rodata` reads through `Scratch`-written memory.
- `Core.update_scr`, `write_scr`, `jump_scr`.
- `chain2` gets `scr`, which names the post-`savestate` memory `M` (`generalize`), and `norm`, which normalises loaded payloads to `slotVal`.

**Per-path lemmas** (`SPLIT_PATHS`):
- A monolithic generated `sim_MOD` needs between 200k and 400k heartbeats for one declaration. It builds at 400k in a scratch copy and fails at the default.
- The `mod` kind therefore emits one lemma per kernel path, from `ArmAt`, and the split calls each one. No limit was raised.

**Relation widening.** `VmRel` as given in the base cannot be proved preserved by MOD or EQ. Nothing in `Ranges` separates `L->top` (a `Scratch` word) from the register slots, so `savestate` could, as far as the relation knows, overwrite a register. Added:
- `VmRegionsAt.L_sep_stack`, `L_al`, `ci_al`, which `gen_lua_boot_witness.py --check` evaluates and which hold at both traced entries;
- `Ranges.L_hi`, `L_al`, `ci_al`, and `Ranges.scr_out`: the scratch words miss the slots and the C frame. `Ranges.of_regions` proves them.

The full rebuild after this change is 1,246 s user CPU, 74 s wall and a 3.06 GB peak. All 28 arms rebuild, and none of the 25 old arms' texts changed.

## Numbers

Line counts are code lines only (non-blank, non-comment); docstrings are excluded. A generator "diff" counts the added lines relative to `3f9797f`.

### Lines

| row | where | lines |
|---|---|---|
| **setup** | `HelperFrame.lean` | 128 |
| | `CloseScratch.lean`, the scratch closes | 105 |
| | `gen_lua_arms.py`, helper infrastructure (+107, of which 5 are `HELPERS` rows) | 102 |
| | `gen_lua_arm.py`, call nodes, `chain2` `scr`/`norm` and `SPLIT_PATHS` machinery (+359, minus 229 per-arm) | 130 |
| | `draft_f1_arms.py` (+3), relation widening (`Rel` +4, `Entry` +5/−5, `Runtime` +3, boot witness +2) | 17 |
| | **setup total** | **482** |
| **callee proofs** | `Callees/Muldi3.lean` (1 loop) | 80 |
| | `Callees/Udivdi3.lean` (2 loops) | 192 |
| | `Callees/Moddi3.lean` (4 sign cases, nested call) | 86 |
| | `Callees/Equalobj.lean`, the summary (jump table, 6 tags) | 255 |
| | `Callees/Equalobj.lean`, `eqRes_spec`/`eqRes_bit` (`δ .eq` on `ValRepr`) | 72 |
| | **callee total** | **685** |
| **per-arm hand** | MUL: `ARMS2` row 2, `CALLEES` row 4, `HELPERS` row 1 | **7** |
| | MOD: `mod` kind template 79, path-lemma table and lemma facts 51, `CALLEES` 4, `HELPERS` 2, `ARMS2` 1, `smod_srem`/`imod_eq_smod`/`guard_bgeu` 83 | **220** |
| | EQ: `eq` kind template 71, `CALLEES` 15, `HELPERS` 2, `ARMS2` 1, `EXTRA_PARAMS` 1, `sim_EQ_lng_Statement` 12 | **102** |
| **generated** | `Arms/Helpers/*` (sites and segments of 4 helpers) | 7,346 |
| | `Sim/Arms/{Mul,Mod,Eq}.lean` | 262 / 942 / 216 = 1,420 |
| | segment modules regenerated (MUL/MOD/EQ now carry the fetch-head registers): 19 `Segs/G*` | +1,939 / −825 raw |
| **refactor `sim_ADD`** | unchanged incumbent: `Add.lean` 233 code lines generated, over the `arith` template (~140 generator lines shared by 9 arms) | 0 new |

### Build CPU and memory

Each new module was measured alone with `lake env lean <file>` under `/usr/bin/time -v`, dependencies already built. The times include about 1.5 s of import loading per module.

| module | wall | user s | peak RSS |
|---|---|---|---|
| `Arms/HelperFrame` | 1.9 | 1.3 | 1.74 GB |
| `Arms/Helpers/Muldi3Sites`, `Muldi3` | 1.8, 2.2 | 1.9, 2.8 | 1.79 GB |
| `Arms/Helpers/Udivdi3Sites`, `Udivdi3` | 2.3, 3.0 | 3.4, 5.7 | 1.83 GB |
| `Arms/Helpers/Moddi3Sites`, `Moddi3` | 2.2, 2.5 | 2.4, 3.4 | 1.79 GB |
| `Arms/Helpers/EqualobjSites`, `Equalobj` | 3.4, 4.7 | 7.3, 14.9 | 2.05 GB |
| `Sim/Callees/Muldi3` | 2.3 | 2.0 | 1.76 GB |
| `Sim/Callees/Udivdi3` | 2.7 | 3.6 | 1.80 GB |
| `Sim/Callees/Moddi3` | 2.0 | 1.8 | 1.77 GB |
| `Sim/Callees/Equalobj` | 5.9 | 8.5 | 1.98 GB |
| `Sim/CloseScratch` | 1.7 | 1.6 | 1.86 GB |
| `Sim/Arms/Mul` | 7.5 | 8.1 | 1.99 GB |
| `Sim/Arms/Mod` | 15.6 | 40.9 | 2.29 GB |
| `Sim/Arms/Eq` | 6.8 | 7.4 | 1.99 GB |
| `Sim/Arms/Add` (reference, unchanged) | 6.1 | 6.8 | 1.96 GB |
| `Runtime` / `Rel` / `Entry` (widened) | 1.4 / 1.7 / 14.3 | 1.0 / 1.5 / 19.9 | 2.21 GB |

The new modules total 117 s user (the arms 56 s, the helper segments and sites 42 s, the callees 16 s). The incremental `lake build Lua` after the widening took 1,246 s user and 74 s wall, with a 3.06 GB peak.

### Failed builds and wall time

The 24 failed `lake build`s (log: every build ran under `MemoryMax=30G`, one at a time), by phase:

| phase | wall (approx.) | failed builds | causes |
|---|---|---|---|
| orientation | 23:05–23:15 | 0 | — |
| MUL: frame lemmas, helper generator, `muldi3_sum`, call node, arm | 23:15–23:26 (11 min) | 5 | `Triple` namespace; `intro` pattern; missing `DeriveLoop` import; implicit args in `loopFromBody`; `len_arith` on `Lout ++ L` |
| MOD: `udivdi3`/`moddi3` (incl. ~4 min waiting for memory), widening, `CloseScratch`, `mod` kind, per-path lemmas | 23:27–00:06 (39 min) | 11 | no `ring` (no Mathlib); `srem`/`umod` spellings; `zopz0zKzJ_u` over `toNatInt`; an unparenthesised `M` argument; `slt_zero` namespace; **heartbeat budget** of the monolithic `sim_MOD` |
| EQ: `luaV_equalobj` segments and summary, `eqRes_spec`, `eq` kind | 00:07–00:52 (45 min) | 8 | code-pin module name casing; liveness lost at `jr a5`; `0x44`/`0x54` vs `4`/`20` (`tt & 63`); **kernel deep recursion** (2 builds, 3–4 min and 22.3 GB each): `simp` proving pin-list membership and index bounds over lists holding BitVec literals; the fix is unification-only `pins_sub` and `rfl` length bounds |
| gate, measurement, report | 00:52–01:15 | 0 | — |

Seven more scratch elaborations (`lake env lean`) were diagnostic: the 400k-heartbeat check of `sim_MOD` and five bisections of the deep recursion.

### Summary row

| setup | callee proofs | per-arm hand (MUL / EQ / MOD) | generated lines | build CPU (s) | peak mem | refactor `sim_ADD` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 482 | 685 (incl. 72 `δ .eq`) | 7 / 102 (+ open long-string premise) / 220 | 8,766 new + 1,939/−825 regenerated | 117 (new modules); 1,246 full rebuild | 2.3 GB (successful builds); 22.3 GB (failed, deep recursion) | 0 (unchanged, 233 generated) | 24 | ≈ 2 h 10 min |

## What the route could not express

1. **Two long strings in EQ.**
   - `luaV_equalobj` tail-calls `luaS_eqlngstr`, which reads `lnglen` at `+16` and calls `memcmp`, a word loop plus a byte loop over the contents at `+24`.
   - The memory reads are of the machine memory. `VmRel` relates that memory to the complement `w.mo` only outside `Win`, and no relation fact puts a register's `TString` outside `Win`.
     - `ValRepr.str` gives only `TStringRepr w.mo …`.
     - Strings and the Lua stack are both `l_alloc` blocks, and `Ranges` says nothing about strings.
   - Two things are missing: a relation field (a register's long string lies outside the window, which CONCAT must also maintain), and the `memcmp`/`luaS_eqlngstr` summaries.
   - The path is the premise `sim_EQ_lng_Statement` (PHASES.md).
   - Forecast: about 250 lines for `memcmp` (two loops, word-to-byte equality), 40 for `luaS_eqlngstr`, and a `ValRepr` widening that touches every arm through its signature. At that point the incumbent's generated arms change text.
2. **The base relation was not enough for any `savestate` arm.** `L_sep_stack` and the alignment facts had to be added (evidence above). The route has no way to find such gaps except failing proofs.
3. **The per-declaration heartbeat budget.**
   - A generated arm's cost grows with paths × segment size. `sim_MOD` (6 paths, one call) does not fit in one declaration.
   - The generator now emits path lemmas, but only for kinds listed in `SPLIT_PATHS`, and each needs a hand-written table of path hypotheses and states (51 lines for MOD).
4. **`simp` over pin lists.**
   - The generic `(by simp)` proofs on pin lists (membership, index bounds) let BitVec simprocs normalise literal values inside the lists.
   - The kernel then re-checks those normalisations. The result was deep recursion, 3–4 min and 22 GB, where MUL/MOD's smaller values had been harmless.
   - The route now uses `pins_sub` (`HelperFrame.lean`) and `rfl` length bounds. Any template that writes `simp` over segment states carries this risk.
5. **Callee memory effects** are a single post-memory expression (`callNode`'s `m'`) related to the entry memory by `ScrEq`, so only writes to `Scratch` can be expressed. A callee that writes the heap, `G`, the console or `L`/`ci` fields (`luaD_precall`, `print`, `luaT_adjustvarargs`, `luaD_poscall`) has no expressible post-state in this route without a new relation close.

## Forecast for the remaining arms (INC route)

| arm | what it needs | forecast |
|---|---|---|
| **FORPREP** | `luaV_forprep` inlined. The F1 integer path calls `luaV_tointeger` (`forlimit`), which writes an out-pointer in `luaV_execute`'s own frame (`sp+40`, inside `Win` but not `0(sp)`). Float paths are excluded by guards. | new `forprep` kind ≈ 150; summary for `luaV_tointeger` ≈ 80 (no loops); a call node whose `m'` writes the C frame (expressible: `Win` covers it) |
| **LOADNIL** | an arm-level loop (`do setnilvalue(ra++) while (b--)`). `chain2` has no loops, so the loop must become a template with a hand invariant over `b` slots (`loopFromBody` inside the arm). | ≈ 120 template + ≈ 40 relation lemma (k slots nil) |
| **VARARGPREP** | `luaT_adjustvarargs` (64 instructions, stack writes, `L->top`, `ci->func`). `func` moves, so the arm must change `w` (a re-witness close `Core.rebase`, which the base chose not to build). | not expressible with `ScrEq` closes; ≈ 300 (re-witness) + ≈ 150 summary |
| **CALL print** | `luaD_precall` → `luaB_print` → `luaL_tolstring` → `fwrite` → … → HTIF: 81 functions and 9,155 dynamic instructions, with heap/`G`/stdio/console effects. Every callee needs generated segments plus a hand summary. At this round's 0.5–7 hand lines per covered instruction (muldi3 80 for 9; equalobj 255 for ~35 on F1 paths), and with summaries composing, ≥ 3,000 hand lines, plus a relation close for heap and console growth. | not reachable at this cost; needs the L-C3′ "runtime" law as an abstraction |
| **RETURN\*** | the `Final` clause: `luaD_poscall` and the exit chain (19 functions, 837 instructions) to HTIF `exit`. Same helper machinery, plus a halt rather than a head close. | ≈ 600–900 hand lines (summaries) |

For callees that are pure leaves (soft-int: `__divdi3` for IDIV, `__muldi3` for MULK), INC is now cheap: MULK ≈ 3 lines (a row), IDIV ≈ 60 (`idiv` sign fix) plus `__divdi3` ≈ 70. MODK, IDIVK and EQK reuse the `mod`/`eq` kinds with the `k` operand form, ≈ 20–40 each.

## Files

- Generators: `scripts/gen_lua_arms.py` (`HELPERS`, `helper_specs`, `live_keep` with `jr_succ`), `scripts/gen_lua_arm.py` (`CALLEES`, `call_node`, `chain2` `scr`/`norm`, kinds `mod` and `eq`, `SPLIT_PATHS`), `scripts/draft_f1_arms.py` (`cfg(lo, hi)`).
- Hand Lean: `Lua/Vm/Arms/HelperFrame.lean`, `Lua/Vm/Sim/CloseScratch.lean`, `Lua/Vm/Sim/Callees/{Muldi3,Udivdi3,Moddi3,Equalobj}.lean`; the widening in `Lua/Vm/Runtime.lean`, `Lua/Vm/Sim/Rel.lean` and `Lua/Vm/Sim/Entry.lean`, with `scripts/gen_lua_boot_witness.py`.
- Generated: `Lua/Vm/Arms/Helpers/*`, `Lua/Vm/Sim/Arms/{Mul,Mod,Eq}.lean`, the regenerated `Lua/Vm/Arms/Segs/G*`.
