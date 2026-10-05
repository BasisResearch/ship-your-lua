# Round-4 bake-off, axis S base (BASE-S)

The axis-S contenders start from this commit. It proves no new arm. It
adds the two relation facts that the string arms (EQ on long strings, LT on
two strings) need in order to be true. Every existing arm builds unchanged.

## Change 1: `TStringRepr.long` carries `shrlen = 0xFF`

`luaS_createlngstrobj` stores `shrlen = 0xFF` at `+11` (lstring.c:160), and
`l_strcmp` branches on it at `0x8001a720`. `TStringRepr.long`
(`Lua/Vm/Repr.lean`) gains the premise `rd8 m (ts + tstringShrlenOff) = some
0xFF` as its last argument, so existing positional patterns still match.

- Consumer: `TStringRepr.long_shrlen` (`Lua/Vm/Boot/Check.lean`).
- Checks: `tstrCheck` reads the byte, and the generator's `check_tstring`
  needs it for every long string.

## Change 2: string ownership, keyed to the allocator's chunks

**Carrier.** `RelPtrs.ι` is now `Strs` (`Lua/Vm/Sim/Rel.lean`), with two
fields:
- `ptr`: the intern map (the old `ι`);
- `own : Nat → List UInt8 → Prop`: the string objects a register or constant
  may point to.

`ValRepr.str` gains a third premise, `ι.own x.toNat s`. Copying a register
copies its `ValRepr`, so ownership travels with the value. No closer
(`Core.write/update/bleach*`), generated arm or kit file restates it. The
churn outside Rel/Entry is small:
- 6 binder types (`{ι : Strs}`) in `Close.lean` and `Kit/Equalobj.lean`;
- one `rename_i` in `ValRepr.eq_iff_payload`.

**The fact.** `RelPtrs` gains `rt : RtPtrs`, and `Complement.runtime` is now
`RuntimeMem w.mo w.L w.ci w.func w.rt` instead of an existential. Two new
definitions:
- `ChunkOwns p w c ts s`: `c ∈ w.rt.chunks` (`HeapAt`'s walk), `c.inuse`,
  and the object `[ts, ts + 24 + |s| + 1)` (header, contents, terminator)
  inside the chunk's user range `[addr + 16, addr + size + 8)`, no byte of
  which is in `Win` (so none is in `Scratch`);
- `StrOwned p w ts s := ∃ c, ChunkOwns p w c ts s`.

A new field holds it: `Complement.own : ∀ ts s, w.ι.own ts s → StrOwned p w ts s`.

**Consumers** (`Rel.lean`):
- `StrOwned.out`;
- `ValRepr.owned`;
- `Core.reg_owned` (a string register's object is owned);
- `Core.k_owned`;
- `Core.str_frame` (each byte of an owned object reads as `w.mo`'s).

S-INC and S-SCAN use these to move `TStringRepr w.mo …` facts to live memory.

**Entry.** `RuntimeReadyAt.kowned : KOwned m L ci w` (`Lua/Vm/Runtime.lean`)
states that every string constant (`KStrAt`) has a chunk with
`StrChunkAt`:
- in use, and in the walk;
- holds the object;
- lies in the heap;
- lies apart from `[stack, stack_last)`, `L` and `ci`.

`vmRel_entry` sets `own := KStrIn` (the string constants). The ownership
proof is factored out of `vmRel_entry`:
- `own_of_kowned` (`Entry.lean`);
- `chunkOwns_of_strChunkAt`: the slots are inside the Lua stack, the scratch
  words are inside `L` and `ci`, and the C frames are above `__heap_end`
  (`cstack_room`).

**What an arm that creates a string (CONCAT, CALL) must do.** It must
re-witness `w` with a larger `ι.own` and prove `ChunkOwns` for the new
object. Window moves (VARARGPREP, stack reallocation) must re-prove
`Complement.own`'s `out` for the new window. Because ownership is keyed to
chunks, that proof is chunk disjointness, not byte tracking.

## New obligations

Both go into the existing boot-witness obligation (PHASES A0.6), and
PHASES.md records them.

| field | content | kernel check | native check |
|---|---|---|---|
| `TStringRepr.long` `shrlen` | `+11 = 0xFF` for a long string | `tstrCheck` | `check_tstring` |
| `RuntimeReadyAt.kowned` (`KOwned`) | each string constant lies in an owned chunk (`StrChunkAt`) | `kownedCheck` (`strLenV` + a search of the chunk walk), `kownedCheck_sound` | `evaluate`'s KOwned loop |

**Results at the two entries.**
- `gen_lua_boot_witness.py --check` passes at both entries with no drift.
  The witness files did not change: `rtOk` is `constructor <;> decide +kernel`
  and picks up the tenth field without edits.
- Both kernel witnesses rebuilt: `vmLoaded_while_entry` and
  `vmLoaded_f1Ops_entry`.

**Coverage.**
- `while` and `f1_ops` have one string constant each (`"print"`, short).
  At those entries, the long-string fact holds vacuously.
- A scratch native run of the generator's `evaluate` on three more programs
  found that both facts hold:
  - `longk.lua`: 2 long constants and 2 short;
  - `l4str_fullgc.lua`: 7 string constants;
  - `f4_strlite.lua`: 13 string constants.
- `longk.lua` is a scratch program and is not committed. A contender that
  needs a kernel witness with a long constant must add a program to
  `PROGRAMS`.

## Summary row

| setup | callees | held-out | generated | CPU | peak mem | largest decl heartbeats | refactor | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 215 hand lines | — | — | 0 | see below | 2.2 GB (`Entry`) | `vmRel_entry` 184.3k (pre-existing; new decls ≤ 2.2k) | — | 4 | ≈ 40 min |

**Hand lines.** Counted as added lines that are not blank and not comments
(`git diff -U0`, docstrings excluded):

| file | lines |
|---|---|
| `Boot/Check.lean` | 72 |
| `Sim/Entry.lean` | 58 |
| `Sim/Rel.lean` | 39 |
| `Runtime.lean` | 17 |
| `gen_lua_boot_witness.py` | 17 |
| `Close.lean` | 5 |
| `Kit/Equalobj.lean` | 4 |
| `Boot/Assemble.lean` | 2 |
| `Repr.lean` | 1 |

**Heartbeats.** Measured with `IO.getNumHeartbeats` around each command, in
thousands, in scratch copies with `Elab.async false`:

| declaration | heartbeats (k) |
|---|---|
| `kownedCheck_sound` | 0.29 |
| `strLenV_sound` | 0.14 |
| `chunkOwnsOk` | 0.45 |
| `chunkOwns_of_strChunkAt` | 2.2 |
| `own_of_kowned` | 0.15 |
| `ProtoRepr.kArr` | 1.1 |
| `TValueRepr.valRepr` | 0.29 |
| `ConstRepr.valRepr` | 0.45 |
| `StrOwned.out` | 0.26 |
| the `Core.*_owned` lemmas | ≤ 0.08 |

**`vmRel_entry` is at 184.3k of the 200k budget.**
- Inlining the ownership proof cost it 0.1k more (184.5k). Most of the
  184k was already there.
- It is the next declaration to split (like `Ranges.of_regions`, 78.9k) when
  the relation widens again.

**CPU and memory.** `lake env lean`, user CPU, peak RSS:

| module | user CPU | peak RSS |
|---|---|---|
| `Check` | 3.3 s | 1.8 GB |
| `Rel` | 2.0 s | 1.8 GB |
| `Entry` | 24 s | 2.2 GB |

The `kownedCheck` `decide +kernel` at the `while` entry, together with
`internedCheck`, takes under 1 s.

Rebuilds:
- both witness modules: 6 min 22 s wall, 3.0 GB peak;
- the full `lake build Lua Vsa VsaIris`: 1543 jobs, ≈ 360 s user CPU after
  the witnesses.

**Failed builds (4).**
- `Complement` field order against the anonymous constructor in
  `vmRel_entry`.
- A `stack_le` rewrite.
- `Close.lean`'s `ι` binder type.
- `Equalobj`'s `rename_i` (the new `ValRepr.str` premise).

**Gate.** `scripts/check.sh` passes every stage except 3c (`a1-kit-arm`, red
as expected). It was run with the gate made non-fatal in a scratch copy, so
that stages 4–6 also ran. Stage 6 has 9 new axiom lines (`own_of_kowned` added after the run, checked separately) (all ⊆ {propext,
Classical.choice, Quot.sound}) and 170 axiom lines in total.
