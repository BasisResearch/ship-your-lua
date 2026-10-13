# Lane F1-13: the `CALL` invariant in `Complement`, `PrintCall_Statement CallInv` from `CALL`'s open parts

Base: `3580008` (merge of lane F1-12). Route: CLAUDE.md's A1 row and the
`CALL print` row (the arm on an invariant). Lines are non-blank,
non-comment lines. CPU and peak memory are one `lake env lean <file>` each
(`/usr/bin/time -v`: user time, maximum resident set). Heartbeats are per
declaration, bracketed by rerunning the file with `-DmaxHeartbeats`
(never raised; default 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1. the invariant `I` in `Complement` | **done** | `Complement.call : CallInv p w` (`Rel.lean`). `CallInvAt` fields: `stdout`'s phase (`io : StdoutIn`: boot with `StdioBoot`/`MemfsBoot`, after an empty write, set up with `StdoutAt`), `pend`, `cells`, the heap room (`room`: before the first `print` or while `ci->next` is NULL), `atexit` (`__atexit = NULL`, from which `ExitOk` comes back), the static objects frozen on a footprint `F` (`stat : Frozen F StatFacts`, `stat_in`: in chunks in use or the image, `stat_apart`: apart from `CallDirty`), the literals frozen on `FL` (`lits`, `lits_in`, `lits_apart`, `lit_strs`, `marks`), the `lua_State`/`g`/`CallInfo`/stack in chunks in use (`L_in`, `g_in`, `ci_in`, `stack_in`), `fits`, `kslots`, `nci : NciApart`, `objs : CallObjs`, `dense` |
| 2. `I` at the entry | **done** | `callInv_boot` (`Entry.lean`), at the entry and after `VARARGPREP` (`Vararg.lean`), from `VmEntryData`'s new fields (`EntryData.lean`). The boot contract checks them natively (`gen_lua_boot_witness.py` `call_facts`: the footprint of what the arms read, the literals' footprint, placement and apartness) and in the kernel (`EntryChecks`: `entryBaseCheck`, `frozenCheck`, `litsEntryCheck`, `placedCheck`, one `decide +kernel` per field over `RTree` footprints; `entryCheck_sound`, `Boot/Check.lean`). Both witnesses regenerated (`--check`: ok) and rebuilt (While 3:15, F1Ops 3:08 wall) |
| 3. `I` preserved by every arm | **done, by one region lemma** | every arm but `CALL` and `VARARGPREP` passes `hc.comp` (so `Complement.call`) unchanged; `VARARGPREP` re-runs `callInv_boot`; `CALL` re-establishes it in `call_close` (`Kit/CallClose.lean`) with `Frozen.trans` (`Sim/StdioState.lean`), the one region lemma (`Frozen F P m`: `P` of every memory agreeing with `m` on `F`) |
| 4. `SimArm .CALL` from `sim_CALL_of`; `OpenArms.CALL` the remaining premises | **done** | `sim_CALL : PrintCall_Statement CallInv → HeapBudget_Statement CallInv → SimArm .CALL` (`Kit/CallArm.lean:346`); `printCall_of : CallOpen → PrintCall_Statement CallInv` (`Kit/CallPrint.lean:1439`); `OpenArms.CALL_open : Kit.CallOpen`, `OpenArms.CALL_heap : Kit.HeapBudget_Statement CallInv`; `armTable`'s case `Kit.sim_CALL (Kit.printCall_of h.CALL_open) h.CALL_heap` (`Fold.lean`) |
| 5. optional: `luaL_tolstring` on strings, `luaD_poscall` with `C ≥ 2` | not done | `PoscallN_Statement` is a `CallOpen` field; strings inside `PrintRel_Statement` |

`CallOpen` (`Kit/CallOpen.lean:206`), the remaining named premises of `CALL`:

* `print : PrintRel_Statement`: `luaB_print` on the C frame (`PrintIn` → `PrintOut`). It covers `PushLit`, `luaL_tolstring` on strings, integers, floats and functions, `IntegerToStr`, `G14From` and `MallocR_Statement`; see obstacle 1.
* `extendCI : ExtendCI_Statement`: `luaE_extendCI`, `PcExt` with `ExtPost`.
* `poscall : PoscallN_Statement`: `luaD_poscall` with `C ≥ 2`, over `PcCxW`.
* `grow : PrintGrow_Statement CallInv`: `luaD_precall`'s stack growth.
* `exitUp : ExitUp_Statement`: `exit(0)` once `stdout` is set up.

`HeapBudget_Statement CallInv` stays beside it, as `OpenArms.CALL_heap`.

## The proof of `printCall_of`

* `printCall_room` (`CallPrint.lean:1382`) handles room on the Lua stack. `printCall_of` splits on it, and `CallOpen.grow` handles the rest.
* `next_ci` splits on `LuaStateRel.next`:
  * reuse: `precall_reuse` with `join_reuse` (`:919`);
  * NULL: `precall_ext` over `ExtendCI_Statement` with `join_ext` (`:1117`).
* Both ways produce the same `JoinIn`: the memory at the join relative to the head's memory and to the complement. From there, the C function (`call_pcc`, `:418`) and `luaD_poscall` (`call_pcpos`, `:785`) are composed once, through `JoinQ`, `join_pcc` and `join_pcpos`.
* `close_post` (`:1307`) closes through `call_close`.
* The head memories against the complement go through one lemma `keep_mo` (`:868`), used for `callMem`, `pcFrameMem` and `callExtMem`.
* `stdout`'s state at any head memory comes from `printSt_head`.
* `call_pcNum` and `call_pcCells` give `luaD_precall`'s numbers and cells.
* `call_bounds` (`CallArm.lean:213`) is factored out of `sim_CALL_of`.

## Numbers

| file | hand lines | generated lines | CPU (user) | peak RSS | largest declaration |
|---|---|---|---|---|---|
| `Kit/CallPrint.lean` | 1250 | 0 | 49.0 s | 4123 MB | `close_words`, `join_reuse`: 100k–200k (all others < 100k; 28 declarations over 50k) |
| `Kit/CallClose.lean` | 276 | 0 | 2.6 s | 2136 MB | < 50k |
| `Kit/CallOpen.lean` | 108 | 0 | 0.9 s | 2066 MB | < 50k |
| `Sim/StdioState.lean` (mostly moved) | 153 | 0 | 1.5 s | 1725 MB | < 50k |
| `EntryData.lean` (mostly moved) | 190 | 0 | 1.0 s | 1581 MB | < 50k |
| `Boot/Check.lean` (+418/−52) | — | 0 | 3.6 s | 1745 MB | < 50k |
| `Boot/Witness/{While,F1Ops}.lean` (kernel `decide`) | 0 | 1 each | 3:15 / 3:08 wall (`lake build`) | ≈ 3.5 GB | one `decide +kernel` per `EntryChecks` field |

Other hand lines (diff vs base, added): `Boot/Check.lean` +418/−52, `Entry.lean` +293/−17, `Rel.lean` +134/−24, `Repr.lean` +66/−61, `CallArm.lean` +41/−18, `Vararg.lean` +14, `Fold.lean` +10/−10, `gen_lua_boot_witness.py` +165. Moved, not new: `StdioState.lean` (the `stdout` predicates out of Kit), `EntryData.lean` (`VmEntryData`, `StrChain`, `RtPtrs`, … out of `Repr`/`Runtime`). Generated: `Boot/Gen/{While,F1Ops}.lean` +3 lines each (the footprints as `RTree` literals, one line of ≈7.9k characters), the witness line `entryOk : EntryChecks …` in `Boot/Witness/*`.

Gate: `python3 abstractions/gate.py`: `a1-kit-arm: 59 cases — ok (first 2.1, last 3.0)`; abstraction gate ok.

## Obstacles

1. **`PrintRel_Statement` is coarser than the per-class premises asked for.** Composing `print_sum` over `luaL_tolstring` per argument class needs:
   * the heap tracked across arguments: one argument's allocations move the next one's heap, and `MallocPost` bounds no break;
   * `"__tostring"` allocated on its first use (strings);
   * `luaS_resize` freeing chunks, which breaks `TolPost.kept`;
   * `LitInterned` re-established after each push.

   These are one statement about `luaB_print`'s loop on the C frame, so `PushLit`, the tolstring classes, `IntegerToStr`, `G14From` and `MallocR_Statement` sit inside `PrintRel_Statement` rather than beside it.
2. **`ExitUp_Statement`'s truth** needs stdin/stderr as `__sinit`'s `std()` left them, which `StdoutIn` does not carry yet.
3. **The kernel check of the footprints.** A flat list of 286 ranges ran out of memory at 12G in `decide +kernel`. `RTree` (a search tree of ranges, `Repr.lean`) and one `decide` per `EntryChecks` field fixed it.
4. **`ExtendCI_Statement` needs heap room in every phase of `stdout`.** `CallInvAt.room` now holds also while `ci->next` is NULL. After a `print`, `ci->next` is the C `CallInfo`, so `call_close` re-establishes `room` vacuously.
