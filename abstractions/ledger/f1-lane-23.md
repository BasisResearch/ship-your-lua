# Lane F1-23: `PrintIn`'s dirty set bounded; `TolInt_Statement` proved

Base: main `cf252a1` (lane F1-20). Route: CLAUDE.md's rows for a callee that replaces the complement
(`CALL print` on the invariant `CallInvAt`, region facts frozen on footprints, boot-checked) and for a C
callee's run (`tolint_sum` from lane F1-20, spliced into `luaB_print`'s state). Lines are non-blank,
non-comment lines. CPU and peak memory are one `lake env lean <file>` each (user time, maximum resident set).
Heartbeats are per declaration, bracketed by rerunning the file with `-DmaxHeartbeats` 50000 and 100000. No
heartbeat or recursion limit was raised; every declaration elaborates at the default 200000.

## Result

| target | status | where |
|---|---|---|
| `PrintIn`'s dirty set `D` bounded | **done**: `dirty_in` (in the entry's chunks in use), `dirty_g` (off `g->currentwhite`, `g->allgc`: `InsG`); `LitsFoot.tab` (`g->strt`'s header and bucket array in the literals' footprint, so off `D`); `StrtSafeIn`'s `W` holds `D` (a found string's bytes survive the push) | `Kit/CallOpen.lean` |
| the caller meets it | **proved**: `call_dirty_in`, `call_dirty_g` (`CallD` in chunks in use, apart from `g`'s words by `CallObjs`), `call_lits` (`LitsFoot.tab` from `CallInvAt.tab_fl`), `call_alloc` (`W` from `CallAllocAt.strt`) | `Kit/CallPrint.lean` |
| new invariant facts | `CallInvAt.tab_fl` (`TabFoot w.mo g ⊆ FL`), `CallAllocAt.strt`'s `W := B ∨ CallLitDirty ∨ NciAt`; boot: `VmEntryData.lits_tab` by `litsCheck_tab` (no new decide: the literals' check over the view restricted to `e.litFoot` pins what it reads), `strt_safe`'s `W := EntryW` by `strSafeCheck`'s `ws` ranges (both boot witnesses re-decided, `entryOk`); re-established by `call_close` (`TabFoot.trans`), `Errno` | `EntryData.lean`, `Boot/Check.lean`, `Sim/Rel.lean`, `Sim/Entry.lean`, `Kit/CallClose.lean`, `Kit/Errno.lean` |
| `TolInt_Statement` | **proved**: `tolInt_proved`; `CallOpen` loses `tolInt` (`CallOpen.print` moved to `Kit/TolIntProof.lean`) | `Kit/TolIntProof.lean` |
| `PrintFlt_Statement`, `PrintFn_Statement` | open; **satisfiable again** (argued below, the lemma that failed now holds: `TiNew.ins`) | `PHASES.md` |
| `printFn` (`"%s: %p"` specs) | not started | — |

### The fix, and why it is the minimal one

Lane F1-20's obstruction: `frozen_lits_head_tt` forces a created string's tag byte into every footprint the
literals' facts are frozen on, and `LitsFoot.apart` keeps that footprint off `D`, which `TolArg` quantifies
with a lower bound only. With `D ⊆` the entry's chunks in use (`dirty_in`) the fresh block is off `D`. The
insertion's footprint (`InsFoot`: the bucket's word, `nuse`, `g->allgc`, the object, `g->strt`'s header,
`g->currentwhite`) needs, besides the fresh object, the table's words and two `g` words off `D`. Two facts the
relation did not carry turned up on the way:

1. **The bucket array apart from the Lua closure's slot** `[ci->func, ci->func + 16)`. `CallLitDirty` (what
   `CALL` writes, so `D`) holds that slot; the string table's safety (`StrtSafe`'s `X = CallX0`) keeps the
   array off the stack only from `ci->func + 16`. The invariant now keeps `g->strt`'s words in the literals'
   footprint (`tab_fl`), which `lits_apart` keeps off all of `CallLitDirty`. Boot: `litsCheck_tab`, a memory
   that differs at one byte outside `e.litFoot` passes the same check at the same witness table, and two reads
   of one value see the same bytes (`rdLE_bytes_eq`).
2. **A found string's bytes apart from `L->top` and the stack's top slot.** `IaNode` kept only a node's mark
   and `u.hnext` off `X`; the contents could, as far as the facts said, overlap the words the push writes
   before `luaB_print` writes them out. `StrtSafe`'s `W` (what a `print` writes outside the table) now holds
   `D` at `PrintIn` and `CallLitDirty ∨ NciAt` in the invariant; boot: `strSafeCheck` checks every node's
   object and the bucket array off `entryWRanges` (the `lua_State`, `g`, the `CallInfo`, the stack from
   `ci->func`).

### `PrintFlt`/`PrintFn` satisfiable again

The lemma that failed is `LitsFoot.apart` for the footprint after an insertion; `TiNew.ins` proves it, for any
created string, from `PrintIn.dirty_in`/`dirty_g` and `LitsFoot.tab` (`frozen_insert` re-freezes the facts on
`FL ∨ InsFoot`). Its proof is generic in the string's bytes but for `lits_ne_intU8` (no literal is the digits:
`%.14g`'s output and `"function: 0x…"` are no literal either) and the integer slot of `TolIIn`. A found
string's bytes survive the push by `StrtSafeIn`'s `W` (`prIntHit`), for any class.

## The proofs (per part)

| part | hand lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|
| boot: `litsCheck_tab`, `rdLE_bytes_eq`, `bytesT{8,4}_toNat_of_fill`, `entryW_sub`, `strSafeCheck`'s `ws` (`Boot/Check.lean`) | +89 net | 5.7 | 1,833 | < 50k |
| invariant: `TabFoot`, `EntryW`, `VmEntryData.lits_tab` (`EntryData.lean`), `TabFoot.trans`, `CallInvAt.tab_fl`, `CallAllocAt.strt`'s `W` (`Rel.lean`), `callInv_boot`/`strt_boot` (`Entry.lean`), `call_close`, `Errno` | +52 net (EntryData 8, Rel 17, Entry 18, CallClose 5, Errno 4) | — | — | < 50k |
| `PrintIn.dirty_in`/`dirty_g`, `LitsFoot.tab`/`.trans`, `InsG`, `StrtSafeIn`'s `D` (`CallOpen.lean`) | +8 net | — | — | — |
| `call_dirty_in`, `call_dirty_g`, `call_lits`, `call_alloc`, `nci_x` as `NciAt` (`CallPrint.lean`) | +9 net (two lemmas moved out to `TolIntProof`) | 92 | 7,406 | 100k–200k (5 over 100k, `call_printIn` among them; its new fields are the separate `call_dirty_in`/`call_dirty_g`) |
| `PrSt.nextKeep` (`next0` its instance), `litKeeps_of` (`litKeeps` its instance) (`PrintRel.lean`) | +18 net | 28.3 | 3,847 | 100k–200k (2 over 100k) |
| `tolInt_proved` and its parts (`Kit/TolIntProof.lean`: `tolI_in`, `tolI_tab`, `KWalk.congr`, `IaTab.congr`, `lits_nomatch`, `prIntHit`, `TiNew` with `keepU`/`keepIn`/`keepS`/`obj`/`insOk`/`ins`/`keeps`/`st`/`io`/`heap`/`cells`/`frame`, `prIntNew`; `Kept.not_mallocW`, `StdoutIn.buf_inUse` moved here) | 1,126 | 26.7 | 4,448 | 50k–100k (2 over 50k: `TiNew.obj`, `TiNew.keeps`) |
| generated | 0 (no generator change; the boot witnesses' `entryOk` re-decides the changed check) | — | — | — |

`python3 abstractions/gate.py` passes (`a1-kit-arm`: 69 cases, first 1.9, last 4.1). `lake build Lua Vsa
VsaIris` completes.

## Abstractions added

* A **context structure for a callee's outcome** (`TiNew`), so the stores are classified once
  (`keepU`/`keepIn`/`keepS`: a byte in use off the named words, a static byte off the allocator's globals) and
  every fact of the state is one application.
* **A footprint pins what a restricted check reads** (`litsCheck_tab`): a boot check over `v.only t` that
  names a fixed witness proves its reads lie in `t`, without a new `decide`.
* **Upper bounds on a callee's dirty set** as named fields the caller discharges from its invariant
  (`dirty_in`, `dirty_g`), never a premise of the callee's statement.

## Obstacles

1. **Two missing invariant facts** (above): `Rel.lean` and `EntryData.lean` changed, so ~500 modules rebuild
   (12.7 MB downstream of `Rel.lean`; the parallel lane F1-22 edits `Rel.lean` too, in `ValRepr`).
2. **Memory**: the default lake parallelism under `MemoryMax=16G` is OOM-killed (systemd stops the scope,
   exit 143); builds ran with `LEAN_NUM_THREADS=4–6` (full build 18 min).
3. **`omega` past the recursion limit** in large contexts holding `heapEnd`/`heapStart` as literals next to
   `sp0 - 64`: moved into small lemmas (`srcLo_of_heap`, `srcOut_of_heap`, `stdioGlob_lt`,
   `MallocGlobal.lt`) or `homega`.
4. **`omega` with metavariables**: `hbx _ ⟨by omega, by omega⟩` elaborates the proofs before the address is
   known; the address is given explicitly.
5. **Layout**: a `by simp only [...];` split over two lines inside a term does not parse; one line or a `have`.

## Axioms

`scripts/check.sh` stage 6 lists `tolInt_proved`, `CallOpen.print`, `tolI_in`, `tolI_tab`, `prIntHit`,
`prIntNew`, `TiNew.ins`, `TiNew.st`, `KWalk.congr`, `PrSt.nextKeep`, `litKeeps_of`, `LitsFoot.trans`,
`TabFoot.trans`, `litsCheck_tab`, `rdLE_bytes_eq`, `entryW_sub`, `call_printIn`:
`[propext, Classical.choice, Quot.sound]`.
