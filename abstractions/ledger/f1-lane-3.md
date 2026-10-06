# F1 lane 3: the `VmSim` fold, `VARARGPREP`, the return family

Base `df460c9`. Lines are non-blank, non-comment lines (`/- … -/` blocks and
`--` lines dropped). CPU and peak memory are one `lake env lean <file>` of the
module alone (`/usr/bin/time`, user s / peak RSS). Heartbeats are per
declaration, measured by lowering `maxHeartbeats` per theorem until it fails
(`set_option maxHeartbeats K in`, never raised): "≤ K" means it elaborates in
K, "> K" that it does not.

## What is proved

| theorem | file | statement |
|---|---|---|
| `fold_sim`, `FoldSim.{reach,diverges,term,stuckOut}` | `Lua/Vm/Sim/Fold.lean` | `Refine.Sim` from a relation and the step/final/stuck clauses at reachable states |
| `vmSim_of_arms` | `Lua/Vm/Sim/Fold.lean` | `(∀ o ∈ armOps, SimArm o) → EntrySim → VarargSim → FinalSim → StuckSim → VmSim luaLayout` |
| `armTable` | `Lua/Vm/Sim/Fold.lean` | `OpenArms → ∀ o ∈ armOps, SimArm o` (34 proved arms, 18 named open premises) |
| `vm_refinement_of_open` | `Lua/Vm/Sim/Fold.lean` | `OpenArms → FinalSim → StuckSim → vm_refinement_Statement luaLayout` |
| `entrySim` (`entry_at`, `relParts`, `entry_fresh`) | `Lua/Vm/Sim/{Entry,Vararg,Fold}.lean` | the entry clause with the entry-only facts `FreshAt` |
| `Kit.varargSim` | `Lua/Vm/Sim/Kit/Varargprep.lean` | `VarargSim`: `OP_VARARGPREP` at the entry, `VmRel` at the moved pointers |
| `Kit.adjvar_sum` (`av1`, `av2`, `av3`) | `Lua/Vm/Sim/Kit/Adjvar.lean` | `luaT_adjustvarargs(L, 0, ci, p)` at the entry, the call-node summary |
| `DefInit.pc_pos`, `reach_pc_zero` | `Lua/FragmentSound.lean`, `Fold.lean` | no supported step targets pc 0; the one reachable pc-0 state is the entry |

Axioms of each: `[propext, Classical.choice, Quot.sound]` (check.sh stage 6).

## Per part

| part | hand lines | generated lines | CPU | peak | largest declaration |
|---|---|---|---|---|---|
| the fold (`Fold.lean`) | 255 | — | 8.1 s | 2.2 GB | `armTable` (53 cases) > 25k; the rest ≤ 25k |
| entry clause (`Vararg.lean`, `Entry.lean` +78) | 141 + 78 | — | 1.9 s | 1.9 GB | all ≤ 25k (`entry_fresh`) |
| entry contract (`Repr` +37, `Runtime` +11, `Boot/{View,Check,Assemble}` +50, generator +2) | 100 | the two witnesses' `rtPostOk` (regenerated, 1 line each) | witness ≈ 320 s wall each | 3.3 GB | `rtOk`/`rtPostOk` (`decide +kernel`) |
| `adjvar_sum` (`Kit/Adjvar.lean`) | 264 | `HluaT_adjustvarargs` segments 1,497 + sites 1,398; `G20`/`G63` re-cut | 17.9 s | 2.0 GB | ≤ 100k (the epilogue `av3` region > 50k; `av1` > 25k) |
| the arm (`Kit/Varargprep.lean`) | 344 | — | 16.4 s | 2.2 GB | all ≤ 50k (`vmem_frame` > 25k) |
| semantics (`Semantics` kernel line, `Fragment` `edges`, `FragmentSound` +8) | 9 | — | — | — | — |

## Route

* **The fold** is the only new abstraction: one generic theorem (`fold_sim`)
  over any relation, so a new arm is one `armTable` case and no arm proof
  touches `Steps` induction.
* **`VARARGPREP` is not on the at-lemma generator** (`gen_lua_at.py`). It cannot
  express this arm:
  * its close `AtFin.close` keeps the relation's pointers `w`, and the arm
    moves `ci->func`;
  * `ld a3,24(a5)` loads through a loaded pointer (`a5 = 8(sp)`, the closure):
    `addr_of` stops on a non-affine base;
  * `lw` (the trap reload) and the callee's `sw` (`nextraargs`) have no
    `Loc`/`Ent`.

  The arm uses the segment-local principle by hand-free means instead: one
  declaration per generated segment (`vp1`, `vp2`, `vp3`; `av1`–`av3` in the
  helper), each `kit_run` over that segment alone, normalised to a named row,
  and composed by `Triple.seq`. There is no hand split, frame or loop
  induction. The relocation's memory frame is one lemma (`vmem_frame`) over the
  store chain against `varargMem`.
* **The complement after the move** comes from the entry contract checked by
  the boot witness (`RuntimeReadyAt.vararg`, `VmEntryData.vararg_proto`), not
  from frame lemmas of `ProtoRepr`/`HeapAt`/`LuaStateAt`. Those would need
  per-object separation facts (the `Proto` header, `g`, the string table's
  chains, the heap chunk headers against the `CallInfo` and the stack) that no
  current invariant states. The kernel check over `postView` is ≈ 30 s per
  program.
* `maxstack_not_dirty` turns the framed `vararg_proto` into the separation
  `p->maxstacksize ∉ CallInfo` (a memory with that byte changed would break
  `ProtoRepr`), so no new address fact was needed for the `savedpc` store.

## Obstacles

* **`SimArm .VARARGPREP` is false-in-general as stated.** `VmRel` leaves
  `L->top` free (`Scratch`), and `luaT_adjustvarargs` moves `ci->func` by
  `L->top - ci->func`. Its `A` was also unconstrained. Fixed in the semantics:
  the kernel exists only at pc 0 with `A = 0`, `supportedB` rejects edges into
  pc 0, and the obligation is `VarargSim` (the entry state only). The corpus
  stays `Supported`; `Lua.Programs.*` rebuilt.
* **`FinalSim` is not provable from `VmRel`.** The return runs
  `luaV_execute`'s epilogue, which reloads `ra` and `s0 … s11` from its C frame.
  `VmRel` leaves that frame free (`Win`). Its `Complement` says nothing about
  the caller frames above `sp` that `ccall`, `luaD_rawrunprotected`,
  `lua_pcallk`, `main` and newlib's `exit` return through. Needed:
  * `Core` keeping the 13 saved words. No arm writes `72…175(sp)`; only the
    prologue does (`objdump` of `luaV_execute`);
  * `Complement` keeping `RuntimeData.callerFrames`;
  * the summaries of `luaF_close` (`openupval = NULL`, `tbclist` below
    `base`), `luaD_poscall` (`wanted = 0`, `moveresults` case 0), the C
    returns, `exit` (`__call_exitprocs`, `__stdio_exit_handler`) and
    `_exit`'s `tohost` store (`TohostSite`).

  Adding `Core` fields is a cross-lane change to every close (`Core.write`,
  `jump`, `update`, `bleach*`, `AtFin.close`), so it was not done in this lane.
* The corpus's main chunks all end in `RETURN A 1 1` (`k` set: `luaF_close`,
  and `ci->func` moved back down by `nextraargs + 1`, undoing
  `VARARGPREP`). `RETURN0`/`RETURN1` take the fast path without
  `luaD_poscall` when `hookmask = 0`.

## Gate

`scripts/check.sh` (all stages, including the full `lake build Lua Vsa VsaIris`
and stage-6 axioms): OK, 4 min 45 s wall, 3.1 GB peak. `abstractions/gate.py`:
ok (`a1-kit-arm` 0 cases: its regex selects `sim_<OP>`/kit path lemmas, and
this lane's arm lemmas are `vp1`–`vp3`, `varargSim`).
