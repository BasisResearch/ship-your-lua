# Lane F1-12: toward `SimArm .CALL`: the arm on an invariant, `luaD_precall`, the literal classes

Base: main `212aa92`. Route: CLAUDE.md's callee-context rows (lanes F1-8..11)
and the arm kit's `kit_run`. Lines are non-blank, non-comment lines (`--`
lines and `/- … -/` blocks dropped). CPU and peak memory are one `lake env
lean <file>` each (`/usr/bin/time -v`: user time, maximum resident set).
Heartbeats are per declaration, bracketed by rerunning the file with
`-DmaxHeartbeats` 25k, 50k, 100k (never raised; default 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1a. `luaL_tolstring` on nil, `true`, `false` | **proved over `lua_pushstring`'s summary** | `tol_nil`, `tol_true`, `tol_false` (`Kit/Tolstring.lean`) through `lua_absindex`, `luaL_callmeta` → `lua_getmetatable`, `lua_type`, `lua_toboolean` (generated at-lemmas `AtF/{TolNil,TolTrue,TolFalse}.lean`) and the tail `lua_tolstring(L, -1, &l)` (`toltop_sum`, `AtF/TolTop.lean`); `TolPost` by `tolPost_of_lit`. Premise: `PushLit_Statement` (`LitInterned`, `luaHash`) |
| 1b. `luaL_tolstring` on strings, integers, floats, functions | open | (PHASES row) |
| 1c. the concrete `S` for `PrintLua` | **done** | `PrS`, `Kept`, `ArgPred`; `printLua_of` proves `PrintLua.gettop`, `settop`, `stable` (`Kit/PrintS.lean`) |
| 2. heap room | **stated** | `HeapBudget w args` (`callBudget`) a hypothesis of `PrintCall_Statement` for the allocating classes only (`Allocates`, `AnyAlloc`); `HeapBudget_Statement I` the emergency-GC path (A8); `sim_CALL_of` splits on it (`Kit/CallArm.lean`) |
| 3a. `luaD_precall`'s C path | **proved over its callees' summaries** | `precall_join`, `precall_reuse`, `precall_ext` (`Kit/Precall.lean`; at-lemmas `AtF/{Precall,PrecallExt}.lean`); the C function (`PcC`), `luaE_extendCI` (`PcExt`), `luaD_poscall` (`PcPos`) hypotheses |
| 3b. `luaD_poscall` | `C = 1` by `poscall_sum` (lane F1-4); `C ≥ 2` open | regenerating `HluaD_poscall` past its stop `0x8000a4d8` changes `seg_8000a4b8_8000a4d0`, which `poscall_sum` uses |
| 3c. relation facts | **partly done** | `LuaStateRel` (`Rel.lean`): `ci->next` NULL or a `CiNext` block, `L->ci = ci`; `RelPtrs.after`, `Ranges.after`, `CallOut`. Open: `stdout`'s state, the heap room for its buffer, the static/dynamic separation and the post-print `exit` as a `Complement` invariant (obstacle 1) |
| 4. `SimArm .CALL` | **the arm proved on an invariant** | `sim_CALL_of : PrintCall_Statement I → HeapBudget_Statement I → SimArmInv .CALL I`; `OpenArms.CALL` stays (its doc says why) |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(`Kept.not_printW`: `[propext, Quot.sound]`). check.sh stage 6 lists
`LuaStateAt.rel`, `precall_join`, `precall_reuse`, `precall_ext`,
`call_step`, `Ranges.after`, `call_ra`, `call_top`, `call_nres`,
`sim_CALL_of`, `Kept.not_printW`, `Kept.mono`, `ApiAt.congrT`,
`printLua_of`, `toltop_sum`, `absindex_pos`, `tol_nil`, `tol_true`,
`tol_false`, `tolPost_of_lit`.

## 1. The arm on an invariant (`sim_CALL_of`)

`OP_CALL`'s segments are sim segments now (`SIM_OPS`), the `jal
luaD_precall` a call node whose arguments stay live (`CALL_ARGS`: `a0` = L,
`a1` = `R[A]`, `a2` = `C - 1`). The arm: `call_step` (the kernel's step:
`print`, the `C - 1` nil results, the frame killed above them, the line),
`dispatchM`, `kit_run` to `luaD_precall`'s entry (the guard `B ≠ 0`, the
fields by `call_ra`, `call_top`, `call_nres`), the premise
`PrintCall_Statement I`, `kit_run` back to the head (`beqz` on `0`,
`updatetrap` reading `ci->u.l.trap = 0`), and the close: `Core` at the
summary's pointers `w.after mo ι rt` from `CallOut` (the frame of the new
complement, `luaV_execute`'s C frame and the registers below `R[A]` kept,
the results nil, the trap word, every representation carried over, the
closure). `SimArmInv o I` is `SimArm o` on the states with an invariant `I`
of the relation's pointers, which the arm keeps.

## 2. The literal classes

`luaL_tolstring` on nil/`true`/`false` is one at-lemma module per literal
tag (the generator's cells are literals, and `G(L)->mt[t]`'s address needs
the type as a literal), 31–38 lemmas each, walked through `lua_absindex`,
`luaL_callmeta` → `lua_getmetatable` (`mt[nil]`, `mt[boolean]` NULL),
`lua_type`, `lua_toboolean`, to the `lua_pushstring` call node and, after
it, the tail `j lua_tolstring` (an `ends`). One macro (`tol_lit_run`) proves
the three: the run, `PushLit_Statement` at the call (its interned facts of
any memory agreeing below `__heap_end`, so no congruence of `LitInterned`
is needed), the run after it (the saved words through `PushPost.keep`),
`toltop_sum`. `tolPost_of_lit` turns `TolLitPost` into `print_sum`'s
`TolPost` for `PrS` (where the pushed slot, `g`'s words and the string lie:
`TolLitAt`).

## Per piece

| piece | hand lines | generated lines | CPU / peak (hand file) | largest declaration |
|---|---|---|---|---|
| `luaD_precall` C path (`Kit/Precall.lean`) | 205 | at-lemmas 326 + 214 (7 + 5, 4 + 2 roots); segments 1,945 (`HluaD_precall`) | 8.0 s / 2.1 GB; at-lemmas 22.3 s, 17.0 s / 2.2 GB | (25k, 50k] |
| the arm on an invariant (`Kit/CallArm.lean`) | 241 | `OP_CALL`'s sim segments (G00, G13, G14, G90: +460 / −169) | 5.5 s / 2.0 GB | `sim_CALL_of` (50k, 100k] |
| concrete `S` (`Kit/PrintS.lean`) | 114 | — | 1.2 s / 2.1 GB | ≤ 25k |
| the literal classes (`Kit/Tolstring.lean`) | 374 | at-lemmas 839 + 1,036 + 986 + 264 (`TolNil`, `TolTrue`, `TolFalse`, `TolTop`); segments 5,800 (seven helpers), code pins 12 files | 51.0 s / 3.0 GB; at-lemmas 135 s, 172 s, 172 s, 12 s / 3.0–3.3 GB | `tol_nil`, `tol_true`, `tol_false` (100k, 200k] |
| relation (`Rel.lean` `LuaStateRel`, `CiNext`; `Entry.lean`, `Vararg.lean`) | 57 + 11 | — | full rebuild 5 min 30 s wall, 73 min CPU | — |

Setup (generators, library): `gen_lua_arms.py` +55 (`OP_CALL` sim, eight
helpers, `CALL_ARGS`, `INDIRECT` `jalr a7`, `CALLEE_READS` of
`luaE_extendCI`, `lua_pushstring`), `gen_lua_at.py` +122 (`luaD_precall`,
`luaD_precall/ext`, `tol_lit` ×3, `lua_tolstring/top`; a NULL test of a
pointer atom decided by its lower bound), `gen_lua_code.py` +5,
`Kit/AtFn.lean` +10 (`fat_shl`: a scaled-index load).

## Obstacles (with evidence)

1. **`SimArm .CALL` is not satisfiable over `VmRel` as it stands.** Before
   this lane, `RuntimeMem.lua : LuaStateAt` held `ci->next = 0`
   (`LuaStateAt.next`), and `Ranges.ci_out` puts that word outside the
   window, so `Core.frame` fixes it in the machine: after the first `print`
   (`precall_ext`: `ci->next` NULL → `luaE_extendCI`, which links the C
   `CallInfo` there) no `VmRelAt` holds at the head. `LuaStateRel` fixes this
   one (`ci->next` NULL or a `CiNext` block). Two remain, outside what the
   relation can say today:
   * `stdout`'s state (`StdoutIn`, `PrintCells`, the buffer's room at boot)
     is not in `Complement`: a `VmRel` state whose `__sf` is garbage
     satisfies every field, and `print` there does not print its line;
   * the complement's static facts (`ProtoRepr`'s upvalue array and nested
     prototypes, `EnvMem`'s table and nodes) have no location the relation
     knows: nothing rules out their bytes in the arena's free chunks, where
     `print`'s `_malloc_r` writes.
   So `PrintCall_Statement I` is true only for an `I` carrying these (the
   `stdout` phase, the room, the static objects in chunks in use apart from
   the `CALL`'s dynamic words, the post-print `exit`), and `SimArm .CALL`
   follows from `sim_CALL_of` once `Complement` carries `I`. Its definitions
   (`StdoutIn` & co.) live in `Kit/` above `Rel.lean`; at the entry, `I` needs
   boot facts the contract does not state yet (`RuntimeReadyAt`: the room
   for the buffer, the objects' chunks), checked by the boot witness as
   `RuntimeReadyAt.vararg` was for `VARARGPREP`.
2. **`luaD_poscall` with `C ≥ 2`.** `HluaD_poscall` stops at `0x8000a4d8`
   (wanted ≠ 0); removing the stop regenerates `seg_8000a4b8_8000a4d0`
   (more paths reach it), which `poscall_sum` (lane F1-4) uses: the
   generalisation needs `poscall_sum` re-run on the new segments.
3. **One at-lemma module per literal tag** (lane F1-11's obstacle 4 again):
   `luaL_tolstring`'s nil/`true`/`false` paths differ only in the tag cell and
   the literal, but `G(L)->mt[t]`'s address needs `t` literal (a symbolic tag
   makes it non-affine: the generator stops). A cell of known low bits would
   merge them; the three proofs are one macro meanwhile.
4. **`omega` and `__heap_end`.** With `heapEnd` (or its literal) in context
   `omega` reaches the recursion limit (as lane F1-10 saw);
   `homega` generalises it first.
5. **Heavy declarations.** `tol_nil`/`tol_true`/`tol_false` take (100k,
   200k] heartbeats each (the at-lemma chain of ~30 rows plus the call);
   `sim_CALL_of` (50k, 100k]. Within the default; not raised.

## What is left (the remainder)

* The `CALL` invariant in `Complement` and its boot facts (obstacle 1); then
  `PrintCall_Statement` from `precall_reuse`/`precall_ext`, `print_sum`
  with `printLua_of`, `poscall_sum`, `luaE_extendCI`, the growth path, the
  post-print `exit`.
* `PushLit_Statement` (`lua_pushstring` → `luaS_new` → `internshrstr`).
* `luaL_tolstring` on strings, integers (`IntegerToStr_Statement`), floats
  (`G14From`), functions.
* `luaD_poscall` with `C ≥ 2` (obstacle 2), the stack-growth path of
  `luaD_precall`, `luaE_extendCI`, `HeapBudget_Statement` (A8),
  `MallocR_Statement` (A0).

## Gate

`abstractions/gate.py`: `a1-kit-arm` ok (58 cases, first 2.1, last 2.9;
`sim_CALL_of` is not matched by the cluster's names). `a1-float-arm` fails
as on the base (its files unchanged).
`scripts/check.sh`: stages 1–3b, 4, 5 (the full `lake build Lua Vsa VsaIris`),
5b and 6 (445 axiom reports, all within `propext`, `Classical.choice`,
`Quot.sound`) pass (296 s wall for the stages after 3c); 3c is the base's
float cluster above.
