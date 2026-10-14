# Lane F1-F7: libm `fmod`, and MOD's and MODK's float paths

The base is main `5b168a5`. The routes are the `SfRef` route with
`gen_lua_fn.py` for the routine, and the join route (A-JOIN, lanes F2–F6's
shape macros) for the arms.

The numbers are taken as in lanes F2–F6:

- **Hand lines** are non-blank, non-comment lines, without `import`, `open`,
  `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports
  built (`LEAN_NUM_THREADS=4`). **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k,
  100k or 150k under which the file builds. The limit is never raised; the
  default is 200k.

## Result

| target | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| libm `fmod`, level (a) | **proved** | `FmodW.sum` (`Lua/Vm/Fn/FmodW.lean`, generated) | 0 | 271 | 21.8 s | 2.71 GB | ≤ 100k |
| `fmod = SfRef.fmod` | **proved** | `FmodR.F_eq`, `FmodR.sum`, `FmodR.model` (`= Lua.Num.fmod`), `FmodR.S_bits` (`Lua/Vm/Fn/FmodR.lean`) | 73 | — | 1.6 s | 2.58 GB | — |
| `__unorddf2`, `__errno` (call nodes) | **proved** | `Unorddf2.sum`, `Errno.sum` (generated), `ErrnoR.sum_imp` | 12 | 78 + 13 | 6.1 s + 1.9 s + 1.2 s | 1.89 GB | — |
| `errno` in the relation | **proved** | `Complement.errno`, `Core.errnoF`, `AtFinE.close`, `sim_arm_onE` (`Kit/{Errno,AtErrno}.lean`) | 208 + 99 | — | 2.3 s + 2.0 s | 2.26 GB | — |
| MOD (float paths) | **proved** | `sim_MOD_flt` (`Kit/AtFltMod.lean`) | 1 | `At/ModF` 1976 | 29.1 s (at-file 385.8 s) | 3.14 GB (at-file 6.50 GB) | ≤ 100k (at-file ≤ 100k) |
| MODK (float paths) | **proved** | `sim_MODK_flt` (`Kit/AtFltModk.lean`) | 1 | `At/ModkF` 1956 | 29.4 s (at-file 432.2 s) | 3.08 GB (at-file 6.65 GB) | ≤ 100k (at-file ≤ 100k) |

`FloatArms` loses `MOD` and `MODK`. It keeps 4 fields: `soft` (empty), `POW`,
`POWK` and `FORPREP : FpCoerce_Statement`.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
They are in check.sh stage 6.

## Setup

| file | hand lines | what |
|---|---|---|
| `scripts/gen_lua_fn.py` | python | `__unorddf2`; `__errno` (`LEAF_MF`: a leaf whose lifted function reads memory and the caller's frame); `fmod`: `PRO_SAVES` (callee-saved registers saved in the prologue and reassigned, read back by the epilogue's restores), `call_g` (a callee whose frame stores the caller's registers gets the frame of the *current* registers, `SFrame.mk`), `FACTS` (node facts every lemma carries: `hgp`, `hsI`, `himp`), `OUTER` (a store outside the frame: the memory is two patches of the memory function), constant propagation (`__errno`'s literal result is the address of the store); five `CALLEES`. The other routines regenerate byte-identically. |
| `Kit/FnOuter.lean` | 79 | `memPatch_wm4_outer`, `bytesT8_wm4_far`, `RodataRead.wm4`, `fn_imp`, `fn_rod_patch4`, `fn_ra_patch4`, `fn_odisch` |
| `Lua/Vm/Sim/Rel.lean` | +6 | `ErrnoW`; `ExitFree` gains it |
| `Kit/ExitUp.lean`, `Kit/RetFinal.lean`, `Entry.lean` | +25 | `exitUp_of_free`, `exit_agree`, `exitOk_entry` with `errno` free (`StdioFoot`, `HeapReads`, the buffer apart from it) |
| `Kit/AtArm.lean` | +5 | `at_close` closes a goal with the pointers free too |
| `Kit/AtFmod.lean` | 51 | `at_fnSp'`, `at_sI`, `Cx.Ok.heap_ptrs`, `Cx.Ok.impure_at`, `at_gp`, `at_imp` |
| `Kit/AtJoinMod.lean` | 167 | the stored-float rule of `luai_nummod`; `at_jmod*` (the kernel's `nummod` left in `hk`); `ArmBodyE`, `armBodyE_cls(P)`, `armBodyE_kcls`, `KCls`, `sim_on_orE`; `mod_flt_arm`, `modk_flt_arm` |
| `scripts/gen_lua_at.py` | python | `OP_MOD_F`, `OP_MODK_F`; `FCALL_ARM` `FmodR` with `FRAME_G` over all thirteen registers (`FRAME_FN`), `FARGS`, `FSP`; `FOUTER` (the `errno` window as a second `Ent.clob`, content the call's memory function over its entry log); `AtFinE`/`at_finE` fin lemmas after it |
| `scripts/gen_lua_arms.py` | python | `fmod` in `FLOAT_CALLS`, MOD/MODK in `FLOAT_ARMS`, `FLOAT_CALL_KEEP` (`s6`, `s10` live into `fmod`'s call). This regenerates `Segs/G30–33, G45–47, G59–62`; `At/Mod`, `At/Modk` regenerate and build. |

## How

1. **The wrapper's value.** `w_fmod.c` returns `z = __ieee754_fmod(x, y)`,
   unless `y == 0` and `x`, `y` are ordered, where it stores `EDOM` and
   returns `0.0/0.0`. On `y = ±0` the reference `SfRef.fmod x y` is already
   `qnan` (`fmod_cls`), and `F64.div 0 0 = qnan`, so `F = SfRef.fmod` on
   every input whatever `__unorddf2` answers (`F_eq`; `__unorddf2` needs no
   level (b)).
2. **`errno` is a store outside the window.** `luai_nummod` calls `fmod`
   with `y = 0` for `x % 0.0`, so the arm reaches the store. The
   relation's complement changes there; the arm closes at `w.errno M` (the
   complement with `errno` from the final memory, `errnoMo`). Nothing the
   complement states reads `errno`: its region facts are the `CALL`
   invariant's (`F`, `FL` in the heap or below `tohost`; `StdioFoot`
   excludes the allocator's words, `errno` among them; `HeapReads` misses
   it), and `ExitFree` now contains it, so `exit` finds it free.
3. **The frame is the row's.** `fmod`'s frame stores the caller's
   callee-saved registers through `__ieee754_fmod`'s and `__divdf3`'s
   frames, and `Ieee754Fmod.Fm`'s dependence on them cannot be cut by `rfl`
   (its cycles recurse on `fnFuel`). Every callee-saved register is kept
   live into the call (`FLOAT_CALL_KEEP`), so the frame is `SFrame.mk` of
   the row (`FRAME_FN`).
4. **The arms.** The kernel's `nummod` is left in `hk`, so the leaf splits
   its comparisons and refutes the side the machine's forks contradict
   (`ofNat_zero_eq`, `SfRef.fmod_model` are `at_atom_simp`). One declaration
   per (float operand, the other's class) keeps each under the budget.

## Open

- **POW, POWK** need newlib `pow`.
- **FORPREP**'s `FpCoerce_Statement` needs `strtod`.

## Builds

- **Module builds.** `Lua.Vm.Fn.FmodR`, `Lua.Vm.Sim.Kit.Errno`,
  `Lua.Vm.Sim.Kit.AtErrno`, `Lua.Vm.Sim.Kit.AtFmod`, `Lua.Vm.At.ModF`,
  `Lua.Vm.At.ModkF`, `Lua.Vm.Sim.Kit.AtFltMod`, `Lua.Vm.Sim.Kit.AtFltModk`,
  `Lua.Vm.Sim.Kit.ExitUp`, `Lua.Vm.Sim.Kit.RetFinal`, `Lua.Vm.Sim.Entry`
  build with exit 0.
- **Full build and check.** `scripts/check.sh` passes every stage, `lake build Lua Vsa VsaIris` included.
- **Gate.** `python3 abstractions/gate.py` is ok: `a1-float-arm` 40 cases
  (first 2.9, last 2.7); `a1-kit-arm` ok.
- **Obstacles met.**
  - `rfl` cannot show `Ieee754Fmod.Fm` ignores the caller's dead registers
    (its fuel recursion): solved by keeping them live (point 3).
  - The whole MOD arm in one declaration exceeds 200k heartbeats: split per
    operand class (`mod_flt_arm`).
