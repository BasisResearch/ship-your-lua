# F1 lane 16: `ErrorSimRest`, the error paths of `vm_refinement_of_open'`

Base main `0f36bdc`. Lines are non-blank, non-comment lines (`/- … -/` blocks
and `--` lines dropped). CPU and peak memory are one `lake env lean <file>`
of the module alone (`/usr/bin/time`, user s / peak RSS). Heartbeats: every
declaration elaborates at the default 200k (no option raised anywhere).

## Result

| target | status | where |
|---|---|---|
| `stuck_cases` after floats | **builds, matches** (rebuilt by float-s1); the module doc was stale (three escape families, "conservative superset"): now `Fault.Escape` is exact (only `FORLOOP`) | `Lua/StuckCases.lean` |
| `Fault.site` | **three mislabels fixed** (below), checked against `lvm.c`/`ltm.c`/`lstrlib.c` and the host `lua` | `Lua/StuckCases.lean` |
| `site_ops` (the enumeration by site: a non-escaping stuck state's opcode is one of `siteOps (φ.site vs)`) | **proved** | `Lua/StuckCases.lean` |
| `ThrowFrom` | **restated with an entry contract** (`ErrIn`): the old form was not dischargeable (below) | `Lua/Vm/Sim/Kit/{AtErr,ErrTail}.lean` |
| `ArmErr` delivers `ErrIn` (`a0 = L`, `a1` the message, `sp`, `gp`; memory off `ErrW` the arm entry's; `L->top = ci->top`, `ci->u.l.savedpc`) | **proved** for `mod_err`, `idiv_err`, `modk_err`, `idivk_err`, `forprep_err` (`at_err`: `Log.den_out`, `err_rd8`) | `Lua/Vm/Sim/Kit/AtErr.lean` |
| the messages (`"attempt to divide by zero"`, `"attempt to perform 'n%%0'"`, `"'for' step is zero"`) | **generated** (`msgIdiv0`, `msgMod0`, `msgForZero`, from `.rodata`, each found once at a string start) | `Lua/Vm/LayoutErr.lean` (`gen_lua_layout.py`) |
| the throw `luaG_errormsg` → `luaD_throw` → `longjmp` → `luaD_rawrunprotected` returns `2` into `luaD_pcall` | **proved**: `Kit.throw_land` (generated segments, `kit_run`) | `Lua/Vm/Sim/Kit/Throw.lean` |
| the shared tail from `luaG_errormsg` | **proved from `Unwind_Statement`**: `Kit.errorTail_of_unwind` (`throwMem_of`: the `jmp_buf` and `luaD_rawrunprotected`'s frame from the caller frames, `throw_callers`) | `Lua/Vm/Sim/Kit/ErrTail.lean` |
| `ThrowFrom f msg` from a head and the tail | **proved**: `Kit.throwFrom_of` | `Lua/Vm/Sim/Kit/ErrTail.lean` |
| a site from its head and the tail | **proved**: `errorSimAt_of_head` | `Lua/Vm/Sim/StuckErr.lean` |
| `ErrorSimRest` | **narrowed** (below) | `Lua/Vm/Sim/StuckErr.lean` |

Axioms of `site_ops`, `throw_land`, `throw_callers`, `throwMem_of`,
`errorTail_of_unwind`, `throwFrom_of`, `errorSimAt_of_head`, `runerrorSim`,
`errorSim_of_rest`, `vm_refinement_of_open'`: `[propext, Classical.choice,
Quot.sound]` (check.sh stage 6).

## The enumeration after floats

`stuck_cases` builds unchanged. `Fault.site` named the wrong C function for
three families (no theorem was false: `ErrorSimAt` only asks `StuckOut`, but
each field claimed to be one raising function):

| stuck state | old site | Lua 5.4.7 raises (host `lua` message) | new site |
|---|---|---|---|
| `OP_UNM` of a non-numeral string | `opinterror` | `__unm` → `arith_unm` → `trymt` → `luaL_error` (`attempt to unm a 'string' with a 'string'`) | `strarith` |
| `OP_BNOT` of a float without an integer value | `opinterror` | `luaT_trybinTM(TM_BNOT)` on two numbers → `luaG_tointerror` (`number has no integer representation`) | `tointerror` |
| `OP_FORPREP` float loop with step `0.0` (or an integer `0` step with a float control value) | `forerror` | `forprep` → `luaG_runerror("'for' step is zero")` | `runerror` (`fltZeroStep`) |

By site (`siteOps`, `site_ops`):

| site | opcodes | C function | arm path to it |
|---|---|---|---|
| `runerror` | MOD, IDIV, MODK, IDIVK, FORPREP | `luaG_runerror` (`msgIdiv0`, `msgMod0`, `msgForZero`) | **proved** (`At.*_err`), but FORPREP's float zero step (`FpFltZero_Statement`) |
| `opinterror` | MMBIN, MMBINI, MMBINK, UNM, BNOT | `luaT_trybinTM` → `luaG_opinterror` | open (`SiteHead_Statement`) |
| `tointerror` | MMBIN, MMBINI, MMBINK, BNOT | `luaT_trybinTM` → `luaG_tointerror` | open |
| `strarith` | MMBIN, MMBINI, MMBINK, UNM | the string metamethod → `trymt` → `luaL_error` | open |
| `typeerror` | LEN | `luaV_objlen` → `luaG_typeerror` | open |
| `ordererror` | LT, LTI, GTI, LE, LEI, GEI | `luaT_callorderTM`/`luaT_callorderiTM` → `luaG_ordererror` | open |
| `concaterror` | CONCAT | `luaV_concat` → `luaT_tryconcatTM` → `luaG_concaterror` | open |
| `forerror` | FORPREP | `forlimit`/`forprep` → `luaG_forerror` | open |
| `callerror` | CALL | `luaD_precall` → `luaD_tryfuncTM` → `luaG_callerror` | open |

## `ThrowFrom` was not dischargeable

`ThrowFrom f := ∀ p c s c', … VmRel p c s → Steps c c' → ErrAt f c' → StuckOut c'`
gave, at `f`'s entry, only the pc: no register (`a0 = L`, the message in
`a1`, `sp`) and nothing about the memory. A summary of `luaG_runerror` is a
statement about its entry state; the only way to discharge the old form was
to re-derive the run from `c` to `c'`, i.e. the arm's path again, for an
arbitrary `c'`. Restated: `ThrowFrom f msg := ∀ X c, Supported X.p → Reach
X.p X.s → Core X.p X.c X.s X.w → ErrIn X f msg c → StuckOut c`, with `ErrIn`
read off the at-lemmas' last row and log (`at_err`); `gen_lua_at.py` keeps an
`auipc` address as a literal (the message), which changed only the five
error rows (one pin each).

## What is left (`ErrorSimRest`)

| field | statement | blocked on |
|---|---|---|
| `runerrorHead` | `RunerrorHead_Statement symLuaGRunerror msg`, per message: `ErrIn` → `ErrMsgIn` (`luaG_errormsg`'s entry, the message pushed) | `luaO_pushvfstring`, `luaS_newlstr`/`internshrstr` (the string table, `luaS_resize`), `_malloc_r` (`MallocR_Statement`), `snprintf("%lld")` (`_svfprintf_r`, as `IntegerToStr_Statement`) |
| `unwind` | `Unwind_Statement`: from `throw_land`'s post (`luaD_pcall`, status 2) to `StuckOut` | `luaD_pcall`'s error branch (`luaD_closeprotected`: a second `setjmp`; `luaD_seterrorobj`; `luaD_shrinkstack`: `luaD_reallocstack` when the stack exceeds three times its use, no `_realloc_r` summary; `luaE_shrinkCI` → `_free_r`, `FreeR_Statement`), `main`'s `fprintf(stderr)` (`_vfprintf_r`, 3,395 instructions, no summary at Lua addresses; `__sinit` if no `print` ran), `exit(2)` with `stderr` written (its `_fclose_r` is not `StdQuiet`'s) |
| `fpFltZero` | `ArmErr .FORPREP FpFltZ symLuaGRunerror msgForZero` | the three-float case is on the at-lemma route (`At/ForprepF.lean` reaches `0x800092cc` with the message; its log is inside `ErrW`): the join route's `at_walk` stops at the fetch head, an error leaf needs a hand-off; the coerced classes call `luaV_tonumber_` (`FpCoerce_Statement`'s node) |
| `opinterror` … `callerror` | `SiteHead_Statement e`: the relation at a stuck state of site `e` → `ErrMsgIn` | each helper on the failing operands (`luaT_trybinTM`, `luaV_objlen`, `luaT_callorderTM`, `luaV_concat`, `luaD_precall`), `varinfo`'s symbolic execution of the prototype (`getobjname`), `luaG_typeerror` → `luaG_runerror`'s formatting (as `runerrorHead`), `lua_error` for `luaL_error` |

The seam `ErrMsgIn X c` (`Kit/ErrTail.lean`) is relative to the arm context
`X`: the memory off `HeadW` (what a message's formatting writes: the C stack
below `luaV_execute`'s frame, the error path's spills, `MallocW`, `g` up to
its string cache, the string table's chunk, the Lua stack above `ci->func`
with `EXTRA_STACK`, `L->top`; all below the entry `sp`) is `X.c`'s,
`L->errfunc = 0`, `L->errorJmp = ljAddr`, a heap keeping `X`'s chunks in use
(but the string table's), the message a string just below `L->top`. All nine
sites end there, so the tail is proved once (`throw_land`) and named once
(`Unwind_Statement`).

## Evidence (Sail)

`c/tests/stuck/e_mod0.lua` on the ELF (`lean_riscv_emulator --trace-pcs` on
every function entry): from `luaG_runerror` (step 180,415) to `_exit` (step
185,129), 4,714 steps: `luaO_pushvfstring` ×2, `internshrstr` ×2, `_malloc_r`
×2, `luaG_getfuncline`, `luaG_addinfo`, `snprintf` → `_svfprintf_r`,
`luaG_errormsg` (182,987), `luaD_throw`, `longjmp`, `luaD_rawrunprotected`
(183,044), `setjmp` (the close's protected call), `closepaux`, `luaF_close`,
`luaD_seterrorobj`, `luaD_shrinkstack`, `luaE_shrinkCI`, `lua_tolstring`,
`fprintf` → `_vfprintf_r` → `__sinit` → `__swsetup_r` → `__smakebuf_r`
(unbuffered: no allocation) → three `_write`s, `exit` → the handler's three
`_fclose_r`, `_exit` with code 2 ("lua: ?:-1: attempt to perform 'n%0'").
The `luaD_rawrunprotected` resume at `setjmp`'s return and the status `2`
agree with `throw_land`.

## Per part

| part | hand lines | generated lines | CPU | peak | largest declaration |
|---|---|---|---|---|---|
| relabel, `site_ops` (`StuckCases.lean`) | +60 | — | | | |
| `ErrIn`, `ArmErr`, `at_err`, `Log.den_out` (`Kit/AtErr.lean`) | +75 | `At/{Mod,Idiv,Idivk,Modk,Forprep}` +1 each; `LayoutErr.lean` +6 | | | |
| the throw (`Kit/Throw.lean`) | 95 | segments + sites 2,280 (`HluaG_errormsg`, `HluaD_throw`, `Hlongjmp`, `HluaD_rawrunprotected`'s new root), code pins 1,319 | | | `throw_land` ≤ 200k |
| the seam and the tail (`Kit/ErrTail.lean`) | 91 | — | | | |
| `ErrorSimRest` (`StuckErr.lean`) | +55 | — | | | |
| generators (`gen_lua_at.py` +3, `gen_lua_layout.py` +17, `gen_lua_arms.py` +16, `gen_lua_code.py` +2) | 38 | — | — | — | — |
