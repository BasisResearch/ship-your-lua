# Remaining unwind invariant seams

Source audit, 2026-10-27. This is a task map, not a new proof.

`Kit/Unwind.lean` keeps `PcallErr_Statement` and `FprintfErr_Statement`
open. `AllocProof.reallocShrink_proved` (`e23fff3`, full gate pending)
now supplies the allocator shrink seam; `freeRHeap_proved` supplies the
free seam. The caller must still establish their ownership and ABI inputs.

## Successor CallInfo

`Sim/Rel.lean`'s `CiNext` records bounds, alignment and `previous`, but
omits `next = NULL`. `luaE_extendCI` writes that NULL in its generated
run; `Kit/ExtendCI.lean`'s `ExtPost` discards it. The field must pass
through `JoinIn`, `CloseIn`, `join_reuse`/`join_ext` and `call_close`.
The initial `LuaStateAt.rel` uses the no-successor branch, so adding a
terminal successor field does not need a new initial-state hypothesis.
`tasks/cinext-terminal.md` scopes this invariant extension.

This is needed because after pcall restores `L->ci` to `base_ci`,
`luaE_shrinkCI` keeps the first free CallInfo (the Lua frame) and frees
its successor (the print frame) if present. Proving merely a null case
from the current `L->ci` would miss this reachable free path.

## Base CallInfo

`LuaStateRel.previous` identifies the Lua frame's predecessor as
`L + stateBaseCiOff`; it does not pin that base frame's `top`, `previous`,
or `next`. The natural home for fields untouched by print is the frozen
`LuaStatic`/`StatFacts` region: add them to `luaStaticWords`, check them
in the boot witness, and transport them through the existing frozen
footprint. The exact values and stack-offset behavior still require
inspection of `stack_init`, boot data, and stack reallocation before a
proof task is issued. Do not assume these facts at `PcallErr_Statement`.

## Error object and stderr

`tasks/seterrorobj.md` targets the status-2 helper at `0x80009984`:
copy payload/tag from the old top, set `L->top` to the destination plus
one TValue, preserve the exact frame and ABI. It does not supply the
close-protected run or stack shrink composition.

The separate console-source lane widens stdout/stderr buffer contracts
to `.rodata`, needed for fprintf's literal fragments. The remaining
stderr invariant must establish `_REENT->_stderr` and stdio fields at
boot/initialization, then preserve them through print. Low-level write
summaries alone cannot prove those caller facts or full `FprintfErr`.
