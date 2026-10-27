# UNM string metamethod lookup

Source/ELF and existing boot-image audit, 2026-10-27; not a proof.
`UnmStr_Statement` is `ArmBody .UNM RegStr`. It cannot be discharged by
calling the string conversion summary directly: the actual arm calls
`luaT_trybinTM`, which obtains the string library metamethod and invokes
it through Lua's C-call machinery. Float numeral strings additionally
need the still-open strtod route. Existing module comments describing
only string integers predate the float semantics.

The actual lookup starts at `luaT_gettmbyobj` 0x8001917c. For a string
TValue it masks the tag to4, loads `g->mt[4]`, loads `g->tmname[18]`
(TM_UNM), and tail-jumps at0x800191b8 to `luaH_getshortstr`0x8001808c.
The boot-checked `StrMtMiss` only establishes absence of __tostring;
it does not establish the __unm hit or its C function value.

Both existing packed boot witnesses (While and F1Ops) have the same
observed lookup: g=0x8006edb0, string metatable0x80071400,
node array0x80071440, lsizenode4, tmname[18]=0x8006fe80,
hash0x7f630ca5. The walk visits0x800714b8 then0x80071578,
whose value tag is22 (vLcf) and payload0x80024e68 (arith_unm).
These observations must become kernel-checked boot facts; they are not
justification for a hard-coded per-node machine proof.

Reuse `shrWalk`, `shrWalk_mem`, its footprint/congruence laws, and
`Kit.Getshortstr.gs_loop`. The existing public `getshortstr_sum` is
parameterized via `_ENV` and its closure. Factor a direct table/key
context and generic successful summary, keeping the current Env-facing
API as a corollary. Do not synthesize a fake closure or copy the walk.
Generate luaT_gettmbyobj's string prefix and compose the tail with that
summary. Name/freeze the metatable hit and function-value invariant on
its actual footprint, kernel-check it at boot/VARARGPREP, and transport
it through the existing CALL dirty-set frame. It belongs in the invariant,
not a new open hypothesis of UnmStr_Statement.

Then the actual call chain still needs luaT_trybinTM, luaT_callTMres,
luaD_call and the C-call/CallInfo lifecycle. The string library arith_unm
uses shared arith: tonum(L,1), tonum(L,2), then lua_arith; UNM pushes the
same operand twice. Its successful integer conversion can reuse
str2num_int, while nonnumerals go to the error pipeline and float strings
to the shared strtod obligation. The result is copied back after restoring
the destination's offset across possible stack changes. Preserve call
room and heap effects; do not identify this lifecycle with CALL print.
