# ELF code-generator entry points

Source/ELF audit, 2026-10-27; this is a task map, not a proof.

`Lua.Compile.Encode` already checks instruction fields and jump patching.
The first machine bridge can reuse its `abx` rather than define a second
encoding: `luaK_codeABx` at `0x80005d44` has five instructions, ending in
a tail jump to `luaK_code` at `0x80005b20`. It shifts Bx by 15 and A by 7,
ORs the opcode, and leaves the resulting instruction in a1. The 32-bit
shifts sign-extend to 64 bits; the correct boundary is the sign extension
of the encoded instruction, including when bit 31 is set. Claiming a
zero-extended register would be wrong for valid large Bx values.

`tasks/b3-code-abx.md` scopes this actual entry-to-tail boundary. It does
not prove `luaK_code`'s allocation/emission, the whole compiler, or
`CompileTV`. Following work can compose the emitter's run at that PC.

The C `fixjump` helper has no standalone symbol in the pinned ELF: it is
inlined. In `luaK_concat` (`0x80005a60`), the link walk is at `0x80005a80`
and the patch is at `0x80005aa4` through `0x80005ac8`; out-of-range jumps
call `luaX_syntaxerror`. A later list-patching proof must handle the real
walk and `NO_JUMP = -1` sentinel, including the last link's displacement
test, instead of inventing a machine entry for C's static `fixjump`.
