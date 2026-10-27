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

## The next emission boundary

`luaK_code` at0x80005b20 always calls `luaM_growaux_` for code storage,
then increments fs->pc, writes the instruction, calls savelineinfo and
returns the old pc. Debug line storage is updated even when the eventual
output chunk is stripped. It cannot be omitted from the machine frame.

A useful next success subcase has spare code and line-array capacity.
`luaM_growaux_` at0x80010f58 loads the signed32 capacity at a3, compares
signed a2 against it, and on room returns a1 through0x80011018/1101c.
This path uses no stack and keeps memory exactly. Prove this reusable
callee summary on honest aligned RAM/return facts; do not replace the call
with an assumed identity.

`savelineinfo` at0x80004dc4 has a48-byte frame. If the line delta fits
[-127,127] and the **old** signed-byte iwthabs is nonnegative, it increments
that byte, grows/checks the line array, writes the signed delta at pc-1,
and updates previousline. If either condition fails, it first appends an
absolute line record and writes the -128 sentinel into lineinfo. The
zero-delta, old counter0..127 subcase covers many straight-line emissions,
but an eventual general emitter must include the absolute-record branch.
For a local append theorem with no allocation, specify spare code and
line capacity, separation of compiler state/arrays/stack, preservation of
the old encoded prefix, pc+1, and the real line metadata writes. Compose
its instruction append with `Encode.emit`; the B2 primitive is already
proved. Keep this partial machine theorem distinct from the full parser
and resource-aware growth obligations.
