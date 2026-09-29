/* Embeds the precompiled Lua chunk named by CHUNK_PATH (a quoted string set
 * from the Makefile; produced by the host `luac` built from the same
 * vendored source). HTIF builds have no filesystem, so main() loads this
 * blob with luaL_loadbufferx(..., "b"). It lives in its own section
 * (.lua_chunk, link.ld) so that no other address depends on it. */
    .section .lua_chunk,"a"
    .globl _chunk_size
    .globl _chunk_start
    .globl _chunk_end
    .balign 8
/* the length first, at a fixed address: main() reads it as data, so its
 * code does not depend on the chunk either */
_chunk_size:
    .dword _chunk_end - _chunk_start
_chunk_start:
    .incbin CHUNK_PATH
_chunk_end:
    .byte 0
