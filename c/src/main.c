/* Bare-metal entry for Lua 5.4 under HTIF.
 *
 * Creates a state, stops the collector before anything is allocated
 * through the Lua API, opens the base/string/table/coroutine libraries (no io,
 * os, package, debug, math, utf8), loads the embedded binary chunk
 * and calls it. The verification cut point (Layer A) is luaV_execute's
 * entry for the main closure of that chunk.
 *
 * Exit codes: 0 ok, 1 load error, 2 runtime error, 3 no memory. */
#include <stdio.h>
#include <stdlib.h>
#include "lua.h"
#include "lauxlib.h"
#include "lualib.h"

extern const char _chunk_start[];     /* chunk.S */
extern const unsigned long _chunk_size; /* chunk.S: its length in bytes */

static void *l_alloc(void *ud, void *ptr, size_t osize, size_t nsize) {
    (void)ud; (void)osize;
    if (nsize == 0) { free(ptr); return NULL; }
    return realloc(ptr, nsize);
}

static const luaL_Reg libs[] = {
    {LUA_GNAME, luaopen_base},
    {LUA_STRLIBNAME, luaopen_string},
    {LUA_TABLIBNAME, luaopen_table},
    {LUA_COLIBNAME, luaopen_coroutine},
    {NULL, NULL}
};

int main(void) {
    lua_State *L = lua_newstate(l_alloc, NULL);
    if (L == NULL) return 3;
    lua_gc(L, LUA_GCSTOP);
    for (const luaL_Reg *lib = libs; lib->func; lib++) {
        luaL_requiref(L, lib->name, lib->func, 1);
        lua_pop(L, 1);
    }
    size_t n = (size_t)_chunk_size;
    if (luaL_loadbufferx(L, _chunk_start, n, "=chunk", "b") != LUA_OK) {
        fprintf(stderr, "lua: %s\n", lua_tostring(L, -1));
        return 1;
    }
    if (lua_pcall(L, 0, 0, 0) != LUA_OK) {
        fprintf(stderr, "lua: %s\n", lua_tostring(L, -1));
        return 2;
    }
    return 0; /* no lua_close: it would run a full collection */
}
