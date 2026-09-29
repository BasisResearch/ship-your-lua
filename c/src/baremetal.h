/* Force-included (-include) into every Lua translation unit of the
 * bare-metal build. Removes every source of nondeterminism so a run is a
 * pure function of the embedded chunk:
 *   - the string-hash seed is a constant (lstate.c: luai_makeseed),
 *   - table.sort's pivot randomisation is off (ltablib.c),
 *   - the decimal point is '.' (no localeconv()).
 * The GC is stopped at startup by main.c (lua_gc(L, LUA_GCSTOP)). */
#ifndef LUA_BAREMETAL_H
#define LUA_BAREMETAL_H
#define luai_makeseed(L)        ((unsigned int)0x5eed5eedu)
#define l_randomizePivot()      ((unsigned int)0)
#define lua_getlocaledecpoint() ('.')
#endif
