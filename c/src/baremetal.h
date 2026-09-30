/* Force-included (-include) into every Lua translation unit of the
 * bare-metal build, and of the host lua/luac (difftests). Removes every
 * source of nondeterminism so a run is a pure function of the embedded
 * chunk:
 *   - the string-hash seed is a constant (lstate.c: luai_makeseed),
 *   - table.sort's pivot randomisation is off (ltablib.c),
 *   - the decimal point is '.' (no localeconv()),
 *   - the clock is frozen at 0: on the ELF by htif.c (_gettimeofday and
 *     _times, TCB.Os.Clock.frozen), on the host by the macros below, so
 *     os.time(), os.clock() and os.date() agree,
 *   - on the ELF, os.execute has no shell: `system` is not linked (newlib's
 *     would need fork/exec), os.execute() is false and os.execute(cmd)
 *     fails with ENOSYS. io.popen fails with "'popen' not supported"
 *     (LUA_USE_POSIX is unset), os.getenv is nil (newlib's environment is
 *     empty).
 * The GC is stopped at startup by main.c (lua_gc(L, LUA_GCSTOP)). */
#ifndef LUA_BAREMETAL_H
#define LUA_BAREMETAL_H
#define luai_makeseed(L)        ((unsigned int)0x5eed5eedu)
#define l_randomizePivot()      ((unsigned int)0)
#define lua_getlocaledecpoint() ('.')
#ifdef LUA_HTIF
/* errno: loslib.c, the only user, includes <errno.h> */
#define l_system(cmd)           ((cmd) == NULL ? 0 : (errno = ENOSYS, -1))
#else
#include <time.h>
#define time(t)                 ((time_t)0)
#define clock()                 ((clock_t)0)
#endif
#endif
