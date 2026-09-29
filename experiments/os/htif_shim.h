/* Pre-include for tcb/validation/driver.c (copied verbatim from
 * ship-your-ocaml): run its MEMFS back end against OUR c/src/htif.c,
 * unchanged, compiled natively (experiments/os/run.sh).
 *
 * driver.c's MEMFS branch #includes "../../c/src/htif.c", which from
 * tcb/validation/ is this repository's htif.c. ship-your-ocaml's htif.c has
 * an in-image file system (files[], fds[], dirs[], _stat, _unlink, rename,
 * opendir/readdir/closedir, _gettimeofday); ours is console-only, and the
 * Lua ELF links none of those functions (nm). This header supplies what the
 * driver expects:
 *   - LUA_HTIF, so htif.c's body is compiled;
 *   - the memfs statics backend_reset() clears (dummies: ours has no state);
 *   - the functions the Lua ELF does not have, each failing with an errno
 *     the driver prints as `unsupported` (EOPNOTSUPP is not in its table),
 *     so the checker skips the rest of that trace; `clock` is rewritten to
 *     `unsupported` by run.sh, since the driver prints _gettimeofday's value
 *     unconditionally;
 *   - _exit renamed, so the native process exits through glibc. */
#ifndef LUA_HTIF_SHIM_H
#define LUA_HTIF_SHIM_H
#define LUA_HTIF 1
#include <errno.h>
#include <stddef.h>
#include <sys/stat.h>
#include <sys/time.h>

#define _exit htif_exit_not_called

#define rename   shim_absent_rename
#define opendir  shim_absent_opendir
#define readdir  shim_absent_readdir
#define closedir shim_absent_closedir
struct direct { char d_name[1]; };
struct embedded_file { const char *name; const unsigned char *data; unsigned long size; };
static char files[1], fds[1], dirs[1];
static int fs_ready;
static int _stat(const char *p, struct stat *s) { (void)p; (void)s; errno = EOPNOTSUPP; return -1; }
static int _unlink(const char *p) { (void)p; errno = EOPNOTSUPP; return -1; }
static int shim_absent_rename(const char *a, const char *b) { (void)a; (void)b; errno = EOPNOTSUPP; return -1; }
static void *shim_absent_opendir(const char *p) { (void)p; errno = EOPNOTSUPP; return NULL; }
static struct direct *shim_absent_readdir(void *d) { (void)d; errno = EOPNOTSUPP; return NULL; }
static int shim_absent_closedir(void *d) { (void)d; return 0; }
static int _gettimeofday(struct timeval *tv, void *tz) { (void)tz; tv->tv_sec = 0; tv->tv_usec = 0; return 0; }
#endif
