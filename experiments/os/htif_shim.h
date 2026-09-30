/* Pre-include for tcb/validation/driver.c (copied from ship-your-ocaml):
 * run its MEMFS back end against OUR c/src/htif.c, unchanged, compiled
 * natively (experiments/os/run.sh).
 *
 * driver.c's MEMFS branch #includes "../../c/src/htif.c" (this repository's
 * htif.c, compiled with -DHOST_MIRROR) and resets it between scripts by
 * zeroing `files`, `fds`, `dirs` and `fs_ready`. Our htif.c has `files`,
 * `fds` and `fs_ready` (zeroed, the file system is empty again) and every
 * function the driver calls except the directory streams: the Lua ELF
 * has no opendir/readdir/closedir (Lua's io/os libraries do not use them;
 * ship-your-ocaml's htif.c has them, marked OCAML). This header supplies
 * what is left:
 *   - `struct embedded_file` (driver.c defines an empty `embedded_files[]`;
 *     the Lua image embeds no files);
 *   - `dirs` and the three directory functions, each failing with an errno
 *     the driver prints as `unsupported` (EOPNOTSUPP is not in its table),
 *     so the checker skips the rest of that trace. */
#ifndef LUA_HTIF_SHIM_H
#define LUA_HTIF_SHIM_H
#include <errno.h>
#include <stddef.h>

#define opendir  shim_absent_opendir
#define readdir  shim_absent_readdir
#define closedir shim_absent_closedir
struct direct { char d_name[1]; };
struct embedded_file { const char *name; const unsigned char *data; unsigned long size; };
static char dirs[1];
static void *shim_absent_opendir(const char *p) { (void)p; errno = EOPNOTSUPP; return NULL; }
static struct direct *shim_absent_readdir(void *d) { (void)d; errno = EOPNOTSUPP; return NULL; }
static int shim_absent_closedir(void *d) { (void)d; return 0; }
#endif
