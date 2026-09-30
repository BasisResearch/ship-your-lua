/* HTIF back end for newlib, with an in-image file system.
 *
 * Console output is the riscv-tests HTIF convention (device 1 / command 1
 * through the 64-bit `tohost` mailbox), exit is device 0 with the low
 * payload bit set. This is what Spike and the sail-riscv emulators
 * (including the Lean one) implement. There is no console input; the
 * script to run is linked into the image (see src/chunk.S).
 *
 * The file system is the one the shared OS spec describes (`tcb/`,
 * `TCB.Os.next`: SibylFS for files and directories, CakeML's console
 * streams on fds 0-2). It starts empty, as `TCB.Os.OsState.init` does,
 * and lives in the heap (`malloc`), so the allocator's proofs cover its
 * memory. Descriptors are one table: 0-2 are the console streams, and
 * `open` takes the smallest free number, as the spec numbers them; a
 * descriptor that is not in the table is `EBADF`. Path resolution is
 * `TCB.Os.Fs.resolveRel` (no symlinks; the working directory is the
 * root). Where the spec allows several errors, the code returns one of
 * them (Linux's choice where it has one). The clock is frozen at 0
 * (`TCB.Os.Clock.frozen`). Validated against the spec by trace checking:
 * experiments/os/run.sh and experiments/os/RESULTS.md. */
#if defined(LUA_HTIF) || defined(HOST_MIRROR)

#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* --- HTIF ---------------------------------------------------------------- */

/* The host locates these by the section name `.tohost` in the ELF. */
volatile uint64_t tohost __attribute__((section(".tohost"), aligned(8)));
volatile uint64_t fromhost __attribute__((section(".tohost"), aligned(8)));

#define HTIF_DEV_CONSOLE (1ULL << 56)
#define HTIF_CMD_WRITE   (1ULL << 48)

/* Each 8-byte store is a complete HTIF command; the sail model processes
 * it synchronously and clears the mailbox, so no ready-polling is needed. */
static void htif_putc(char c) {
    tohost = HTIF_DEV_CONSOLE | HTIF_CMD_WRITE | (uint8_t)c;
}

#ifndef HOST_MIRROR
void _exit(int code) {
    tohost = ((uint64_t)(uint32_t)code << 1) | 1;
    for (;;) {}
}
#endif

/* --- in-memory file system ----------------------------------------------- */

#define MAX_FILES 64   /* files and directories; files[0] is the root */
#define MAX_FDS   32
#define FS_ROOT      0

/* A file or directory (the spec's inode). While `linked`, it is the entry
 * `name` of directory `parent`; an unlinked file lives on while a
 * descriptor refers to it (link count 0). */
struct mfile {
    unsigned char used, dir, linked;
    int parent;
    char *name;
    size_t nlen;
    char *data;           /* file contents */
    size_t size, cap;
    int opens;            /* descriptors referring to it */
};

enum { FD_FREE, FD_STDIN, FD_STDOUT, FD_STDERR, FD_FILE };
struct mfd { int kind; int node; size_t pos; int flags; };

static struct mfile files[MAX_FILES];
static struct mfd fds[MAX_FDS];
static int fs_ready;

static void fs_init(void) {
    if (fs_ready) return;
    fs_ready = 1;
    files[FS_ROOT].used = 1;
    files[FS_ROOT].dir = 1;
    fds[0].kind = FD_STDIN;
    fds[1].kind = FD_STDOUT;
    fds[2].kind = FD_STDERR;
}

static void release(int i) {
    struct mfile *f = &files[i];
    if (i == FS_ROOT || f->linked || f->opens) return;
    free(f->name);
    free(f->data);
    memset(f, 0, sizeof *f);
}

static int child(int d, const char *n, size_t k) {
    for (int i = 1; i < MAX_FILES; i++)
        if (files[i].used && files[i].linked && files[i].parent == d &&
            files[i].nlen == k && memcmp(files[i].name, n, k) == 0)
            return i;
    return -1;
}

static int dir_empty(int d) {
    for (int i = 1; i < MAX_FILES; i++)
        if (files[i].used && files[i].linked && files[i].parent == d) return 0;
    return 1;
}

static int nsubdirs(int d) {
    int k = 0;
    for (int i = 1; i < MAX_FILES; i++)
        if (files[i].used && files[i].linked && files[i].dir && files[i].parent == d) k++;
    return k;
}

/* `a` is `d` or one of its ancestors. */
static int ancestor(int a, int d) {
    for (int n = 0; n <= MAX_FILES; n++) {
        if (d == a) return 1;
        if (d == FS_ROOT) return 0;
        d = files[d].parent;
    }
    return 0;
}

/* The result of resolving a path (the spec's `RN`). */
enum { R_DIR, R_FILE, R_NONE, R_ERR };
struct res {
    int kind;
    int dir;              /* R_DIR: it; R_FILE/R_NONE: the directory holding it */
    int node;             /* R_FILE: the file; R_ERR: the file before a trailing '/', or -1 */
    const char *name;     /* R_FILE/R_NONE: the last component */
    size_t nlen;
    int err;              /* R_ERR */
    int slash;            /* the path ends with '/' (`endsWithSlash`) */
    int last_dot;         /* the last non-empty component is "." */
    int last_dotdot;      /* ... is ".." */
};

static int only_slashes(const char *p) {
    while (*p == '/') p++;
    return *p == 0;
}

/* `processPath` + `resolveRel` (tcb/TCB/Os/Fs.lean). */
static void resolve(const char *path, struct res *r) {
    fs_init();
    memset(r, 0, sizeof *r);
    r->node = -1;
    size_t len = strlen(path);
    r->slash = len > 0 && path[len - 1] == '/';
    /* the last non-empty component */
    size_t e = len;
    while (e > 0 && path[e - 1] == '/') e--;
    size_t b = e;
    while (b > 0 && path[b - 1] != '/') b--;
    r->last_dot = e - b == 1 && path[b] == '.';
    r->last_dotdot = e - b == 2 && path[b] == '.' && path[b + 1] == '.';
    if (len == 0) { r->kind = R_ERR; r->err = ENOENT; return; }
    int d = FS_ROOT;
    const char *p = path;
    for (;;) {
        const char *q = strchr(p, '/');
        size_t k = q ? (size_t)(q - p) : strlen(p);
        const char *rest = q ? q + 1 : NULL;       /* NULL: no more components */
        int last = rest == NULL || only_slashes(rest);
        if (k == 0 || (k == 1 && p[0] == '.')) {
            /* stay */
        } else if (k == 2 && p[0] == '.' && p[1] == '.') {
            d = files[d].parent;                      /* the root's parent is the root */
        } else {
            int c = child(d, p, k);
            if (c < 0) {
                if (last) { r->kind = R_NONE; r->dir = d; r->name = p; r->nlen = k; }
                else { r->kind = R_ERR; r->err = ENOENT; }
                return;
            }
            if (files[c].dir) {
                d = c;
            } else if (rest == NULL) {
                r->kind = R_FILE; r->dir = d; r->node = c; r->name = p; r->nlen = k;
                return;
            } else {
                r->kind = R_ERR; r->err = ENOTDIR;
                if (last) { r->dir = d; r->node = c; }
                return;
            }
        }
        if (rest == NULL) break;
        p = rest;
    }
    r->kind = R_DIR; r->dir = d;
}

static int new_node(int d, const char *n, size_t k, int dir) {
    for (int i = 1; i < MAX_FILES; i++)
        if (!files[i].used) {
            char *nm = malloc(k + 1);
            if (!nm) return -1;
            memcpy(nm, n, k);
            nm[k] = 0;
            memset(&files[i], 0, sizeof files[i]);
            files[i].used = 1; files[i].dir = (unsigned char)dir; files[i].linked = 1;
            files[i].parent = d; files[i].name = nm; files[i].nlen = k;
            return i;
        }
    return -1;
}

/* Remove the entry naming node `i` (the spec's `unlink`/`rmdir` of it). */
static void unlink_node(int i) {
    files[i].linked = 0;
    release(i);
}

static struct mfd *getfd(int fd) {
    fs_init();
    if (fd < 0 || fd >= MAX_FDS || fds[fd].kind == FD_FREE) return NULL;
    return &fds[fd];
}

int _open(const char *path, int flags, int mode) {
    (void)mode;
    int acc = flags & O_ACCMODE;
    if (acc != O_RDONLY && acc != O_WRONLY && acc != O_RDWR) { errno = EINVAL; return -1; }
    int wr = acc != O_RDONLY, creat = (flags & O_CREAT) != 0;
    if (creat && (flags & O_DIRECTORY)) { errno = EINVAL; return -1; }
    struct res r;
    resolve(path, &r);
    int err = 0;
    if (r.kind == R_ERR) err = r.err;
    else if (r.kind == R_NONE && !creat) err = ENOENT;
    else if (creat && r.slash) err = EISDIR;
    else if ((wr || (flags & O_TRUNC)) && r.kind == R_DIR) err = EISDIR;
    else if ((flags & O_DIRECTORY) && r.kind == R_FILE) err = ENOTDIR;
    else if (creat && (flags & O_EXCL) && r.kind != R_NONE) err = EEXIST;
    else if (creat && r.kind == R_DIR) err = EISDIR;
    if (err) { errno = err; return -1; }
    int fd = 0;
    while (fd < MAX_FDS && fds[fd].kind != FD_FREE) fd++;
    if (fd == MAX_FDS) { errno = EMFILE; return -1; }
    int node = r.kind == R_DIR ? r.dir : r.node;
    if (r.kind == R_NONE && (node = new_node(r.dir, r.name, r.nlen, 0)) < 0) {
        errno = ENOSPC; return -1;
    }
    if ((flags & O_TRUNC) && !files[node].dir) files[node].size = 0;
    fds[fd].kind = FD_FILE; fds[fd].node = node; fds[fd].pos = 0; fds[fd].flags = flags;
    files[node].opens++;
    return fd;
}

int _close(int fd) {
    struct mfd *d = getfd(fd);
    if (!d) { errno = EBADF; return -1; }
    if (d->kind == FD_FILE) {
        files[d->node].opens--;
        release(d->node);
    }
    d->kind = FD_FREE;
    return 0;
}

ssize_t _read(int fd, void *buf, size_t len) {
    struct mfd *d = getfd(fd);
    if (!d || d->kind == FD_STDOUT || d->kind == FD_STDERR) { errno = EBADF; return -1; }
    if (d->kind == FD_STDIN) return 0;  /* no console input over HTIF */
    if ((d->flags & O_ACCMODE) == O_WRONLY) { errno = EBADF; return -1; }
    struct mfile *f = &files[d->node];
    if (f->dir) { errno = EISDIR; return -1; }
    size_t avail = d->pos < f->size ? f->size - d->pos : 0;
    if (len > avail) len = avail;
    memcpy(buf, f->data + d->pos, len);
    d->pos += len;
    return (ssize_t)len;
}

ssize_t _write(int fd, const void *buf, size_t len) {
    const char *p = buf;
    struct mfd *d = getfd(fd);
    if (!d || d->kind == FD_STDIN) { errno = EBADF; return -1; }
    if (d->kind != FD_FILE) {       /* stdout and stderr: the HTIF console */
        for (size_t i = 0; i < len; i++) htif_putc(p[i]);
        return (ssize_t)len;
    }
    if ((d->flags & O_ACCMODE) == O_RDONLY) { errno = EBADF; return -1; }
    struct mfile *f = &files[d->node];
    if (len == 0) return 0;         /* the offset stays, also with O_APPEND */
    size_t pos = (d->flags & O_APPEND) ? f->size : d->pos;
    if (pos + len > f->cap) {
        size_t cap = f->cap ? f->cap : 256;
        while (cap < pos + len) cap *= 2;
        char *nd = realloc(f->data, cap);
        if (!nd) { errno = ENOSPC; return -1; }
        f->data = nd; f->cap = cap;
    }
    if (pos > f->size) memset(f->data + f->size, 0, pos - f->size);
    memcpy(f->data + pos, p, len);
    d->pos = pos + len;
    if (d->pos > f->size) f->size = d->pos;
    return (ssize_t)len;
}

off_t _lseek(int fd, off_t offset, int whence) {
    struct mfd *d = getfd(fd);
    if (!d) { errno = EBADF; return -1; }
    if (whence != SEEK_SET && whence != SEEK_CUR && whence != SEEK_END) { errno = EINVAL; return -1; }
    if (d->kind != FD_FILE) { errno = ESPIPE; return -1; }
    struct mfile *f = &files[d->node];
    if (whence == SEEK_END && f->dir) { errno = EINVAL; return -1; }
    off_t base = whence == SEEK_SET ? 0 : whence == SEEK_CUR ? (off_t)d->pos : (off_t)f->size;
    if (offset < 0 ? base < -offset : 0) { errno = EINVAL; return -1; }
    d->pos = (size_t)(base + offset);
    return (off_t)d->pos;
}

static void fill_stat(int i, struct stat *st) {
    struct mfile *f = &files[i];
    memset(st, 0, sizeof *st);
    if (f->dir) {
        st->st_mode = S_IFDIR | 0755;
        st->st_nlink = 2 + nsubdirs(i);
    } else {
        st->st_mode = S_IFREG | 0644;
        st->st_size = (off_t)f->size;
        st->st_nlink = f->linked;
    }
}

int _fstat(int fd, struct stat *st) {
    struct mfd *d = getfd(fd);
    if (!d) { errno = EBADF; return -1; }
    if (d->kind != FD_FILE) {
        memset(st, 0, sizeof *st);
        st->st_mode = S_IFCHR;
        st->st_nlink = 1;
        return 0;
    }
    fill_stat(d->node, st);
    return 0;
}

int _stat(const char *path, struct stat *st) {
    struct res r;
    resolve(path, &r);
    if (r.kind == R_ERR) { errno = r.err; return -1; }
    if (r.kind == R_NONE) { errno = ENOENT; return -1; }
    fill_stat(r.kind == R_DIR ? r.dir : r.node, st);
    return 0;
}

int _unlink(const char *path) {
    struct res r;
    resolve(path, &r);
    if (r.kind == R_ERR) { errno = r.err; return -1; }
    if (r.kind == R_NONE) { errno = r.slash ? ENOTDIR : ENOENT; return -1; }
    if (r.kind == R_DIR) { errno = EISDIR; return -1; }
    unlink_node(r.node);
    return 0;
}

int mkdir(const char *path, mode_t mode) {
    (void)mode;
    struct res r;
    resolve(path, &r);
    if (r.kind == R_ERR) { errno = r.err; return -1; }
    if (r.kind != R_NONE) { errno = EEXIST; return -1; }
    if (new_node(r.dir, r.name, r.nlen, 1) < 0) { errno = ENOSPC; return -1; }
    return 0;
}

int rmdir(const char *path) {
    struct res r;
    resolve(path, &r);
    if (r.last_dot) { errno = EINVAL; return -1; }
    if (r.kind == R_ERR) { errno = r.err; return -1; }
    if (r.kind == R_NONE) { errno = ENOENT; return -1; }
    if (r.kind == R_FILE) { errno = ENOTDIR; return -1; }
    if (!dir_empty(r.dir)) { errno = ENOTEMPTY; return -1; }
    if (r.dir == FS_ROOT) { errno = EBUSY; return -1; }
    unlink_node(r.dir);
    return 0;
}

/* `fsop_rename` (tcb/TCB/Os/Fs.lean: `renameChecks`, `renameCore`). */
int rename(const char *from, const char *to) {
    struct res a, b;
    resolve(from, &a);
    resolve(to, &b);
    int err = 0;
    if (a.last_dot || a.last_dotdot || b.last_dot || b.last_dotdot) err = EBUSY;
    else if (!(a.kind == R_DIR && b.kind == R_DIR && a.dir == b.dir)) {
        if (a.kind == R_NONE) err = ENOENT;
        else if (a.kind == R_ERR) err = a.err;
        else if (b.kind == R_ERR) err = b.err;
        else if (a.kind == R_FILE && b.kind == R_DIR) err = EISDIR;
        else if (a.kind == R_FILE && b.kind == R_NONE && b.slash) err = ENOTDIR;
        else if (a.kind == R_DIR && (b.kind == R_FILE || b.kind == R_ERR)) err = ENOTDIR;
        else if (b.kind == R_DIR && !dir_empty(b.dir)) err = ENOTEMPTY;
    }
    if (!err && a.kind == R_DIR) {
        /* moving the root, or a directory below itself */
        if (a.dir == FS_ROOT) err = EBUSY;
        else if (b.kind == R_DIR ? (a.dir != b.dir && ancestor(a.dir, b.dir))
                                 : ancestor(a.dir, b.dir)) err = EINVAL;
        else if (b.kind == R_DIR && b.dir == FS_ROOT) err = ENOTEMPTY;
    }
    if (err) { errno = err; return -1; }
    int src = a.kind == R_DIR ? a.dir : a.node;
    int dst = b.kind == R_DIR ? b.dir : b.kind == R_FILE ? b.node : -1;
    if (src == dst) return 0;
    int d1; const char *n1; size_t k1;
    if (dst >= 0) { d1 = files[dst].parent; n1 = files[dst].name; k1 = files[dst].nlen; }
    else { d1 = b.dir; n1 = b.name; k1 = b.nlen; }
    char *nm = malloc(k1 + 1);
    if (!nm) { errno = ENOSPC; return -1; }
    memcpy(nm, n1, k1);
    nm[k1] = 0;
    if (dst >= 0) unlink_node(dst);
    free(files[src].name);
    files[src].name = nm; files[src].nlen = k1; files[src].parent = d1;
    return 0;
}

int _isatty(int fd) {
    struct mfd *d = getfd(fd);
    if (d && d->kind != FD_FILE) return 1;
    errno = d ? ENOTTY : EBADF;
    return 0;
}

int _link(const char *from, const char *to) { (void)from; (void)to; errno = EMLINK; return -1; }

/* --- heap -------------------------------------------------------------- */

extern char _end[];       /* from link.ld */
extern char __heap_end[];

void *_sbrk(ptrdiff_t incr) {
    static char *brk;
    if (!brk) brk = _end;
    if (brk + incr > __heap_end) { errno = ENOMEM; return (void *)-1; }
    char *prev = brk;
    brk += incr;
    return prev;
}

/* --- time ------------------------------------------------------------- */

/* The clock is frozen at 0 (`TCB.Os.Clock.frozen`, which meets the spec's
 * monotone clock). newlib's libgloss implements _gettimeofday and _times
 * with an `ecall`, which on this bare machine traps with no handler and
 * never returns: these replace them (scripts/check.sh fails if an ecall is
 * linked). os.time() and os.clock() are then 0. */
#include <sys/time.h>
#include <sys/times.h>
int _gettimeofday(struct timeval *tv, void *tz) {
    (void)tz;
    if (tv) { tv->tv_sec = 0; tv->tv_usec = 0; }
    return 0;
}
clock_t _times(struct tms *t) {
    if (t) memset(t, 0, sizeof *t);
    return 0;
}

/* --- process ----------------------------------------------------------- */

int _kill(int pid, int sig) { (void)pid; (void)sig; errno = EINVAL; return -1; }
int _getpid(void) { return 1; }

#else
/* Non-HTIF build: nothing here. */
typedef int not_empty_translation_unit;
#endif
