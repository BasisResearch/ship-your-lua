/* Trace driver for the OS-spec validation (tcb/validation/README in
 * RESULTS.md). Reads scripts (one call per line, `## NAME` headers; the
 * call syntax of TCB/Os/Trace.lean), runs each call against a back end, and
 * writes `CALL => RET` lines.
 *
 *   driver-linux  SCRIPTS OUT SANDBOX_BASE   real Linux system calls, each
 *                 script in a fresh directory under SANDBOX_BASE whose path
 *                 plays the role of "/" (absolute paths are prefixed with it,
 *                 the process's cwd is it);
 *   driver-memfs  SCRIPTS OUT                the in-image file system of
 *                 c/src/htif.c (compiled natively, -DHOST_MIRROR), reset
 *                 before each script; absolute paths are prefixed with
 *                 "/sb" (the memfs has no path resolution, so this is where
 *                 its deviations show); mkdir and rmdir are `unsupported`
 *                 (the memfs has no directories, only path prefixes).
 *
 * Directory handles are numbered as the spec numbers them (smallest free
 * from 1); a handle the driver never issued gives EBADF without calling
 * the C library (passing a bogus DIR* is undefined behaviour), and the
 * spec's EBADF for it is thus only checked for consistency, not against
 * the kernel. Output goes to OUT, so writes to fds 1/2 do not mix with it;
 * run with stdin and stdout on /dev/null. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#ifdef MEMFS
/* Pull in the in-image file system itself, statics included, so it can be
 * reset between scripts. */
#define _sbrk mf_sbrk_unused
#define HOST_MIRROR 1
#include "../../c/src/htif.c"
#undef _sbrk
char _end[1], __heap_end[1];
const struct embedded_file embedded_files[] = {{0, 0, 0}};
static void backend_reset(void) {
    memset(files, 0, sizeof files);
    memset(fds, 0, sizeof fds);
    memset(dirs, 0, sizeof dirs);
    fs_ready = 0;
}
#define B_OPEN(p, f) _open(p, f, 0666)
#define B_CLOSE(fd) _close(fd)
#define B_READ(fd, b, n) _read(fd, b, n)
#define B_WRITE(fd, b, n) _write(fd, b, n)
#define B_LSEEK(fd, o, w) _lseek(fd, o, w)
#define B_STAT(p, s) _stat(p, s)
#define B_FSTAT(fd, s) _fstat(fd, s)
#define B_UNLINK(p) _unlink(p)
#define B_RENAME(a, b) rename(a, b)
#define B_OPENDIR(p) opendir(p)
#define B_READDIR(d) readdir(d)
#define B_CLOSEDIR(d) closedir(d)
#define DIRENT struct direct
static const char *ROOT = "";   /* real path resolution: no prefix needed */
#else
#include <dirent.h>
#include <ftw.h>
#define B_OPEN(p, f) open(p, f, 0666)
#define B_CLOSE(fd) close(fd)
#define B_READ(fd, b, n) read(fd, b, n)
#define B_WRITE(fd, b, n) write(fd, b, n)
#define B_LSEEK(fd, o, w) lseek(fd, o, w)
#define B_STAT(p, s) stat(p, s)
#define B_FSTAT(fd, s) fstat(fd, s)
#define B_UNLINK(p) unlink(p)
#define B_RENAME(a, b) rename(a, b)
#define B_OPENDIR(p) opendir(p)
#define B_READDIR(d) readdir(d)
#define B_CLOSEDIR(d) closedir(d)
#define DIRENT struct dirent
static char ROOT_BUF[4096];
static const char *ROOT = ROOT_BUF;
#endif

static FILE *out;

/* ---- errno names (TCB/Os/Errno.lean) ---- */
static const char *ename(int e) {
    switch (e) {
    case EPERM: return "EPERM"; case ENOENT: return "ENOENT"; case EBADF: return "EBADF";
    case EACCES: return "EACCES"; case EBUSY: return "EBUSY"; case EEXIST: return "EEXIST";
    case EXDEV: return "EXDEV"; case ENOTDIR: return "ENOTDIR"; case EISDIR: return "EISDIR";
    case EINVAL: return "EINVAL"; case EMFILE: return "EMFILE"; case ESPIPE: return "ESPIPE";
    case ENOSPC: return "ENOSPC"; case EROFS: return "EROFS"; case EMLINK: return "EMLINK";
    case ENAMETOOLONG: return "ENAMETOOLONG"; case ENOSYS: return "ENOSYS";
    case ENOTEMPTY: return "ENOTEMPTY"; case ELOOP: return "ELOOP"; case EOVERFLOW: return "EOVERFLOW";
    default: return NULL;
    }
}

/* ---- tokens ---- */
typedef struct { int is_str; char *s; size_t len; } tok;

static int tokenize(const char *line, tok *t, int max) {
    int n = 0;
    const char *p = line;
    while (*p && n < max) {
        while (*p == ' ' || *p == '\t') p++;
        if (!*p || *p == '\n') break;
        if (*p == '"') {
            p++;
            char *buf = malloc(strlen(p) + 1); size_t k = 0;
            while (*p && *p != '"') {
                if (*p == '\\') {
                    p++;
                    if (*p == 'n') { buf[k++] = '\n'; p++; }
                    else if (*p == 'x') { unsigned v; sscanf(p + 1, "%2x", &v); buf[k++] = (char)v; p += 3; }
                    else buf[k++] = *p++;
                } else buf[k++] = *p++;
            }
            if (*p == '"') p++;
            buf[k] = 0;
            t[n].is_str = 1; t[n].s = buf; t[n].len = k; n++;
        } else {
            const char *q = p;
            while (*q && *q != ' ' && *q != '\t' && *q != '\n') q++;
            t[n].is_str = 0; t[n].s = strndup(p, q - p); t[n].len = q - p; n++;
            p = q;
        }
    }
    return n;
}

static void put_bytes(const char *b, size_t n) {
    fputc('"', out);
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)b[i];
        if (c == '"') fputs("\\\"", out);
        else if (c == '\\') fputs("\\\\", out);
        else if (c == '\n') fputs("\\n", out);
        else if (c >= 32 && c < 127) fputc(c, out);
        else fprintf(out, "\\x%02x", c);
    }
    fputc('"', out);
}

/* map a script path into the back end: "/..." is under ROOT */
static char *mapp(const tok *t) {
    static char buf[2][8192]; static int which;
    char *b = buf[which ^= 1];
    if (t->len > 0 && t->s[0] == '/') snprintf(b, sizeof buf[0], "%s%s", ROOT, t->s);
    else snprintf(b, sizeof buf[0], "%s", t->s);
    return b;
}

static void ret_err(void) {
    const char *n = ename(errno);
    if (n) fprintf(out, "err %s\n", n); else fprintf(out, "unsupported\n");
}

static void ret_stat(struct stat *st) {
    const char *k = S_ISDIR(st->st_mode) ? "dir" : S_ISREG(st->st_mode) ? "reg" :
                    S_ISCHR(st->st_mode) ? "chr" : "other";
    fprintf(out, "stats %s %lld %lld\n", k, (long long)st->st_size, (long long)st->st_nlink);
}

/* directory handles, numbered from 1 */
#define MAXDH 64
static void *dhs[MAXDH + 1];

static int flags_of(const char *s) {
    int f = 0;
    char *d = strdup(s), *save = NULL;
    for (char *p = strtok_r(d, "|", &save); p; p = strtok_r(NULL, "|", &save)) {
        if (!strcmp(p, "O_RDONLY")) f |= O_RDONLY;
        else if (!strcmp(p, "O_WRONLY")) f |= O_WRONLY;
        else if (!strcmp(p, "O_RDWR")) f |= O_RDWR;
        else if (!strcmp(p, "O_CREAT")) f |= O_CREAT;
        else if (!strcmp(p, "O_EXCL")) f |= O_EXCL;
        else if (!strcmp(p, "O_TRUNC")) f |= O_TRUNC;
        else if (!strcmp(p, "O_APPEND")) f |= O_APPEND;
        else if (!strcmp(p, "O_DIRECTORY")) f |= O_DIRECTORY;
    }
    free(d);
    return f;
}

static int open_fds[4096]; static int n_open_fds;

static void run_call(char *line) {
    tok t[8]; int n = tokenize(line, t, 8);
    if (n == 0) return;
    size_t L = strlen(line); while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
    fprintf(out, "%s => ", line);
    const char *c = t[0].s;
    errno = 0;
    if (!strcmp(c, "open")) {
        int fd = B_OPEN(mapp(&t[1]), flags_of(t[2].s));
        if (fd < 0) ret_err(); else { fprintf(out, "num %d\n", fd); if (n_open_fds < 4096) open_fds[n_open_fds++] = fd; }
    } else if (!strcmp(c, "close")) {
        if (B_CLOSE(atoi(t[1].s)) < 0) ret_err(); else fprintf(out, "none\n");
    } else if (!strcmp(c, "read")) {
        size_t k = strtoul(t[2].s, 0, 10); char *b = malloc(k + 1);
        ssize_t r = B_READ(atoi(t[1].s), b, k);
        if (r < 0) ret_err(); else { fputs("bytes ", out); put_bytes(b, r); fputc('\n', out); }
        free(b);
    } else if (!strcmp(c, "write")) {
        size_t k = strtoul(t[3].s, 0, 10);
        ssize_t r = B_WRITE(atoi(t[1].s), t[2].s, k);
        if (r < 0) ret_err(); else fprintf(out, "num %zd\n", r);
    } else if (!strcmp(c, "lseek")) {
        off_t r = B_LSEEK(atoi(t[1].s), strtoll(t[2].s, 0, 10), atoi(t[3].s));
        if (r < 0) ret_err(); else fprintf(out, "num %lld\n", (long long)r);
    } else if (!strcmp(c, "stat")) {
        struct stat st; if (B_STAT(mapp(&t[1]), &st) < 0) ret_err(); else ret_stat(&st);
    } else if (!strcmp(c, "fstat")) {
        struct stat st; if (B_FSTAT(atoi(t[1].s), &st) < 0) ret_err(); else ret_stat(&st);
    } else if (!strcmp(c, "unlink")) {
        if (B_UNLINK(mapp(&t[1])) < 0) ret_err(); else fprintf(out, "none\n");
    } else if (!strcmp(c, "rename")) {
        char a[8192]; snprintf(a, sizeof a, "%s", mapp(&t[1]));
        if (B_RENAME(a, mapp(&t[2])) < 0) ret_err(); else fprintf(out, "none\n");
    } else if (!strcmp(c, "mkdir")) {
        if (mkdir(mapp(&t[1]), 0777) < 0) ret_err(); else fprintf(out, "none\n");
    } else if (!strcmp(c, "rmdir")) {
        if (rmdir(mapp(&t[1])) < 0) ret_err(); else fprintf(out, "none\n");
    } else if (!strcmp(c, "opendir")) {
        void *d = B_OPENDIR(mapp(&t[1]));
        if (!d) { ret_err(); }
        else {
            int h = 1; while (h <= MAXDH && dhs[h]) h++;
            if (h > MAXDH) { B_CLOSEDIR(d); fprintf(out, "unsupported\n"); }
            else { dhs[h] = d; fprintf(out, "num %d\n", h); }
        }
    } else if (!strcmp(c, "readdir")) {
        int h = atoi(t[1].s);
        if (h < 1 || h > MAXDH || !dhs[h]) fprintf(out, "err EBADF\n");
        else {
            errno = 0;
            DIRENT *e = B_READDIR(dhs[h]);
            if (e) { fputs("bytes ", out); put_bytes(e->d_name, strlen(e->d_name)); fputc('\n', out); }
            else if (errno) ret_err(); else fprintf(out, "none\n");
        }
    } else if (!strcmp(c, "closedir")) {
        int h = atoi(t[1].s);
        if (h < 1 || h > MAXDH || !dhs[h]) fprintf(out, "err EBADF\n");
        else { B_CLOSEDIR(dhs[h]); dhs[h] = NULL; fprintf(out, "none\n"); }
    } else if (!strcmp(c, "clock")) {
        struct timeval tv;
#ifdef MEMFS
        _gettimeofday(&tv, 0);
#else
        struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
        tv.tv_sec = ts.tv_sec; tv.tv_usec = ts.tv_nsec / 1000;
#endif
        fprintf(out, "num %lld\n", (long long)tv.tv_sec * 1000000 + tv.tv_usec);
    } else {
        fprintf(out, "unsupported\n");
    }
    for (int i = 0; i < n; i++) free(t[i].s);
}

#ifndef MEMFS
static int rm_cb(const char *p, const struct stat *s, int f, struct FTW *w) {
    (void)s; (void)f; (void)w; return remove(p);
}
#endif

static void end_script(void) {
    for (int h = 1; h <= MAXDH; h++) if (dhs[h]) { B_CLOSEDIR(dhs[h]); dhs[h] = NULL; }
    for (int i = 0; i < n_open_fds; i++) if (open_fds[i] > 2) B_CLOSE(open_fds[i]);
    n_open_fds = 0;
#ifndef MEMFS
    if (chdir("/") == 0 && ROOT_BUF[0]) nftw(ROOT_BUF, rm_cb, 16, FTW_DEPTH | FTW_PHYS);
    ROOT_BUF[0] = 0;
#endif
}

static void start_script(const char *base) {
#ifdef MEMFS
    (void)base;
    backend_reset();
#else
    snprintf(ROOT_BUF, sizeof ROOT_BUF, "%s/sbXXXXXX", base);
    if (!mkdtemp(ROOT_BUF)) { perror("mkdtemp"); exit(2); }
    if (chdir(ROOT_BUF) < 0) { perror("chdir"); exit(2); }
#endif
}

int main(int argc, char **argv) {
#ifdef MEMFS
    if (argc < 3) { fprintf(stderr, "usage: driver-memfs SCRIPTS OUT\n"); return 2; }
    const char *base = NULL;
#else
    if (argc < 4) { fprintf(stderr, "usage: driver-linux SCRIPTS OUT SANDBOX_BASE\n"); return 2; }
    const char *base = argv[3];
#endif
    /* keep the driver's own files far above the descriptors scripts use */
    int ifd = open(argv[1], O_RDONLY), ofd = open(argv[2], O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (ifd < 0 || ofd < 0) { perror("open"); return 2; }
    if (dup2(ifd, 1000) < 0 || dup2(ofd, 1001) < 0) { perror("dup2"); return 2; }
    close(ifd); close(ofd);
    FILE *in = fdopen(1000, "r");
    out = fdopen(1001, "w");
    if (!in || !out) { perror("fdopen"); return 2; }
    char *line = NULL; size_t cap = 0; int active = 0;
    while (getline(&line, &cap, in) > 0) {
        if (!strncmp(line, "## ", 3)) {
            if (active) end_script();
            start_script(base); active = 1;
            fputs(line, out);
        } else if (line[0] == '#' || line[0] == '\n') {
            continue;
        } else if (active) {
            run_call(line);
        }
    }
    if (active) end_script();
    fclose(out);
    return 0;
}
