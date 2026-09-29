# OS-spec validation results

The method is SibylFS's: generate call scripts, run them on a real system,
record what each call returned, and check every recorded trace against the
specification. Here the specification is the Lean port (`TCB.Os.next`,
`tcb/TCB/Os/Syscall.lean`), the checker is `tcbcheck` (sound by
`TCB.Os.checkTrace_sound`), and there are two systems under test: the Linux
host, and the in-image file system of `c/src/htif.c` compiled natively.

Reproduce: `tcb/validation/run.sh` (about 3 s; outputs in
`tcb/validation/out/`, not committed). `tcb/validation/quick.sh` is the
gate subset (`scripts/check_all.sh` stage t1).

Measured 2026-09-29 on aws-dev, Linux 7.0.0-1012-aws, sandbox directories
on the `/data` file system (ext4), glibc 2.43.

## Scripts

`tcb/validation/gen.py` (seed 20260929), 6,490 scripts:

* systematic (3,490): a fixture (`/d` non-empty with `/d/sub`, `/e` empty,
  files `/f` = `hello` and `/d/g`), then one call under test for every
  path in a table covering each resolution outcome (existing file,
  directory, empty directory, missing last component, missing parent, file
  used as a directory, trailing slashes, `.`, `..`, `//`, the empty path)
  and, for `open`, all 96 combinations of one access mode with
  `O_CREAT`/`O_EXCL`/`O_TRUNC`/`O_APPEND`/`O_DIRECTORY`; descriptor calls
  on files opened each way, on a directory, on closed and bogus
  descriptors; `readdir` while the directory changes (added, removed,
  renamed, emptied entries); fd reuse; the clock;
* random (2,000): 8-24 calls over names `a`,`b`,`c` at depth 1-3;
* flat (1,000): root-level files only, no `mkdir`/`rmdir`, descriptors the
  script opened (what the in-image file system supports).

Calls executed on Linux: 101,621 (open 22,268, mkdir 16,273, close
14,943, write 10,701, stat 10,550, read 6,419, rename 5,159, lseek 4,700,
fstat 3,235, unlink 3,015, rmdir 2,008, opendir 1,630, readdir 691,
closedir 26, clock 3). Errors observed: ENOENT 21,565, EBADF 21,506,
ENOTDIR 2,717, EISDIR 1,440, EEXIST 1,221, EINVAL 765, EBUSY 82,
ENOTEMPTY 56, ESPIPE 1.

## Linux: 6,490 traces — 6,398 accepted, 0 rejected, 92 special

The 92 `special` verdicts are calls the spec leaves unconstrained, and
each observed return is one the spec also lists:

| class | traces | Linux returned |
|---|---|---|
| `open` with `O_RDONLY|O_TRUNC` on a directory (implementation-defined in SibylFS, spec:3014) | 72 | `EISDIR` |
| `lseek` `SEEK_END` on a directory (DEVIATION 5) | 19 | `num 9223372036854775807` (ext4's end-of-directory cookie) or `EINVAL` |
| `lseek` on fd 0-2 (EXTENSION: depends on the device) | 1 | `ESPIPE` / `num 0` (`/dev/null`) |

Before the fixes below the first full run rejected 645 traces. Each
rejection class was either a porting error in the spec or a difference
between SibylFS (2015, Linux 3.x) and today's Linux. The fixes are
documented deviations in the Lean source (`DEVIATION n`):

| class (first run) | traces | resolution |
|---|---|---|
| `open` with `O_CREAT|O_DIRECTORY` returns `EINVAL` | 540 | DEVIATION 7: Linux ≥ 6.4 rejects the flag pair before path lookup |
| `rename` with a last component `.`/`..` returns `EBUSY` (incl. `rename "/d" "/d/."`, which SibylFS's same-directory shortcut accepted) | 82 | DEVIATION 9 (Linux `do_renameat2`) |
| `mkdir "/f/"` on an existing file returns `EEXIST` | 20 | DEVIATION 8 (SibylFS allows it only on Mac OS X) |
| after `opendir`, `open` returns the next fd number | 7 (quick run) | DEVIATION 6: glibc's `DIR` holds a descriptor; `opendir` may take the smallest free fd |
| `read` on that descriptor returns `EINVAL`; closing it breaks the handle (`readdir` → `EBADF`) | 3 | DEVIATION 6 (`FdObj.dirfd`) |
| zero-length `write` with `O_APPEND` leaves the offset | 1 (quick) | DEVIATION 4 (SibylFS moves it to end of file, contradicting its own spec:4221 comment) |
| unlinked-but-open file has link count 0 | 1 (quick) | DEVIATION 2 corrected (derived count = entries naming the file) |
| `rmdir "/d/."` returns `EINVAL` | 1 (quick) | DEVIATION 3 (POSIX `rmdir` EINVAL) |
| `lseek` SEEK_END on a directory; `lseek` on fd 0 (`/dev/null`) succeeds | 3 (quick) | DEVIATION 5 and EXTENSION: unconstrained |
| `O_TRUNC` on a directory stopped the check although `EISDIR` was allowed | 6 (quick) | checker: a `special` alternative only stops checking when no normal alternative matches |

## In-image file system: 6,490 traces — 245 accepted, 1,781 rejected, 4,464 unsupported

The in-image file system (`c/src/htif.c`) has no `mkdir`/`rmdir`, so the
driver reports those calls as unsupported and the checker skips the rest
of those traces (4,464, every systematic and random script with a
fixture). On the flat family, which it should support, it passes 243 of
1,000. Every rejection is a real deviation of the in-image file system
from POSIX, not of the spec:

| class | rejections | what the in-image file system does |
|---|---|---|
| M1: descriptors it never issued | 555 `read` → `bytes ""`, 545 `write` → written, 212 `lseek` → `ESPIPE`, 112 `close` → success, 95 `fstat` → `chr` | any fd outside its table is treated as the console (`_read`: EOF, `_write`: HTIF output); POSIX says `EBADF` |
| M2: no directories | 226 `open` with `O_CREAT` under a missing directory or with a trailing slash succeeds; 1 `rename` into a "subdirectory" of a file succeeds | names are opaque strings containing `/` |
| M3: `ENOENT` where POSIX says `ENOTDIR` | 18 (`rename`/`unlink`/`stat`/`opendir`/`open` through a file) | no path resolution |
| M4: link count of an unlinked-but-open file | 12 `fstat` → 1 | `_fstat` reports `st_nlink = 1` always (POSIX: 0 after unlink) |

(`readdir` without `.`/`..` never shows up: every script that opens a
directory also calls `mkdir` first.)

So the in-image file system is **not yet** an implementation of the spec.
To discharge the bare-metal obligation (`tcb/README.md` §A) it must first
return `EBADF` for descriptors it did not issue (M1), report `st_nlink = 0`
after unlink (M4), and either implement directories and path resolution
(M2, M3) or the bare-metal instance of the spec must be restricted to
programs that only use root-level files and descriptors they opened. The
OCaml programs run so far (`c/tests/`, `boot/ocamlc` compiling a file)
stay inside that restriction except for `Sys.readdir` on `/lib/ocaml`.

## Clock

`clock` calls: Linux returns increasing microsecond counts, the in-image
clock always 0; both accepted (monotone), the second being
`TCB.Os.Clock.frozen`.
