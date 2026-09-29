#!/usr/bin/env python3
"""Generate validation scripts for the OS spec (TCB/Os/Syscall.lean).

    python3 tcb/validation/gen.py OUT.scripts [--random N] [--seed S] [--quick]

Two families, both in the call syntax of TCB/Os/Trace.lean:

* systematic: a fixture (directories /d (non-empty), /e (empty),
  /d/sub (non-empty), files /f (content "hello") and /d/g), then ONE call
  under test with every argument from a table of paths that cover each
  resolution outcome (existing file / directory / empty directory, missing
  last component, missing parent, file used as a directory, trailing
  slashes, ".", "..", "//", the empty path) and, for open, every
  combination of the flags in scope; descriptor calls on files opened each
  way, on a directory, on a closed and a bogus descriptor; readdir with the
  directory changed while it is being read;
* random: sequences of calls over a small name space, chosen so the spec's
  error cases come up often.

Paths never resolve above the root, and no call renames or removes the
root: the Linux driver plays "/" with a sandbox directory, which (unlike the
spec's root) has a parent and could be renamed.
"""
import argparse
import itertools
import random

FIXTURE = [
    'mkdir "/d"', 'mkdir "/e"', 'mkdir "/d/sub"',
    'open "/f" O_WRONLY|O_CREAT', 'write 3 "hello" 5', 'close 3',
    'open "/d/g" O_WRONLY|O_CREAT', 'close 3',
    'open "/d/sub/x" O_WRONLY|O_CREAT', 'close 3',
]

# (path, resolves to root?) — resolution outcomes after FIXTURE
PATHS = [
    ("/f", False), ("/f/", False), ("/f/x", False), ("/f/.", False),
    ("/d", False), ("/d/", False), ("/d/.", False), ("/d/sub/..", False),
    ("/e", False), ("/e/", False),
    ("/d/g", False), ("/d/g/", False), ("//d/g", False), ("/d/./g", False),
    ("/d/sub/../g", False),
    ("/m", False), ("/m/", False), ("/m/x", False), ("/d/m", False), ("/d/m/", False),
    ("f", False), ("d/g", False), ("m", False),
    ("/", True), (".", True), ("/d/..", True), ("", False),
]
NONROOT = [p for p, r in PATHS if not r]

ACCESS = ["O_RDONLY", "O_WRONLY", "O_RDWR"]
EXTRA = ["O_CREAT", "O_EXCL", "O_TRUNC", "O_APPEND", "O_DIRECTORY"]


def q(p):
    return '"' + p.replace("\\", "\\\\").replace('"', '\\"') + '"'


def all_flags():
    for a in ACCESS:
        for k in range(len(EXTRA) + 1):
            for c in itertools.combinations(EXTRA, k):
                yield "|".join([a, *c])


def systematic(quick=False):
    out = []
    paths = PATHS if not quick else PATHS[::3]
    flags = list(all_flags()) if not quick else ["O_RDONLY", "O_WRONLY|O_CREAT", "O_RDWR|O_CREAT|O_EXCL",
                                                 "O_RDONLY|O_DIRECTORY", "O_WRONLY|O_TRUNC|O_APPEND"]
    for p, _ in paths:
        for f in flags:
            # open, then observe what was opened / created
            out.append((f"open {p!r} {f}", FIXTURE + [f"open {q(p)} {f}", "fstat 3", "read 3 3",
                                                  'write 3 "ab" 2', "lseek 3 0 1", "close 3",
                                                  f"stat {q(p)}"]))
    for p, _ in paths:
        for call in ["stat", "unlink", "mkdir", "opendir"]:
            out.append((f"{call} {p!r}", FIXTURE + [f"{call} {q(p)}", f"stat {q(p)}", 'stat "/d"']))
    for p in (NONROOT if not quick else NONROOT[::3]):
        out.append((f"rmdir {p!r}", FIXTURE + [f"rmdir {q(p)}", f"stat {q(p)}", 'stat "/d"']))
    srcs = NONROOT if not quick else NONROOT[::4]
    dsts = NONROOT + ["/d/sub/y", "/e/y", "/d/sub/z/"]
    dsts = dsts if not quick else dsts[::4]
    for a in srcs:
        for b in dsts:
            out.append((f"rename {a!r} {b!r}", FIXTURE + [f"rename {q(a)} {q(b)}", f"stat {q(a)}",
                                                        f"stat {q(b)}", 'stat "/d"', 'stat "/e"']))
    # rename into own subdirectory, onto non-empty / empty dirs
    for a, b in [("/d", "/d/sub/n"), ("/d", "/d/n"), ("/d/sub", "/e"), ("/e", "/d"),
                 ("/e", "/d/sub"), ("/d", "/e/x"), ("/f", "/e"), ("/e", "/f")]:
        out.append((f"rename {a} {b}", FIXTURE + [f"rename {q(a)} {q(b)}", f"stat {q(b)}",
                                                  'opendir "/"', "readdir 1", "readdir 1", "readdir 1",
                                                  "readdir 1", "readdir 1", "readdir 1"]))
    # descriptor calls
    opens = {"ro": 'open "/f" O_RDONLY', "wo": 'open "/f" O_WRONLY', "rw": 'open "/f" O_RDWR',
             "ap": 'open "/f" O_WRONLY|O_APPEND', "dir": 'open "/d" O_RDONLY'}
    ops = ["read 3 0", "read 3 2", "read 3 100", 'write 3 "xyz" 3', 'write 3 "xyz" 0', "lseek 3 2 0",
           "lseek 3 -1 0", "lseek 3 3 1", "lseek 3 -10 1", "lseek 3 0 2", "lseek 3 5 2", "lseek 3 0 7",
           "fstat 3", "close 3"]
    for (k, o), op in itertools.product(opens.items(), ops):
        out.append((f"{k} {op}", FIXTURE + [o, op, "lseek 3 0 1", "fstat 3", "read 3 100"]))
    for op in ["read 9 1", 'write 9 "a" 1', "lseek 9 0 0", "lseek 9 0 7", "fstat 9", "close 9",
               "readdir 7", "closedir 7", "fstat 0", "lseek 0 0 0", "lseek 2 0 0"]:
        out.append((f"bad {op}", FIXTURE + [op]))
    # write past the end, then read the hole
    out.append(("hole", FIXTURE + ['open "/f" O_RDWR', "lseek 3 8 0", 'write 3 "Z" 1', "lseek 3 0 0",
                                   "read 3 100", "fstat 3"]))
    # unlink while open
    out.append(("unlink open", FIXTURE + ['open "/f" O_RDWR', 'unlink "/f"', "read 3 100",
                                          'write 3 "q" 1', "fstat 3", 'stat "/f"']))
    # readdir with concurrent changes
    for mods in [[], ['open "/d/new" O_WRONLY|O_CREAT'], ['unlink "/d/g"'], ['rename "/d/g" "/d/h"'],
                 ['rmdir "/d/sub/x"', 'unlink "/d/sub/x"', 'rmdir "/d/sub"'], ['mkdir "/d/n2"']]:
        for when in range(4):
            body = FIXTURE + ['opendir "/d"'] + ["readdir 1"] * when + mods + ["readdir 1"] * 7 + ["closedir 1",
                                                                                                  "readdir 1"]
            out.append((f"readdir {when} {mods}", body))
    # two handles
    out.append(("two dh", FIXTURE + ['opendir "/d"', 'opendir "/e"', "readdir 2", "readdir 2", "readdir 2",
                                     "closedir 1", 'opendir "/d/sub"', "readdir 1", "readdir 1", "readdir 1",
                                     "readdir 1"]))
    # smallest free fd
    out.append(("fd reuse", FIXTURE + ['open "/f" O_RDONLY', 'open "/d/g" O_RDONLY', "close 3",
                                       'open "/d" O_RDONLY', "fstat 3", "fstat 4"]))
    # clock (monotone; the memfs clock is frozen at 0)
    out.append(("clock", ["clock", "clock", 'mkdir "/c"', "clock"]))
    return out


NAMES = ["a", "b", "c"]


def rand_path(rng):
    depth = rng.choice([1, 1, 1, 2, 2, 3])
    comps = [rng.choice(NAMES) for _ in range(depth)]
    p = "/" + "/".join(comps)
    r = rng.random()
    if r < 0.08:
        p += "/"
    elif r < 0.12 and depth > 1:
        p = "/" + comps[0] + "/./" + "/".join(comps[1:])
    elif r < 0.16 and depth > 1:
        p = "/" + comps[0] + "/" + comps[1] + "/../" + "/".join(comps[1:])
    return p


def random_scripts(n, seed):
    rng = random.Random(seed)
    out = []
    for k in range(n):
        body = []
        fds = []
        dhs = 0
        for _ in range(rng.randint(8, 24)):
            r = rng.random()
            p = rand_path(rng)
            if r < 0.18:
                body.append(f"mkdir {q(p)}")
            elif r < 0.36:
                f = rng.choice(["O_RDONLY", "O_WRONLY|O_CREAT", "O_RDWR|O_CREAT", "O_RDWR|O_CREAT|O_EXCL",
                                "O_WRONLY|O_CREAT|O_TRUNC", "O_WRONLY|O_APPEND", "O_RDONLY|O_DIRECTORY"])
                body.append(f"open {q(p)} {f}")
                fds.append(3 + len(fds))
            elif r < 0.46:
                fd = rng.choice(fds) if fds and rng.random() < 0.9 else rng.randint(3, 8)
                s = rng.choice(["x", "hello", "0123456789"])
                body.append(f"write {fd} {q(s)} {len(s)}")
            elif r < 0.54:
                fd = rng.choice(fds) if fds and rng.random() < 0.9 else rng.randint(3, 8)
                body.append(f"read {fd} {rng.choice([1, 4, 64])}")
            elif r < 0.58:
                fd = rng.choice(fds) if fds else 3
                body.append(f"lseek {fd} {rng.choice([0, 2, -1, 20])} {rng.choice([0, 1, 2])}")
            elif r < 0.66:
                body.append(f"stat {q(p)}")
            elif r < 0.72:
                body.append(f"unlink {q(p)}")
            elif r < 0.78:
                body.append(f"rmdir {q(p)}")
            elif r < 0.88:
                body.append(f"rename {q(p)} {q(rand_path(rng))}")
            elif r < 0.93:
                body.append(f"opendir {q(p)}")
                dhs += 1
            elif r < 0.97 and dhs:
                body.append(f"readdir {rng.randint(1, dhs)}")
            elif fds:
                fd = rng.choice(fds)
                body.append(f"close {fd}")
        out.append((f"random {k}", body))
    return out


def flat_scripts(n, seed):
    """Files at the root only, no mkdir/rmdir, descriptors the script opened:
    what the in-image file system (which has no directories) supports."""
    rng = random.Random(seed + 1)
    out = []
    for k in range(n):
        body = []
        fds = []
        for _ in range(rng.randint(6, 20)):
            r = rng.random()
            p = "/" + rng.choice(["a", "b", "c"])
            if r < 0.25:
                f = rng.choice(["O_RDONLY", "O_WRONLY|O_CREAT", "O_RDWR|O_CREAT", "O_RDWR|O_CREAT|O_EXCL",
                                "O_WRONLY|O_CREAT|O_TRUNC", "O_WRONLY|O_APPEND", "O_RDWR"])
                body.append(f"open {q(p)} {f}")
                fds.append(None)
            elif r < 0.40 and fds:
                s = rng.choice(["x", "hello", "0123456789"])
                body.append(f"write FD {q(s)} {len(s)}")
            elif r < 0.52 and fds:
                body.append(f"read FD {rng.choice([1, 4, 64])}")
            elif r < 0.60 and fds:
                body.append(f"lseek FD {rng.choice([0, 2, 20])} {rng.choice([0, 1, 2])}")
            elif r < 0.66 and fds:
                body.append("fstat FD")
            elif r < 0.74:
                body.append(f"stat {q(p)}")
            elif r < 0.82:
                body.append(f"unlink {q(p)}")
            elif r < 0.92:
                body.append(f"rename {q(p)} {q('/' + rng.choice(['a', 'b', 'c']))}")
            elif fds:
                body.append("close FD")
        out.append((f"flat {k}", body))
    return out


def resolve_fds(scripts):
    """Replace the FD placeholder by a descriptor number the script's own
    successful-looking opens would get: the driver's real numbers are only
    known at run time, so FD cycles over 3..(3 + opens - 1)."""
    out = []
    for name, body in scripts:
        n_open = 0
        res = []
        rng = random.Random(name)
        for line in body:
            if line.startswith("open "):
                n_open += 1
            if " FD" in line or line.endswith("FD"):
                fd = 3 + rng.randrange(max(n_open, 1))
                line = line.replace("FD", str(fd), 1)
            res.append(line)
        out.append((name, res))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--random", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=20260929)
    ap.add_argument("--quick", action="store_true")
    a = ap.parse_args()
    scripts = (systematic(a.quick) + random_scripts(a.random if not a.quick else 40, a.seed)
               + resolve_fds(flat_scripts(1000 if not a.quick else 40, a.seed)))
    with open(a.out, "w") as f:
        for i, (name, body) in enumerate(scripts):
            f.write(f"## {i:05d} {name}\n")
            for line in body:
                f.write(line + "\n")
    print(f"{len(scripts)} scripts, {sum(len(b) for _, b in scripts)} calls -> {a.out}")


if __name__ == "__main__":
    main()
