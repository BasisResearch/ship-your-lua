/-!
# Linux errno values (TRUSTED: part of the OS interface)

The error codes the ported specification (`TCB/Os/Fs.lean`) can return, with
their Linux (x86-64 and RISC-V `asm-generic/errno-base.h`, `errno.h`)
numbers. SibylFS's `error` type (`upstream/sibylfs/t_fs_spec.lem_cppo`,
`Fs_types.error`) names them; the numbers are only used to print and parse
traces.
-/

namespace TCB.Os

inductive Errno where
  | EPERM | ENOENT | EBADF | EACCES | EBUSY | EEXIST | EXDEV | ENOTDIR | EISDIR
  | EINVAL | EMFILE | ESPIPE | ENOSPC | EROFS | EMLINK | ENAMETOOLONG | ENOSYS
  | ENOTEMPTY | ELOOP | EOVERFLOW
  deriving DecidableEq, Repr, Inhabited

namespace Errno

def all : List Errno :=
  [EPERM, ENOENT, EBADF, EACCES, EBUSY, EEXIST, EXDEV, ENOTDIR, EISDIR, EINVAL, EMFILE,
   ESPIPE, ENOSPC, EROFS, EMLINK, ENAMETOOLONG, ENOSYS, ENOTEMPTY, ELOOP, EOVERFLOW]

/-- Linux errno numbers. -/
def toNat : Errno → Nat
  | EPERM => 1 | ENOENT => 2 | EBADF => 9 | EACCES => 13 | EBUSY => 16 | EEXIST => 17
  | EXDEV => 18 | ENOTDIR => 20 | EISDIR => 21 | EINVAL => 22 | EMFILE => 24
  | ESPIPE => 29 | ENOSPC => 28 | EROFS => 30 | EMLINK => 31 | ENAMETOOLONG => 36
  | ENOSYS => 38 | ENOTEMPTY => 39 | ELOOP => 40 | EOVERFLOW => 75

def name : Errno → String
  | EPERM => "EPERM" | ENOENT => "ENOENT" | EBADF => "EBADF" | EACCES => "EACCES"
  | EBUSY => "EBUSY" | EEXIST => "EEXIST" | EXDEV => "EXDEV" | ENOTDIR => "ENOTDIR"
  | EISDIR => "EISDIR" | EINVAL => "EINVAL" | EMFILE => "EMFILE" | ESPIPE => "ESPIPE"
  | ENOSPC => "ENOSPC" | EROFS => "EROFS" | EMLINK => "EMLINK"
  | ENAMETOOLONG => "ENAMETOOLONG" | ENOSYS => "ENOSYS" | ENOTEMPTY => "ENOTEMPTY"
  | ELOOP => "ELOOP" | EOVERFLOW => "EOVERFLOW"

def ofName? (s : String) : Option Errno := all.find? (·.name == s)

end Errno
end TCB.Os
