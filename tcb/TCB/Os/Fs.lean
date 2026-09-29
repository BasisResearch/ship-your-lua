import TCB.Os.Errno

/-!
# POSIX file system: a port of SibylFS (Linux flavour), files and directories

TRUSTED when used as the specification of a real kernel; a SPECIFICATION
(proof obligation) when used for the in-image file system (`tcb/README.md`).

Source: SibylFS, `sibylfs/sibylfs_src` at `30675bc3b91e73f7133d0c30f18857bb1f4df8fa`
(ISC licence, `tcb/LICENSE-sibylfs`), files copied to `tcb/upstream/sibylfs/`:
`t_fs_spec.lem_cppo` (the specification; cited below as `spec:LINE`) and
`t_dir_heap.lem_cppo` (the reference file-system state; `dh:LINE`). Lem
definitions are transcribed rule by rule for the Linux architecture
(`is_linux_arch` true, `aspect_perms` off: every process has full
permissions, as SibylFS's `full_permissions` environment).

Scope: regular files and directories. Left out, and so outside every
statement that uses this spec: symlinks (`OS_SYMLINK`/`OS_READLINK`/
`OS_LSTAT`, and the symlink cases of path resolution), hard links
(`OS_LINK`), permissions and ownership (`chmod`/`chown`/`umask`, `EACCES`/
`EPERM` from permission checks), `truncate`, `pread`/`pwrite`, `chdir`,
`rewinddir`, multiple processes.

Deviations from the Lem source, each marked `DEVIATION` below:
1. `dhops_mv` (dh:530) moves a directory without updating the moved
   directory's parent pointer, so `..` and real paths go stale after a
   directory rename; here the parent is updated (POSIX `rename`).
2. Link counts are derived, not stored: a file's is the number of directory
   entries naming it (1, or 0 once unlinked while still open), a
   directory's two plus its subdirectories; in this fragment (no `link`)
   this is what the dir heap's counts (dh:439-483, dh:490-507) compute.
3. `rmdir` of a path whose last component is `.` fails with `EINVAL`
   (POSIX `rmdir`, EINVAL: "The path argument contains a last component
   that is dot"; Linux does this). SibylFS resolves `d/.` to `d` and
   reports `ENOTEMPTY`/`EEXIST` or removes it. Found by the Linux traces
   (`tcb/validation/RESULTS.md`).
7. `open` with both `O_CREAT` and `O_DIRECTORY` fails with `EINVAL` before
   any path check (Linux since 6.4, commit 43b450632676 "open: return
   EINVAL for O_DIRECTORY | O_CREAT"; SibylFS predates it).
8. `mkdir` of an existing file named with a trailing slash (`f/`) may also
   fail with `EEXIST` (Linux; SibylFS allows `ENOTDIR`/`ENOENT`, and
   `EEXIST` only on Mac OS X, spec:2853).
9. `rename` whose source or destination has a last component `.` or `..`
   fails with `EBUSY` (Linux `do_renameat2`: a last component that is not a
   plain name is `EBUSY`), in addition to SibylFS's errors; SibylFS's
   "same directory" shortcut (spec:3729) does not apply to such paths.

Deviations at the process level (`TCB/Os/Syscall.lean`) are listed there.

The model is a nondeterministic state monad (`M`, spec:2376-2600): an
operation returns the finite list of allowed results, and `par` is
SibylFS's `|||` (spec:2586; `⋈` here): the union of the errors of both sides, and a
normal result only if both sides allow one. So an operation whose checks
raise any error returns only errors, one of which the implementation may
choose.
-/

namespace TCB.Os.Fs

abbrev Name := String

/-- A directory entry (spec: `entry`, `Dir_ref_entry`/`File_ref_entry`). -/
inductive Entry where
  | dir (d : Nat)
  | file (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Directory change events for open directory handles (dh:333-344). -/
inductive Change where
  | added (n : Name)
  | removed (n : Name)
  deriving DecidableEq, Repr

/-- A directory (dh: `dh_dir`, fields that matter without permissions). -/
structure Dir where
  entries : List (Name × Entry)
  parent : Option (Nat × Name)
  /-- observers (open directory handles): handle ↦ changes, newest first -/
  observers : List (Nat × List Change)
  deriving DecidableEq, Repr

/-- The file-system state (dh: `dir_heap_state`): directories and files
share one inode numbering (`dh_get_free_inode`, dh:360); the root is
inode 0 (`dh_get_root`, dh:290). -/
structure State where
  dirs : List (Nat × Dir)
  files : List (Nat × List UInt8)
  next : Nat
  deriving DecidableEq, Repr

/-! ## Association-list helpers -/

def alookup {α β} [BEq α] (l : List (α × β)) (k : α) : Option β := (l.find? (·.1 == k)).map (·.2)
def aupdate {α β} [BEq α] (l : List (α × β)) (k : α) (v : β) : List (α × β) :=
  if l.any (·.1 == k) then l.map fun p => if p.1 == k then (k, v) else p else l ++ [(k, v)]
def aremove {α β} [BEq α] (l : List (α × β)) (k : α) : List (α × β) := l.filter (·.1 != k)

def root : Nat := 0

def State.init : State := ⟨[(root, ⟨[], none, []⟩)], [], 1⟩

namespace State
variable (s : State)

def dir? (d : Nat) : Option Dir := alookup s.dirs d
def file? (i : Nat) : Option (List UInt8) := alookup s.files i
def setDir (d : Nat) (x : Dir) : State := { s with dirs := aupdate s.dirs d x }
def setFile (i : Nat) (c : List UInt8) : State := { s with files := aupdate s.files i c }

/-- `dhops_get_parent` (dh:426). -/
def parent (d : Nat) : Option (Nat × Name) := (s.dir? d).bind (·.parent)

/-- `dh_resolve` (dh:302). -/
def resolve (d : Nat) (n : Name) : Option Entry := (s.dir? d).bind fun x => alookup x.entries n

/-- `dh_update_dir_entries` (dh:330): set or remove an entry and notify the
directory's observers. -/
def updEntry (d : Nat) (n : Name) (e : Option Entry) : State :=
  match s.dir? d with
  | none => s
  | some x =>
    let had := (alookup x.entries n).isSome
    let obs := match had, e with
      | true, none => x.observers.map fun (h, cs) => (h, .removed n :: cs)
      | false, some _ => x.observers.map fun (h, cs) => (h, .added n :: cs)
      | _, _ => x.observers
    let ents := match e with
      | some e => aupdate x.entries n e
      | none => aremove x.entries n
    s.setDir d { x with entries := ents, observers := obs }

/-- `dhops_mkdir` (dh:490). -/
def mkdir (d0 : Nat) (n : Name) : State × Nat :=
  let d1 := s.next
  let s1 := { s with next := s.next + 1 }
  let s2 := s1.setDir d1 ⟨[], some (d0, n), []⟩
  (s2.updEntry d0 n (some (.dir d1)), d1)

/-- `dhops_mkfile` (dh:513). -/
def mkfile (d0 : Nat) (n : Name) : State × Nat :=
  let i := s.next
  let s1 := { s with next := s.next + 1 }
  let s2 := s1.setFile i []
  (s2.updEntry d0 n (some (.file i)), i)

/-- `dhops_unlink` (dh:464); the file object survives while open. -/
def unlink (d0 : Nat) (n : Name) : State := s.updEntry d0 n none

/-- `dhops_mv` (dh:530), with DEVIATION 1: a moved directory's parent is
updated. -/
def mv (d0 : Nat) (n0 : Name) (d1 : Nat) (n1 : Name) : State :=
  match s.resolve d0 n0 with
  | none => s
  | some ent =>
    let s := if (s.resolve d1 n1).isSome then s.unlink d1 n1 else s
    let s := s.updEntry d1 n1 (some ent)
    let s := match ent with
      | .dir d => match s.dir? d with
        | some x => s.setDir d { x with parent := some (d1, n1) }
        | none => s
      | .file _ => s
    s.unlink d0 n0

/-- `dhops_read` (dh:547). -/
def contents (i : Nat) : List UInt8 := (s.file? i).getD []

/-- `dhops_readdir` (dh:559): names, sorted. -/
def names (d : Nat) : List Name :=
  (((s.dir? d).map (·.entries)).getD []).map (·.1) |>.mergeSort (fun a b => decide (a ≤ b))

/-- `dir_is_empty` (spec:2656). -/
def dirEmpty (d : Nat) : Bool := s.names d |>.isEmpty

/-- Link count of a file (DEVIATION 2: derived): the entries naming it. -/
def fileNlink (i : Nat) : Nat :=
  (s.dirs.map fun (_, x) => (x.entries.filter fun p => p.2 == .file i).length).sum

/-- Link count of a directory (DEVIATION 2: derived). -/
def dirNlink (d : Nat) : Nat :=
  2 + ((((s.dir? d).map (·.entries)).getD []).filter fun p => match p.2 with
    | .dir _ => true | .file _ => false).length

/-- `real_path_dir_ref` (spec:1986): `["",""]` for the root, `["","a","b"]`
for `/a/b`; fuel = number of directories. -/
def realPath (d : Nat) : List Name :=
  let rec go : Nat → Nat → List Name
    | 0, _ => ["", ""]
    | f + 1, d =>
      if d = root then ["", ""] else
      match s.parent d with
      | none => ["", ""]
      | some (d1, n) => if d1 = root then ["", n] else go f d1 ++ [n]
  go (s.dirs.length + 1) d

end State

/-! ## Path resolution (spec:2020-2330, symlink cases removed) -/

/-- `split_path_string` (spec:2067): `"/"` ↦ `["",""]`, `""` ↦ `[""]`. -/
def splitPath (p : String) : List Name := p.splitOn "/"

/-- `name_list_ends_with_slash` (spec:487). -/
def endsWithSlash (nl : List Name) : Bool := nl != [""] && nl.getLast? == some ""

/-- `ty_realpath_rec` (spec:529): the input name list and the real path. -/
structure RP where
  nl : List Name
  ns : List Name
  deriving DecidableEq, Repr

/-- `res_name` (spec:565). An error keeps the input name list and, for a
trailing slash after a file (`RR_error (ENOTDIR, Just (RR_file …))`),
the file it would have named. -/
inductive RN where
  | dir (d : Nat) (rp : RP)
  | file (d : Nat) (n : Name) (i : Nat) (rp : RP)
  | none (d : Nat) (n : Name) (rp : RP)
  | error (e : Errno) (nl : Option (List Name)) (fileRp : Option (Nat × Name × Nat × RP))
  deriving DecidableEq, Repr

namespace RN
def isDir : RN → Bool | .dir .. => true | _ => false
def isFile : RN → Bool | .file .. => true | _ => false
def isNone : RN → Bool | .none .. => true | _ => false
def isError : RN → Bool | .error .. => true | _ => false
/-- `name_list_of_res_name` (spec:594) + `rn_ends_with_slash` (spec:602). -/
def nl? : RN → Option (List Name)
  | .dir _ rp | .file _ _ _ rp | .none _ _ rp => some rp.nl
  | .error _ nl _ => nl
def endsWithSlash (r : RN) : Bool := (r.nl?.map Fs.endsWithSlash).getD false
/-- The last non-empty component of the input path. -/
def lastComp (r : RN) : Option Name := r.nl?.bind fun nl => (nl.filter (· != "")).getLast?
def lastIsDotOrDotDot (r : RN) : Bool := r.lastComp == some "." || r.lastComp == some ".."
end RN

/-- `ty_resolve_relative_result` (spec:2023). -/
inductive RR where
  | dir (d : Nat)
  | file (d : Nat) (n : Name) (i : Nat)
  | none (d : Nat) (n : Name)
  | error (e : Errno) (file : Option (Nat × Name × Nat))

/-- `alt_rr` (spec:2233) without symlinks and permissions: `""` and `"."`
stay, `".."` goes to the parent (the root is its own parent, `rr_dot_dot`
spec:2160), a missing last component is `RR_none`, a missing inner one
`ENOENT`, a file before more components `ENOTDIR` (remembering the file if
only slashes follow). -/
def resolveRel (s : State) : Nat → List Name → RR
  | d, [] => .dir d
  | d, n :: ns =>
    let last := ns.all (· == "")
    if n = "" ∨ n = "." then resolveRel s d ns
    else if n = ".." then resolveRel s ((s.parent d).map (·.1) |>.getD d) ns
    else match s.resolve d n with
      | none => if last then .none d n else .error .ENOENT none
      | some (.dir d') => resolveRel s d' ns
      | some (.file i) => match ns with
        | [] => .file d n i
        | _ => .error .ENOTDIR (if last then some (d, n, i) else none)

/-- `ty_resolve_relative_result2res_name` (spec:2034). -/
def toRN (s : State) (nl : List Name) : RR → RN
  | .dir d => .dir d ⟨nl, s.realPath d⟩
  | .file d n i =>
    let rp := s.realPath d
    .file d n i ⟨nl, (if rp = ["", ""] then [""] else rp) ++ [n]⟩
  | .none d n =>
    let rp := s.realPath d
    .none d n ⟨nl, (if rp = ["", ""] then [""] else rp) ++ [n]⟩
  | .error e f =>
    .error e (some nl) (f.map fun (d, n, i) =>
      let rp := s.realPath d
      (d, n, i, ⟨nl, (if rp = ["", ""] then [""] else rp) ++ [n]⟩))

/-- `process_path` (spec:2303): the empty path is `ENOENT`; absolute paths
start at the root. -/
def processPath (s : State) (cwd : Nat) (path : String) : RN :=
  let nl := splitPath path
  if path = "" then .error .ENOENT (some nl) none
  else
    let start := if nl.head? == some "" then root else cwd
    toRN s nl (resolveRel s start nl)

/-- `realpath_proper_subdir` (spec:548). -/
def properSubdir (s d : RP) : Bool :=
  s.ns != d.ns && (s.ns == ["", ""] || s.ns.isPrefixOf d.ns)

/-! ## The monad (spec:2376-2600) -/

inductive Res (α : Type) where
  | ok (s : State) (a : α)
  | err (s : State) (e : Errno)
  | special (msg : String)
  deriving Repr

def Res.isOk {α} : Res α → Bool | .ok .. => true | _ => false

/-- `fsmonad`: the finite list of allowed results. -/
abbrev M (α : Type) := State → List (Res α)

namespace M
def ret {α} (a : α) : M α := fun s => [.ok s a]
def bind {α β} (m : M α) (f : α → M β) : M β := fun s =>
  (m s).flatMap fun
    | .ok s a => f a s
    | .err s e => [.err s e]
    | .special msg => [.special msg]
instance : Monad M where
  pure := ret
  bind := bind
def get : M State := fun s => [.ok s s]
def put (s' : State) : M Unit := fun _ => [.ok s' ()]
/-- `fsm_raises` (spec:2508). -/
def raises {α} (es : List Errno) : M α := fun s => es.map (.err s ·)
def raise {α} (e : Errno) : M α := raises [e]
/-- `fsm_cond_raises` (spec:2526). -/
def condRaises (l : List (Errno × Bool)) : M Unit :=
  let es := (l.filter (·.2)).map (·.1)
  if es.isEmpty then ret () else raises es
def condRaise (e : Errno) (b : Bool) : M Unit := condRaises [(e, b)]
def special {α} (msg : String) : M α := fun _ => [.special msg]
def condSpecial (msg : String) (b : Bool) : M Unit := if b then special msg else ret ()
/-- `fsm_choose_nat` (spec:2484): `0 … n`. -/
def chooseNat (n : Nat) : M Nat := fun s => (List.range (n + 1)).map (.ok s ·)
/-- `|||`, `fsm_parallel_composition_drop` (spec:2586). -/
def par (m1 m2 : M Unit) : M Unit := fun s =>
  let r1 := m1 s
  let r2 := m2 s
  let bad := (r1.filter (!·.isOk)) ++ (r2.filter (!·.isOk))
  if r1.any (·.isOk) && r2.any (·.isOk) then .ok s () :: bad else bad
end M

/-- SibylFS's `|||` (Lean reserves `|||` for bitwise or). -/
infixl:60 " ⋈ " => M.par

open M

/-! ## File-system operations (`Fs_operations`, spec:2644-4440) -/

/-- Access modes and the open flags of this fragment (spec: `open_flag`). -/
inductive Access where
  | rdonly | wronly | rdwr
  deriving DecidableEq, Repr, Inhabited

structure OpenFlags where
  access : Access
  creat : Bool := false
  excl : Bool := false
  trunc : Bool := false
  append : Bool := false
  directory : Bool := false
  deriving DecidableEq, Repr, Inhabited

def OpenFlags.canRead (f : OpenFlags) : Bool := f.access == .rdonly || f.access == .rdwr
def OpenFlags.canWrite (f : OpenFlags) : Bool := f.access == .wronly || f.access == .rdwr

/-- `fsop_mkdir_checks` (spec:2846) and `fsop_mkdir_core` (spec:2888). -/
def mkdir (rp : RN) : M Unit := do
  (match rp with
    | .none .. => ret ()
    | .error e _ fopt => condRaises [(e, true), (.ENOENT, e == .ENOTDIR),
                                      (.EEXIST, e == .ENOTDIR && fopt.isSome)]  -- DEVIATION 8
    | .dir .. | .file .. => raise .EEXIST)
  match rp with
  | .none d n _ => do let s ← get; put (s.mkdir d n).1
  | _ => special "impossible: error raised before"

/-- `fsop_open_checks_rpath` (spec:2998), Linux cases. -/
def openChecks (rp : RN) (f : OpenFlags) : M Unit :=
  (match rp with | .error e _ _ => raise e | _ => ret ())
  ⋈ (match rp with | .none .. => condRaise .ENOENT (!f.creat) | _ => ret ())
  ⋈ condRaise .EISDIR (f.canWrite && rp.isDir)
  ⋈ condSpecial "open: O_TRUNC, directory (implementation defined, spec:3014)" (f.trunc && rp.isDir)
  ⋈ condRaise .ENOTDIR (f.directory && rp.isFile)
  ⋈ condRaise .EEXIST (f.excl && f.creat && (rp.isDir || rp.isFile))
  ⋈ condRaise .ENOTDIR (f.creat && rp.endsWithSlash)
  ⋈ condRaise .EISDIR (f.creat && (rp.isDir || rp.endsWithSlash))
  ⋈ condRaise .ENOENT (f.creat && rp.endsWithSlash && (rp.isNone || rp.isError))
  -- `fsop_open_checks_flags` (spec:2966): on Linux every flag check is
  -- `fsm_do_nothing` except "exactly one access mode", which `Access`
  -- makes true by construction.

/-- `fsop_open_core` (spec:3134-3205): create if absent, truncate if
`O_TRUNC` (even when opened `O_RDONLY`, spec:2977 "tr/16"). -/
def openCore (rp : RN) (f : OpenFlags) : M Entry := do
  let e ← (match rp with
    | .dir d _ => ret (Entry.dir d)
    | .file _ _ i _ => ret (Entry.file i)
    | .none d n _ => do let s ← get; let (s', i) := s.mkfile d n; put s'; ret (Entry.file i)
    | .error .. => special "impossible: error raised before")
  if f.trunc then
    match e with
    | .file i => do let s ← get; put (s.setFile i []); ret e
    | .dir _ => special "impossible: error raised before"
  else ret e

/-- `fsop_open` (spec:3278), with DEVIATION 7. -/
def openFs (rp : RN) (f : OpenFlags) : M Entry := do
  if f.creat && f.directory then raise .EINVAL else do
  openChecks rp f
  openCore rp f

/-- `fsop_pread` (spec:3337-3389) at offset `ofs`: `EINVAL` for a negative
offset, `EISDIR` for a directory, else any prefix of the available bytes
(`fsm_choose_nat len_max`). -/
def pread (e : Entry) (len : Nat) (ofs : Int) : M (List UInt8) := do
  condRaise .EINVAL (ofs < 0) ⋈ (match e with | .dir _ => raise .EISDIR | .file _ => ret ())
  match e with
  | .dir _ => special "impossible: error raised before"
  | .file i => do
    let s ← get
    let bs := s.contents i
    let o := ofs.toNat
    let lenMax := if o + len ≤ bs.length then len else bs.length - o
    let k ← chooseNat lenMax
    ret ((bs.drop o).take k)

/-- `list_array_write (bs,0,k) (bs',ofs)`: write `k` bytes of `bs` into
`bs'` at `ofs`, zero-filling a gap. -/
def writeAt (old new : List UInt8) (ofs : Nat) : List UInt8 :=
  let pre := old.take ofs ++ List.replicate (ofs - old.length) 0
  pre ++ new ++ old.drop (ofs + new.length)

/-- `fsop_pwrite` (spec:4202-4245): any `0 … len` bytes written; a
zero-length write never extends the file. -/
def pwrite (e : Entry) (bs : List UInt8) (len : Nat) (ofs : Int) : M Nat := do
  condRaise .EINVAL (ofs < 0) ⋈ condRaise .EISDIR (match e with | .dir _ => true | _ => false)
  match e with
  | .dir _ => special "impossible: error raised before"
  | .file i =>
    if len = 0 then ret 0 else do
    let s ← get
    let k ← chooseNat len
    put (s.setFile i (writeAt (s.contents i) (bs.take k) ofs.toNat))
    ret k

/-- `fsop_opendir` (spec:3480-3510). -/
def opendir (rp : RN) : M Nat := do
  (match rp with
    | .error e _ _ => raise e
    | .none .. => raise .ENOENT
    | .file .. => raise .ENOTDIR
    | .dir .. => ret ())
  match rp with
  | .dir d _ => ret d
  | _ => special "impossible: error raised before"

/-- `fsop_rename_same_rsrc_rdst` (spec:3707), no symlinks: the same
directory. (The file case is decided by the core, spec:3756.) -/
def renameSame (src dst : RN) : Bool :=
  match src, dst with
  | .dir d0 _, .dir d1 _ => d0 == d1
  | _, _ => false

/-- `fsop_rename_checks` (spec:3528-3744), Linux cases without symlinks
and permissions. -/
def renameChecks (s : State) (src dst : RN) : M Unit :=
  -- DEVIATION 9
  condRaise .EBUSY (src.lastIsDotOrDotDot || dst.lastIsDotOrDotDot) ⋈
  if renameSame src dst then ret () else
  -- fsop_rename_checks_rsrc_rdst (spec:3528)
  ( condRaise .ENOENT src.isNone
    ⋈ (match src with | .error e _ _ => raise e | _ => ret ())
    ⋈ (match dst with | .error e _ _ => raise e | _ => ret ())
    ⋈ condRaise .EISDIR (src.isFile && dst.isDir)
    ⋈ condRaise .ENOTDIR (src.isFile && dst.isNone && dst.endsWithSlash)
    ⋈ condRaise .ENOTDIR (src.isFile && dst.isDir && dst.endsWithSlash)
    ⋈ condRaise .ENOTDIR (src.isDir && (dst.isFile || dst.isError))
    ⋈ (match dst with
          | .dir d _ => if !s.dirEmpty d then raises [.ENOTEMPTY, .EEXIST] else ret ()
          | _ => ret ()) )
  -- fsop_rename_checks_root (spec:3590): renaming the root is EBUSY on Linux
  ⋈ (match src with | .dir d _ => condRaise .EBUSY (d == root) | _ => ret ())
  -- fsop_rename_checks_subdir (spec:3608)
  ⋈ (let rps := match src with | .dir _ rp => some rp | _ => none
       let rpd := match dst with
         | .dir _ rp | .file _ _ _ rp | .none _ _ rp => some rp
         | .error _ _ (some (_, _, _, rp)) => some rp
         | .error _ _ none => none
       match rps, rpd with
       | some a, some b => condRaise .EINVAL (properSubdir a b)
       | _, _ => ret ())
  -- fsop_rename_checks_parentdirs (spec:3630)
  ⋈ (match src with | .dir d _ => condRaise .EINVAL (s.parent d).isNone | _ => ret ())
  ⋈ (match dst with
        | .dir d _ => condRaises [(.ENOTEMPTY, (s.parent d).isNone && src.isDir),
                                  (.EEXIST, (s.parent d).isNone && src.isDir)]
        | _ => ret ())

/-- `fsop_rename_core` (spec:3751). -/
def renameCore (src dst : RN) : M Unit := do
  let s ← get
  match src, dst with
  | .file d0 n0 _ _, .none d1 n1 _ => put (s.mv d0 n0 d1 n1)
  | .file d0 n0 i0 _, .file d1 n1 i1 _ => if i0 == i1 then ret () else put (s.mv d0 n0 d1 n1)
  | .dir d0 _, .none d1 n1 _ =>
    match s.parent d0 with
    | none => special "impossible: src was root"
    | some (p, n0) => put (s.mv p n0 d1 n1)
  | .dir d0 _, .dir d1 _ =>
    if d0 == d1 then ret () else
    match s.parent d0, s.parent d1 with
    | some (p0, n0), some (p1, n1) => put (s.mv p0 n0 p1 n1)
    | _, _ => special "impossible: root"
  | _, _ => special "impossible: error raised before"

/-- `fsop_rename` (spec:3792). -/
def rename (src dst : RN) : M Unit := do
  let s ← get
  renameChecks s src dst
  renameCore src dst

/-- The last non-empty component of the input path is `.` (for DEVIATION 3). -/
def RN.lastIsDot (r : RN) : Bool := r.lastComp == some "."

/-- `fsop_rmdir` (spec:3829-3878), with DEVIATION 3 (`EINVAL` for a last
component `.`). -/
def rmdir (rp : RN) : M Unit := do
  let s ← get
  condRaise .EINVAL rp.lastIsDot ⋈
  (match rp with
    | .file .. => raise .ENOTDIR
    | .none .. => raise .ENOENT
    | .error e _ _ => raise e
    | .dir d _ =>
      (if !s.dirEmpty d then raises [.ENOTEMPTY, .EEXIST] else ret ())
      ⋈ (match s.parent d with | none => raise .EBUSY | some _ => ret ()))
  match rp with
  | .dir d _ => match s.parent d with
    | some (p, n) => put (s.unlink p n)
    | none => special "impossible: error raised before"
  | _ => special "impossible: error raised before"

/-- `fsop_unlink` (spec:4030-4072), Linux, no symlinks. -/
def unlink (rp : RN) : M Unit := do
  (match rp with
    | .error e _ _ => raise e
    | .none .. => condRaises [(.ENOENT, true), (.ENOTDIR, rp.endsWithSlash)]
    | .dir .. => condRaises [(.EISDIR, true), (.EPERM, true)]
    | .file .. => ret ())
  match rp with
  | .file d n _ _ => do let s ← get; put (s.unlink d n)
  | _ => special "impossible: error raised before"

/-- File kinds reported by `stat`. -/
inductive Kind where
  | reg | dir | chr
  deriving DecidableEq, Repr, Inhabited

/-- The fields of `ty_stats` this fragment compares: kind, size (not
compared for directories, spec:5575 `mask_dir`), link count. -/
structure Stats where
  kind : Kind
  size : Nat
  nlink : Nat
  deriving DecidableEq, Repr, Inhabited

def statFile (s : State) (i : Nat) : Stats := ⟨.reg, (s.contents i).length, s.fileNlink i⟩
def statDir (s : State) (d : Nat) : Stats := ⟨.dir, 0, s.dirNlink d⟩

/-- `fsop_stat` (spec:3890-3915). -/
def stat (rp : RN) : M Stats := do
  (match rp with
    | .error e _ _ => raise e
    | .none .. => raise .ENOENT
    | _ => ret ())
  let s ← get
  match rp with
  | .file _ _ i _ => ret (statFile s i)
  | .dir d _ => ret (statDir s d)
  | _ => special "impossible: error raised before"

end TCB.Os.Fs
