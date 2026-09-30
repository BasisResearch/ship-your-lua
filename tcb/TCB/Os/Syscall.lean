import TCB.Os.Fs
import TCB.Os.Streams
import TCB.Os.Clock
import TCB.Os.Process

/-!
# The system-call interface (TRUSTED for a real kernel)

One process's view of the OS: the SibylFS file system (`TCB/Os/Fs.lean`)
behind file descriptors and directory handles (SibylFS's process level,
`spec:4526-5470`: `os_open`, `os_close`, `os_read`, `os_write`, `os_lseek`,
`os_opendir`, `os_readdir`, `os_closedir`), the CakeML-style console
streams on fds 0-2 (`TCB/Os/Streams.lean`), a monotone clock, and the
process's command line, environment and exit.

**The specification is `next`**: given a state, a call and the value the
call returned, the list of states the OS may be in afterwards (empty: that
return is not allowed). Like SibylFS's Lem spec, it is an executable
function whose meaning is a relation; `OsStep s c r s'` is membership, and
`OsSpecial s c` marks calls whose behaviour the spec leaves unconstrained
(SibylFS's special states: implementation-defined or undefined behaviour).
The trace checker (`checkTrace`) runs `next` over sets of states; its
soundness (`checkTrace_sound`) says every state it keeps is reachable by
`OsStep`s that produce exactly the observed returns.

Extensions beyond the two sources, marked `EXTENSION`: `fstat` (not a
SibylFS command; specified as `stat` of the descriptor's object), and
`read`/`write`/`lseek` on the console streams (SibylFS has no streams;
whether fd 0-2 are seekable depends on what they are — a terminal, a pipe,
`/dev/null` — so `lseek` on them is left unconstrained).

Deviations from SibylFS's process level, marked `DEVIATION` (all found by
the Linux traces, `tcb/validation/RESULTS.md`):
4. A zero-length `write` does not move the offset, also with `O_APPEND`
   (Linux; SibylFS sets the offset to the end of file, spec:4948, although
   its own `fsop_pwrite_core` calls such a write a no-op, spec:4221).
5. `lseek(fd, off, SEEK_END)` on a directory is left unconstrained
   (SibylFS: `EOVERFLOW`, spec:5014; Linux's answer depends on the file
   system, e.g. ext4 returns the largest offset).
6. `opendir` may use a file descriptor (POSIX: a `DIR` "may be implemented
   using a file descriptor"; glibc does): it either takes none, as in
   SibylFS, or the smallest free one, open read-only on the directory, and
   `closedir` closes it. This is what makes later `open`s return the next
   number on Linux. That descriptor (`FdObj.dirfd`) is glibc's directory
   stream: `read` on it fails with `EISDIR` or `EINVAL` (Linux gives
   `EINVAL` for glibc's stream, `EISDIR` for a directory `open`ed by the
   program), `lseek` on it is unconstrained (offsets are opaque cookies),
   and `close` on it breaks the handle: `readdir`/`closedir` then fail
   with `EBADF`.
-/

namespace TCB.Os

open Fs

/-- What a file descriptor refers to (SibylFS `fd_state` + `fid_state`,
spec:4653; one process and no `dup`, so the fid indirection is folded
in). -/
inductive FdObj where
  | file (e : Entry) (offset : Nat) (flags : OpenFlags)
  | stream (s : Stream)
  /-- the descriptor of a directory stream (DEVIATION 6) -/
  | dirfd (d : Nat)
  deriving DecidableEq, Repr

/-- A directory handle (spec: `dh_state`, spec:4719): the directory, its
observer handle, names that must still be reported and names that may be. -/
structure DhState where
  dir : Nat
  obs : Nat
  must : List Name
  may : List Name
  /-- the file descriptor the handle uses, if any (DEVIATION 6) -/
  fd : Option Nat
  /-- that descriptor was closed by `close` (DEVIATION 6) -/
  broken : Bool := false
  deriving DecidableEq, Repr

structure OsState where
  fs : Fs.State
  fds : List (Nat × FdObj)
  dhs : List (Nat × DhState)
  cwd : Nat
  streams : Streams
  clock : Clock
  proc : Process
  deriving DecidableEq, Repr

def OsState.init (argv : List String := []) (env : List (String × String) := [])
    (input : List UInt8 := []) : OsState :=
  ⟨Fs.State.init, [(0, .stream .stdin), (1, .stream .stdout), (2, .stream .stderr)], [],
   Fs.root, Streams.init input, Clock.init, Process.init argv env⟩

/-- The calls. Paths are strings, resolved against the root / cwd. -/
inductive Call where
  | «open» (path : String) (flags : OpenFlags)
  | close (fd : Nat)
  | read (fd : Nat) (n : Nat)
  | write (fd : Nat) (bs : List UInt8) (n : Nat)
  | lseek (fd : Nat) (off : Int) (whence : Int)
  | stat (path : String)
  | fstat (fd : Nat)
  | unlink (path : String)
  | rename (src dst : String)
  | mkdir (path : String)
  | rmdir (path : String)
  | opendir (path : String)
  | readdir (dh : Nat)
  | closedir (dh : Nat)
  | clock
  | getenv (name : String)
  | exit (code : Nat)
  deriving DecidableEq, Repr

/-- Return values (SibylFS `ret_value` + `error`). `none` is `RV_none`:
success without a value, and the end of a directory for `readdir`. -/
inductive Ret where
  | none
  | num (n : Int)
  | bytes (b : List UInt8)
  | stats (st : Stats)
  | err (e : Errno)
  deriving DecidableEq, Repr

/-- Observed-vs-specified return (spec:5552-5580): stats of a directory
are compared without the size. -/
def Ret.matches : Ret → Ret → Bool
  | .stats a, .stats b => if a.kind == .dir then a.kind == b.kind && a.nlink == b.nlink else a == b
  | a, b => a == b

/-- One allowed result: a successor and its return, or unconstrained. -/
inductive Out where
  | ok (s : OsState) (r : Ret)
  | special (msg : String)

/-- The smallest natural `≥ lo` not in `used` (`smallest_free_nat`,
spec:4617). -/
def smallestFree (used : List Nat) (lo : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, n => n
    | f + 1, n => if used.contains n then go f (n + 1) else n
  go (used.length + 1) lo

/-- Run a file-system operation and build OS results (`os_run_fs_command`
and the result processing of `os_open` etc.). -/
def liftFs {α} (s : OsState) (m : Fs.M α) (k : Fs.State → α → OsState × Ret) : List Out :=
  (m s.fs).map fun
    | .ok fs' a => let (s', r) := k fs' a; .ok s' r
    | .err fs' e => .ok { s with fs := fs' } (.err e)
    | .special msg => .special msg

def lookupFd (s : OsState) (fd : Nat) : Option FdObj := alookup s.fds fd
def lookupDh (s : OsState) (dh : Nat) : Option DhState := alookup s.dhs dh

/-- Descriptor numbers in use. -/
def usedFds (s : OsState) : List Nat := s.fds.map (·.1)

/-- `os_open` (spec:4787): create the fd with the smallest free number. -/
def osOpen (s : OsState) (path : String) (f : OpenFlags) : List Out :=
  liftFs s (Fs.openFs (processPath s.fs s.cwd path) f) fun fs' e =>
    let fd := smallestFree (usedFds s) 0
    ({ s with fs := fs', fds := aupdate s.fds fd (.file e 0 f) }, .num fd)

/-- `os_close` (spec:4759). -/
def osClose (s : OsState) (fd : Nat) : List Out :=
  match lookupFd s fd with
  | none => [.ok s (.err .EBADF)]
  | some _ =>
    let dhs := s.dhs.map fun (k, h) => (k, if h.fd == some fd then { h with broken := true } else h)
    [.ok { s with fds := aremove s.fds fd, dhs := dhs } .none]

/-- `os_read` (spec:4849); streams per CakeML (EXTENSION for fds 1-2:
not readable, `EBADF`). -/
def osRead (s : OsState) (fd n : Nat) : List Out :=
  match lookupFd s fd with
  | none => [.ok s (.err .EBADF)]
  | some (.stream .stdin) =>
    (s.streams.readLengths n).map fun k =>
      .ok { s with streams := s.streams.doRead k } (.bytes (s.streams.input.take k))
  | some (.stream _) => [.ok s (.err .EBADF)]
  | some (.dirfd _) => [.ok s (.err .EISDIR), .ok s (.err .EINVAL)]
  | some (.file e ofs f) =>
    if !f.canRead then [.ok s (.err .EBADF)] else
    liftFs s (Fs.pread e n ofs) fun fs' bs =>
      ({ s with fs := fs', fds := aupdate s.fds fd (.file e (ofs + bs.length) f) }, .bytes bs)

/-- `os_write` (spec:4909): `O_APPEND` writes at the end; streams per
CakeML (EXTENSION for fd 0: not writable, `EBADF`). -/
def osWrite (s : OsState) (fd : Nat) (bs : List UInt8) (n : Nat) : List Out :=
  match lookupFd s fd with
  | none => [.ok s (.err .EBADF)]
  | some (.stream .stdin) => [.ok s (.err .EBADF)]
  | some (.dirfd _) => [.ok s (.err .EBADF)]
  | some (.stream st) =>
    (Streams.writeLengths n).map fun k =>
      .ok { s with streams := s.streams.doWrite st (bs.take k) } (.num k)
  | some (.file e ofs f) =>
    if !f.canWrite then [.ok s (.err .EBADF)] else
    let o : Nat := if f.append then
        (match e with | .file i => (s.fs.contents i).length | .dir _ => ofs)
      else ofs
    liftFs s (Fs.pwrite e bs n o) fun fs' k =>
      -- DEVIATION 4: a zero-length write leaves the offset alone
      let o' := if k = 0 then ofs else o + k
      ({ s with fs := fs', fds := aupdate s.fds fd (.file e o' f) }, .num k)

/-- `os_lseek` (spec:4976), whence 0/1/2 = SEEK_SET/CUR/END; streams are
not seekable (EXTENSION, POSIX ESPIPE). -/
def osLseek (s : OsState) (fd : Nat) (off whence : Int) : List Out :=
  let badWhence := !(whence == 0 || whence == 1 || whence == 2)
  match lookupFd s fd with
  | none => if badWhence then [.ok s (.err .EBADF), .ok s (.err .EINVAL)] else [.ok s (.err .EBADF)]
  | some fo =>
    if badWhence then [.ok s (.err .EINVAL)] else
    match fo with
    | .stream _ => [.special "lseek on a console stream (EXTENSION: depends on the device)"]
    | .dirfd _ => [.special "lseek on a directory stream's descriptor (DEVIATION 6: opaque offsets)"]
    | .file e ofs f =>
      let new? : Option Int :=
        if whence == 0 then some off
        else if whence == 1 then some (ofs + off)
        else match e with
          | .dir _ => none
          | .file i => some ((s.fs.contents i).length + off)
      match new? with
      | none => [.special "lseek SEEK_END on a directory (DEVIATION 5: file-system dependent)"]
      | some n =>
        if n < 0 then [.ok s (.err .EINVAL)]
        else [.ok { s with fds := aupdate s.fds fd (.file e n.toNat f) } (.num n)]

/-- `fstat` (EXTENSION): `stat` of the descriptor's object. -/
def osFstat (s : OsState) (fd : Nat) : List Out :=
  match lookupFd s fd with
  | none => [.ok s (.err .EBADF)]
  | some (.stream _) => [.ok s (.stats ⟨.chr, 0, 1⟩)]
  | some (.file (.file i) _ _) => [.ok s (.stats (statFile s.fs i))]
  | some (.file (.dir d) _ _) => [.ok s (.stats (statDir s.fs d))]
  | some (.dirfd d) => [.ok s (.stats (statDir s.fs d))]

/-- `os_opendir` + `create_dh` (spec:5123, spec:4719): handles are the
smallest free number from 1; the observer handle is one more than the
largest registered (dh:659); the handle must report `.`, `..` and the
current entries (`rewind_dhs`, spec:4700). -/
def osOpendir (s : OsState) (path : String) : List Out :=
  liftFs s (Fs.opendir (processPath s.fs s.cwd path)) fun fs' d =>
    let dh := smallestFree (s.dhs.map (·.1)) 1
    match fs'.dir? d with
    | none => ({ s with fs := fs' }, .err .ENOENT)
    | some x =>
      let oh := x.observers.foldl (fun m p => if p.1 ≥ m then p.1 + 1 else m) 0
      let fs'' := fs'.setDir d { x with observers := x.observers ++ [(oh, [])] }
      ({ s with fs := fs'', dhs := aupdate s.dhs dh ⟨d, oh, "." :: ".." :: fs'.names d, [], none, false⟩ },
       .num dh)

/-- `opendir` with DEVIATION 6: the handle may also take the smallest free
file descriptor, open read-only on the directory. -/
def osOpendirFd (s : OsState) (path : String) : List Out :=
  (osOpendir s path).flatMap fun
    | .ok s' (.num dh) =>
      match lookupDh s' dh.toNat with
      | some h =>
        let k := smallestFree (usedFds s') 0
        [.ok s' (.num dh),
         .ok { s' with dhs := aupdate s'.dhs dh.toNat { h with fd := some k },
                       fds := aupdate s'.fds k (.dirfd h.dir) }
             (.num dh)]
      | none => [.ok s' (.num dh)]
    | o => [o]

/-- `os_readdir` (spec:5165): consume the observed changes (added names may
be reported, removed ones need not be), then return any name that must or
may still be reported, or the end if none must.

DEVIATION 10: at the end of the directory the source (spec:5214-5216)
drops the updated handle — the observed changes are consumed but not
recorded — so after an entry that still had to be reported is removed, a
first `readdir` may return the end and a second one must then return the
removed name. That rejects POSIX/Linux behaviour (once at the end, `readdir`
keeps returning the end); found by the in-image file system's run
(`tcb/validation/RESULTS.md`). Here the end result records the updated
handle. -/
def osReaddir (s : OsState) (dh : Nat) : List Out :=
  match lookupDh s dh with
  | none => [.ok s (.err .EBADF)]
  | some h =>
    if h.broken then [.ok s (.err .EBADF)] else
    match s.fs.dir? h.dir with
    | none => [.ok s (.err .EBADF)]
    | some x =>
      let changes := ((alookup x.observers h.obs).getD []).reverse
      let fs1 := s.fs.setDir h.dir { x with observers := aupdate x.observers h.obs [] }
      let s1 := { s with fs := fs1 }
      let h' := changes.foldl (fun h c => match c with
        | .added n => { h with may := n :: h.may }
        | .removed n =>
          if h.must.contains n then { h with must := h.must.erase n, may := n :: h.may } else h) h
      let names := (h'.must ++ h'.may).eraseDups
      let named := names.map fun n =>
        let h'' := if h'.must.contains n then { h' with must := h'.must.erase n }
          else { h' with may := h'.may.erase n }
        Out.ok { s1 with dhs := aupdate s.dhs dh h'' } (.bytes n.toUTF8.toList)
      if h'.must.isEmpty then .ok { s1 with dhs := aupdate s.dhs dh h' } .none :: named else named

/-- `os_closedir` (spec:5237). -/
def osClosedir (s : OsState) (dh : Nat) : List Out :=
  match lookupDh s dh with
  | none => [.ok s (.err .EBADF)]
  | some h =>
    let fs' := match s.fs.dir? h.dir with
      | some x => s.fs.setDir h.dir { x with observers := aremove x.observers h.obs }
      | none => s.fs
    let fds' := match h.fd with | some k => if h.broken then s.fds else aremove s.fds k | none => s.fds
    [.ok { s with fs := fs', dhs := aremove s.dhs dh, fds := fds' } (if h.broken then .err .EBADF else .none)]

/-- Everything but the clock (whose choice is unbounded, so `next` takes it
from the observed return). -/
def outs (s : OsState) : Call → List Out
  | .«open» p f => osOpen s p f
  | .close fd => osClose s fd
  | .read fd n => osRead s fd n
  | .write fd bs n => osWrite s fd bs n
  | .lseek fd off w => osLseek s fd off w
  | .stat p => liftFs s (Fs.stat (processPath s.fs s.cwd p)) fun fs' st => ({ s with fs := fs' }, .stats st)
  | .fstat fd => osFstat s fd
  | .unlink p => liftFs s (Fs.unlink (processPath s.fs s.cwd p)) fun fs' _ => ({ s with fs := fs' }, .none)
  | .rename a b =>
    liftFs s (Fs.rename (processPath s.fs s.cwd a) (processPath s.fs s.cwd b)) fun fs' _ =>
      ({ s with fs := fs' }, .none)
  | .mkdir p => liftFs s (Fs.mkdir (processPath s.fs s.cwd p)) fun fs' _ => ({ s with fs := fs' }, .none)
  | .rmdir p => liftFs s (Fs.rmdir (processPath s.fs s.cwd p)) fun fs' _ => ({ s with fs := fs' }, .none)
  | .opendir p => osOpendirFd s p
  | .readdir dh => osReaddir s dh
  | .closedir dh => osClosedir s dh
  | .clock => []
  | .getenv n => [.ok s (match s.proc.getenv n with
      | some v => .bytes v.toUTF8.toList
      | none => .none)]
  | .exit c => [.ok { s with proc := { s.proc with exited := some c } } .none]

/-- **The specification**: the states the OS may be in after call `c`
returned `r` in state `s`. A process that has exited makes no calls. -/
def next (s : OsState) (c : Call) (r : Ret) : List OsState :=
  if s.proc.exited.isSome then [] else
  match c with
  | .clock => match r with
    | .num t => if t ≥ 0 ∧ s.clock.now ≤ t.toNat then [{ s with clock := s.clock.read t.toNat }] else []
    | _ => []
  | c => (outs s c).filterMap fun
    | .ok s' r' => if r'.matches r then some s' else none
    | .special _ => none

/-- The call's behaviour is left unconstrained in `s` (SibylFS special
state). -/
def special (s : OsState) (c : Call) : Bool :=
  !s.proc.exited.isSome && (outs s c).any fun | .special _ => true | _ => false

/-- **`OsStep s c r s'`**: from `s`, call `c` may return `r` and leave the
OS in `s'`. -/
def OsStep (s : OsState) (c : Call) (r : Ret) (s' : OsState) : Prop := s' ∈ next s c r

/-- `OsSpecial s c`: any behaviour of `c` in `s` is allowed. -/
def OsSpecial (s : OsState) (c : Call) : Prop := special s c = true

/-- The executable checker for one step. -/
def allowed (s : OsState) (c : Call) (r : Ret) : Option OsState := (next s c r).head?

theorem allowed_sound {s s' : OsState} {c : Call} {r : Ret}
    (h : allowed s c r = some s') : OsStep s c r s' := by
  unfold allowed at h
  unfold OsStep
  exact List.mem_of_head? h

theorem allowed_complete {s s' : OsState} {c : Call} {r : Ret}
    (h : OsStep s c r s') : (allowed s c r).isSome := by
  unfold allowed OsStep at *
  cases hn : next s c r with
  | nil => rw [hn] at h; cases h
  | cons _ _ => rfl

/-! ## Traces -/

/-- States reachable by a sequence of steps with the given calls/returns. -/
inductive Reach : OsState → List (Call × Ret) → OsState → Prop where
  | nil (s : OsState) : Reach s [] s
  | step {s s' s'' : OsState} {c : Call} {r : Ret} {t : List (Call × Ret)} :
      OsStep s c r s' → Reach s' t s'' → Reach s ((c, r) :: t) s''

/-- Verdict of checking a trace from a set of states. -/
inductive Verdict where
  /-- every step allowed; the possible final states -/
  | accepted (finals : List OsState)
  /-- step `i` (0-based) is not allowed from any possible state -/
  | rejected (i : Nat)
  /-- step `i` is unconstrained by the spec; checking stops -/
  | special (i : Nat)

/-- Check a trace, tracking every state the spec allows (SibylFS's
checker tracks state sets likewise). -/
def checkFrom (ss : List OsState) (i : Nat) : List (Call × Ret) → Verdict
  | [] => .accepted ss
  | (c, r) :: t =>
    let ss' := ss.flatMap (next · c r)
    if ss'.isEmpty then (if ss.any (special · c) then .special i else .rejected i)
    else checkFrom ss' (i + 1) t

def checkTrace (s0 : OsState) (t : List (Call × Ret)) : Verdict := checkFrom [s0] 0 t

theorem checkFrom_sound :
    ∀ (t : List (Call × Ret)) (ss : List OsState) (i : Nat) (finals : List OsState),
      checkFrom ss i t = .accepted finals →
      ∀ f ∈ finals, ∃ s ∈ ss, Reach s t f := by
  intro t
  induction t with
  | nil =>
    intro ss i finals h f hf
    simp only [checkFrom, Verdict.accepted.injEq] at h
    subst h
    exact ⟨f, hf, .nil f⟩
  | cons cr t ih =>
    intro ss i finals h f hf
    obtain ⟨c, r⟩ := cr
    simp only [checkFrom] at h
    split at h
    · split at h <;> cases h
    · obtain ⟨s', hs', hr⟩ := ih _ _ _ h f hf
      obtain ⟨s, hs, hn⟩ := List.mem_flatMap.1 hs'
      exact ⟨s, hs, .step hn hr⟩

/-- **Soundness of the trace checker**: every final state it reports is
reachable from the initial state by steps the spec allows, with exactly the
trace's calls and returns. -/
theorem checkTrace_sound {s0 : OsState} {t : List (Call × Ret)} {finals : List OsState}
    (h : checkTrace s0 t = .accepted finals) : ∀ f ∈ finals, Reach s0 t f := by
  intro f hf
  obtain ⟨s, hs, hr⟩ := checkFrom_sound t [s0] 0 finals h f hf
  simp only [List.mem_singleton] at hs
  subst hs
  exact hr

end TCB.Os
