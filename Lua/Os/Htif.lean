import Lua.Os.HtifFs
import Lua.Vm.Loaded

/-!
# The Lua ELF's system-call functions against the OS spec (statements)

The instance of `HtifFsImplements` (`Lua/Os/HtifFs.lean`) for
`c/lua-riscv-htif.elf`: what `c/src/htif.c` must do for the OS spec
`TCB.Os.next` to describe it. Nothing here is proved; the two statements are
recorded in PHASES.md (OS bullet).

The ELF has twelve functions that implement a `TCB.Os.Call` (addresses
from `Lua/Vm/Layout.lean`, generated from `nm`, so they follow the ELF):
`_open`, `_close`, `_read`, `_write`, `_lseek`, `_fstat`, `_stat`,
`_unlink`, `rename`, `mkdir`, `rmdir` and `_gettimeofday` (the clock). The
`io` and `os` libraries reach them through newlib (`fopen`, `fread`,
`fseek`, `remove`, `rename`, `time`, ...). Its other system-call functions
(`_isatty`, `_times`, `_link`, `_sbrk`, `_exit`, `_kill`, `_getpid`) have no
counterpart in `TCB.Os.Call`, apart from `_exit` (the spec's `exit`, which
ends the run and so is not a returning call). The spec's `opendir`,
`readdir` and `closedir` have no function in the ELF, and `getenv` is
newlib's (an empty environment, as `OsState.init` has).

* `HtifCallAt c call`: `c` is at the entry of the function for `call`,
  with the arguments in `a0`-`a2` (RISC-V psABI) decoding to `call`
  (newlib's flag values, `Layout.o*`).
* `HtifRetAt call c c' r`: at the return `c'`, the result is `r` as newlib
  sees it: `a0`, `errno` (`_impure_ptr->_errno`, newlib's errno numbers
  `Layout.errno*`), and the out-parameter buffer (`read`, `fstat`).
* `LuaCallConv scope cc`: `cc` decodes exactly that, and decodes every
  in-scope call (so the obligation cannot be met by decoding nothing).
* `HtifRepr Boot R`: `R` holds at boot for the initial OS state, implies the
  good machine state, and ties the spec's console stream to the HTIF output.

`HtifFs_Statement` is the full obligation (every call). `htif.c` has an
in-image file system written against the spec, and the trace validation
(`experiments/os/RESULTS.md`) rejects none of its traces: 5,275 generated
scripts accepted, 79 at calls the spec leaves unconstrained, the rest
skipped at `opendir`, which the ELF does not have; all console scripts
accepted. So `HtifFs_Statement` is now plausibly true of the ELF, with two
qualifications:
* **Resource limits.** `htif.c` has 64 files and directories, 32
  descriptors and the heap; past them it returns `EMFILE`/`ENOSPC`, which
  the spec never allows. A proof needs a resource bound in the scope (like
  the `Fits` budget of the VM refinement).
* **Vacuity.** As stated, `R` may hold at boot only (`HtifRepr`), which
  makes the statement hold vacuously; the meaningful form comes with the
  frame obligation of `OsState` in the semantics (PHASES.md, OS).

`HtifPrint_Statement` is the part a `print`-only program uses: `write` to
fds 1-2, `read` from fd 0, and newlib's `_fstat` of the console.
-/

namespace Lua.Os

open Vsa.Machine Lua.Vm Lua.Vm.Layout TCB.Os TCB.Os.Fs
open LeanRV64DExecutable Sail
open Vsa.Sim (gprGet)

/-- The program counter of `c` is `a`. -/
def PcAt (c : Config) (a : Nat) : Prop :=
  c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 a)

/-- Register `x<r>` holds the non-negative value `n` (a C `int`, `long`,
`size_t` or pointer argument). The bound makes the decoding unique. -/
structure RegIs (c : Config) (r n : Nat) : Prop where
  lt : n < 2 ^ 63
  get : gprGet c.σ r = some (BitVec.ofNat 64 n)

/-- Register `x<r>` holds the signed value `i` (`off_t`, `int whence`). -/
def RegInt (c : Config) (r : Nat) (i : Int) : Prop :=
  -2 ^ 63 ≤ i ∧ i < 2 ^ 63 ∧ gprGet c.σ r = some (BitVec.ofInt 64 i)

/-- A NUL-terminated C string at `a` whose bytes are the UTF-8 of `s`. -/
structure CStringAt (m : Mem) (a : Nat) (s : String) : Prop where
  bytes : BytesAt m a s.toUTF8.toList
  nul : m[a + s.toUTF8.size]? = some 0
  no_nul : 0 ∉ s.toUTF8.toList

/-- newlib's `open` flags decoded to the spec's (`Layout.o*`); other bits
are outside the spec's scope and ignored. -/
def decodeFlags (f : Nat) : Option OpenFlags :=
  let acc := f &&& oAccmode
  let access? : Option Access :=
    if acc = oRdonly then some .rdonly else if acc = oWronly then some .wronly
    else if acc = oRdwr then some .rdwr else none
  access?.map fun a =>
    { access := a, creat := f &&& oCreat != 0, excl := f &&& oExcl != 0,
      trunc := f &&& oTrunc != 0, append := f &&& oAppend != 0,
      directory := f &&& oDirectory != 0 }

/-- **The calls the ELF's system-call functions implement**, decoded at
their entry (psABI: arguments in `a0` = `x10`, `a1` = `x11`, `a2` = `x12`). -/
inductive HtifCallAt (c : Config) : Call → Prop where
  /-- `int _open(const char *path, int flags, int mode)` -/
  | «open» {path : String} {flags : OpenFlags} {p f : Nat} :
      PcAt c symOpen → RegIs c 10 p → CStringAt c.σ.mem p path → RegIs c 11 f →
      decodeFlags f = some flags → HtifCallAt c (.open path flags)
  /-- `int _close(int fd)` -/
  | close {fd : Nat} : PcAt c symClose → RegIs c 10 fd → HtifCallAt c (.close fd)
  /-- `ssize_t _read(int fd, void *buf, size_t len)` -/
  | read {fd n buf : Nat} :
      PcAt c symRead → RegIs c 10 fd → RegIs c 11 buf → RegIs c 12 n → HtifCallAt c (.read fd n)
  /-- `ssize_t _write(int fd, const void *buf, size_t len)` -/
  | write {fd n buf : Nat} {bs : List UInt8} :
      PcAt c symWrite → RegIs c 10 fd → RegIs c 11 buf → RegIs c 12 n →
      BytesAt c.σ.mem buf bs → bs.length = n → HtifCallAt c (.write fd bs n)
  /-- `off_t _lseek(int fd, off_t offset, int whence)` -/
  | lseek {fd : Nat} {off whence : Int} :
      PcAt c symLseek → RegIs c 10 fd → RegInt c 11 off → RegInt c 12 whence →
      HtifCallAt c (.lseek fd off whence)
  /-- `int _fstat(int fd, struct stat *st)` -/
  | fstat {fd buf : Nat} : PcAt c symFstat → RegIs c 10 fd → RegIs c 11 buf → HtifCallAt c (.fstat fd)
  /-- `int _stat(const char *path, struct stat *st)` -/
  | stat {path : String} {p buf : Nat} :
      PcAt c symStat → RegIs c 10 p → CStringAt c.σ.mem p path → RegIs c 11 buf →
      HtifCallAt c (.stat path)
  /-- `int _unlink(const char *path)` (newlib's `remove`, Lua's `os.remove`) -/
  | unlink {path : String} {p : Nat} :
      PcAt c symUnlink → RegIs c 10 p → CStringAt c.σ.mem p path → HtifCallAt c (.unlink path)
  /-- `int rename(const char *from, const char *to)` (Lua's `os.rename`) -/
  | rename {src dst : String} {p q : Nat} :
      PcAt c symRename → RegIs c 10 p → CStringAt c.σ.mem p src → RegIs c 11 q →
      CStringAt c.σ.mem q dst → HtifCallAt c (.rename src dst)
  /-- `int mkdir(const char *path, mode_t mode)` (the mode is outside the spec) -/
  | mkdir {path : String} {p : Nat} :
      PcAt c symMkdir → RegIs c 10 p → CStringAt c.σ.mem p path → HtifCallAt c (.mkdir path)
  /-- `int rmdir(const char *path)` -/
  | rmdir {path : String} {p : Nat} :
      PcAt c symRmdir → RegIs c 10 p → CStringAt c.σ.mem p path → HtifCallAt c (.rmdir path)
  /-- `int _gettimeofday(struct timeval *tv, void *tz)` with `tv` non-null:
  the clock (newlib's `time`, Lua's `os.time`) -/
  | clock {tv : Nat} : PcAt c symGettimeofday → RegIs c 10 tv → tv ≠ 0 → HtifCallAt c .clock

/-- newlib's number for an errno (`Layout.errno*`, from `<errno.h>`; it
differs from Linux's `Errno.toNat` for some). -/
def newlibErrno : Errno → Nat
  | .EPERM => errnoEPERM | .ENOENT => errnoENOENT | .EBADF => errnoEBADF
  | .EACCES => errnoEACCES | .EBUSY => errnoEBUSY | .EEXIST => errnoEEXIST
  | .EXDEV => errnoEXDEV | .ENOTDIR => errnoENOTDIR | .EISDIR => errnoEISDIR
  | .EINVAL => errnoEINVAL | .EMFILE => errnoEMFILE | .ESPIPE => errnoESPIPE
  | .ENOSPC => errnoENOSPC | .EROFS => errnoEROFS | .EMLINK => errnoEMLINK
  | .ENAMETOOLONG => errnoENAMETOOLONG | .ENOSYS => errnoENOSYS
  | .ENOTEMPTY => errnoENOTEMPTY | .ELOOP => errnoELOOP | .EOVERFLOW => errnoEOVERFLOW

/-- The `S_IFMT` bits of a file kind. -/
def kindBits : Kind → Nat
  | .reg => sIfreg | .dir => sIfdir | .chr => sIfchr

/-- `errno` (`_impure_ptr->_errno`, a 32-bit `int`) holds `e`. -/
inductive ErrnoIs (m : Mem) (e : Errno) : Prop where
  | mk (reent : Nat) (impure : rd64 m symImpurePtr = some reent)
      (errno : rd32 m (reent + reentErrnoOff) = some (newlibErrno e))

/-- The `struct stat` at `a` says `st` (the fields the spec has). -/
structure StatAt (m : Mem) (a : Nat) (st : Stats) : Prop where
  mode : ∃ v, rd32 m (a + statModeOff) = some v ∧ v &&& sIfmt = kindBits st.kind
  nlink : rd16 m (a + statNlinkOff) = some st.nlink
  size : rd64 m (a + statSizeOff) = some st.size

/-- The calls whose success value is a number in `a0`. -/
def retsNum : Call → Bool
  | .open .. | .write .. | .lseek .. => true
  | _ => false

/-- The calls whose success value is `0` in `a0` and nothing else. -/
def retsNone : Call → Bool
  | .close .. | .unlink .. | .rename .. | .mkdir .. | .rmdir .. => true
  | _ => false

/-- The calls that fill the `struct stat` whose address is in `a1`. -/
def retsStats : Call → Bool
  | .stat .. | .fstat .. => true
  | _ => false

/-- **The result of the call entered at `c`, read at its return `c'`**. -/
inductive HtifRetAt : Call → Config → Config → Ret → Prop where
  /-- failure: `-1` and `errno` -/
  | err {call c c' e} : RegInt c' 10 (-1) → ErrnoIs c'.σ.mem e → HtifRetAt call c c' (.err e)
  /-- `open`, `write`, `lseek`: a non-negative number -/
  | num {call c c' n} : retsNum call → RegIs c' 10 n → HtifRetAt call c c' (.num n)
  /-- `close`, `unlink`, `rename`, `mkdir`, `rmdir`: `0` -/
  | none {call c c'} : retsNone call → RegIs c' 10 0 → HtifRetAt call c c' .none
  /-- `read`: the count, and that many bytes in the buffer given at entry -/
  | bytes {fd n buf c c'} {bs : List UInt8} :
      RegIs c 11 buf → RegIs c' 10 bs.length → BytesAt c'.σ.mem buf bs →
      HtifRetAt (.read fd n) c c' (.bytes bs)
  /-- `stat`, `fstat`: `0`, and the `struct stat` at the pointer given at entry -/
  | stats {call buf c c'} {st : Stats} :
      retsStats call → RegIs c 11 buf → RegIs c' 10 0 → StatAt c'.σ.mem buf st →
      HtifRetAt call c c' (.stats st)
  /-- the clock: `0`, and the `struct timeval` at the pointer given at entry,
  in microseconds -/
  | clock {tv sec usec : Nat} {c c'} :
      RegIs c 10 tv → RegIs c' 10 0 → rd64 c'.σ.mem (tv + timevalSecOff) = some sec →
      rd64 c'.σ.mem (tv + timevalUsecOff) = some usec →
      HtifRetAt .clock c c' (.num (sec * 1000000 + usec))

/-- `c'` is the return of the function entered at `c`: the return address
`ra` = `x1` of the entry is the pc, with the entry's stack pointer
`sp` = `x2`. -/
inductive ReturnsTo (c c' : Config) : Prop where
  | mk (ra : Nat) (ra_at : RegIs c 1 ra) (pc : PcAt c' ra) (sp : gprGet c'.σ 2 = gprGet c.σ 2)

/-- **The calling convention of the Lua ELF's system-call functions**,
restricted to the calls in `scope`. -/
structure LuaCallConv (scope : Call → Prop) (cc : CallConv) : Prop where
  /-- a decoded call is an in-scope call at its function's entry -/
  callAt_sound : ∀ c call, cc.callAt c = some call → HtifCallAt c call ∧ scope call
  /-- every in-scope call at a function's entry, in a good state, is decoded -/
  callAt_complete : ∀ c call, Vsa.Sim.GoodState c.σ → HtifCallAt c call → scope call →
    cc.callAt c = some call
  returnsTo_sound : ∀ c c', cc.returnsTo c c' → ReturnsTo c c'
  retOf_sound : ∀ c c' call, cc.callAt c = some call → cc.returnsTo c c' →
    HtifRetAt call c c' (cc.retOf c c')

/-- The machine at `_start` with the ELF's `.text` and `.rodata` loaded.
The in-image file system's state is in `.bss` (`files`, `fds`,
`fs_ready`), which `crt0.S` zeroes; `fs_ready = 0` makes the first call
set up the root and fds 0-2, so the initial state needs no data here. -/
structure BootAt (c : Config) : Prop where
  good : Vsa.Sim.GoodState c.σ
  pc : PcAt c symStart
  text : Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize Image.textByte c.σ.mem
  rodata : Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte c.σ.mem

/-- **What a representation relation must satisfy**: it starts at the
spec's initial state (no arguments, environment or input), holds only in
good states, and the spec's console stream is what HTIF printed.

These fields do not force `R` to hold at any call entry: `R` could hold at
boot only. What rules that out is the end-to-end statement that uses
`HtifFsImplements`, which also needs `R` preserved by every step outside
`htif.c` (the rest of the ELF leaves the in-image file system and the HTIF
output alone). That frame obligation comes with `OsState` in the semantics
(PHASES.md, OS). -/
structure HtifRepr (R : Config → OsState → Prop) : Prop where
  init : ∀ c, BootAt c → R c (OsState.init)
  good : ∀ c st, R c st → Vsa.Sim.GoodState c.σ
  console : ∀ c st, R c st → (output c.σ).toList = st.streams.console.map (fun b => Char.ofNat b.toNat)

/-- **`htif.c` implements the OS spec** on every call of its twelve
functions (statement). The traces accept the current `htif.c`
(`experiments/os/RESULTS.md`); see the module doc for the resource limits
a proof must scope out, and for why `HtifRepr` alone leaves it vacuous. -/
def HtifFs_Statement : Prop :=
  ∃ cc R, LuaCallConv (fun _ => True) cc ∧ HtifRepr R ∧ HtifFsImplements cc R

/-- The calls a `print`-only Lua program makes that the spec constrains:
`write` to stdout/stderr, `read` from stdin, and `fstat` of the console
(newlib's first `print` calls `_fstat(1)`, and `_isatty(1)`, which the
spec does not have). -/
def PrintScope : Call → Prop
  | .write fd _ _ => fd = 1 ∨ fd = 2
  | .read fd _ => fd = 0
  | .fstat fd => fd ≤ 2
  | _ => False

/-- **`htif.c` implements the OS spec on the console calls of `print`**
(statement). The traces accept the current `htif.c` on these
(`experiments/os/RESULTS.md`, scripts c01-c05, c08-c10, c24). -/
def HtifPrint_Statement : Prop :=
  ∃ cc R, LuaCallConv PrintScope cc ∧ HtifRepr R ∧ HtifFsImplements cc R

end Lua.Os
