import Lua.Os.HtifFs
import Lua.Vm.Loaded

/-!
# The Lua ELF's system-call functions against the OS spec (statements)

The instance of `HtifFsImplements` (`Lua/Os/HtifFs.lean`) for
`c/lua-riscv-htif.elf`: what `c/src/htif.c` must do for the OS spec
`TCB.Os.next` to describe it. Nothing here is proved; the two statements are
recorded in PHASES.md (OS bullet).

The ELF has six functions that implement a `TCB.Os.Call` (addresses from
`Lua/Vm/Layout.lean`, generated from `nm`): `_open`, `_close`, `_read`,
`_write`, `_lseek`, `_fstat`. Its other system-call functions (`_isatty`,
`_sbrk`, `_exit`, `_kill`, `_getpid`) have no counterpart in `TCB.Os.Call`,
and the spec's other calls (`stat`, `unlink`, `rename`, `mkdir`, `rmdir`,
`opendir`, `readdir`, `closedir`, `clock`, `getenv`) have no function in the
ELF: the Lua build links no `io`/`os` library.

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

`HtifFs_Statement` is the full obligation (every call). The trace
validation (`experiments/os/RESULTS.md`) shows the current console-only
`htif.c` does not meet it: unknown and closed descriptors act as the
console instead of `EBADF`, `fstat` reports `st_nlink = 0` for the
console, and `open` with `O_CREAT` fails with `ENOENT`. `HtifPrint_Statement`
is the part a `print`-only program uses, which the traces accept: `write` to
fds 1-2 and `read` from fd 0.
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

/-- **The result of the call entered at `c`, read at its return `c'`**. -/
inductive HtifRetAt : Call → Config → Config → Ret → Prop where
  /-- failure: `-1` and `errno` -/
  | err {call c c' e} : RegInt c' 10 (-1) → ErrnoIs c'.σ.mem e → HtifRetAt call c c' (.err e)
  /-- `open`, `write`, `lseek`: a non-negative number -/
  | num {call c c' n} : retsNum call → RegIs c' 10 n → HtifRetAt call c c' (.num n)
  /-- `close`: `0` -/
  | none {fd c c'} : RegIs c' 10 0 → HtifRetAt (.close fd) c c' .none
  /-- `read`: the count, and that many bytes in the buffer given at entry -/
  | bytes {fd n buf c c'} {bs : List UInt8} :
      RegIs c 11 buf → RegIs c' 10 bs.length → BytesAt c'.σ.mem buf bs →
      HtifRetAt (.read fd n) c c' (.bytes bs)
  /-- `fstat`: `0`, and the `struct stat` at the pointer given at entry -/
  | stats {fd buf c c'} {st : Stats} :
      RegIs c 11 buf → RegIs c' 10 0 → StatAt c'.σ.mem buf st →
      HtifRetAt (.fstat fd) c c' (.stats st)

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
  callAt_complete : ∀ c call, LuaGoodState c.σ → HtifCallAt c call → scope call →
    cc.callAt c = some call
  returnsTo_sound : ∀ c c', cc.returnsTo c c' → ReturnsTo c c'
  retOf_sound : ∀ c c' call, cc.callAt c = some call → cc.returnsTo c c' →
    HtifRetAt call c c' (cc.retOf c c')

/-- The machine at `_start` with the ELF's `.text` and `.rodata` loaded.
The in-image file system's initial state (`.data`/`.bss`) is added here
when `htif.c` gets one (PHASES.md, OS). -/
structure BootAt (c : Config) : Prop where
  good : LuaGoodState c.σ
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
  good : ∀ c st, R c st → LuaGoodState c.σ
  console : ∀ c st, R c st → (output c.σ).toList = st.streams.console.map (fun b => Char.ofNat b.toNat)

/-- **`htif.c` implements the OS spec** on every call of its six functions
(statement). Not true of the current `htif.c`
(`experiments/os/RESULTS.md`): it needs a conforming in-image file system. -/
def HtifFs_Statement : Prop :=
  ∃ cc R, LuaCallConv (fun _ => True) cc ∧ HtifRepr R ∧ HtifFsImplements cc R

/-- The calls a `print`-only Lua program makes that the spec constrains:
`write` to stdout/stderr and `read` from stdin. (newlib's first `print`
also calls `_fstat(1)`, and `_isatty(1)`; the former is outside this scope
because the current `htif.c` reports `st_nlink = 0` where the spec says 1.) -/
def PrintScope : Call → Prop
  | .write fd _ _ => fd = 1 ∨ fd = 2
  | .read fd _ => fd = 0
  | _ => False

/-- **`htif.c` implements the OS spec on the console calls of `print`**
(statement). The traces accept the current `htif.c` on these
(`experiments/os/RESULTS.md`, scripts c01-c05). -/
def HtifPrint_Statement : Prop :=
  ∃ cc R, LuaCallConv PrintScope cc ∧ HtifRepr R ∧ HtifFsImplements cc R

end Lua.Os
