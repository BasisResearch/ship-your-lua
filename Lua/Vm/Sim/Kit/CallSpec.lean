import Lua.Vm.Sim.Kit.Sflush
import Lua.Vm.Runtime

/-!
# `OP_CALL print`: the open machine-level obligations (lane F1-6)

The console end of `print`'s stdio chain is proved (`Kit/Console.lean`,
`Kit/Write.lean`, `Kit/Swrite.lean`, `Kit/Sflush.lean`: the `tohost` seam,
`_write`, `_write_r`, `__swrite`, `__sflush_r`). What `print(v)` runs above it,
as the emulator trace of `c/tests/while.lua` shows it (lane F1-6 ledger), is
stated here as named obligations, each in the summary shape of the proved
ones (`Triple` from a callee's entry pins to its return, `wrRet`):

* `FwriteStdout_Statement`: `fwrite(src, 1, n, stdout)` (`lua_writestring`)
  on the set-up, line-buffered `stdout` (`__sfvwrite_r`'s line-buffered branch:
  `memchr` for the newline, `memmove` into the buffer, `_fflush_r` →
  `__sflush_r` at a newline or a full buffer);
* `FflushStdout_Statement`: `fflush(stdout)` (the end of `lua_writeline`):
  the lock no-ops around `__sflush_r` (`sflush_sum`);
* `StdoutSetup_Statement`: the first `fwrite` from the boot state
  (`StdioBoot`, `MemfsBoot`): `__sinit`, `__swsetup_r`, `__smakebuf_r`
  (`_fstat` → `fs_init`, `_malloc_r` of the 1024-byte buffer, `_isatty`);
* `IntegerToStr_Statement`: `lua_integer2str` = `snprintf(buf, 44, "%lld", i)`
  (`_svfprintf_r`), the bytes `luaL_tolstring` prints for an integer.

The Lua side (`luaD_precall`'s C path, `luaB_print`, `luaL_tolstring` →
`luaO_pushvfstring` → `luaS_newlstr` → `internshrstr` → `luaC_newobj` →
`_malloc_r`, `luaD_poscall`) and the relation facts `SimArm .CALL` needs are in
PHASES.md (A1, the `CALL` row).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **newlib's stdio set up** (after the first `fwrite`): the words the
`fwrite`/`fflush` entries test. -/
structure StdioUp (m : Mem) : Prop where
  /-- `_REENT` -/
  impure : bytesT8 m symImpurePtr = BitVec.ofNat 64 symImpureData
  /-- `CHECK_INIT` (`ld a5, 72(ptr)`): `__sinit` ran -/
  init : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64
  /-- `_flags2`: the stream is locked through the no-op `__retarget_lock_*` -/
  flags2 : bytesT4 m (stdoutFile + fileFlags2Off) = 0#32

/-- The stack a stdio call runs in: `[sp - 2048, sp)` above the buffer. -/
structure StdioCtx (sp buf : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : buf + 1024 + 2048 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0

/-- The bytes a stdio call keeps: the caller's frames above `sp`, and below it
everything but `stdout`, its buffer, `errno` and the callee frames. -/
structure StdoutKeep (m m' : Mem) (sp buf : Nat) : Prop where
  keep_hi : ∀ a, sp ≤ a → bytesT1 m' a = bytesT1 m a
  keep_lo : ∀ a, a + 2048 ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
    (a < buf ∨ buf + 1024 ≤ a) → (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- What a stdio call that runs callees of its own keeps: as `StdoutKeep`,
below `sp` only past its callees' stack depth `d`. -/
structure StdoutKeepD (m m' : Mem) (sp buf d : Nat) : Prop where
  keep_hi : ∀ a, sp ≤ a → bytesT1 m' a = bytesT1 m a
  keep_lo : ∀ a, a + d ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
    (a < buf ∨ buf + 1024 ≤ a) → (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- A callee's entry pins: the arguments, `ra`, `sp`, `gp`, the caller's frame. -/
abbrev callPre (args : List Pin) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  args ++ ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- **`fwrite(src, 1, n, stdout)` on the set-up `stdout`** (`0x800342e4`):
returns `n`; the console gains `out` and the buffer holds `pend'`, where
`out ++ pend' = pend ++ (the n bytes at src)` (the flushes happen at the
newlines and when the buffer fills; the logical console is all that `print`'s
final `fflush` needs). The stack below `sp` is the callees' down to 4 KiB
(`fwrite` → `__sfvwrite_r` → `_fflush_r` → `__sflush_r` → `__swrite` → …). -/
def FwriteStdout_Statement : Prop :=
  ∀ (sp buf src n : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String),
    StdioCtx sp buf r → StdoutAt m buf pend → StdioUp m → buf + 4096 ≤ sp →
    errnoAddr + 4 ≤ src → src + n + 4096 ≤ sp →
    (src + n ≤ buf ∨ buf + 1024 ≤ src) → (src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src) →
    Triple (SegSt 0x800342e4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' out pend', wrRet r sp n f m' (pushes o out) c ∧ StdoutAt m' buf pend' ∧ StdioUp m' ∧
        out ++ pend' = pend ++ bytesAt m src n ∧ StdoutKeepD m m' sp buf 4096)

/-- **`fflush(stdout)`** (`0x80032a1c`): the pending bytes on the console,
`0` returned, the buffer empty. -/
def FflushStdout_Statement : Prop :=
  ∀ (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String),
    StdioCtx sp buf r → StdoutAt m buf pend → StdioUp m →
    Triple (SegSt 0x80032a1c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' (pushes o pend) c ∧ StdoutAt m' buf [] ∧ StdioUp m' ∧
        StdoutKeep m m' sp buf)

/-- **The first `fwrite`** from the boot state (`StdioBoot`, `MemfsBoot`,
the allocator's `HeapAt`): `stdout` set up with a 1024-byte buffer `buf`
from the heap, then as `FwriteStdout_Statement`. -/
def StdoutSetup_Statement : Prop :=
  ∀ (sp src n top brk : Nat) (chunks : List Lua.Vm.DlHeap.Chunk) (bins : Nat → List Nat) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String),
    StdioBoot m → MemfsBoot m → Lua.Vm.DlHeap.HeapAt m top brk chunks bins →
    r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 → brk + 4096 ≤ sp →
    0x80000000 ≤ src → src + n + 4096 ≤ sp → (src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src) →
    Triple (SegSt 0x800342e4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' out pend' buf top' brk' chunks' bins', wrRet r sp n f m' (pushes o out) c ∧
        StdoutAt m' buf pend' ∧ StdioUp m' ∧ out ++ pend' = bytesAt m src n ∧
        Lua.Vm.DlHeap.HeapAt m' top' brk' chunks' bins' ∧ (src + n ≤ buf ∨ buf + 1024 ≤ src))

/-- The bytes of `toString i` (`%lld`), one per character. -/
def intBytes (i : BitVec 64) : List (BitVec 8) := (toString i.toInt).toList.map fun ch => BitVec.ofNat 8 ch.toNat

/-- **`lua_integer2str`**: `snprintf(buf, 44, fmt, i)` with `fmt` the
`"%lld"` (`LUA_INTEGER_FMT`), `snprintf` at `0x80034de0`, writes the decimal
digits of `i` and a `'\0'` at `buf` and returns their count (the bytes
`luaL_tolstring` prints for an integer: `Value.show (.int i) = toString i.toInt`). -/
def IntegerToStr_Statement : Prop :=
  ∀ (sp buf fmt : Nat) (i r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String),
    bytesAt m fmt 5 = [0x25#8, 0x6c#8, 0x6c#8, 0x64#8, 0#8] →
    r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 → 0x80000000 ≤ buf → buf + 44 + 4096 ≤ sp →
    Triple (SegSt 0x80034de0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 buf⟩, ⟨Register.x11, BitVec.ofNat 64 44⟩,
        ⟨Register.x12, BitVec.ofNat 64 fmt⟩, ⟨Register.x13, i⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (intBytes i).length f m' o c ∧
        bytesAt m' buf ((intBytes i).length + 1) = intBytes i ++ [0#8] ∧
        ∀ a, (a + 4096 ≤ sp ∨ sp ≤ a) → (a < buf ∨ buf + 44 ≤ a) → bytesT1 m' a = bytesT1 m a)

end Lua.Vm.Sim.Kit
