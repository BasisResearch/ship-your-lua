import Lua.Vm.Sim.Kit.BigHeap
import Lua.Vm.Sim.Kit.CallSpec
import Lua.Num.Decimal

/-!
# `lua_number2str`: `snprintf(buf, 44, "%.14g", x)` (lane F1-25)

`tostringbuff` (lobject.c:355-368) formats a float by `lua_number2str` =
`l_sprintf(buf, 44, LUAI_NUMFFORMAT, x)` (luaconf.h: `"%.14g"`), newlib's
`snprintf` → `_svfprintf_r`'s `'g'` conversion → `cvt` → `_dtoa_r(…, mode 2,
ndigits 14, …)`. Unlike `%lld` (`IntegerToStr_Statement`), the call
**allocates**: `_dtoa_r` frees `_REENT->_result`, its bignums come from
`_Balloc` (the free lists `_REENT->_freelist`, or `_calloc_r` → `_malloc_r`),
`__pow5mult` caches powers of five on `_REENT->_p5s`. So its summary is a
**bignum computation** (`BigRun`, `Kit/BigHeap.lean`): the heap grows within
`dtoaRoom`, the bignums `B` become `B'` (within `B` and fresh blocks, frozen
again), every byte off the allocator's, the bignums, `_REENT`'s words, the
callees' frames and the buffer kept.

`FloatToStr_Statement` is the named premise: the machine run of `snprintf` on
`%.14g` (`_svfprintf_r`'s float path, `cvt`, `_dtoa_r` mode 2 with its quick,
small-integer and bignum paths, the bignum routines of `mprec.c`, the
soft-float calls) and its value, the model's `fmt14gBits` (`Lua/Num/Decimal.lean`:
`dec14`, the correctly rounded fourteen digits with ties to even, and
`keepsZeros`, the measured small-integer quirk). Evidence that it is true:
`c/tests/float/run.sh` (the Lean model equals the ELF on Sail on every vector,
lane float-s0b) and the `print` traces of lane F1-19 (at most four `_malloc_r`
per float, far within `dtoaRoom`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- The bytes of `"%.14g"` and its terminator. -/
def g14Fmt : List (BitVec 8) := [0x25#8, 0x2e#8, 0x31#8, 0x34#8, 0x67#8, 0#8]

/-- **The break `_dtoa_r`'s bignums may claim** (`argCost`'s fifteen
`_malloc_r` beyond the string's: each with its request, the 16 KiB top pad and
a page, `MallocPost.brk_hi`). -/
def dtoaRoom : Nat := 15 * (16384 + 4096 + 128)

/-- **What `snprintf(buf, 44, "%.14g", x)` may write besides the allocator's**:
its callees' frames below `sp` and the buffer. -/
def G14Fr (sp buf a : Nat) : Prop := Below sp 8192 a ∨ Rng buf 44 a

/-- `%.14g` of a double, as bytes. -/
def g14Bytes (x : BitVec 64) : List (BitVec 8) := (Lua.Num.fmt14gBits x).map fun c => BitVec.ofNat 8 c.toNat

/-- **`lua_number2str`'s call** (`snprintf(buf, 44, fmt, x)` from
`tostringbuff`): the format `"%.14g"` in `.rodata`, the stack above the heap,
the buffer in the caller's frame, the static words (`FmtStatic`, `.rodata`:
the conversion switch, `__mprec_tens`, `__mprec_bigtens`), the heap and
`_dtoa_r`'s bignums `B` (frozen on their footprint, in chunks in use), room for
their allocations. -/
structure FltFmtIn (m : Mem) (sp buf fmt : Nat) (r : BitVec 64) (H : HeapIx) (B : Nat → Prop) : Prop where
  fmtb : bytesAt m fmt 6 = g14Fmt
  f_lo : 0x80000000 ≤ fmt
  f_hi : fmt + 6 ≤ 0x8005c6c0
  ra : r.toNat % 4 = 0
  sp_lo : heapEnd + 8192 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  b_lo : sp ≤ buf
  b_hi : buf + 44 ≤ 2 ^ 32
  stat : FmtStatic m
  rod : RodataRead m
  heap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins
  room : H.brk + dtoaRoom ≤ heapEnd
  big : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m
  big_in : ∀ a, B a → InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd

/-- **What `snprintf(buf, 44, "%.14g", x)` leaves**: its count, one to
twenty-one bytes (`-d.ddddddddddddde+ddd` at most), `%.14g` of `x` and a
`'\0'` at `buf`, a bignum computation within `dtoaRoom` off its frames and the
buffer. -/
structure G14Post (sp buf : Nat) (x : BitVec 64) (m m' : Mem) (H H' : HeapIx) (B B' : Nat → Prop) : Prop where
  len_lo : 1 ≤ (g14Bytes x).length
  len_hi : (g14Bytes x).length ≤ 21
  bytes : bytesAt m' buf ((g14Bytes x).length + 1) = g14Bytes x ++ [0#8]
  big : BigRun (G14Fr sp buf) m m' H H' B B' dtoaRoom

/-- **Named premise: `lua_number2str`** (lane F1-25; PHASES S0b `G14From`):
`snprintf(buf, 44, fmt, x)` with `fmt` the `"%.14g"` (`LUAI_NUMFFORMAT`),
`snprintf` at `0x80034de0`, writes `%.14g` of the double `x` (`fmt14gBits`,
the bytes `luaL_tolstring` prints for a float before `tostringbuff`'s `".0"`)
and a `'\0'` at `buf`, returns their count (one to twenty-one: the machine's
bound, which the model meets by `decExp`'s exactness), and is a bignum computation
(`BigRun`) within `dtoaRoom`, off its frames and the buffer (`G14Fr`). Its
machine side is `_svfprintf_r`'s float path and `_dtoa_r` mode 2 (the bignum
routines over the region abstraction `BigRun`: `_Balloc`, `_Bfree`,
`__multadd`, `__pow5mult`, `__lshift`, `__mcmp`, `__mdiff`, `__multiply`,
`quorem`, `__d2b`, `__i2b`, the soft-float calls); its value side is
`_dtoa_r`'s digits against `Lua.Num.dec14`. -/
def FloatToStr_Statement : Prop :=
  ∀ (sp buf fmt : Nat) (x r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) (H : HeapIx)
    (B : Nat → Prop), FltFmtIn m sp buf fmt r H B →
    Triple (SegSt 0x80034de0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 buf⟩, ⟨Register.x11, BitVec.ofNat 64 44⟩,
        ⟨Register.x12, BitVec.ofNat 64 fmt⟩, ⟨Register.x13, x⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' H' B', wrRet r sp (g14Bytes x).length f m' o c ∧ G14Post sp buf x m m' H H' B B')

end Lua.Vm.Sim.Kit
