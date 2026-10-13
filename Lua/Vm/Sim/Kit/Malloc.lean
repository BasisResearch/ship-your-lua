import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.DlHeap

/-!
# `_malloc_r` at the Lua ELF's addresses: the named premise (lane F1-10)

Every allocation `print` reaches goes through newlib's dlmalloc:
`__smakebuf_r`'s 1024-byte `stdout` buffer at the first write,
`luaS_newlstr` (`luaM_malloc_` → `l_alloc` → `realloc`) for an integer's
string, `luaE_extendCI` for the `CallInfo` of the call to `print`.

**Why a premise.** The instruction-level proof of `_malloc_r` exists in
ship-your-interpreter at its WHILE addresses (`VsaIris/Vsa/MallocRunAll.lean`,
`mallocLocalRun_proved`, over 9,700 lines of `VsaIris/Vsa/Malloc*.lean` on
its allocation ledger `DlHeap`/`AllocLedger`); this repository has its step
tables at the Lua ELF's addresses (`VsaIris.Vsa.AllocSteps`) but not the
proof, and the copied `VsaIris/MallocRun.lean` keeps `MallocLocalRun` as an
assumption (PHASES A0). Porting it is A0 work, not a summary at Lua
addresses. So `MallocR_Statement` is stated here over the WHILE-free
`DlHeap.HeapAt` (`Lua/Vm/DlHeap.lean`, checked on the boot heap by the boot
witness) and taken as a named premise.

**The statement** (`_malloc_r(_REENT, n)` at `0x8002fa34`, `1 ≤ n`): with
room for one `_sbrk` of `n` plus the top pad, `MINSIZE`, a page of rounding
and a page of correction (`brk + n + 16384 ≤ __heap_end`), it returns a
16-aligned block `p` of a chunk now in use, inside the arena below the new
break; the heap shape holds again; every chunk in use at the call is still
one; and it writes nothing but its globals (`MallocGlobal`), the arena off
the chunks in use (`InUse`: a chunk's payload, up to the next chunk's
`prev_size`, which a request of `n ≤ size - 8` may use) and its stack below
`sp` (1 KiB: its frame, `_sbrk_r`, `_sbrk`, `__errno`).

**The heap is stated of the zero fill** (`Vsa.Densify.fillZeroMem`, lane
F1-11): `HeapAt` reads with `rd64` (bytes present), but the machine reads
totally (`readByte = getD 0`), so `_malloc_r`'s run depends only on the
fill. `VmRel` holds the machine's memory only by total reads (`Core.frame`),
so a heap stated of the machine memory itself could never be met from the
relation; of the fill it can (`HeapAt.ofTotal`, `Kit/HeapFill.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap

/-- `_malloc_r`'s entry. -/
abbrev symMallocR : Nat := 0x8002fa34

/-- The words `_malloc_r` writes outside the arena (`nm -S`): `__malloc_av_`
(`0x810` bytes), `__malloc_sbrk_base`, `brk.0` (htif.c's `_sbrk`),
`__malloc_max_total_mem`, `__malloc_max_sbrked_mem`, `__malloc_top_pad` (read), `errno`
(`_sbrk_r`), `__malloc_current_mallinfo` (`0x50` bytes); and (lane F1-A0-M, the ported proof's
footprint `VsaIris.VsaHeap.allocGlobal`) `_REENT->_errno` (`_sbrk_r`'s failure
path) and `__malloc_trim_threshold` (read by `_free_r`, never written). -/
def MallocGlobal (a : Nat) : Prop :=
  (symMallocAv ≤ a ∧ a < symMallocAv + 0x810) ∨ (0x8005d1b8 ≤ a ∧ a < 0x8005d1bc) ∨
  (symMallocSbrkBase ≤ a ∧ a < symMallocSbrkBase + 16) ∨ (symBrk ≤ a ∧ a < symBrk + 8) ∨
  (0x8005d3c8 ≤ a ∧ a < 0x8005d3e0) ∨ (errnoAddr ≤ a ∧ a < errnoAddr + 4) ∨
  (symMallocMallinfo ≤ a ∧ a < symMallocMallinfo + 0x50)

/-- **What `_malloc_r(_REENT, n)` leaves**: the block `p` of a chunk in use,
fresh, in the arena below the new break; the heap's shape; the chunks in use
kept, and every byte off its writes. -/
structure MallocPost (m m' : Mem) (sp n p : Nat) (brk : Nat) (chunks : List Chunk)
    (top' brk' : Nat) (chunks' : List Chunk) (bins' : Nat → List Nat) : Prop where
  heap : HeapAt (Vsa.Densify.fillZeroMem m') top' brk' chunks' bins'
  brk_le : brk ≤ brk'
  /-- (lane F1-14) the break grows by at most the request, the 16 KiB of
  room the call has for `top_pad` (0: `HeapAt.top_pad`) and `MINSIZE`, and a
  page of rounding (`malloc_extend_top`: one page-rounded `_sbrk` and one
  alignment correction) -/
  brk_hi : brk' ≤ brk + n + 16384 + 4096
  lo : heapStart + 16 ≤ p
  hi : p + n ≤ brk'
  al : p % 16 = 0
  /-- the block's chunk, in use, holding at least `n + 8` bytes -/
  block : ∃ sz, (⟨p - 16, sz, true⟩ : Chunk) ∈ chunks' ∧ n + 8 ≤ sz
  /-- the block was no chunk's in use -/
  fresh : ∀ a, p ≤ a → a < p + n → ¬ InUse chunks a
  /-- the chunks in use stay in use -/
  kept : ∀ c ∈ chunks, c.inuse = true → c ∈ chunks'
  keep : ∀ a, ¬ MallocGlobal a → (a < heapStart ∨ heapEnd ≤ a ∨ InUse chunks a) →
    (a + 1024 ≤ sp ∨ sp ≤ a) → m'[a]? = m[a]?

/-- **`_malloc_r(_REENT, n)`** (named premise: the dlmalloc proof is
ship-your-interpreter's, at its WHILE addresses, PHASES A0): the block's
address returned. -/
def MallocR_Statement : Prop :=
  ∀ (sp n top brk : Nat) (chunks : List Chunk) (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String),
    HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins → r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 → heapEnd + 1024 ≤ sp →
    1 ≤ n → brk + n + 16384 ≤ heapEnd →
    Triple (SegSt 0x8002fa34#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 n⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' p top' brk' chunks' bins', wrRet r sp p f m' o c ∧
        MallocPost m m' sp n p brk chunks top' brk' chunks' bins')

/-- `_free_r`'s entry. -/
abbrev symFreeR : Nat := 0x8003be24

/-- **`_free_r(_REENT, p)`** (lane F1-14; named premise, PHASES A0: the
dlmalloc proof is ship-your-interpreter's, at its WHILE addresses, as
`MallocR_Statement`'s): on a heap of the shape `HeapAt` (of the zero fill),
`p` the payload of a chunk in use in the arena, it returns (no result) with
the caller's frame, writing nothing but its globals (`MallocGlobal`: the bins,
`_malloc_trim_r`'s `_sbrk`), the arena and its stack below `sp` (1 KiB).
`exit`'s `_fclose_r(stdout)` frees `stdout`'s buffer through it. -/
def FreeR_Statement : Prop :=
  ∀ (sp p top brk : Nat) (chunks : List Chunk) (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String),
    HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins → r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 →
    heapEnd + 1024 ≤ sp → (∃ sz, (⟨p - 16, sz, true⟩ : Chunk) ∈ chunks) → heapStart + 16 ≤ p →
    Triple (SegSt (BitVec.ofNat 64 symFreeR) (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 p⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
          ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins) (ArmPay m' o) c ∧
        ∀ a, ¬ MallocGlobal a → (a < heapStart ∨ heapEnd ≤ a) → (a + 1024 ≤ sp ∨ sp ≤ a) → m'[a]? = m[a]?)

end Lua.Vm.Sim.Kit
