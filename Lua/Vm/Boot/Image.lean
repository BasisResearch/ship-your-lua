import Lua.Vm.Boot.Log
import Lua.Vm.Boot.View
import Lua.Vm.Boot.ImageData
import Lua.Vm.Image

/-!
# The loader's memory and the entry memory of a chunk build of the Lua ELF

Ported from ship-your-interpreter's `Vsa/Sim/Boot/Image.lean`. The loader
(`initializeMemory .B64`) inserts the PT_LOAD segment's `p_filesz` bytes
`[segBase, segBase + segSize)`: `.text` and `.rodata` (`Lua/Vm/Image.lean`),
the data bytes up to `.bss` (`ImageData.lean`), `.bss` as zeros (it lies inside
`p_filesz`, before `.lua_chunk`), and the chunk region, which is the only part
that differs between programs (link.ld; `scripts/gen_lua_boot_witness.py`
checks the committed ELF is reproduced from `c/tests/while.luac`).

* `loadedMem chunk`: those insertions. ELF metadata the loader also inserts
  below RAM is not modelled; no read of the run reaches it, and a boot witness
  only needs a *partial* view of the real memory.
* `bootMem chunk L`: the store log `L` over `loadedMem chunk`;
  `bootMem_get`: its bytes under `LogOk L t` are `bootView chunk t`.
-/

namespace Lua.Vm.Boot

open Lua.Vm

/-- `n` insertions of `byte` from `base`, in address order. -/
def insertRange (m : Mem) (base : Nat) (byte : Nat → BitVec 8) : Nat → Mem
  | 0 => m
  | n + 1 => (insertRange m base byte n).insert (base + n) (byte (base + n))

theorem insertRange_get (m : Mem) (base : Nat) (byte : Nat → BitVec 8) (n x : Nat) :
    (insertRange m base byte n)[x]? =
      if base ≤ x ∧ x < base + n then some (byte x) else m[x]? := by
  induction n with
  | zero => simp [insertRange]; omega
  | succ n ih =>
    rw [insertRange, Std.ExtHashMap.getElem?_insert, ih]
    by_cases h : base + n = x
    · subst h; simp
    · simp only [beq_iff_eq, h, ↓reduceIte]
      split <;> split <;> first | rfl | omega

/-- The loaded segment's byte at `x` for the chunk region `chunk` (packed
little-endian: `_chunk_size`, the chunk, a NUL; zeros beyond). -/
def imageByte (chunk : Nat) (x : Nat) : BitVec 8 :=
  if x < Image.rodataBase then Image.textByte (x - Image.textBase)
  else if x < dataBase then Image.rodataByte (x - Image.rodataBase)
  else if x < bssStart then dataByte (x - dataBase)
  else if x < chunkRegion then 0
  else BitVec.ofNat 8 (chunk >>> (8 * (x - chunkRegion)))

/-- The loader's byte view: present exactly on the segment. -/
def imageView (chunk : Nat) (x : Nat) : Option (BitVec 8) :=
  if segBase ≤ x ∧ x < segBase + segSize then some (imageByte chunk x) else none

/-- The loader's memory for a chunk build. -/
def loadedMem (chunk : Nat) : Mem := insertRange ∅ segBase (imageByte chunk) segSize

theorem loadedMem_get (chunk x : Nat) : (loadedMem chunk)[x]? = imageView chunk x := by
  rw [loadedMem, insertRange_get]
  simp [imageView]

/-- The memory at `luaV_execute`'s entry: the boot store log over the loader's memory. -/
def bootMem (chunk : Nat) (L : PackedLog) : Mem := Vsa.Sim.writeLog (loadedMem chunk) L.log

/-- The entry memory's byte view: the final byte map over the loader's view. -/
def bootView (chunk : Nat) (t : RunTree) : View := logView t (imageView chunk)

theorem bootMem_get {chunk : Nat} {L : PackedLog} {t : RunTree} (h : LogOk L t) :
    ViewOf (bootMem chunk L) (bootView chunk t) := by
  intro x
  rw [bootMem, writeLog_view h, bootView,
    show (fun a => (loadedMem chunk)[a]?) = imageView chunk from funext (loadedMem_get chunk)]

end Lua.Vm.Boot
