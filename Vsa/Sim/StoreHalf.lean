import Vsa.Sim.BlockMem

/-!
# The width-2 store `sh` for the generated site batteries

newlib's `FILE` keeps `_flags` and `_file` as `short`s, so the stdio chain
stores halfwords (`sh a5, 16(a4)`: `__swrite` clearing `__SOFF`). The copied
`exec_sh_bm` (`Vsa/Sim/BlockMem.lean`) characterises the store as two byte
inserts; `writeMap2` names that image, as `writeMap4`/`writeMap8` name theirs,
so that `scripts/syi/gen_sites.py` emits an `sh` site exactly like an `sw` site.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

namespace Vsa.Sim

/-- The width-2 write-map: `mem` updated with 2 little-endian bytes at `a`. -/
def writeMap2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 2)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)

/-- **`sh rs2, off(rs1)`** stores the low halfword of `rs2` (`exec_sh_bm`,
named by `writeMap2`). -/
theorem exec_sh (σ : MState) (pc : BitVec 64) (imm : BitVec 12) (rs2 rs1 : regidx)
    (vbase vdata : BitVec 64) (hG : GoodState σ)
    (hrs1 : (rX_bits rs1).run (afterNextPC (afterPrelude σ) pc)
      = .ok vbase (afterNextPC (afterPrelude σ) pc))
    (hrs2 : (rX_bits rs2).run (afterNextPC (afterPrelude σ) pc)
      = .ok vdata (afterNextPC (afterPrelude σ) pc))
    (hlo : 0x80000000 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (hhiram : (vbase + sign_extend (m := 64) imm).toNat + 2 ≤ 0x100000000)
    (hhiwin : tohostAddr + 16 ≤ (vbase + sign_extend (m := 64) imm).toNat)
    (halign : (vbase + sign_extend (m := 64) imm).toNat % 2 = 0) :
    (execute (instruction.STORE (imm, rs2, rs1, 2))).run (afterNextPC (afterPrelude σ) pc)
      = .ok RETIRE_SUCCESS
          (sigma3_store σ pc
            (writeMap2 (afterNextPC (afterPrelude σ) pc).mem
              (vbase + sign_extend (m := 64) imm).toNat (shData vdata))) :=
  exec_sh_bm σ pc imm rs2 rs1 vbase vdata hG hrs1 hrs2 hlo hhiram hhiwin halign

/-- A read outside the halfword. -/
theorem getElem?_writeMap2_out (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 2))
    (x : Nat) (h : x < a ∨ a + 2 ≤ x) : (writeMap2 mem a d)[x]? = mem[x]? := by
  unfold writeMap2
  rw [Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem?_insert]
  simp only [beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega)]

end Vsa.Sim
