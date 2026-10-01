import Lua.Vm.Sim.Kit.Udivdi3
import Lua.Vm.Arms.Segs.Hmoddi3

/-!
# `__moddi3` at the Lua ELF's address: the call-node summary (M5)

`moddi3_sum`: from `0x8002f7b0` with `a0 = m`, `a1 = n ≠ 0`, `ra = r`, the
helper returns to `r` (through `t0`) with `a0 = BitVec.srem m n`, the C
remainder: the signs are taken off (`neg`), `__udivdi3` (`udivdi3_sum`, a
nested call node returning into `__moddi3`) divides the magnitudes, and the
remainder takes the dividend's sign, which is `srem`'s own case split
(`BitVec.srem_eq`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

/-- `bltz`/`bgez` read the sign bit. -/
theorem slt_zero (x : BitVec 64) : zopz0zI_s x 0#64 = x.msb := by
  simp [zopz0zI_s, BitVec.msb_eq_toInt]

theorem sge_zero (x : BitVec 64) : zopz0zKzJ_s x 0#64 = !x.msb := by
  rw [BitVec.msb_eq_toInt]; unfold zopz0zKzJ_s
  by_cases h : x.toInt < 0 <;> simp [h] <;> omega

/-- `jr t0`'s target once `t0 = ra + 0` is normalised. -/
theorem ret_tgt0 (r : BitVec 64) (h : r.toNat % 4 = 0) : Sail.BitVec.update r 0 0#1 = r := by
  simpa [Vsa.Sim.sext_zero] using Vsa.Sim.ret_tgt r h

local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [Vsa.Sim.sext_zero, BitVec.add_zero,
      BitVec.zero_sub, slt_zero, sge_zero])

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`__moddi3`, the call-node summary.** -/
theorem moddi3_sum (m n r : BitVec 64) (f : HFrame) (mem : Mem) (o : Array String)
    (hn : n ≠ 0#64) (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f7b0#64 (⟨Register.x10, m⟩ :: ⟨Register.x11, n⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay mem o))
      (SegSt r (⟨Register.x10, m.srem n⟩ :: f.pins) (ArmPay mem o)) := by
  intro c h
  have acc := Steps.refl c
  have hn' : -n ≠ 0#64 := fun e => hn (by simpa using e)
  rw [BitVec.srem_eq]
  cases hsn : n.msb <;> cases hsm : m.msb
  all_goals
    kit_run h acc until [0x8002f734]
    simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_sub] at h
    obtain ⟨_, acc, h⟩ := h.call acc (by pins_of h)
      (udivdi3_sum _ _ _ _ hframe? _ _ (by first | exact hn | exact hn') (by decide))
    kit_run h acc
    simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_sub] at h
    exact ⟨_, acc, (h.at (ret_tgt0 r hr)).repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit
