import Lua.Vm.Sim.Kit.Moddi3
import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Arms.Segs.Hdivdi3
import Lua.Vm.Arms.Segs.Humoddi3

/-!
# `__divdi3` at the Lua ELF's address: the call-node summary (M5)

`divdi3_sum`: from `0x8002f72c` with `a0 = m`, `a1 = n ≠ 0`, `ra = r`, the
helper returns to `r` with `a0 = BitVec.sdiv m n`, the C quotient: the signs
are taken off (`neg`, in the fix-ups objdump labels `__umoddi3+0x10`/`+0x20`),
`__udivdi3` (`udivdi3_sum`) divides the magnitudes (a tail call when the
signs agree, a nested call returning through `t0` when they differ, then
`neg`), which is `sdiv`'s own case split (`BitVec.sdiv_eq`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

/-- `bgtz`: positive, read off the sign bit and zero. -/
theorem sgt_zero (x : BitVec 64) (h : x ≠ 0#64) : zopz0zI_s 0#64 x = !x.msb := by
  rw [BitVec.msb_eq_toInt]; unfold zopz0zI_s
  have : x.toInt ≠ 0 := fun e => h (by
    apply BitVec.eq_of_toInt_eq; simpa using e)
  by_cases hx : x.toInt < 0 <;> simp [hx] <;> omega

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [Vsa.Sim.sext_zero, BitVec.add_zero,
      BitVec.zero_sub, slt_zero, sge_zero, sgt_zero _ hn, sgt_zero _ hn'])

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`__divdi3`, the call-node summary.** -/
theorem divdi3_sum (m n r : BitVec 64) (f : HFrame) (mem : Mem) (o : Array String)
    (hn : n ≠ 0#64) (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f72c#64 (⟨Register.x10, m⟩ :: ⟨Register.x11, n⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay mem o))
      (SegSt r (⟨Register.x10, m.sdiv n⟩ :: f.pins) (ArmPay mem o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨t, h⟩ := h.pin5
  have hn' : -n ≠ 0#64 := fun e => hn (by simpa using e)
  rw [BitVec.sdiv_eq]
  cases hsn : n.msb <;> cases hsm : m.msb
  all_goals
    kit_run h acc until [0x8002f734]
    try simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_sub] at h
    obtain ⟨_, acc, h⟩ := h.call acc (by pins_of h)
      (udivdi3_sum _ _ _ _ hframe? _ _ (by first | exact hn | exact hn') (by first | decide | exact hr))
    try kit_run h acc
    try simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_sub] at h
    first
    | exact ⟨_, acc, h.repin (by pins_of h)⟩
    | exact ⟨_, acc, (h.at (ret_tgt0 r hr)).repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit
