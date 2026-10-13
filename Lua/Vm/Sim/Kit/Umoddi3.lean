import Lua.Vm.Sim.Kit.Udivdi3
import Lua.Vm.Arms.Segs.Humoddi3

/-!
# `__udivdi3` on every divisor, and `__umoddi3`: call-node summaries (lane float-sf4)

`__divdf3`'s `udiv_qrnnd` (longlong.h's `__udiv_qrnnd_c`) divides by the
normalised divisor's high half with `__udivdi3` and `__umoddi3`. Its call
nodes run the summaries below, which hold for every divisor, so a node needs
no path fact about the divisor (`d ≠ 0` there is a fact of the operands'
unpacking, proved at level (b), not a guard of the path):

* `udivdi3_sumT`: from `0x8002f734`, `a0 = udivT n d` (libgcc's `udivmoddi4`
  loop: `li a0, -1` then `beqz a2` for a zero divisor) and `a1 = n % d`
  (`n` for a zero divisor, `BitVec.umod_zero`); `t0` kept;
* `umoddi3_sum`: from `0x8002f77c` (`mv t0, ra; jal __udivdi3; mv a0, a1;
  jr t0`), `a0 = n % d`; the callee clobbers `ra` (its own `jal`) and `t0`
  (the saved return address), both caller-saved.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

/-- `__udivdi3`'s quotient register on every divisor (`-1` for `0`). -/
def udivT (n d : BitVec 64) : BitVec 64 := if d = 0#64 then BitVec.allOnes 64 else n / d

theorem udivT_ne {n d : BitVec 64} (h : d ≠ 0#64) : udivT n d = n / d := by
  unfold udivT; rw [if_neg h]

local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [Vsa.Sim.sext_zero, Vsa.Sim.sext_one,
      BitVec.add_zero, BitVec.zero_add])

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`__udivdi3` on every divisor, the call-node summary.** -/
theorem udivdi3_sumT (n d r t : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f734#64 (⟨Register.x10, n⟩ :: ⟨Register.x11, d⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x5, t⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, udivT n d⟩ :: ⟨Register.x11, n % d⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x5, t⟩ :: f.pins) (ArmPay m o)) := by
  by_cases hd : d = 0#64
  · subst hd
    intro c h
    have acc := Steps.refl c
    kit_run h acc
    have e1 : udivT n 0#64 = (0#64) + sign_extend (m := 64) (0xfff#12) := by
      unfold udivT; rw [if_pos rfl]; decide
    have e2 : n % 0#64 = n + sign_extend (m := 64) (0x000#12) := by
      rw [BitVec.umod_zero, Vsa.Sim.sext_zero, BitVec.add_zero]
    rw [e1, e2]
    exact ⟨_, acc, (h.at (Vsa.Sim.ret_tgt r hr)).repin (by pins_of h)⟩
  · intro c h
    obtain ⟨c', hs, h'⟩ := udivdi3_sum n d r t f m o hd hr c h
    exact ⟨c', hs, by rw [udivT_ne hd]; exact h'⟩

/-- **`__umoddi3`, the call-node summary**: `a0 = n % d`; `ra` and `t0`
clobbered (`t0` holds the return address). -/
theorem umoddi3_sum (n d r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f77c#64 (⟨Register.x10, n⟩ :: ⟨Register.x11, d⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m o))
      (SegSt r (⟨Register.x10, n % d⟩ :: ⟨Register.x5, r⟩ :: f.pins)
        (ArmPay m o)) := by
  intro c h
  have acc := Steps.refl c
  kit_run h acc until [0x8002f734]
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (udivdi3_sumT n d 0x8002f784#64 _ hframe? m o (by decide))
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  kit_run h acc
  have h := h.at (Vsa.Sim.ret_tgt r hr)
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit
