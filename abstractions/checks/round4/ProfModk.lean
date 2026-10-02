import Lua.Vm.Sim.Kit.Modk

/-!
# Round 4, C-budget: heartbeats per segment on `OP_MODK`'s general path

`modk_call` and `modk_rz` (`Lua/Vm/Sim/Kit/Modk.lean`) with the kit macros
`kit_div_pre`/`kit_div_post` expanded, and the run cut at every segment
boundary of the path (`abstractions/checks/round4/lcall_frames.py`), with
`hb` logging the heartbeat counter (in `maxHeartbeats` units) between the
steps. Measurement only: not imported by `Lua`.

Measured (2026-10-02, base 3ae6bf6; thousands of heartbeats, cumulative):
`modk_call'` setup 4, seg1 36, seg2 74, seg3 81, seg4 123, seg5 133,
normalise 144, call node 151; `modk_rz_post` setup 5, two segments 14, to
the head 28, close 52. The same path as ONE declaration (`kit_div_pre` and
`kit_div_post` concatenated, one setup) measured setup 5, to the call 135,
call node 153, to the head 177, then the close hit the 200k budget
(`(deterministic) timeout at whnf`): pre + post − one setup = 198k, so the
cost is additive in segments and the split's only heartbeat cost is a
second setup (≈ 5k). The one-declaration variant is not kept (it fails).

    lake env lean abstractions/checks/round4/ProfModk.lean
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit.Prof

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

elab "hb " s:str : tactic => do
  let n ← IO.getNumHeartbeats
  Lean.logInfo m!"HB {s.getString} {n / 1000}"

set_option hygiene false in
theorem modk_call' : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvR, dvK] at hy
  kitk_ints 0x8001dad0
  hb "setup"
  have hz := fun e => hy (Or.inl e)
  kit_run h0 acc until [0x8001e46c]
  hb "seg1 dad0-db14 (17 ins)"
  kit_run h0 acc until [0x8001e474]
  hb "seg2 e46c-e474 (2)"
  kit_run h0 acc until [0x8001f7a0]
  hb "seg3 e474-e478 (1)"
  kit_run h0 acc until [0x8001f7b0]
  hb "seg4 f7a0-f7b0 (4)"
  kit_run h0 acc until [0x8002f7b0]
  hb "seg5 f7b0-f7bc (3)"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "call node"
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩

set_option hygiene false in
/-- The post half of `modk_rz` (`kit_div_post` expanded), cut per segment. -/
theorem modk_rz_post : ArmPost .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.srem y = 0#64)
    0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "post start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩ c1 ⟨h1⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvR, dvK] at hy hq
  kitk_ints 0x8001dad0
  have hz := fun e => hy (Or.inl e)
  have heq := fun m => imodC_eq m _ hz
  simp only [Opnd.fill, δ, BinOp.int, heq] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  clear h0 acc
  have acc := Steps.refl c1
  have h0 := h1
  hb "post setup"
  kit_run h0 acc until [0x8001f7cc]
  hb "post seg f7bc-f7c4-f7cc (2 segs, 4 ins)"
  kit_run h0 acc
  hb "post seg f7cc-f7e0 (5 ins) to head"
  kit_div_close [hq]
  hb "post close"

end Lua.Vm.Sim.Kit.Prof
