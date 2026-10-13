import Lua.Vm.Sim.Kit.AtFltForloop
import Lua.Vm.Sim.Kit.AtFltSub
import Lua.Vm.Sim.Kit.AtFltForprep
import Lua.Vm.Sim.Kit.AtFltLt

/-!
# Round 5 bake-off, A-JOIN: heartbeats per arm declaration

Each held-out arm's proof (and the FORLOOP refactor) re-elaborated with the
heartbeat counter logged at its start and end (`hb`, thousands of
`maxHeartbeats` units). Measurement only: not imported by `Lua`.

    systemd-run --user --scope -p MemoryMax=12G -q lake env lean abstractions/bakeoff5/ajoin/Measure.lean
-/

set_option Elab.async false

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At.Measure5

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Vm.Sim.At Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

elab "hb " s:str : tactic => do
  let n ← IO.getNumHeartbeats
  Lean.logInfo m!"HB {s.getString} {n / 1000}"


theorem m_sim_FORLOOP_flt (hsf : SoftFloatSpec) : SimArmOn .FORLOOP FltStep :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  hb "sim_FORLOOP_flt start"
  kit_setup 0x8001c1ec
  rcases hj : jumpTo (s.pc + 1) (-(ins.bx : Int)) with _ | t <;> simp [hj] at hk htop
  simp [forloopK, Kernel.regTop] at hk htop
  kit_bound hA2 (ins.a + 2)
  flt_views; flt_reg_q st (ins.a + 2), hT; flt_reg2 i ins.a, l (ins.a + 1)
  have hbx : ins.bx ≤ s.pc + 1 := by simp [jumpTo] at hj; omega
  obtain rfl : t = s.pc + 1 - ins.bx := by simp [jumpTo] at hj; omega
  simp only [model_add_comm i st] at hk
  at_walk Lua.Vm.At.FORLOOP
  all_goals at_leaf Lua.Vm.At.FORLOOP
  hb "sim_FORLOOP_flt end"

theorem m_sim_SUB_flt (hsf : SoftFloatSpec) : SimArmOn .SUB FltBC :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  hb "sim_SUB_flt start"
  kit_setup 0x8001d964
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  refine hT.elim (fun hq => ?fb) (fun hq => ?fc)
  case' fb => flt_reg_q x ins.b, hq; num_reg ins.c, hn
  case' fc => flt_reg_q x ins.c, hq; num_reg ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_walk Lua.Vm.At.SUB
    all_goals at_leaf Lua.Vm.At.SUB
  hb "sim_SUB_flt end"

theorem m_fp_flt3 (hsf : SoftFloatSpec) : ArmBody .FORPREP FpFlt3 := by
  hb "fp_flt3 start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hq0, hq1, hq2⟩
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  kit_bound hA0 ins.a; kit_bound hA3 (ins.a + 3)
  flt_views; flt_reg_s ins.a, hq0; flt_reg_s (ins.a + 1), hq1; flt_reg_s (ins.a + 2), hq2
  simp [Value.tonumber?] at hk
  at_walk Lua.Vm.At.FORPREP_F
  all_goals at_leaf Lua.Vm.At.FORPREP_F
  hb "fp_flt3 end"

theorem m_sim_LT_flt (hsf : SoftFloatSpec) (hf2i : LtF2I_Statement) : SimArmOn .LT FltAB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  hb "sim_LT_flt start"
  kit_setup 0x8001c894
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  refine hT.elim (fun hq => ?fa) (fun hq => ?fb)
  case' fa => flt_reg_s ins.a, hq; num_regf ins.b, hn
  case' fb => num_regf ins.a, hn; all_goals flt_reg_s ins.b, hq
  all_goals simp only [Opnd.fill] at hk
  all_goals try (rcases v with _ | _ | _ | _ | _ | _ <;> simp [δ, Value.toNum?] at hk hn <;> done)
  all_goals simp [δ, Value.toNum?, ltNum, ltIntFloat, ltFloatInt] at hk
  all_goals try simp only [hfit, ite_true] at hk
  all_goals first
    | exact hf2i hS hA hf hop hstep (by first
        | exact .inl ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩
        | exact .inr ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩)
    | skip
  all_goals at_walk Lua.Vm.At.LT_F
  all_goals at_leaf Lua.Vm.At.LT_F
  hb "sim_LT_flt end"

end Lua.Vm.Sim.At.Measure5
