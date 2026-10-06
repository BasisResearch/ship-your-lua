import Lua.Vm.Sim.Kit.RetPoscall
import Lua.Vm.Sim.Kit.At
import Lua.Vm.Arms.Segs.G03
import Lua.Vm.Arms.Segs.G04
import Lua.Vm.Arms.Segs.G05
import Lua.Vm.Arms.Segs.G06
import Lua.Vm.Arms.Segs.G13
import Lua.Vm.Arms.Segs.G58
import Lua.Vm.Arms.Segs.G59
import Lua.Vm.Arms.Segs.G70
import Lua.Vm.Arms.Segs.G84

/-!
# The end of `OP_RETURN*`: `luaD_poscall`, `CIST_FRESH`, the epilogue (lane F1-4)

From the `luaD_poscall` call site `0x8001c784` (`OP_RETURN`'s; `OP_RETURN0`
and `OP_RETURN1` join at `0x8001c274`): the call node `poscall_sum`, the
trap reload (`ci->u.l.trap = 0`), the `CIST_FRESH` test (`bnez` taken), and
`luaV_execute`'s epilogue, which reloads `ra`, `s0 … s11` from the saved
words (`SavedAt`) and returns into `ccall` (`RuntimeData.retCcall`) with the
entry `sp`. The memory stays in agreement with the head memory off the
return path's words (`RAgree`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- `a2`'s value, present by `RegsOk`. -/
theorem _root_.Vsa.Sim.SegSt.pin12 {pc : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    {c : Vsa.Machine.Config} (h : SegSt pc L (ArmPay m o) c) :
    ∃ t, SegSt pc (⟨Register.x12, t⟩ :: L) (ArmPay m o) c := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h.armOk.gpr 12 (by decide) (by decide))
  exact ⟨t, h.repin ⟨ht, h.pins⟩⟩

/-- The callers' value of a saved register (`RuntimeData.calleeSavedEntry`). -/
def entryVal (r : Nat) : Nat :=
  ((RuntimeData.calleeSavedEntry.find? (·.1 == r)).map (·.2)).getD 0

theorem entryVal_mem : ∀ r ∈ [9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27],
    (r, entryVal r) ∈ RuntimeData.calleeSavedEntry := by decide

/-- **The facts the return path reads from the head memory `m0`.** -/
structure RetCx (p : Proto) (w : RelPtrs) (m0 : Mem) : Prop where
  ranges : Ranges p w
  reads : HeadReads m0 w
  saved : SavedAt m0 w
  /-- `L->tbclist < base`: nothing to close (`luaF_close`) -/
  tbc_lt : w.rt.stack < w.base

theorem _root_.Lua.Vm.Sim.Core.retCx {c : Config} {s : State} {p : Proto} {w : RelPtrs} (hc : Core p c s w) :
    RetCx p w c.σ.mem := by
  refine ⟨hc.ranges, hc.headReads, hc.saved, ?_⟩
  have := hc.comp.runtime.lua.stack_le
  have := hc.comp.runtime.func
  simp only [RelPtrs.base, stackValueSize]
  omega

/-- **The registers at the return into `ccall`**: the entry `sp`, `ra`, `gp`,
`s0 = L` and the callers' `s1 … s11`. -/
abbrev retRow (L : Nat) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 RuntimeData.spEntry⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 L⟩, ⟨Register.x9, BitVec.ofNat 64 (entryVal 9)⟩,
   ⟨Register.x18, BitVec.ofNat 64 (entryVal 18)⟩, ⟨Register.x19, BitVec.ofNat 64 (entryVal 19)⟩,
   ⟨Register.x20, BitVec.ofNat 64 (entryVal 20)⟩, ⟨Register.x21, BitVec.ofNat 64 (entryVal 21)⟩,
   ⟨Register.x22, BitVec.ofNat 64 (entryVal 22)⟩, ⟨Register.x23, BitVec.ofNat 64 (entryVal 23)⟩,
   ⟨Register.x24, BitVec.ofNat 64 (entryVal 24)⟩, ⟨Register.x25, BitVec.ofNat 64 (entryVal 25)⟩,
   ⟨Register.x26, BitVec.ofNat 64 (entryVal 26)⟩, ⟨Register.x27, BitVec.ofNat 64 (entryVal 27)⟩]

/-- **Back in `ccall`**: some memory in agreement with the head's, at `retCcall`. -/
def AtCcall (w : RelPtrs) (m0 : Mem) (o : Array String) (c : Config) : Prop :=
  ∃ M, RAgree w m0 M ∧ SegSt (BitVec.ofNat 64 RuntimeData.retCcall) (retRow w.L) (ArmPay M o) c

/-- The registers at the `luaD_poscall` call site (`0x8001c784`). -/
abbrev pcRow (w : RelPtrs) (q9 q18 q19 q20 q21 q24 q25 q27 : BitVec 64) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 w.L⟩, ⟨Register.x23, BitVec.ofNat 64 w.ci⟩,
   ⟨Register.x9, q9⟩, ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩,
   ⟨Register.x21, q21⟩, ⟨Register.x24, q24⟩, ⟨Register.x25, q25⟩, ⟨Register.x27, q27⟩]

/-- **The memory facts of the tail**, through the agreement. -/
structure TailMem (w : RelPtrs) (M : Mem) : Prop where
  hook : bytesT4 M (w.L + 192) = 0#32
  nres : bytesT2 M (w.ci + 60) = 0#16
  trap : bytesT4 M (w.ci + 40) = 0#32
  cs : bytesT2 M (w.ci + 62) = 4#16
  ra : bytesT8 M (w.sp + 168) = BitVec.ofNat 64 RuntimeData.retCcall
  s0 : bytesT8 M (w.sp + 160) = BitVec.ofNat 64 w.L
  s1 : bytesT8 M (w.sp + 152) = BitVec.ofNat 64 (entryVal 9)
  s2 : bytesT8 M (w.sp + 144) = BitVec.ofNat 64 (entryVal 18)
  s3 : bytesT8 M (w.sp + 136) = BitVec.ofNat 64 (entryVal 19)
  s4 : bytesT8 M (w.sp + 128) = BitVec.ofNat 64 (entryVal 20)
  s5 : bytesT8 M (w.sp + 120) = BitVec.ofNat 64 (entryVal 21)
  s6 : bytesT8 M (w.sp + 112) = BitVec.ofNat 64 (entryVal 22)
  s7 : bytesT8 M (w.sp + 104) = BitVec.ofNat 64 (entryVal 23)
  s8 : bytesT8 M (w.sp + 96) = BitVec.ofNat 64 (entryVal 24)
  s9 : bytesT8 M (w.sp + 88) = BitVec.ofNat 64 (entryVal 25)
  s10 : bytesT8 M (w.sp + 80) = BitVec.ofNat 64 (entryVal 26)
  s11 : bytesT8 M (w.sp + 72) = BitVec.ofNat 64 (entryVal 27)

/-- A saved register's word, through the agreement. -/
theorem saved_M {p : Proto} {w : RelPtrs} {m0 M : Mem} (hr : Ranges p w) (hS : SavedAt m0 w)
    (hM : RAgree w m0 M) {r v : Nat} (h : (r, v) ∈ RuntimeData.calleeSavedEntry) :
    bytesT8 M (w.sp + savedOff r) = BitVec.ofNat 64 v := by
  have h2 := savedOff_mem _ h
  simp only at h2
  rw [hM.bytesT8 (hr.nd_sp (by simp only [execFrame]; omega))]
  exact hS.s (r, v) h

theorem tailMem {p : Proto} {w : RelPtrs} {m0 M : Mem} (hX : RetCx p w m0) (hM : RAgree w m0 M) :
    TailMem w M := by
  have hr := hX.ranges
  have hR := hX.reads
  have hS := hX.saved
  exact ⟨by rw [hM.bytesT4 (hr.nd_L (by decide) (by decide))]; exact hR.hookmask,
    by rw [hM.bytesT2 (hr.nd_ci (by decide) (by decide))]; exact hR.nresults,
    by rw [hM.bytesT4 (hr.nd_ci (by decide) (by decide))]; exact hR.trap,
    by rw [hM.bytesT2 (hr.nd_ci (by decide) (by decide))]; exact hR.callstatus,
    by rw [hM.bytesT8 (hr.nd_sp (by decide))]; exact hS.ra,
    by rw [hM.bytesT8 (hr.nd_sp (by decide))]; exact hS.s0,
    saved_M hr hS hM (r := 9) (by decide), saved_M hr hS hM (r := 18) (by decide),
    saved_M hr hS hM (r := 19) (by decide), saved_M hr hS hM (r := 20) (by decide),
    saved_M hr hS hM (r := 21) (by decide), saved_M hr hS hM (r := 22) (by decide),
    saved_M hr hS hM (r := 23) (by decide), saved_M hr hS hM (r := 24) (by decide),
    saved_M hr hS hM (r := 25) (by decide), saved_M hr hS hM (r := 26) (by decide),
    saved_M hr hS hM (r := 27) (by decide)⟩

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    pcMem, stateTopOff, stateCiOff, ciFuncOff, ciPreviousOff, bytesT2_wm8_out', bytesT4_wm8_out'',
    bytesT8_wm8_out', sext64_id, hT.trap, hT.cs, hT.ra,
    hT.s0, hT.s1, hT.s2, hT.s3, hT.s4, hT.s5, hT.s6, hT.s7, hT.s8, hT.s9, hT.s10,
    hT.s11] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          pcMem, stateTopOff, stateCiOff, ciFuncOff, ciPreviousOff, bytesT2_wm8_out', hT.cs]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          pcMem, stateTopOff, stateCiOff, ciFuncOff, ciPreviousOff, bytesT8_wm8_out', hT.ra, sext64_id, Vsa.Sim.sext_zero, BitVec.add_zero]
         rw [rtgt _ (by decide)]; decide))

/-- The registers at the `CIST_FRESH` test (`0x8001c274`, where `OP_RETURN0`
and `OP_RETURN1` join). -/
abbrev freshRow (w : RelPtrs) (q9 q18 q19 q20 q21 q24 q25 q27 : BitVec 64) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 w.L⟩, ⟨Register.x23, BitVec.ofNat 64 w.ci⟩,
   ⟨Register.x9, q9⟩, ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩,
   ⟨Register.x21, q21⟩, ⟨Register.x24, q24⟩, ⟨Register.x25, q25⟩, ⟨Register.x27, q27⟩]

/-- **`CIST_FRESH` and the epilogue**: from `0x8001c274` to the return into
`ccall`, the saved registers reloaded. -/
theorem ret_fresh {p : Proto} {w : RelPtrs} {m0 M : Mem} (hX : RetCx p w m0) (hM : RAgree w m0 M)
    (q9 q18 q19 q20 q21 q24 q25 q27 : BitVec 64) (o : Array String) :
    Triple (SegSt 0x8001c274#64 (freshRow w q9 q18 q19 q20 q21 q24 q25 q27) (ArmPay M o))
      (AtCcall w m0 o) := by
  intro c h
  have acc := Steps.refl c
  have hr := hX.ranges
  have hT := tailMem hX hM
  ret_facts hr
  simp only [freshRow] at h
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  have hsp := hr.sp_eq
  simp only [execFrame] at hsp
  rw [hsp] at h
  exact ⟨_, acc, _, hM, h.repin (by pins_of h)⟩

/-- **The tail of `OP_RETURN`**: from the `luaD_poscall` call site to the
return into `ccall`. -/
theorem ret_tail {p : Proto} {w : RelPtrs} {m0 M : Mem} (hX : RetCx p w m0) (hM : RAgree w m0 M)
    (q9 q18 q19 q20 q21 q24 q25 q27 : BitVec 64) (o : Array String) :
    Triple (SegSt 0x8001c784#64 (pcRow w q9 q18 q19 q20 q21 q24 q25 q27) (ArmPay M o))
      (AtCcall w m0 o) := by
  intro c h
  have acc := Steps.refl c
  have hr := hX.ranges
  have hT := tailMem hX hM
  ret_facts hr
  simp only [pcRow] at h
  kit_run h acc until [0x8000a39c]
  obtain ⟨t12, h⟩ := h.pin12
  obtain ⟨t22, h⟩ := h.pin22
  obtain ⟨t26, h⟩ := h.pin26
  have hpc : PcCx w.L w.ci w.sp 0x8001c790#64 M :=
    { ra := by decide
      sp_lo := by omega
      sp_hi := by omega
      sp_al := by omega
      L_lo := by omega
      L_hi := by simp only [stateSize]; omega
      ci_lo := by omega
      ci_hi := by simp only [ciSize]; omega
      ci_al := by omega
      L_al := by omega
      hook := hT.hook
      nres := hT.nres }
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (poscall_sum hpc ⟨BitVec.ofNat 64 symGlobalPointer, BitVec.ofNat 64 w.L, q9, q18, q19, q20, q21,
      t22, BitVec.ofNat 64 w.ci, q24, q25, t26, q27⟩ t12 o)
  simp only [RFrame.pins] at h
  kit_run h acc until [0x8001c274]
  have hspl := hr.ci_top
  simp only [ciSize, cStackBudget, RuntimeData.spEntry] at hspl
  have hM' : RAgree w m0 (pcMem M w.L w.ci w.sp 0x8001c790#64) :=
    ((hM.wm8 _ fun i hi => RetDirty.below (by simp only [cStackBudget, RuntimeData.spEntry]; omega)
      (by omega)).wm8 _ fun i hi => RetDirty.top hi).wm8 _ fun i hi => RetDirty.lci hi
  obtain ⟨c', hs, hq⟩ := ret_fresh hX hM' _ _ _ _ _ _ _ _ o _ (h.repin (by pins_of h))
  exact ⟨c', acc.trans hs, hq⟩

end Lua.Vm.Sim.Ret
