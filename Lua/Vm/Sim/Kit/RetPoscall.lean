import Lua.Vm.Sim.Kit.RetClose
import Lua.Vm.Arms.Segs.HluaD_poscall

/-!
# `luaD_poscall` with no hooks and `wanted = 0`, the call-node summary (lane F1-4)

`luaD_poscall(L, ci, n)` (`0x8000a39c`): `L->hookmask = 0` (`beqz` taken to
`0x8000a4d0`), `res = ci->func`, `wanted = ci->nresults = 0` (`beqz` taken:
`moveresults` case 0) so `L->top = res`, then `L->ci = ci->previous` and the
return. It saves `ra` at `56(sp)` of its frame `[sp - 64, sp)`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- What `luaD_poscall` reads. -/
structure PcCx (L ci sp : Nat) (r : BitVec 64) (m : Mem) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 64 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  L_lo : tohostAddr + 16 ≤ L
  L_hi : L + stateSize + 64 ≤ sp
  ci_lo : tohostAddr + 16 ≤ ci
  ci_hi : ci + ciSize + 64 ≤ sp
  ci_al : ci % 8 = 0
  L_al : L % 8 = 0
  hook : bytesT4 m (L + stateHookmaskOff) = 0#32
  nres : bytesT2 m (ci + ciNresultsOff) = 0#16

/-- The memory at the return: `ra` saved, `L->top = ci->func`, `L->ci = ci->previous`. -/
abbrev pcMem (m : Mem) (L ci sp : Nat) (r : BitVec 64) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m (sp - 64 + 56) r) (L + stateTopOff)
    (bytesT8 m (ci + ciFuncOff))) (L + stateCiOff) (bytesT8 m (ci + ciPreviousOff))

set_option hygiene false in
macro "pc_facts " hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).L_lo; have := ($hx).L_hi; have := ($hx).ci_lo; have := ($hx).ci_hi
  have := ($hx).ci_al; have := ($hx).L_al
  have hhk := ($hx).hook; have hnr := ($hx).nres
  simp only [stateSize, ciSize, stateHookmaskOff, ciNresultsOff, stateTopOff, stateCiOff,
    ciFuncOff, ciPreviousOff] at *))

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    bytesT2_wm8_out', bytesT8_wm8_out', hnr, sext16_zero, sext64_id, bytesT8_writeMap8,
    sdData_id] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, hhk]; decide)
      | (simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          sext64_id, bytesT8_writeMap8, sdData_id, Nat.reduceSub, Vsa.Sim.sext_zero,
          BitVec.add_zero]
         rw [rtgt _ hra]; exact hra))

/-- **`luaD_poscall(L, ci, n)` with no hooks and `ci->nresults = 0`**: it
returns to `ra` with the caller's `sp` and callee-saved registers, having
stored `ra` in its frame, `L->top = ci->func` and `L->ci = ci->previous`
(`pcMem`). -/
theorem poscall_sum {L ci sp : Nat} {r : BitVec 64} {m : Mem} (hx : PcCx L ci sp r m)
    (f : RFrame) (n : BitVec 64) (o : Array String) :
    Triple (SegSt 0x8000a39c#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 ci⟩ :: ⟨Register.x12, n⟩ ::
        ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (pcMem m L ci sp r) o)) := by
  intro c h
  have acc := Steps.refl c
  have hra := hx.ra
  pc_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [RFrame.pins] at h ⊢
  kit_run h acc
  have h := h.at (rtgt _ hra)
  rw [show sp - 64 + 64 = sp by omega] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

end Lua.Vm.Sim.Ret
