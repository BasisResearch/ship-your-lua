import Lua.Vm.Sim.Kit.Stdio
import Lua.Vm.AtF.Fflush

/-!
# `fflush(stdout)` (lane F1-8): `FflushStdout_Statement`

The first summary on the callee-context route: `fflush`'s at-lemmas are
generated (`Lua/Vm/AtF/Fflush.lean`, `scripts/gen_lua_at.py --fn fflush`);
this file chains them (`fat_run`) over the two roots (the entry; the return
from `__sflush_r`, whose summary `sflush_sum` is applied between them) and
supplies the root facts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- **`fflush(stdout)`**: the pending bytes on the console, `0` returned, the
buffer empty. -/
theorem fflush_stdout : FflushStdout_Statement := by
  intro sp buf pend r f m o hx hs hu c h
  have hb := hs.buf_lo; have hr := hs.room
  have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al
  stdio_nums
  have hEA : errnoAddr = 0x8005d408 := rfl
  -- the entry
  have hX : Lua.Vm.AtF.Fflush.Ok (abiCx sp r f m o) := ⟨by show _ ≤ sp; omega, h2, h3, hx.ra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032a1c#64 (Lua.Vm.AtF.Fflush.r0 (abiCx sp r f m o))
      (ArmPay (abiCx sp r f m o).m (abiCx sp r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 := hu.impure'; have hc1 := hs.flags'; have hc2 := hu.flags2'; have hg := hu.init'
  fat_run Lua.Vm.AtF.Fflush h acc until [0x800326f8]
  -- `__sflush_r`
  have hs2 : StdoutAt (Lua.Vm.AtF.Fflush.m2 (abiCx sp r f m o)) buf pend :=
    hs.below fun a ha => by fcx_unfold; simp (disch := omega) only [getElem?_writeMap8_out]
  obtain ⟨c2, s2, m', hret, hout⟩ := sflush_sum 0x8005d1b8#64 (sp - 32) buf pend 0x80032a68#64 f
    (Lua.Vm.AtF.Fflush.m2 (abiCx sp r f m o)) o ⟨by decide, by omega, by omega, by omega⟩ hs2 _
    (h.repin (by pins_of h))
  have acc := acc.trans s2
  -- the return from `__sflush_r`: a fresh root over `m'`
  simp only [wrRet] at hret
  have hY : Lua.Vm.AtF.Fflush.Ok (abiCx sp r f m' (pushes o pend)) := ⟨by show _ ≤ sp; omega, h2, h3, hx.ra⟩
  have h : SegSt 0x80032a68#64 (Lua.Vm.AtF.Fflush.r3 (abiCx sp r f m' (pushes o pend)))
      (ArmPay (abiCx sp r f m' (pushes o pend)).m (abiCx sp r f m' (pushes o pend)).o) c2 :=
    hret.repin (by pins_of hret)
  have keep_hi := hout.keep_hi; have keep_lo := hout.keep_lo; have keep_file := hout.keep_file
  fcx_unfold at keep_hi keep_lo keep_file
  have hk3 : bytesT8 m' (sp - 32) = 0x8005e668#64 := by
    rw [bytesT8_congrT fun i _ => keep_hi _ (by omega)]
    simp (disch := omega) only [fw8_same]
  have hk4 : bytesT8 m' (sp - 8) = r := by
    rw [bytesT8_congrT fun i _ => keep_hi _ (by omega)]
    simp (disch := omega) only [fw8_wm8, fw8_same]
  have hk1 := hout.stdout.flags'
  have hk2 : bytesT4 m' 0x8005e718 = 0x0#32 := by
    rw [bT4_congrT fun i _ => keep_file _ (by omega) (by omega)]
    simp (disch := omega) only [fw4_wm8]; exact hc2
  fat_run Lua.Vm.AtF.Fflush h acc
  -- the return of `fflush`
  have hU : StdioUp m' := by
    refine ⟨?_, ?_, ?_⟩
    · rw [bytesT8_congrT fun i _ => keep_lo _ (by omega) (by omega) (by omega)]
      simp (disch := omega) only [fw8_wm8]; exact hu.impure
    · rw [bytesT8_congrT fun i _ => keep_lo _ (by omega) (by omega) (by omega)]
      simp (disch := omega) only [fw8_wm8]; exact hu.init
    · rw [bT4_congrT fun i _ => keep_file _ (by omega) (by omega)]
      simp (disch := omega) only [fw4_wm8]; exact hu.flags2
  refine ⟨_, acc, _, h.repin (by pins_of h),
    hout.stdout.below fun a ha => by fcx_unfold; exact getElem?_writeMap8_out _ _ _ _ (by omega),
    hU.below fun a ha => by fcx_unfold; exact getElem?_writeMap8_out _ _ _ _ (by omega),
    ⟨fun a ha => ?_, fun a ha h1 h2 h3 => ?_⟩⟩
  · fcx_unfold
    rw [fw1_wm8 (by omega), keep_hi a (by omega)]
    simp (disch := omega) only [fw1_wm8]
  · fcx_unfold
    rw [fw1_wm8 (by omega), keep_lo a (by omega) h1 h3]
    simp (disch := omega) only [fw1_wm8]

end Lua.Vm.Sim.Kit
