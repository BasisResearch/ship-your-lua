import Lua.Vm.Sim.Kit.Stdio
import Lua.Vm.AtF.Fflush
import Lua.Vm.AtF.Fflush_r

/-!
# `fflush(stdout)` and `_fflush_r(_REENT, stdout)` (lane F1-8)

The first summaries on the callee-context route. Both functions' at-lemmas
are generated (`Lua/Vm/AtF/Fflush.lean`, `Lua/Vm/AtF/Fflush_r.lean`,
`scripts/gen_lua_at.py --fn`); both reach `__sflush_r` with the same frame
(`[sp - 32, sp)`: `stdout`, `_REENT`, `ra`), and leave the same memory after
it. That shared middle is stated once: `sfl_mid32` (the call, `sflush_sum`,
and what the caller reads back: `FlushMid`) and `flush_fin` (the caller's
last store and the summary's post, `FlushPost`). Each function is then its
two `fat_run`s around them.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- **A flush's post**: `0` returned, the pending bytes on the console,
`stdout` empty, newlib's set-up words, and the caller's bytes kept. -/
def FlushPost (r : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (f : AbiFrame) (m : Mem)
    (o : Array String) (c : Config) : Prop :=
  ∃ m', wrRet r sp 0 f m' (pushes o pend) c ∧ StdoutAt m' buf [] ∧ StdioUp m' ∧ StdoutKeep m m' sp buf

/-- What the caller of `__sflush_r` (frame `[sp - 32, sp)`) reads back after
it, and what it keeps of the memory `m` before the call. -/
structure FlushMid (m m' : Mem) (sp buf : Nat) (r : BitVec 64) : Prop where
  k32 : bytesT8 m' (sp - 32) = 0x8005e668#64
  k8 : bytesT8 m' (sp - 8) = r
  flags : bytesT2 m' 0x8005e678 = 0x2889#16
  flags2 : bytesT4 m' 0x8005e718 = 0x0#32
  stdout : StdoutAt m' buf []
  up : StdioUp m'
  keep_hi : ∀ a, sp ≤ a → bytesT1 m' a = bytesT1 m a
  keep_lo : ∀ a, a + 2048 ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
    (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- **The call to `__sflush_r`** from a frame at `sp - 32` that holds
`stdout` at `sp - 32` and `ra` at `sp - 8`, over a memory `M` equal to `m`
outside the frame. -/
theorem sfl_mid32 {sp buf : Nat} {pend : List (BitVec 8)} {r ret : BitVec 64} {f : AbiFrame} {m M : Mem}
    {o : Array String} {c : Config} (hx : StdioCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (hu : StdioUp m)
    (hret : ret.toNat % 4 = 0) (hM : ∀ a, (a < sp - 32 ∨ sp ≤ a) → M[a]? = m[a]?)
    (h32 : bytesT8 M (sp - 32) = 0x8005e668#64) (h8 : bytesT8 M (sp - 8) = r)
    (h : SegSt 0x800326f8#64 (sflPre 0x8005d1b8#64 (sp - 32) ret f) (ArmPay M o) c) :
    ∃ c' m', Steps c c' ∧ wrRet ret (sp - 32) 0 f m' (pushes o pend) c' ∧ FlushMid m m' sp buf r := by
  have hb := hs.buf_lo; have hr := hs.room
  have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al
  stdio_nums
  have hEA : errnoAddr = 0x8005d408 := rfl
  obtain ⟨c', s, m', hret', hout⟩ := sflush_sum 0x8005d1b8#64 (sp - 32) buf pend ret f M o
    ⟨hret, by omega, by omega, by omega⟩ (hs.below fun a ha => hM a (by omega)) c h
  have kh := hout.keep_hi; have kl := hout.keep_lo; have kf := hout.keep_file
  have bM : ∀ a, (a < sp - 32 ∨ sp ≤ a) → bytesT1 M a = bytesT1 m a := fun a ha => bT1_congr (hM a ha)
  refine ⟨c', m', s, hret', ⟨?_, ?_, hout.stdout.flags', ?_, hout.stdout, ⟨?_, ?_, ?_⟩, fun a ha => ?_,
    fun a ha h1 h2 => ?_⟩⟩
  · rw [bytesT8_congrT fun i _ => kh _ (by omega)]; exact h32
  · rw [bytesT8_congrT fun i _ => kh _ (by omega)]; exact h8
  · rw [bT4_congrT fun i _ => (kf _ (by omega) (by omega)).trans (bM _ (by omega))]; exact hu.flags2'
  · rw [bytesT8_congrT fun i _ => (kl _ (by omega) (by omega) (by omega)).trans (bM _ (by omega))]
    exact hu.impure
  · rw [bytesT8_congrT fun i _ => (kl _ (by omega) (by omega) (by omega)).trans (bM _ (by omega))]
    exact hu.init
  · rw [bT4_congrT fun i _ => (kf _ (by omega) (by omega)).trans (bM _ (by omega))]; exact hu.flags2
  · exact (kh a (by omega)).trans (bM a (by omega))
  · exact (kl a (by omega) h1 h2).trans (bM a (by omega))

/-- **The caller's return after the flush**: its last store (`sd a0, 0(sp)`,
`0` at `sp - 32`) and the summary's post. -/
theorem flush_fin {sp buf : Nat} {pend : List (BitVec 8)} {r : BitVec 64} {f : AbiFrame} {m m' : Mem}
    {o : Array String} {c : Config} (hx : StdioCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv)
    (hmid : FlushMid m m' sp buf r)
    (h : wrRet r sp 0 f (writeMap8 m' (sp - 32) (sdData_val 0x0#64)) (pushes o pend) c) :
    FlushPost r sp buf pend f m o c := by
  have hb := hs.buf_lo; have hr := hs.room
  have h1 := hx.sp_lo; have h2 := hx.sp_hi
  stdio_nums
  refine ⟨_, h, hmid.stdout.below fun a ha => getElem?_writeMap8_out _ _ _ _ (by omega),
    hmid.up.below fun a ha => getElem?_writeMap8_out _ _ _ _ (by omega),
    ⟨fun a ha => ?_, fun a ha h1 h2 h3 => ?_⟩⟩
  · rw [fw1_wm8 (by omega)]; exact hmid.keep_hi a ha
  · rw [fw1_wm8 (by omega)]; exact hmid.keep_lo a ha h1 h3

/-- **`fflush(stdout)`**: the pending bytes on the console, `0` returned, the
buffer empty. -/
theorem fflush_stdout : FflushStdout_Statement := by
  intro sp buf pend r f m o hx hs hu c h
  have hb := hs.buf_lo; have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al; have hra := hx.ra
  stdio_nums
  have hX : Lua.Vm.AtF.Fflush.Ok (abiCx sp r f m o) := by fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032a1c#64 (Lua.Vm.AtF.Fflush.r0 (abiCx sp r f m o))
      (ArmPay (abiCx sp r f m o).m (abiCx sp r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 := hu.impure'; have hc1 := hs.flags'; have hc2 := hu.flags2'; have hg := hu.init'
  fat_run Lua.Vm.AtF.Fflush h acc until [0x800326f8]
  fcx_unfold at h
  obtain ⟨c2, m', s2, hret, hmid⟩ := sfl_mid32 (ret := 0x80032a68#64) hx hs hu (by decide)
    (fun a ha => by simp (disch := omega) only [getElem?_writeMap8_out])
    (by simp (disch := omega) only [fw8_same]) (by simp (disch := omega) only [fw8_wm8, fw8_same])
    (h.repin (by pins_of h))
  have acc := acc.trans s2
  have hY : Lua.Vm.AtF.Fflush.Ok (abiCx sp r f m' (pushes o pend)) := by fcx_ok
  simp only [wrRet] at hret
  have h : SegSt 0x80032a68#64 (Lua.Vm.AtF.Fflush.r3 (abiCx sp r f m' (pushes o pend)))
      (ArmPay (abiCx sp r f m' (pushes o pend)).m (abiCx sp r f m' (pushes o pend)).o) c2 :=
    hret.repin (by pins_of hret)
  have hk1 := hmid.flags; have hk2 := hmid.flags2; have hk3 := hmid.k32; have hk4 := hmid.k8
  fat_run Lua.Vm.AtF.Fflush h acc
  fcx_unfold at h
  exact ⟨_, acc, flush_fin hx hs hmid (h.repin (by pins_of h))⟩

/-- **`_fflush_r(_REENT, stdout)`** (`__sfvwrite_r`'s flushes): as `fflush`. -/
theorem fflush_r_stdout (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : StdioCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (hu : StdioUp m) :
    Triple (SegSt 0x80032954#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (FlushPost r sp buf pend f m o) := by
  intro c h
  have hb := hs.buf_lo; have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al; have hra := hx.ra
  stdio_nums
  have hX : Lua.Vm.AtF.Fflush_r.Ok (abiCx sp r f m o) := by fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032954#64 (Lua.Vm.AtF.Fflush_r.r0 (abiCx sp r f m o))
      (ArmPay (abiCx sp r f m o).m (abiCx sp r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc1 := hs.flags'; have hc2 := hu.flags2'; have hg := hu.init'
  fat_run Lua.Vm.AtF.Fflush_r h acc until [0x800326f8]
  fcx_unfold at h
  obtain ⟨c2, m', s2, hret, hmid⟩ := sfl_mid32 (ret := 0x80032998#64) hx hs hu (by decide)
    (fun a ha => by simp (disch := omega) only [getElem?_writeMap8_out])
    (by simp (disch := omega) only [fw8_same]) (by simp (disch := omega) only [fw8_wm8, fw8_same])
    (h.repin (by pins_of h))
  have acc := acc.trans s2
  have hY : Lua.Vm.AtF.Fflush_r.Ok (abiCx sp r f m' (pushes o pend)) := by fcx_ok
  simp only [wrRet] at hret
  have h : SegSt 0x80032998#64 (Lua.Vm.AtF.Fflush_r.r3 (abiCx sp r f m' (pushes o pend)))
      (ArmPay (abiCx sp r f m' (pushes o pend)).m (abiCx sp r f m' (pushes o pend)).o) c2 :=
    hret.repin (by pins_of hret)
  have hk1 := hmid.flags; have hk2 := hmid.flags2; have hk3 := hmid.k32; have hk4 := hmid.k8
  fat_run Lua.Vm.AtF.Fflush_r h acc
  fcx_unfold at h
  exact ⟨_, acc, flush_fin hx hs hmid (h.repin (by pins_of h))⟩

end Lua.Vm.Sim.Kit
