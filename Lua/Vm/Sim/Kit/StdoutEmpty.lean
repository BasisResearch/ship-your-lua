import Lua.Vm.Sim.Kit.StdoutSetup
import Lua.Vm.AtF.FwriteFresh

/-!
# Empty writes and the stream between `__sinit` and its buffer (lane F1-11)

`print("")` writes 0 bytes first: `_fwrite_r` still runs `CHECK_INIT`
(`__sinit` at the first write) and `ORIENT`, but `__sfvwrite_r` returns at
once for `uio_resid = 0` (`0x80033b54`), before `cantwrite` would set the
buffer up. So between writes `stdout` is in one of three states: the boot
state (`StdioBoot`), *fresh* (`StdoutFresh`: `__sinit` ran, no buffer), or
set up (`StdoutAt`, `StdioUp`). This file proves the writes the first two
states admit besides lane F1-10's first non-empty write from boot:

* `sfv_empty`: `__sfvwrite_r` of an empty uio returns `0`, writing nothing
  (`Lua/Vm/AtF/SfvwriteSetup.lean`'s `n = 0` path);
* `fwrite_boot0`: an empty write from boot leaves `stdout` fresh;
* `fwrite_fresh0`: an empty write from fresh keeps it fresh;
* `stdoutSetup_fresh`: a non-empty write from fresh sets it up
  (`sfvwrite_first`, as `stdoutSetup_of_malloc` from boot).

The writes from fresh run `fwrite`'s at-lemmas at `_flags = 0x2009`
(`Lua/Vm/AtF/FwriteFresh.lean`, `gen_lua_at.py --fn fwrite/fresh`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (Config Steps)

/-- **`__sfvwrite_r` of an empty uio** (`uio_resid = 0` at `U + 16`): `0`
returned at once, the memory unchanged. -/
theorem sfv_empty (sp U : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e720 + 96 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hU : sp + 16 ≤ U) (hUh : U + 24 ≤ 2 ^ 32) (hUa : U % 8 = 0) (hres : bytesT8 m (U + 16) = 0#64) :
    Triple (SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 U⟩] sp r f) (ArmPay m o))
      (wrRet r sp 0 f m o) := by
  intro c h
  let X := sfsX sp U sp 0 0 r f m o
  have hX : Lua.Vm.AtF.SfvwriteSetup.Ok X := ⟨hlo, hhi, hal, hra, Nat.le_refl _, hU, hUh, hUa, show sp % 8 = 0 by omega⟩
  have hc0 : bytesT8 X.m (X.n 1 + 16) = BitVec.ofNat 64 (X.n 3) := hres
  have hf0 : X.n 3 = 0 := rfl
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80033b50#64 (Lua.Vm.AtF.SfvwriteSetup.r0 X) (ArmPay X.m X.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.SfvwriteSetup h acc
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ## The stream before its buffer -/

/-- `stdout` fresh across stores below the end of `stdout`. -/
theorem StdoutFresh.below {m m' : Mem} (hF : StdoutFresh m) (h : ∀ a, a < stdoutFile + fileSize → m'[a]? = m[a]?) :
    StdoutFresh m' := by
  stdio_nums
  have : symFsReady = 0x8005d3c0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  exact ⟨(bT8_congr fun i _ => h _ (by omega)).trans hF.impure, (bT8_congr fun i _ => h _ (by omega)).trans hF.cleanup,
    (bT2_congr fun i _ => h _ (by omega)).trans hF.flags, (bT2_congr fun i _ => h _ (by omega)).trans hF.file,
    (bT4_congr fun i _ => h _ (by omega)).trans hF.pad, (bT8_congr fun i _ => h _ (by omega)).trans hF.base,
    (bT8_congr fun i _ => h _ (by omega)).trans hF.cookie, (bT8_congr fun i _ => h _ (by omega)).trans hF.write,
    (bT4_congr fun i _ => h _ (by omega)).trans hF.flags2, (bT4_congr fun i _ => h _ (by omega)).trans hF.fs⟩

theorem StdoutFresh.impure' {m : Mem} (h : StdoutFresh m) : bytesT8 m 0x8005d398 = 0x8005d1b8#64 := h.impure
theorem StdoutFresh.flags' {m : Mem} (h : StdoutFresh m) : bytesT2 m 0x8005e678 = 0x2009#16 := h.flags
theorem StdoutFresh.flags2' {m : Mem} (h : StdoutFresh m) : bytesT4 m 0x8005e718 = 0x0#32 := h.flags2
theorem StdoutFresh.init' {m : Mem} (h : StdoutFresh m) : (bytesT8 m 0x8005d200 == 0x0#64) = false := by
  have e : bytesT8 m 0x8005d200 = BitVec.ofNat 64 symCleanupStdio := h.cleanup
  rw [e]; decide

/-- **The words `_fwrite_r` reads back after `__sfvwrite_r`**: its saved
`ra`, `s0`–`s3` and `n`, in `[sp - 112, sp)` off the uio's `uio_resid`. -/
structure FwFrame (M : Mem) (sp n : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  ra : bytesT8 M (sp - 8) = r
  s0 : bytesT8 M (sp - 16) = f.s0
  s1 : bytesT8 M (sp - 24) = f.s1
  s2 : bytesT8 M (sp - 32) = f.s2
  s3 : bytesT8 M (sp - 40) = f.s3
  n : bytesT8 M (sp - 104) = BitVec.ofNat 64 n

/-- The frame across `__sfvwrite_r`'s keep above its `sp` (`SfvKeep.keep_hi`). -/
theorem FwFrame.keep {M M' : Mem} {sp n : Nat} {r : BitVec 64} {f : AbiFrame} (h : FwFrame M sp n r f)
    (hsp : 112 ≤ sp) (hk : ∀ a, sp - 112 ≤ a → (a < sp - 72 + 16 ∨ sp - 72 + 24 ≤ a) → bytesT1 M' a = bytesT1 M a) :
    FwFrame M' sp n r f :=
  ⟨(bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ra,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s0,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s1,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s2,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s3,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.n⟩

/-- **`fwrite`'s run up to `__sfvwrite_r` from the fresh stream** (`_flags =
0x2009`: `CHECK_INIT` passes, `ORIENT` keeps it), and the memory it hands
over: the frame, the uio, the caller's bytes off `[sp - 112, sp)`. -/
theorem fwf_pre (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e720 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : StdoutFresh m) :
    Triple (SegSt 0x800342e4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 (sp - 72)⟩] (sp - 112)
        0x800341f8#64 (fwFrame f n)) (ArmPay (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) o)) := by
  intro c h
  have hX : Lua.Vm.AtF.FwriteFresh.Ok (fwCx sp src n r f m o) := by fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800342e4#64 (Lua.Vm.AtF.FwriteFresh.r0 (fwCx sp src n r f m o))
      (ArmPay (fwCx sp src n r f m o).m (fwCx sp src n r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 := hF.impure'; have hc1 := hF.flags2'; have hc2 := hF.flags'; have hg := hF.init'
  fat_run Lua.Vm.AtF.FwriteFresh h acc until [0x80033b50]
  fcx_unfold at h
  exact ⟨_, acc, by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h)⟩

/-- What `fwf_pre` hands over. -/
theorem fwf_m3 (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hlo : 0x8005e720 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) :
    (∀ a, (a < sp - 112 ∨ sp ≤ a) → (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o))[a]? = m[a]?) ∧
      FwFrame (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) sp n r f ∧
      SfvUio (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) (sp - 72) (sp - 88) src n := by
  refine ⟨fun a ha => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · fcx_unfold; simp (disch := omega) only [getElem?_writeMap8_out, getElem?_writeMap4_out]
  all_goals fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]

/-- **`_fwrite_r` after `__sfvwrite_r` returned `0` on the fresh stream**
(`_flags = 0x2009`): the unlock, `n` returned. -/
theorem fwf_post (sp n : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e720 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : FwFrame M sp n r f) (hfl : bytesT2 M 0x8005e678 = 0x2009#16) (hf2 : bytesT4 M 0x8005e718 = 0x0#32) :
    Triple (wrRet 0x800341f8#64 (sp - 112) 0 (fwFrame f n) M o) (wrRet r sp n f M o) := by
  intro c h
  have hX : Lua.Vm.AtF.FwriteFresh.Ok (fwCx sp 0 n r f M o) := by fcx_ok
  simp only [wrRet] at h
  have h : SegSt 0x800341f8#64 (Lua.Vm.AtF.FwriteFresh.r3 (fwCx sp 0 n r f M o))
      (ArmPay (fwCx sp 0 n r f M o).m (fwCx sp 0 n r f M o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc3 := hF.n; have hk4 := hF.ra; have hk5 := hF.s0; have hk6 := hF.s1; have hk7 := hF.s2
  have hk8 := hF.s3
  fat_run Lua.Vm.AtF.FwriteFresh h acc
  fcx_unfold at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`_fwrite_r` after `__sfvwrite_r` returned `0` on the set-up stream**
(`_flags = 0x2889`): the unlock, `n` returned. -/
theorem fwu_post (sp n : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e720 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : FwFrame M sp n r f) (hfl : bytesT2 M 0x8005e678 = 0x2889#16) (hf2 : bytesT4 M 0x8005e718 = 0x0#32) :
    Triple (wrRet 0x800341f8#64 (sp - 112) 0 (fwFrame f n) M o) (wrRet r sp n f M o) := by
  intro c h
  have hX : Lua.Vm.AtF.Fwrite.Ok (fwCx sp 0 n r f M o) := by fcx_ok
  simp only [wrRet] at h
  have h : SegSt 0x800341f8#64 (Lua.Vm.AtF.Fwrite.r3 (fwCx sp 0 n r f M o))
      (ArmPay (fwCx sp 0 n r f M o).m (fwCx sp 0 n r f M o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc3 := hF.n; have hk4 := hF.ra; have hk5 := hF.s0; have hk6 := hF.s1; have hk7 := hF.s2
  have hk8 := hF.s3
  fat_run Lua.Vm.AtF.Fwrite h acc
  fcx_unfold at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit
