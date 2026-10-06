import Lua.Vm.Sim.Kit.Fflush
import Lua.Vm.AtF.Fwrite

/-!
# `fwrite(src, 1, n, stdout)` from `__sfvwrite_r` (lane F1-8)

`fwrite` tail-calls `_fwrite_r`, which multiplies (`__muldi3`, a call that
keeps the memory), takes the no-op lock, builds a one-iov `uio` on its stack
and calls `__sfvwrite_r`; on its `0` it unlocks and returns `n`. The
at-lemmas are generated (`Lua/Vm/AtF/Fwrite.lean`, `gen_lua_at.py --fn
fwrite`). `__sfvwrite_r`'s summary on the line-buffered `stdout` is the
named obligation `SfvwriteLbf_Statement` (its 155 at-lemmas are generated,
`Lua/Vm/AtF/Sfvwrite.lean`; the loop's proof is open, PHASES A0.2), and
`FwriteStdout_Statement` follows from it (`fwrite_stdout_of_sfv`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- **A one-iov `uio`** at `U` (`uio_iov = I`, `uio_resid = n`) over the iov
`[src, n]` at `I`. -/
structure SfvUio (m : Mem) (U I src n : Nat) : Prop where
  iov : bytesT8 m U = BitVec.ofNat 64 I
  resid : bytesT8 m (U + 16) = BitVec.ofNat 64 n
  base : bytesT8 m I = BitVec.ofNat 64 src
  len : bytesT8 m (I + 8) = BitVec.ofNat 64 n

/-- What `__sfvwrite_r` keeps: the caller's frames above `sp` but the
`uio_resid` it counts down, and below `sp` everything but `stdout`, its
buffer, `errno` and the callee frames (3 KiB: its own 96 bytes, then
`_fflush_r`'s 2 KiB). -/
structure SfvKeep (m m' : Mem) (sp buf U : Nat) : Prop where
  keep_hi : ∀ a, sp ≤ a → (a < U + 16 ∨ U + 24 ≤ a) → bytesT1 m' a = bytesT1 m a
  keep_lo : ∀ a, a + 3072 ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
    (a < buf ∨ buf + 1024 ≤ a) → (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- **`__sfvwrite_r(_REENT, stdout, uio)` on the set-up line-buffered
`stdout`** (`0x80033b50`), one iov of `n` bytes at `src` (apart from `stdout`
and its buffer, below the stack): `0` returned, the console gains `out` and
the buffer holds `pend'`, `out ++ pend' = pend ++ (the n bytes)`. Proved in
`Kit/Sfvwrite.lean` (`sfvwrite_lbf`). -/
def SfvwriteLbf_Statement : Prop :=
  ∀ (sp buf U I src n : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String),
    r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 → buf + 3584 ≤ sp →
    StdoutAt m buf pend → StdioUp m → SfvUio m U I src n →
    sp ≤ I → I + 16 ≤ U → U + 24 ≤ sp + 2048 → U % 8 = 0 → I % 8 = 0 →
    errnoAddr + 4 ≤ src → src + n + 3072 ≤ sp →
    (src + n ≤ buf ∨ buf + 1024 ≤ src) → (src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src) →
    Triple (SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 U⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' out pend', wrRet r sp 0 f m' (pushes o out) c ∧ StdoutAt m' buf pend' ∧ StdioUp m' ∧
        out ++ pend' = pend ++ bytesAt m src n ∧ SfvKeep m m' sp buf U)

/-- The context of `fwrite`'s rows: `sp`, `src`, `n`; `ra` and the frame. -/
@[at_row] abbrev fwCx (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, src, n] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- The frame `__sfvwrite_r` sees: `s0 = stdout`, `s1 = _REENT`, `s2 = 1`, `s3 = n`. -/
abbrev fwFrame (f : AbiFrame) (n : Nat) : AbiFrame :=
  ⟨BitVec.ofNat 64 stdoutFile, BitVec.ofNat 64 symImpureData, 0x1#64, BitVec.ofNat 64 n, f.s4, f.s5, f.s6,
    f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- **`fwrite(src, 1, n, stdout)` from `__sfvwrite_r`'s summary.** -/
theorem fwrite_stdout_of_sfv (hsfv : SfvwriteLbf_Statement) : FwriteStdout_Statement := by
  intro sp buf src n pend r f m o hx hs hu hbs hsrc hsp hb hst c h
  have hb0 := hs.buf_lo; have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al; have hra := hx.ra
  stdio_nums
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hX : Lua.Vm.AtF.Fwrite.Ok (fwCx sp src n r f m o) := by fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800342e4#64 (Lua.Vm.AtF.Fwrite.r0 (fwCx sp src n r f m o))
      (ArmPay (fwCx sp src n r f m o).m (fwCx sp src n r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 := hu.impure'; have hc1 := hu.flags2'; have hc2 := hs.flags'; have hg := hu.init'
  fat_run Lua.Vm.AtF.Fwrite h acc until [0x80033b50]
  fcx_unfold at h
  -- `__sfvwrite_r` on the uio at `sp - 72`
  have hM : ∀ a, (a < sp - 112 ∨ sp ≤ a) →
      (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o))[a]? = m[a]? := by
    intro a ha; fcx_unfold
    simp (disch := omega) only [getElem?_writeMap8_out, getElem?_writeMap4_out]
  have hs3 : StdoutAt (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) buf pend :=
    hs.below fun a ha => hM a (by omega)
  have hu3 : StdioUp (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) :=
    hu.below fun a ha => hM a (by omega)
  have hio : SfvUio (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) (sp - 72) (sp - 88) src n := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> fcx_unfold <;>
      simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  obtain ⟨c2, s2, m', out, pend', hret, hs', hu', hout, hkeep⟩ :=
    hsfv (sp - 112) buf (sp - 72) (sp - 88) src n pend 0x800341f8#64 (fwFrame f n)
      (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) o (by decide) (by omega) (by omega) (by omega) hs3 hu3 hio
      (by omega) (by omega) (by omega) (by omega) (by omega) hsrc (by omega) hb hst _
      (by fcx_unfold; simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s2
  -- the return from `__sfvwrite_r`: a fresh root over `m'`
  simp only [wrRet] at hret
  have hY : Lua.Vm.AtF.Fwrite.Ok (fwCx sp src n r f m' (pushes o out)) := by fcx_ok
  have h : SegSt 0x800341f8#64 (Lua.Vm.AtF.Fwrite.r3 (fwCx sp src n r f m' (pushes o out)))
      (ArmPay (fwCx sp src n r f m' (pushes o out)).m (fwCx sp src n r f m' (pushes o out)).o) c2 :=
    hret.repin (by pins_of hret)
  have kh := hkeep.keep_hi
  have rd : ∀ a, sp - 112 ≤ a → a + 8 ≤ sp - 56 →
      bytesT8 m' a = bytesT8 (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) a := fun a ha hb' =>
    bytesT8_congrT fun i _ => kh _ (by omega) (by omega)
  have hk1 := hu'.flags2'; have hk2 := hs'.flags'
  have hk3 : bytesT8 m' (sp - 104) = BitVec.ofNat 64 n := by
    rw [rd _ (by omega) (by omega)]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  have hk4 : bytesT8 m' (sp - 8) = r := by
    rw [bytesT8_congrT fun i _ => kh _ (by omega) (by omega)]; fcx_unfold
    simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  have hk5 : bytesT8 m' (sp - 16) = f.s0 := by
    rw [bytesT8_congrT fun i _ => kh _ (by omega) (by omega)]; fcx_unfold
    simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  have hk6 : bytesT8 m' (sp - 24) = f.s1 := by
    rw [bytesT8_congrT fun i _ => kh _ (by omega) (by omega)]; fcx_unfold
    simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  have hk7 : bytesT8 m' (sp - 32) = f.s2 := by
    rw [bytesT8_congrT fun i _ => kh _ (by omega) (by omega)]; fcx_unfold
    simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  have hk8 : bytesT8 m' (sp - 40) = f.s3 := by
    rw [bytesT8_congrT fun i _ => kh _ (by omega) (by omega)]; fcx_unfold
    simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4]
  fat_run Lua.Vm.AtF.Fwrite h acc
  fcx_unfold at h
  -- the bytes `__sfvwrite_r` read are the caller's
  have hby : bytesAt (Lua.Vm.AtF.Fwrite.m3 (fwCx sp src n r f m o)) src n = bytesAt m src n :=
    bytesAt_congr fun i hi => bT1_congr (hM _ (by omega))
  refine ⟨_, acc, m', out, pend', h.repin (by pins_of h), hs', hu', by rw [hout, hby],
    ⟨fun a ha => ?_, fun a ha h1 h2 h3 => ?_⟩⟩
  · rw [kh a (by omega) (by omega)]; exact bT1_congr (hM a (by omega))
  · rw [hkeep.keep_lo a (by omega) h1 h2 h3]; exact bT1_congr (hM a (by omega))

end Lua.Vm.Sim.Kit
