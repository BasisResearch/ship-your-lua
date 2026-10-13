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
    (bT4_congr fun i _ => h _ (by omega)).trans hF.flags2, (bT4_congr fun i _ => h _ (by omega)).trans hF.fs,
    hF.tail.congrT fun a _ h2 => bT1_congr (h a (by omega))⟩

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

/-! ## The writes -/

/-- `fwrite`'s entry pins for `fwrite(src, 1, n, stdout)`. -/
abbrev fwPre (src n sp : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
    ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f

/-- **An empty `fwrite` on the fresh stream**: `0` returned, nothing written
but `fwrite`'s frame; `stdout` stays fresh. -/
theorem fwrite_fresh0 (sp src : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e720 + 96 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : StdoutFresh m) :
    Triple (SegSt 0x800342e4#64 (fwPre src 0 sp r f) (ArmPay m o))
      (fun c => ∃ M, wrRet r sp 0 f M o c ∧ StdoutFresh M ∧ Agree (Below sp 112) m M) := by
  intro c h
  obtain ⟨c1, s1, h1⟩ := fwf_pre sp src 0 r f m o hra (by omega) hhi hal hF c h
  obtain ⟨hM, hfr, hio⟩ := fwf_m3 sp src 0 r f m o (by omega) hhi
  have hF' : StdoutFresh (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src 0 r f m o)) :=
    hF.below fun a ha => hM a (by stdio_nums; omega)
  obtain ⟨c2, s2, h2⟩ := sfv_empty (sp - 112) (sp - 72) 0x800341f8#64 (fwFrame f 0) _ o (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rw [show sp - 72 + 16 = sp - 56 by omega]; have := hio.resid
      rw [show sp - 72 + 16 = sp - 56 by omega] at this; exact this) c1 h1
  obtain ⟨c3, s3, h3⟩ := fwf_post sp 0 r f _ o hra (by omega) hhi hal hfr hF'.flags' hF'.flags2' c2 h2
  exact ⟨c3, s1.trans (s2.trans s3), _, h3, hF', fun a ha => hM a (by simp only [Below] at ha; omega)⟩

/-- **An empty `fwrite` from boot**: `CHECK_INIT` runs `__sinit`, `ORIENT`
marks the stream, `__sfvwrite_r` returns at once; `stdout` is fresh. -/
theorem fwrite_boot0 (sp src : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e7d8 + 64 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hB : StdioBoot (Vsa.Densify.fillZeroMem m)) (hMf : MemfsBoot (Vsa.Densify.fillZeroMem m)) :
    Triple (SegSt 0x800342e4#64 (fwPre src 0 sp r f) (ArmPay m o))
      (fun c => ∃ M, wrRet r sp 0 f M o c ∧ StdoutFresh M ∧ Agree (fun a => SinitW a ∨ Below sp 176 a) m M ∧
      StdioRest M) := by
  intro c h
  obtain ⟨c1, s1, M, h1, mid⟩ := fws_pre sp src 0 r f m o hra hlo hhi hal hB (bT4_of_fill (bytesT4_of_rd32 hMf.ready)) c h
  obtain ⟨c2, s2, h2⟩ := sfv_empty (sp - 112) (sp - 72) 0x800341f8#64 (fwFrame f 0) M o (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      have := mid.uio.resid
      rw [show sp - 72 + 16 = sp - 56 by omega] at this ⊢; exact this) c1 h1
  have hfr : FwFrame M sp 0 r f := ⟨mid.frame.ra, mid.frame.s0, mid.frame.s1, mid.frame.s2, mid.frame.s3, mid.frame.n⟩
  obtain ⟨c3, s3, h3⟩ := fwf_post sp 0 r f M o hra (by omega) hhi hal hfr mid.fresh.flags' mid.fresh.flags2' c2 h2
  exact ⟨c3, s1.trans (s2.trans s3), M, h3, mid.fresh, mid.agree, mid.rest⟩

/-- **The first non-empty `fwrite` from the fresh stream** (after an empty
first write): as `StdoutSetup_Statement` from boot, without `__sinit`. -/
theorem stdoutSetup_fresh (hM : MallocR_Statement) (sp src n top brk : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hF : StdoutFresh m) (hR : StdioRest m) (hheap : HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins)
    (hra : r.toNat % 4 = 0) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0) (hlo : heapEnd + 8192 ≤ sp)
    (hroom : brk + 1024 + 16384 ≤ heapEnd) (hn : 1 ≤ n) (hsl : SrcLo src n) (hsh : src + n + 4096 ≤ sp)
    (hsf : src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src)
    (hsrc : ∀ a, src ≤ a → a < src + n → ¬ FsGlobal a ∧ ¬ MallocW chunks a) :
    Triple (SegSt 0x800342e4#64 (fwPre src n sp r f) (ArmPay m o))
      (fun c => ∃ M m' out pend' buf top' brk' chunks' bins', wrRet r sp n f m' (pushes o out) c ∧
        SetupPost m M m' sp src n buf brk chunks top' brk' chunks' bins' out pend') := by
  have q : heapEnd + 4096 ≤ sp - 112 ∧ 0x8005e7d8 + 64 + 112 ≤ sp ∧ heapEnd + 32 ≤ sp - 112 := by
    obtain ⟨H, hH⟩ : ∃ H, heapEnd = H := ⟨_, rfl⟩
    have : H = 0x87800000 := hH ▸ rfl
    rw [hH] at hlo ⊢; omega
  intro c h
  fs_nums
  stdio_nums
  have : symSf = 0x8005e5b0 := rfl
  obtain ⟨c1, s1, h1⟩ := fwf_pre sp src n r f m o hra (by omega) hhi hal hF c h
  obtain ⟨hM3, hfr, hio⟩ := fwf_m3 sp src n r f m o (by omega) hhi
  have hF3 : StdoutFresh (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) :=
    hF.below fun a ha => hM3 a (by omega)
  have hH3 : HeapAt (Vsa.Densify.fillZeroMem (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o))) top brk chunks bins :=
    hheap.congr fun a ha => fill_congr <| hM3 a (.inl (by
      have e4 : symMallocAv = 0x8005c6d0 := rfl
      have e5 : symMallocSbrkBase = 0x8005d388 := rfl
      have e6 : symBrk = 0x8005d3b8 := rfl
      have e7 : symMallocTopPad = 0x8005d3d8 := rfl
      have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
      have e9 : symMallocMallinfo = 0x8005e560 := rfl
      have e2 : heapStart = 0x8006ecd0 := rfl
      simp only [HeapReads] at ha; omega))
  obtain ⟨c2, s2, M, m', out, pend', buf, top', brk', chunks', bins', hret, FW⟩ :=
    sfvwrite_first hM (sp - 112) (sp - 72) (sp - 88) src n top brk chunks bins 0x800341f8#64 (fwFrame f n) _ o
      (by decide) q.1 (by omega) (by omega) hF3 hH3 hroom hio (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hn hsl (by omega) hsf hsrc c1 h1
  have hfrM : FwFrame M sp n r f := hfr.keep (by omega) fun a h1 h2 => bT1_congr (FW.agree a (by
    simp only [FsGlobal, MallocW, MallocGlobal, Below, StdoutW, Rng, not_or, not_and]
    have e4 : symMallocAv = 0x8005c6d0 := rfl
    have e5 : symMallocSbrkBase = 0x8005d388 := rfl
    have e6 : symBrk = 0x8005d3b8 := rfl
    have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
    have e9 : symMallocMallinfo = 0x8005e560 := rfl
    have e2 : heapStart = 0x8006ecd0 := rfl
    have : symFiles = 0x8005d760 := rfl
    omega))
  have hfr' : FwFrame m' sp n r f := hfrM.keep (by omega) fun a h1 h2 => FW.keep.keep_hi a h1 h2
  obtain ⟨c3, s3, h3⟩ := fwu_post sp n r f m' (pushes o out) hra (by omega) hhi hal hfr' FW.stdout.flags'
    FW.up.flags2' c2 hret
  have hR3 : StdioRest (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) :=
    hR.congrT fun a ha => bT1_congr (hM3 a (by
      have : symSglue = 0x8005cee0 := rfl
      have : symStdioExitHandler = 0x8005d3e0 := rfl
      simp only [RestFoot, stdinFile, stderrFile] at ha; omega))
  refine ⟨c3, s1.trans (s2.trans s3), M, m', out, pend', buf, top', brk', chunks', bins', h3,
    ⟨FW.stdout, FW.up, ?_, FW.grant, ?_, FW.keep, FW.src_buf, hR3.of_first FW (by omega)⟩⟩
  · rw [FW.out]
    exact bytesAt_congr fun i hi => bT1_congr (hM3 (src + i) (by omega))
  · have k : Agree (Below sp 112) m (Lua.Vm.AtF.FwriteFresh.m3 (fwCx sp src n r f m o)) :=
      fun a ha => hM3 a (by simp only [Below] at ha; omega)
    exact (k.trans FW.agree).mono fun a ha => by
      have : symStdioExitHandler = 0x8005d3e0 := rfl
      have : symImpureData = 0x8005d1b8 := rfl
      have : reentCleanupOff = 72 := rfl
      rcases ha with hb | hg | hw | hb2 | hs
      · simp only [Below] at hb; exact .inr (.inr (.inr ⟨hb.1, by omega⟩))
      · exact .inl hg
      · exact .inr (.inl hw)
      · simp only [Below] at hb2; exact .inr (.inr (.inr ⟨by omega, by omega⟩))
      · simp only [StdoutW, SinitW, Rng] at hs ⊢; omega

end Lua.Vm.Sim.Kit
