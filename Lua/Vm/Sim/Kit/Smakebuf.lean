import Lua.Vm.Sim.Kit.Setup
import Lua.Vm.AtF.Smakebuf_r

/-!
# `__smakebuf_r(_REENT, stdout)` (lane F1-10)

Four roots (`Lua/Vm/AtF/Smakebuf_r.lean`): the entry up to `_fstat_r`, its
return up to `_malloc_r`, the return from `_malloc_r` (the buffer installed)
up to `_isatty_r`, its return (the flags) to the caller. Each root's run is
one lemma over any context (`smb_run*`), each root memory's stores one region
and its reads (`smb_m*`); the summary splices the callees' summaries
(`fstat_sum`, `MallocR_Statement`, `isatty_sum`) between them and composes
the regions (`Agree.trans`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (Config Steps)
open Lua.Vm.AtF.Smakebuf_r (Ok)

/-! ## The roots' runs -/

theorem smb_run0 (X : FCx) (hX : Ok X) (hc0 : bytesT2 X.m 0x8005e678 = 0x2009#16)
    (hc1 : bytesT2 X.m 0x8005e67a = 0x1#16) :
    Triple (SegSt 0x80049a2c#64 (Lua.Vm.AtF.Smakebuf_r.r0 X) (ArmPay X.m X.o))
      (SegSt 0x8003b0e8#64 (Lua.Vm.AtF.Smakebuf_r.r2 X) (ArmPay (Lua.Vm.AtF.Smakebuf_r.m1 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Smakebuf_r h acc until [0x8003b0e8]
  exact ⟨_, acc, h⟩

theorem smb_run1 (X : FCx) (hX : Ok X) (hc2 : bytesT8 X.m (X.n 0 - 160) = 0x8005e668#64)
    (hc3 : bytesT4 X.m (X.n 0 - 132) = 0x2000#32) :
    Triple (SegSt 0x80049a78#64 (Lua.Vm.AtF.Smakebuf_r.r3 X) (ArmPay X.m X.o))
      (SegSt 0x8002fa34#64 (Lua.Vm.AtF.Smakebuf_r.r5 X) (ArmPay (Lua.Vm.AtF.Smakebuf_r.m2 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Smakebuf_r h acc until [0x8002fa34]
  exact ⟨_, acc, h⟩

theorem smb_run2 (X : FCx) (hX : Ok X) (hc0 : bytesT2 X.m 0x8005e678 = 0x2009#16)
    (hc1 : bytesT2 X.m 0x8005e67a = 0x1#16) (hc2 : bytesT8 X.m (X.n 0 - 160) = 0x8005e668#64)
    (hf0 : X.n 1 ≠ 0) (hg_3 : (BitVec.ofNat 64 (X.n 1) == 0x0#64) = false) :
    Triple (SegSt 0x80049a98#64 (Lua.Vm.AtF.Smakebuf_r.r6 X) (ArmPay X.m X.o))
      (SegSt 0x8004a170#64 (Lua.Vm.AtF.Smakebuf_r.r8 X) (ArmPay (Lua.Vm.AtF.Smakebuf_r.m4 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Smakebuf_r h acc until [0x8004a170]
  exact ⟨_, acc, h⟩

theorem smb_run3 (X : FCx) (hX : Ok X) (hc2 : bytesT8 X.m (X.n 0 - 160) = 0x8005e668#64)
    (hc4 : bytesT2 X.m 0x8005e678 = 0x2089#16) (hc5 : bytesT8 X.m (X.n 0 - 24) = X.b 2)
    (hc6 : bytesT8 X.m (X.n 0 - 8) = X.b 0) (hc7 : bytesT8 X.m (X.n 0 - 16) = X.b 1) :
    Triple (SegSt 0x80049adc#64 (Lua.Vm.AtF.Smakebuf_r.r9 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.Smakebuf_r.r11 X) (ArmPay (Lua.Vm.AtF.Smakebuf_r.m5 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Smakebuf_r h acc
  exact ⟨_, acc, h⟩

/-! ## The roots' memories -/

/-- The saved words of `__smakebuf_r`'s frame and the `FILE` pointer at `0(sp)`. -/
structure SmbFrame (M : Mem) (X : FCx) : Prop where
  fp : bytesT8 M (X.n 0 - 160) = 0x8005e668#64
  ra : bytesT8 M (X.n 0 - 8) = X.b 0
  s0 : bytesT8 M (X.n 0 - 16) = X.b 1

theorem SmbFrame.congr {M M' : Mem} {X : FCx} (h : SmbFrame M X) (h160 : 160 ≤ X.n 0)
    (hk : ∀ a, X.n 0 - 160 ≤ a → (a < X.n 0 - 152 ∨ X.n 0 - 16 ≤ a) → a < X.n 0 → M'[a]? = M[a]?) :
    SmbFrame M' X :=
  ⟨(bT8_congr fun i _ => hk _ (by omega) (by omega) (by omega)).trans h.fp,
   (bT8_congr fun i _ => hk _ (by omega) (by omega) (by omega)).trans h.ra,
   (bT8_congr fun i _ => hk _ (by omega) (by omega) (by omega)).trans h.s0⟩

theorem smb_m1 (X : FCx) (hX : Ok X) :
    Agree (Below (X.n 0) 160) X.m (Lua.Vm.AtF.Smakebuf_r.m1 X) ∧ SmbFrame (Lua.Vm.AtF.Smakebuf_r.m1 X) X := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · simp only [Below, not_and] at ha
    simp only [Lua.Vm.AtF.Smakebuf_r.m1]; fs_off
  all_goals simp only [Lua.Vm.AtF.Smakebuf_r.m1]; fat_rd

theorem smb_m2 (X : FCx) (hX : Ok X) :
    Agree (fun a => Rng (X.n 0 - 24) 8 a ∨ Rng (X.n 0 - 160) 8 a) X.m (Lua.Vm.AtF.Smakebuf_r.m2 X) ∧
      bytesT8 (Lua.Vm.AtF.Smakebuf_r.m2 X) (X.n 0 - 160) = 0x8005e668#64 ∧
      bytesT8 (Lua.Vm.AtF.Smakebuf_r.m2 X) (X.n 0 - 24) = X.b 2 := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.Smakebuf_r.m2]; fs_off
  all_goals simp only [Lua.Vm.AtF.Smakebuf_r.m2]; fat_rd

/-- Root 2's stores: `stdout`'s `_bf._size`, `_flags`, `_p`, `_bf._base`, and `0(sp)`. -/
structure SmbM4 (M : Mem) (X : FCx) : Prop where
  flags : bytesT2 M 0x8005e678 = 0x2089#16
  p : bytesT8 M 0x8005e668 = BitVec.ofNat 64 (X.n 1)
  base : bytesT8 M 0x8005e680 = BitVec.ofNat 64 (X.n 1)
  size : bytesT4 M 0x8005e688 = 1024#32
  fp : bytesT8 M (X.n 0 - 160) = 0x8005e668#64

theorem smb_m4 (X : FCx) (hX : Ok X) :
    Agree (fun a => Rng (X.n 0 - 160) 8 a ∨ StdoutW a) X.m (Lua.Vm.AtF.Smakebuf_r.m4 X) ∧
      SmbM4 (Lua.Vm.AtF.Smakebuf_r.m4 X) X := by
  have := hX.sp_lo
  have : stdoutFile = 0x8005e668 := rfl
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rng, StdoutW, not_and, not_or] at ha
    simp only [Lua.Vm.AtF.Smakebuf_r.m4]; fs_off
  all_goals simp only [Lua.Vm.AtF.Smakebuf_r.m4]; fat_rd; try decide

theorem smb_m5 (X : FCx) :
    Agree (Rng (stdoutFile + 16) 2) X.m (Lua.Vm.AtF.Smakebuf_r.m5 X) ∧
      bytesT2 (Lua.Vm.AtF.Smakebuf_r.m5 X) 0x8005e678 = 0x2889#16 := by
  have : stdoutFile = 0x8005e668 := rfl
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [Rng, not_and] at ha
    simp only [Lua.Vm.AtF.Smakebuf_r.m5]; fs_off
  · simp only [Lua.Vm.AtF.Smakebuf_r.m5]; fat_rd; decide

/-! ## The summary -/

/-- **What `__smakebuf_r(_REENT, stdout)` leaves** on the console: the
buffer `buf` from the heap installed (`_p = _bf._base = buf`, `_bf._size =
1024`), `_flags` `0x2889` (`__SMBF | __SLBF | __SNPT` added), htif.c's
tables set up; the heap's shape with `buf`'s chunk in use; written: htif.c's
tables, the allocator's, its frames and those fields of `stdout`. -/
structure SmakebufPost (m m' : Mem) (sp buf brk : Nat) (chunks : List Chunk) (top' brk' : Nat)
    (chunks' : List Chunk) (bins' : Nat → List Nat) : Prop where
  flags : bytesT2 m' (stdoutFile + 16) = 0x2889#16
  p : bytesT8 m' stdoutFile = BitVec.ofNat 64 buf
  base : bytesT8 m' (stdoutFile + 24) = BitVec.ofNat 64 buf
  size : bytesT4 m' (stdoutFile + 32) = 1024#32
  ready : bytesT4 m' symFsReady = 1#32
  console : bytesT4 m' (symFds + 24) = 2#32
  fds : FdsStd m'
  heap : HeapAt (Vsa.Densify.fillZeroMem m') top' brk' chunks' bins'
  brk_le : brk ≤ brk'
  /-- (lane F1-18) `_malloc_r(1024)`'s growth -/
  brk_hi : brk' ≤ brk + 1024 + 16384 + 4096
  lo : heapStart + 16 ≤ buf
  hi : buf + 1024 ≤ brk'
  block : ∃ sz, (⟨buf - 16, sz, true⟩ : Chunk) ∈ chunks' ∧ 1024 + 8 ≤ sz
  fresh : ∀ a, buf ≤ a → a < buf + 1024 → ¬ InUse chunks a
  kept : ∀ c ∈ chunks, c.inuse = true → c ∈ chunks'
  agree : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ Below sp 1184 a ∨ StdoutW a) m m'

/-- The caller's frame `__smakebuf_r`'s calls see (`s0 = _REENT`, `s1` the
caller's or `st_mode`). -/
abbrev smbF (X : FCx) (s1 : BitVec 64) : AbiFrame :=
  ⟨0x8005d1b8#64, s1, X.b 3, X.b 4, X.b 5, X.b 6, X.b 7, X.b 8, X.b 9, X.b 10, X.b 11, X.b 12⟩

/-- The context of `__smakebuf_r`'s roots: `sp`, the buffer, `ra` and the
caller's `s0`-`s11`, the root memory. -/
abbrev smbX (sp buf : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, buf] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] M o

/-- **`__smakebuf_r` up to `_malloc_r`**: the entry, `_fstat_r`, the
`stat`'s mode. -/
theorem smb_pre (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : heapEnd + 32 + 2048 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hfl : bytesT2 m (stdoutFile + 16) = 0x2009#16) (hfile : bytesT2 m (stdoutFile + 18) = 1#16)
    (hrd : bytesT4 m symFsReady = 0#32) :
    Triple (SegSt 0x80049a2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m1, SegSt 0x8002fa34#64 (Lua.Vm.AtF.Smakebuf_r.r5 (smbX sp 0 r f m1 o))
        (ArmPay (Lua.Vm.AtF.Smakebuf_r.m2 (smbX sp 0 r f m1 o)) o) c ∧
        Agree (fun a => Below sp 192 a ∨ FsGlobal a) m m1 ∧ SmbFrame m1 (smbX sp 0 r f m1 o) ∧
        bytesT4 m1 symFsReady = 1#32 ∧ bytesT4 m1 (symFds + 24) = 2#32 ∧ FdsStd m1) := by
  intro c h
  fs_nums
  have hX0 : Ok (smbX sp 0 r f m o) := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  have e0 : (smbX sp 0 r f m o).n 0 = sp := rfl
  simp only [callPre, List.cons_append, List.nil_append] at h
  obtain ⟨c0, s0, h⟩ := smb_run0 (smbX sp 0 r f m o) hX0 hfl hfile c (h.repin (by pins_of h))
  obtain ⟨k0, fr0⟩ := smb_m1 (smbX sp 0 r f m o) hX0
  have hcall : SegSt 0x8003b0e8#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩, ⟨Register.x11, 1#64⟩,
      ⟨Register.x12, BitVec.ofNat 64 (sp - 160 + 24)⟩] (sp - 160) 0x80049a78#64 (smbF (smbX sp 0 r f m o) f.s1))
      (ArmPay (Lua.Vm.AtF.Smakebuf_r.m1 (smbX sp 0 r f m o)) o) c0 := by
    simp only [Lua.Vm.AtF.Smakebuf_r.r2, show (smbX sp 0 r f m o).n 0 - 136 = sp - 160 + 24 by
      show sp - 136 = _; omega] at h
    exact h.repin (by pins_of h)
  obtain ⟨c1, s1, m1, hr1, F⟩ := fstat_sum (sp - 160) 0x80049a78#64 _ _ o (by decide) (by omega) (by omega)
    (by omega) ((k0.b4 fun i _ => by simp only [Below, smbX, FCx.mk', List.getD_cons_zero]; omega).trans hrd) c0 hcall
  have k1 : Agree (fun a => Below sp 192 a ∨ FsGlobal a) m m1 :=
    (k0.trans F.agree).mono fun a ha => by
      rcases ha with h | h | h | h
      · exact .inl (by simp only [Below, smbX, FCx.mk', List.getD_cons_zero] at h ⊢; omega)
      · exact .inr h
      · exact .inl (by simp only [Below] at h ⊢; omega)
      · exact .inl (by simp only [Below, Rng] at h ⊢; omega)
  have fr1 : SmbFrame m1 (smbX sp 0 r f m1 o) := by
    have fr := fr0.congr (M' := m1) (show 160 ≤ (smbX sp 0 r f m o).n 0 by omega) fun a h1 h2 h3 =>
      F.agree a (by rw [e0] at h1 h2 h3; simp only [FsGlobal, Below, Rng, not_or, not_and]; omega)
    exact ⟨fr.fp, fr.ra, fr.s0⟩
  have hX1 : Ok (smbX sp 0 r f m1 o) := ⟨hX0.sp_lo, hX0.sp_hi, hX0.sp_al, hX0.ra⟩
  simp only [wrRet] at hr1
  obtain ⟨c2, s2, h2⟩ := smb_run1 (smbX sp 0 r f m1 o) hX1 fr1.fp
    (by show bytesT4 m1 (sp - 132) = _; rw [show sp - 132 = sp - 160 + 28 by omega]; exact F.mode) c1
    (hr1.repin (by pins_of hr1))
  exact ⟨c2, s0.trans (s1.trans s2), m1, h2, k1, fr1, F.ready, F.console, F.fds⟩


/-- The regions of the set-up, unfolded for `omega` (off the chunks in use). -/
macro "rg_simp" : tactic => `(tactic|
  simp only [FsGlobal, MallocGlobal, Arena, Below, Rng, StdoutW, HeapReads, smbX, FCx.mk', List.getD_cons_zero,
    List.getD_cons_succ, not_or, not_and])

/-- **`__smakebuf_r(_REENT, stdout)`** on the stream `std()` left (`_flags`
`__SORD | __SWR | __SLBF`, file 1, htif.c's tables before `fs_init`), given
`_malloc_r`'s summary. -/
theorem smakebuf_sum (hM : MallocR_Statement) (sp top brk : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : heapEnd + 32 + 2048 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hfl : bytesT2 m (stdoutFile + 16) = 0x2009#16) (hfile : bytesT2 m (stdoutFile + 18) = 1#16)
    (hrd : bytesT4 m symFsReady = 0#32) (hheap : HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins)
    (hroom : brk + 1024 + 16384 ≤ heapEnd) :
    Triple (SegSt 0x80049a2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' buf top' brk' chunks' bins', voidRet r sp f m' o c ∧
        SmakebufPost m m' sp buf brk chunks top' brk' chunks' bins') := by
  have q3 : heapEnd + 1024 ≤ sp - 160 := by have := hlo; generalize heapEnd = H at *; omega
  intro c h
  obtain ⟨c1, s1, m1, h, k1, fr1, rdy, con, fds⟩ := smb_pre sp r f m o hra hlo hhi hal hfl hfile hrd c h
  fs_nums
  have hX1 : Ok (smbX sp 0 r f m1 o) := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  obtain ⟨k2, fp2, s12⟩ := smb_m2 _ hX1
  have k2' : Agree (fun a => Rng (sp - 24) 8 a ∨ Rng (sp - 160) 8 a) m1
      (Lua.Vm.AtF.Smakebuf_r.m2 (smbX sp 0 r f m1 o)) := k2
  have k12 := k1.trans k2'
  -- `_malloc_r(_REENT, 1024)`
  have hH : HeapAt (Vsa.Densify.fillZeroMem (Lua.Vm.AtF.Smakebuf_r.m2 (smbX sp 0 r f m1 o))) top brk chunks bins :=
    hheap.congr fun a ha => fill_congr <| k12.get (by simp only [HeapReads] at ha; rg_simp; omega)
  have hcall : SegSt 0x8002fa34#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 1024⟩] (sp - 160) 0x80049a98#64 (smbF (smbX sp 0 r f m1 o) 0x2000#64))
      (ArmPay (Lua.Vm.AtF.Smakebuf_r.m2 (smbX sp 0 r f m1 o)) o) c1 := by
    simp only [Lua.Vm.AtF.Smakebuf_r.r5, show (smbX sp 0 r f m1 o).n 0 - 160 = sp - 160 from rfl] at h
    exact h.repin (by pins_of h)
  obtain ⟨c2, s2, m2, buf, top', brk', chunks', bins', hr2, P⟩ :=
    hM (sp - 160) 1024 top brk chunks bins 0x80049a98#64 _ _ o hH (by decide) (by omega) (by omega) q3
      (by decide) hroom c1 hcall
  have hb0 := P.lo; have hb1 := P.hi; have hb2 := P.heap.brk_le
  have kc : Agree (fun a => MallocGlobal a ∨ Arena a ∨ Below (sp - 160) 1024 a)
      (Lua.Vm.AtF.Smakebuf_r.m2 (smbX sp 0 r f m1 o)) m2 :=
    P.agree.mono fun a ha => by
      rcases ha with hw | hb
      · rcases hw.coarse with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr hb)
  have k3 := k12.trans kc
  -- root 2: the buffer installed, `_isatty_r`
  let X2 := smbX sp buf r f m2 o
  have hX2 : Ok X2 := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  simp only [wrRet] at hr2
  obtain ⟨c3, s3, h3⟩ := smb_run2 X2 hX2
    ((k3.b2 (a := 0x8005e678) fun i _ => by rg_simp; omega).trans hfl)
    ((k3.b2 (a := 0x8005e67a) fun i _ => by rg_simp; omega).trans hfile)
    ((kc.b8 (a := sp - 160) fun i _ => by rg_simp; omega).trans fp2)
    (by show buf ≠ 0; omega)
    (by rw [show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by show buf < 2 ^ 64; omega) (by decide)]
        simp only [decide_eq_false_iff_not]; show buf ≠ 0; omega)
    c2 (hr2.repin (by pins_of hr2))
  obtain ⟨k4, M4⟩ := smb_m4 X2 hX2
  have k4' : Agree (fun a => Rng (sp - 160) 8 a ∨ StdoutW a) m2 (Lua.Vm.AtF.Smakebuf_r.m4 X2) := k4
  have km := (k2'.trans kc).trans k4'
  have hcall3 : SegSt 0x8004a170#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩, ⟨Register.x11, 1#64⟩]
      (sp - 160) 0x80049adc#64 (smbF X2 0x2000#64)) (ArmPay (Lua.Vm.AtF.Smakebuf_r.m4 X2) o) c3 := by
    simp only [Lua.Vm.AtF.Smakebuf_r.r8, show X2.n 0 - 160 = sp - 160 from rfl] at h3
    exact h3.repin (by pins_of h3)
  obtain ⟨c4, s4, m3, hr3, k5⟩ := isatty_sum (sp - 160) 0x80049adc#64 (smbF X2 0x2000#64) _ o (by decide)
    (by omega) (by omega) (by omega)
    ((km.b4 fun i _ => by rg_simp; omega).trans rdy) ((km.b4 fun i _ => by rg_simp; omega).trans con)
    c3 hcall3
  -- root 3: the flags, the epilogue
  let X3 := smbX sp buf r f m3 o
  have hX3 : Ok X3 := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  simp only [wrRet] at hr3
  have kn := km.trans k5
  have fr : SmbFrame m3 (smbX sp 0 r f m1 o) :=
    ⟨(k5.b8 (a := sp - 160) fun i _ => by rg_simp; omega).trans M4.fp,
     (kn.b8 (a := sp - 8) fun i _ => by rg_simp; omega).trans fr1.ra,
     (kn.b8 (a := sp - 16) fun i _ => by rg_simp; omega).trans fr1.s0⟩
  obtain ⟨c5, s5, h5⟩ := smb_run3 X3 hX3 fr.fp
    ((k5.b2 (a := 0x8005e678) fun i _ => by rg_simp; omega).trans M4.flags)
    (((k4'.trans k5).b8 (a := sp - 24) fun i _ => by rg_simp; omega).trans
      ((kc.b8 (a := sp - 24) fun i _ => by rg_simp; omega).trans s12))
    fr.ra fr.s0 c4 (hr3.repin (by pins_of hr3))
  obtain ⟨k6, fl⟩ := smb_m5 X3
  have kS := k5.trans k6
  refine ⟨_, s1.trans (s2.trans (s3.trans (s4.trans s5))), Lua.Vm.AtF.Smakebuf_r.m5 X3, buf, top', brk', chunks',
    bins', h5.repin (by pins_of h5), ⟨fl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, P.brk_le, P.brk_hi, P.lo, P.hi, P.block, P.fresh, P.kept, ?_⟩⟩
  · exact (kS.b8 (a := 0x8005e668) fun i _ => by rg_simp; omega).trans M4.p
  · exact (kS.b8 (a := 0x8005e680) fun i _ => by rg_simp; omega).trans M4.base
  · exact (kS.b4 (a := 0x8005e688) fun i _ => by rg_simp; omega).trans M4.size
  · exact ((kn.trans k6).b4 fun i _ => by rg_simp; omega).trans rdy
  · exact ((kn.trans k6).b4 fun i _ => by rg_simp; omega).trans con
  · exact fds.congrT fun a h1 h2 => (kn.trans k6).t1 (by rg_simp; omega)
  · exact P.heap.congr fun a ha => fill_congr <| ((k4'.trans k5).trans k6).get (by simp only [HeapReads] at ha; rg_simp; omega)
  · intro a ha
    by_cases hw : MallocW chunks a
    · exact absurd (.inr (.inl hw)) ha
    · have kf := (((k1.trans k2').trans P.agree).trans ((k4'.trans k5).trans k6))
      refine kf a fun hr => ha ?_
      simp only [hw, false_or, or_false] at hr ⊢
      simp only [FsGlobal, Below, Rng, StdoutW, smbX, FCx.mk', List.getD_cons_zero] at hr ⊢
      omega

end Lua.Vm.Sim.Kit
