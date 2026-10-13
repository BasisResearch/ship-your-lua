import Lua.Vm.Sim.Kit.Swsetup
import Lua.Vm.Sim.Kit.Sfvwrite
import Lua.Vm.AtF.SfvwriteSetup

/-!
# `__sfvwrite_r` at the first write (lane F1-10)

On the stream `std()` and `_fwrite_r`'s `ORIENT` left (`StdoutFresh`):
`cantwrite` → `__swsetup_r` (`swsetup_sum`), then the line-buffered entry up
to the first `memchr` (`Lua/Vm/AtF/SfvwriteSetup.lean`, two roots), where the
run's invariant `SfvSt` holds over the memory after the set-up and the loop
of `Kit/Sfvwrite.lean` takes over (`sfv_mc`, `seg_loop`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (Config Steps)

/-! ## Reads of different widths -/

theorem b4_of_b2s {m : Mem} {a : Nat} {x y : BitVec 16} (hx : bytesT2 m a = x)
    (hy : bytesT2 m (a + 2) = y) : bytesT4 m a = y ++ x := by
  subst hx hy
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bytesT2, bytesT4, BitVec.append_eq, BitVec.getLsbD_append, show a + 2 + 1 = a + 3 by omega]
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) := by omega
  rcases this with h | h | h | h <;> simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> congr 1 <;> omega

theorem b8_of_b4s {m : Mem} {a : Nat} {x y : BitVec 32} (hx : bytesT4 m a = x)
    (hy : bytesT4 m (a + 4) = y) : bytesT8 m a = y ++ x := by
  subst hx hy
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bytesT4, bytesT8, BitVec.append_eq, BitVec.getLsbD_append, show a + 4 + 1 = a + 5 by omega,
    show a + 4 + 2 = a + 6 by omega, show a + 4 + 3 = a + 7 by omega]
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨
    (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases this with h | h | h | h | h | h | h | h <;> simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    congr 1 <;> omega

theorem b2_hi_of_b4 {m : Mem} {a : Nat} {x : BitVec 32} (h : bytesT4 m a = x) :
    bytesT2 m (a + 2) = x.extractLsb' 16 16 := by
  subst h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bytesT2, bytesT4, BitVec.append_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    show a + 2 + 1 = a + 3 by omega]
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) := by omega
  rcases this with h | h <;> simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_true, Bool.true_and, hi] <;>
    congr 1 <;> omega

/-! ## The stream before its set-up -/

/-- **`stdout` as `std()` and `_fwrite_r`'s `ORIENT` leave it** (`__sinit`
ran; `_flags` `__SORD | __SWR | __SLBF`, file 1, no buffer), htif.c's tables
before `fs_init`. -/
structure StdoutFresh (m : Mem) : Prop where
  impure : bytesT8 m symImpurePtr = BitVec.ofNat 64 symImpureData
  cleanup : bytesT8 m (symImpureData + reentCleanupOff) = BitVec.ofNat 64 symCleanupStdio
  flags : bytesT2 m (stdoutFile + 16) = 0x2009#16
  file : bytesT2 m (stdoutFile + 18) = 1#16
  pad : bytesT4 m (stdoutFile + 20) = 0#32
  base : bytesT8 m (stdoutFile + 24) = 0#64
  cookie : bytesT8 m (stdoutFile + 48) = BitVec.ofNat 64 stdoutFile
  write : bytesT8 m (stdoutFile + 64) = BitVec.ofNat 64 symSwrite
  flags2 : bytesT4 m (stdoutFile + 176) = 0#32
  fs : bytesT4 m symFsReady = 0#32

theorem StdoutFresh.flags8 {m : Mem} (h : StdoutFresh m) : bytesT8 m (stdoutFile + 16) = 0x12009#64 := by
  rw [b8_of_b4s (b4_of_b2s h.flags h.file) h.pad]; decide

/-- The run's atoms: `sp`, uio, iov, `n`, `src`; `ra` and the caller's frame. -/
abbrev sfsX (sp U I n src : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, U, I, n, src] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] M o

theorem sfs_run0 (X : FCx) (hX : Lua.Vm.AtF.SfvwriteSetup.Ok X)
    (hc0 : bytesT8 X.m (X.n 1 + 16) = BitVec.ofNat 64 (X.n 3)) (hc1 : bytesT2 X.m 0x8005e678 = 0x2009#16)
    (hc2 : bytesT8 X.m 0x8005e680 = 0x0#64) (hf1 : X.n 3 ≠ 0)
    (hg_2 : (BitVec.ofNat 64 (X.n 3) == 0x0#64) = false) :
    Triple (SegSt 0x80033b50#64 (Lua.Vm.AtF.SfvwriteSetup.r0 X) (ArmPay X.m X.o))
      (SegSt 0x8003587c#64 (Lua.Vm.AtF.SfvwriteSetup.r4 X) (ArmPay (Lua.Vm.AtF.SfvwriteSetup.m0 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.SfvwriteSetup h acc until [0x8003587c]
  exact ⟨_, acc, h⟩

theorem sfs_run1 (X : FCx) (hX : Lua.Vm.AtF.SfvwriteSetup.Ok X) (hc3 : bytesT2 X.m 0x8005e678 = 0x2889#16)
    (hc4 : bytesT8 X.m (X.n 1) = BitVec.ofNat 64 (X.n 2)) (hc5 : bytesT8 X.m (X.n 2 + 8) = BitVec.ofNat 64 (X.n 3))
    (hc6 : bytesT8 X.m (X.n 2) = BitVec.ofNat 64 (X.n 4)) (hf1 : X.n 3 ≠ 0)
    (hg_4 : (BitVec.ofNat 64 (X.n 3) == 0x0#64) = false) :
    Triple (SegSt 0x80033c38#64 (Lua.Vm.AtF.SfvwriteSetup.r5 X) (ArmPay X.m X.o))
      (SegSt 0x800360d8#64 (Lua.Vm.AtF.SfvwriteSetup.r7 X) (ArmPay (Lua.Vm.AtF.SfvwriteSetup.m2 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.SfvwriteSetup h acc until [0x800360d8]
  exact ⟨_, acc, h⟩

/-- The entry root's stores: `ra`, `s0`, `s4`, `s5` saved. -/
theorem sfs_m0 (X : FCx) (hX : Lua.Vm.AtF.SfvwriteSetup.Ok X) :
    Agree (fun a => Rng (X.n 0 - 56) 16 a ∨ Rng (X.n 0 - 16) 16 a) X.m (Lua.Vm.AtF.SfvwriteSetup.m0 X) ∧
      bytesT8 (Lua.Vm.AtF.SfvwriteSetup.m0 X) (X.n 0 - 8) = X.b 0 ∧
      bytesT8 (Lua.Vm.AtF.SfvwriteSetup.m0 X) (X.n 0 - 16) = X.b 1 ∧
      bytesT8 (Lua.Vm.AtF.SfvwriteSetup.m0 X) (X.n 0 - 48) = X.b 5 ∧
      bytesT8 (Lua.Vm.AtF.SfvwriteSetup.m0 X) (X.n 0 - 56) = X.b 6 := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.SfvwriteSetup.m0]; fs_off
  all_goals simp only [Lua.Vm.AtF.SfvwriteSetup.m0]; fat_rd

/-- Root 1's stores: `s1`-`s3`, `s6`-`s9` saved. -/
structure SfsM2 (M : Mem) (X : FCx) : Prop where
  s1 : bytesT8 M (X.n 0 - 24) = X.b 2
  s2 : bytesT8 M (X.n 0 - 32) = X.b 3
  s3 : bytesT8 M (X.n 0 - 40) = X.b 4
  s6 : bytesT8 M (X.n 0 - 64) = X.b 7
  s7 : bytesT8 M (X.n 0 - 72) = X.b 8
  s8 : bytesT8 M (X.n 0 - 80) = X.b 9
  s9 : bytesT8 M (X.n 0 - 88) = X.b 10

theorem sfs_m2 (X : FCx) (hX : Lua.Vm.AtF.SfvwriteSetup.Ok X) :
    Agree (fun a => Rng (X.n 0 - 88) 24 a ∨ Rng (X.n 0 - 64) 8 a ∨ Rng (X.n 0 - 40) 24 a) X.m
      (Lua.Vm.AtF.SfvwriteSetup.m2 X) ∧ SfsM2 (Lua.Vm.AtF.SfvwriteSetup.m2 X) X := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.SfvwriteSetup.m2]; fs_off
  all_goals simp only [Lua.Vm.AtF.SfvwriteSetup.m2]; fat_rd


/-- A read off a region of the set-up, by `omega` (the chunks in use coarsened). -/
macro "sfr" : tactic => `(tactic| (
  simp only [FsGlobal, MallocGlobal, Arena, Below, Rng, StdoutW, not_or, not_and]; omega))

/-- **What the set-up leaves at the first `memchr`**: `stdout` set up and
empty, the frame saved, `uio_resid`, the heap block, the region written. -/
structure SfsMid (m M : Mem) (sp U n buf brk : Nat) (r : BitVec 64) (f : AbiFrame) (chunks : List Chunk)
    (top' brk' : Nat) (chunks' : List Chunk) (bins' : Nat → List Nat) : Prop where
  stdout : StdoutAt M buf []
  up : StdioUp M
  frame : SfvFrame ⟨sp, buf, U, 0, 0, n, [], r, f, M, #[]⟩ M
  res : bytesT8 M (U + 16) = BitVec.ofNat 64 n
  grant : HeapGrant chunks 1024 buf brk M top' brk' chunks' bins'
  agree : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ Below sp 1312 a ∨ StdoutW a) m M

/-- **`__sfvwrite_r` at the first write, up to its first `memchr`**: the
entry, `__swsetup_r`, the line-buffered entry. -/
theorem sfs_pre (hM : MallocR_Statement) (sp U I src n top brk : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : heapEnd + 32 + 2048 + 32 + 96 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : StdoutFresh m) (hheap : HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins) (hroom : brk + 1024 + 16384 ≤ heapEnd)
    (hio : SfvUio m U I src n) (hi : sp ≤ I) (hiu : I + 16 ≤ U) (huh : U + 24 ≤ sp + 2048)
    (hut : U + 24 ≤ 2 ^ 32) (hua : U % 8 = 0) (hia : I % 8 = 0) (hn : 1 ≤ n) (hnb : n < 2 ^ 32) :
    Triple (SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 U⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M buf top' brk' chunks' bins',
        SegSt 0x800360d8#64 (Lua.Vm.AtF.SfvwriteSetup.r7 (sfsX sp U I n src r f M o)) (ArmPay M o) c ∧
        SfsMid m M sp U n buf brk r f chunks top' brk' chunks' bins') := by
  have q1 : heapEnd + 32 + 2048 + 32 ≤ sp - 96 := by have := hlo; generalize heapEnd = H at *; omega
  have q2 : (sp - 96) % 16 = 0 := by omega
  intro c h
  fs_nums
  stdio_nums
  have : symImpurePtr = 0x8005d398 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  let X0 := sfsX sp U I n src r f m o
  have hX0 : Lua.Vm.AtF.SfvwriteSetup.Ok X0 := by
    constructor <;> (try simp only [X0, sfsX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]) <;>
      first | omega | assumption
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hn0 : n ≠ 0 := by omega
  have hg : (BitVec.ofNat 64 n == 0x0#64) = false := by
    rw [show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]
    simp only [decide_eq_false_iff_not]; exact hn0
  obtain ⟨c0, s0, h0⟩ := sfs_run0 X0 hX0 hio.resid hF.flags hF.base hn0 hg c (h.repin (by pins_of h))
  obtain ⟨k0, ra0, s00, s40, s50⟩ := sfs_m0 X0 hX0
  have k0' : Agree (fun a => Rng (sp - 56) 16 a ∨ Rng (sp - 16) 16 a) m (Lua.Vm.AtF.SfvwriteSetup.m0 X0) := k0
  have hcall : SegSt 0x8003587c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (sp - 96) 0x80033c38#64
      ⟨0x8005e668#64, f.s1, f.s2, f.s3, BitVec.ofNat 64 U, 0x8005d1b8#64, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩)
      (ArmPay (Lua.Vm.AtF.SfvwriteSetup.m0 X0) o) c0 := by
    simp only [Lua.Vm.AtF.SfvwriteSetup.r4, show X0.n 0 - 96 = sp - 96 from rfl] at h0
    exact h0.repin (by pins_of h0)
  obtain ⟨c1, s1, M1, buf, top', brk', chunks', bins', hr1, P⟩ :=
    swsetup_sum hM (sp - 96) top brk chunks bins 0x80033c38#64 _ _ o (by decide) q1 (by omega) q2
      ((k0'.b8 fun i _ => by sfr).trans hF.impure) ((k0'.b8 fun i _ => by sfr).trans hF.cleanup)
      ((k0'.b2 fun i _ => by sfr).trans hF.flags) ((k0'.b2 fun i _ => by sfr).trans hF.file)
      ((k0'.b8 fun i _ => by sfr).trans hF.flags8) ((k0'.b8 fun i _ => by sfr).trans hF.base)
      ((k0'.b4 fun i _ => by sfr).trans hF.fs)
      (hheap.congr fun a ha => fill_congr <| k0'.get (by simp only [HeapReads] at ha; sfr)) hroom c0 hcall
  have hb0 := P.grant.lo; have hb1 := P.grant.hi; have hb2 := P.grant.heap.brk_le
  have hbl : stdoutFile + fileSize ≤ buf := Nat.le_trans (by decide) hb0
  have hbh : buf + 1024 ≤ 2 ^ 32 := Nat.le_trans (Nat.le_trans hb1 hb2) (by decide)
  have Pc : Agree (fun a => FsGlobal a ∨ (MallocGlobal a ∨ Arena a) ∨ Below (sp - 96) 1216 a ∨ StdoutW a)
      (Lua.Vm.AtF.SfvwriteSetup.m0 X0) M1 :=
    P.agree.mono fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h.coarse)
      · exact .inr (.inr h)
  have kk := k0'.trans Pc
  let X1 := sfsX sp U I n src r f M1 o
  have hX1 : Lua.Vm.AtF.SfvwriteSetup.Ok X1 := ⟨hX0.sp_lo, hX0.sp_hi, hX0.sp_al, hX0.ra, hX0.i_ge, hX0.i_u,
    hX0.u_hi, hX0.u_al, hX0.i_al⟩
  simp only [wrRet] at hr1
  obtain ⟨c2, s2, h2⟩ := sfs_run1 X1 hX1 P.set.flags ((kk.b8 (a := U) fun i _ => by sfr).trans hio.iov)
    ((kk.b8 (a := I + 8) fun i _ => by sfr).trans hio.len) ((kk.b8 (a := I) fun i _ => by sfr).trans hio.base) hn0 hg c1
    (hr1.repin (by pins_of hr1))
  obtain ⟨k2, F2⟩ := sfs_m2 X1 hX1
  have k2' : Agree (fun a => Rng (sp - 88) 24 a ∨ Rng (sp - 64) 8 a ∨ Rng (sp - 40) 24 a) M1
      (Lua.Vm.AtF.SfvwriteSetup.m2 X1) := k2
  have k02 := Pc.trans k2'
  have hstd : StdoutAt (Lua.Vm.AtF.SfvwriteSetup.m2 X1) buf [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show bytesT8 _ (stdoutFile + 0) = BitVec.ofNat 64 (buf + 0)
      exact (k2'.b8 (a := stdoutFile + 0) fun i _ => by sfr).trans P.set.p
    · show bytesT4 _ (stdoutFile + 12) = 0#32 - BitVec.ofNat 32 0
      rw [(k2'.b4 (a := stdoutFile + 12) fun i _ => by sfr).trans P.set.w]; decide
    · exact (k2'.b2 (a := stdoutFile + 16) fun i _ => by sfr).trans P.set.flags
    · exact (k02.b2 (a := stdoutFile + 18) fun i _ => by sfr).trans
        ((k0'.b2 (a := stdoutFile + 18) fun i _ => by sfr).trans hF.file)
    · exact (k2'.b8 (a := stdoutFile + 24) fun i _ => by sfr).trans P.set.base
    · exact (k2'.b4 (a := stdoutFile + 32) fun i _ => by sfr).trans P.set.size
    · exact (k2'.b4 (a := stdoutFile + 40) fun i _ => by sfr).trans P.set.lbf
    · exact (k02.b8 (a := stdoutFile + 48) fun i _ => by sfr).trans
        ((k0'.b8 (a := stdoutFile + 48) fun i _ => by sfr).trans hF.cookie)
    · exact (k02.b8 (a := stdoutFile + 64) fun i _ => by sfr).trans
        ((k0'.b8 (a := stdoutFile + 64) fun i _ => by sfr).trans hF.write)
    · rfl
    · simp
    · exact hbl
    · exact hbh
    · rw [(k2'.b4 (a := symFsReady) fun i _ => by sfr).trans P.set.ready]; decide
    · exact (k2'.b4 (a := symFds + 24) fun i _ => by sfr).trans P.set.console
  have hup : StdioUp (Lua.Vm.AtF.SfvwriteSetup.m2 X1) := by
    refine ⟨?_, ?_, ?_⟩
    · exact (k02.b8 (a := symImpurePtr) fun i _ => by sfr).trans
        ((k0'.b8 (a := symImpurePtr) fun i _ => by sfr).trans hF.impure)
    · rw [(k02.b8 (a := symImpureData + reentCleanupOff) fun i _ => by sfr).trans
        ((k0'.b8 (a := symImpureData + reentCleanupOff) fun i _ => by sfr).trans hF.cleanup)]; decide
    · exact (k02.b4 (a := stdoutFile + fileFlags2Off) fun i _ => by sfr).trans
        ((k0'.b4 (a := stdoutFile + fileFlags2Off) fun i _ => by sfr).trans hF.flags2)
  have hfr : SfvFrame ⟨sp, buf, U, 0, 0, n, [], r, f, Lua.Vm.AtF.SfvwriteSetup.m2 X1, #[]⟩
      (Lua.Vm.AtF.SfvwriteSetup.m2 X1) :=
    ⟨(k02.b8 (a := sp - 8) fun i _ => by sfr).trans ra0, (k02.b8 (a := sp - 16) fun i _ => by sfr).trans s00,
     F2.s1, F2.s2, F2.s3, (k02.b8 (a := sp - 48) fun i _ => by sfr).trans s40,
     (k02.b8 (a := sp - 56) fun i _ => by sfr).trans s50, F2.s6, F2.s7, F2.s8, F2.s9⟩
  have hres : bytesT8 (Lua.Vm.AtF.SfvwriteSetup.m2 X1) (U + 16) = BitVec.ofNat 64 n :=
    (k02.b8 (a := U + 16) fun i _ => by sfr).trans ((k0'.b8 (a := U + 16) fun i _ => by sfr).trans hio.resid)
  have hgr : HeapGrant chunks 1024 buf brk (Lua.Vm.AtF.SfvwriteSetup.m2 X1) top' brk' chunks' bins' :=
    ⟨P.grant.heap.congr fun a ha => fill_congr <| k2'.get (by simp only [HeapReads] at ha; sfr), P.grant.brk_le,
      P.grant.lo, P.grant.hi, P.grant.block, P.grant.fresh, P.grant.kept⟩
  have hag : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ Below sp 1312 a ∨ StdoutW a) m
      (Lua.Vm.AtF.SfvwriteSetup.m2 X1) := by
    intro a ha
    by_cases hw : MallocW chunks a
    · exact absurd (.inr (.inl hw)) ha
    · refine ((k0'.trans P.agree).trans k2') a fun hr => ha ?_
      simp only [hw, false_or, or_false] at hr ⊢
      simp only [FsGlobal, Below, Rng, StdoutW] at hr ⊢
      omega
  exact ⟨_, s0.trans (s1.trans s2), Lua.Vm.AtF.SfvwriteSetup.m2 X1, buf, top', brk', chunks', bins',
    h2.repin (by pins_of h2), ⟨hstd, hup, hfr, hres, hgr, hag⟩⟩

/-- **What the first write leaves**: `stdout` set up holding `pend'` with
`out ++ pend' = (the n bytes at src)`; the heap block `buf` (granted at the
set-up's memory `M`, the region the set-up wrote), then the loop's keep. -/
structure FirstWrite (m M m' : Mem) (sp U src n buf brk : Nat) (chunks : List Chunk) (top' brk' : Nat)
    (chunks' : List Chunk) (bins' : Nat → List Nat) (out pend' : List (BitVec 8)) : Prop where
  stdout : StdoutAt m' buf pend'
  up : StdioUp m'
  out : out ++ pend' = bytesAt m src n
  grant : HeapGrant chunks 1024 buf brk M top' brk' chunks' bins'
  agree : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ Below sp 1312 a ∨ StdoutW a) m M
  keep : SfvKeep M m' sp buf U
  src_buf : src + n ≤ buf ∨ buf + 1024 ≤ src

/-- A range no byte of which the allocator may write lies apart from a
fresh block of the arena. -/
theorem apart_of_fresh {chunks : List Chunk} {src n buf k : Nat}
    (hs : ∀ a, src ≤ a → a < src + n → ¬ MallocW chunks a) (hlo : heapStart ≤ buf) (hhi : buf + k ≤ heapEnd)
    (hf : ∀ a, buf ≤ a → a < buf + k → ¬ InUse chunks a) (hk : 0 < k) (hn : 0 < n) :
    src + n ≤ buf ∨ buf + k ≤ src := by
  refine Classical.byContradiction fun hn => ?_
  have h1 : ¬ src + n ≤ buf := fun h => hn (.inl h)
  have h2 : ¬ buf + k ≤ src := fun h => hn (.inr h)
  by_cases hc : src ≤ buf
  · exact hs buf hc (by omega) (.inr ⟨hlo, by omega, hf buf (Nat.le_refl _) (by omega)⟩)
  · exact hs src (Nat.le_refl _) (by omega) (.inr ⟨by omega, by omega, hf src (by omega) (by omega)⟩)

/-- **`__sfvwrite_r(_REENT, stdout, uio)` at the first write** (one iov of
`n ≥ 1` bytes at `src`; `stdout` as `std()` and `ORIENT` left it), given
`_malloc_r`'s summary: the set-up, then the line-buffered loop. -/
theorem sfvwrite_first (hM : MallocR_Statement) (sp U I src n top brk : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : heapEnd + 4096 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hF : StdoutFresh m) (hheap : HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins) (hroom : brk + 1024 + 16384 ≤ heapEnd)
    (hio : SfvUio m U I src n) (hi : sp ≤ I) (hiu : I + 16 ≤ U) (huh : U + 24 ≤ sp + 2048)
    (hut : U + 24 ≤ 2 ^ 32) (hua : U % 8 = 0) (hia : I % 8 = 0) (hn : 1 ≤ n)
    (hsl : errnoAddr + 4 ≤ src) (hsh : src + n + 3072 ≤ sp)
    (hsf : src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src)
    (hsrc : ∀ a, src ≤ a → a < src + n → ¬ FsGlobal a ∧ ¬ MallocW chunks a) :
    Triple (SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 U⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M m' out pend' buf top' brk' chunks' bins', wrRet r sp 0 f m' (pushes o out) c ∧
        FirstWrite m M m' sp U src n buf brk chunks top' brk' chunks' bins' out pend') := by
  have hlo' : heapEnd + 32 + 2048 + 32 + 96 ≤ sp := by
    obtain ⟨H, hH⟩ : ∃ H, heapEnd = H := ⟨_, rfl⟩
    rw [hH] at hlo ⊢; omega
  intro c h
  have hnb : n < 2 ^ 32 := by omega
  obtain ⟨c1, s1, M, buf, top', brk', chunks', bins', h1, mid⟩ :=
    sfs_pre hM sp U I src n top brk chunks bins r f m o hra hlo' hhi hal hF hheap hroom hio hi hiu huh hut hua hia
      hn hnb c h
  have hb0 := mid.grant.lo; have hb1 := mid.grant.hi; have hb2 := mid.grant.heap.brk_le
  have hsb : src + n ≤ buf ∨ buf + 1024 ≤ src :=
    apart_of_fresh (fun a h1 h2 => (hsrc a h1 h2).2) (Nat.le_trans (Nat.le_add_right _ _) hb0) (Nat.le_trans hb1 hb2)
      mid.grant.fresh (by decide) hn
  have hbl : stdoutFile + fileSize ≤ buf := Nat.le_trans (by decide) hb0
  have hbsp : buf + 3584 ≤ sp := by
    have h3 := Nat.le_trans hb1 hb2
    obtain ⟨H, hH⟩ : ∃ H, heapEnd = H := ⟨_, rfl⟩
    rw [hH] at hlo h3; omega
  let G : SfvG := ⟨sp, buf, U, I, src, n, [], r, f, M, o⟩
  have hG : G.Ok := ⟨hra, hhi, hal, hbl, hbsp, hi, hiu, huh, hut, hua, hia, hsl, hsh, hsb, hsf⟩
  let X1 := sfsX sp U I n src r f M o
  have hX : SfvAt G X1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have st : SfvStA G M o [] (src - G.src) :=
    ⟨mid.stdout, mid.up, ⟨[], rfl, by simp [bytesAt, G]⟩,
      ⟨mid.frame.ra, mid.frame.s0, mid.frame.s1, mid.frame.s2, mid.frame.s3, mid.frame.s4, mid.frame.s5,
        mid.frame.s6, mid.frame.s7, mid.frame.s8, mid.frame.s9⟩,
      ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩, by simp [G]⟩
  have hcall : SegSt 0x800360d8#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, 0xa#64⟩,
      ⟨Register.x12, BitVec.ofNat 64 n⟩] (G.sp - 96) 0x80033e4c#64
      (sfvF X1 f.s2 f.s3 f.s6 (BitVec.ofNat 64 n) 0x0#64 (BitVec.ofNat 64 src))) (ArmPay M o) c1 := by
    simp only [Lua.Vm.AtF.SfvwriteSetup.r7, show X1.n 0 - 96 = sp - 96 from rfl] at h1
    exact h1.repin (by pins_of h1)
  obtain ⟨c2, s2, h2⟩ := sfv_mc (μ0 := 2 * n + 2) hG hX st mid.res (by simp [G]) (by simp [G]) hn
    (by simp) hcall
  have post : ∃ c3, Steps c2 c3 ∧ SfvPost G c3 := by
    rcases h2 with ⟨a, _, hl⟩ | hpost
    · exact seg_loop (S := SfvLoop G) (X := SfvPost G) sfvMu (fun a => sfv_turn hG a) a c2 hl
    · exact ⟨c2, Steps.refl _, hpost⟩
  obtain ⟨c3, s3, m', out, pend', hret, hs, hu, ho, hk⟩ := post
  refine ⟨c3, s1.trans (s2.trans s3), M, m', out, pend', buf, top', brk', chunks', bins', hret,
    ⟨hs, hu, ?_, mid.grant, mid.agree, hk, hsb⟩⟩
  rw [ho]
  show [] ++ bytesAt M src n = bytesAt m src n
  rw [List.nil_append]
  refine bytesAt_congr fun i hi => ?_
  have hx := hsrc (src + i) (by omega) (by omega)
  simp only [bytesT1]
  rw [mid.agree (src + i) fun hr => by
    rcases hr with h | h | h | h
    · exact hx.1 h
    · exact hx.2 h
    · simp only [Below] at h; omega
    · simp only [StdoutW, Rng] at h; have : fileSize = 184 := rfl; have : stdoutFile = 0x8005e668 := rfl; omega]

end Lua.Vm.Sim.Kit
