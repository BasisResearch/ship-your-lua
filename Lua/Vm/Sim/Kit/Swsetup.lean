import Lua.Vm.Sim.Kit.Smakebuf
import Lua.Vm.AtF.Swsetup_r

/-!
# `__swsetup_r(_REENT, stdout)` (lane F1-10)

`__sfvwrite_r`'s `cantwrite` on the stream `std()` left: writable, no
buffer, so `__smakebuf_r` (`smakebuf_sum`), then the line-buffered set-up
(`_w = 0`, `_lbfsize = -1024`). Two roots (`Lua/Vm/AtF/Swsetup_r.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (Config Steps)

/-- **A heap block granted**: `buf`'s chunk of the new heap in use, fresh,
inside the arena below the new break; the chunks in use kept. -/
structure HeapGrant (chunks : List Chunk) (n buf brk : Nat) (m' : Mem) (top' brk' : Nat) (chunks' : List Chunk)
    (bins' : Nat → List Nat) : Prop where
  heap : HeapAt m' top' brk' chunks' bins'
  brk_le : brk ≤ brk'
  lo : heapStart + 16 ≤ buf
  hi : buf + n ≤ brk'
  block : ∃ sz, (⟨buf - 16, sz, true⟩ : Chunk) ∈ chunks' ∧ n + 8 ≤ sz
  fresh : ∀ a, buf ≤ a → a < buf + n → ¬ InUse chunks a
  kept : ∀ c ∈ chunks, c.inuse = true → c ∈ chunks'

/-- **`stdout` set up, empty** (what `__swsetup_r` leaves): line-buffered on
the heap buffer `buf`, `_w = 0`, `_lbfsize = -1024`; htif.c's tables set up. -/
structure StdoutSet (m : Mem) (buf : Nat) : Prop where
  flags : bytesT2 m (stdoutFile + 16) = 0x2889#16
  p : bytesT8 m stdoutFile = BitVec.ofNat 64 buf
  w : bytesT4 m (stdoutFile + 12) = 0#32
  base : bytesT8 m (stdoutFile + 24) = BitVec.ofNat 64 buf
  size : bytesT4 m (stdoutFile + 32) = 1024#32
  lbf : bytesT4 m (stdoutFile + 40) = 0#32 - 1024#32
  ready : bytesT4 m symFsReady = 1#32
  console : bytesT4 m (symFds + 24) = 2#32

/-- What `__swsetup_r` leaves. -/
structure SwsetupPost (m m' : Mem) (sp buf brk : Nat) (chunks : List Chunk) (top' brk' : Nat)
    (chunks' : List Chunk) (bins' : Nat → List Nat) : Prop where
  set : StdoutSet m' buf
  grant : HeapGrant chunks 1024 buf brk m' top' brk' chunks' bins'
  agree : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ Below sp 1216 a ∨ StdoutW a) m m'

theorem sws_run0 (X : FCx) (hX : Lua.Vm.AtF.Swsetup_r.Ok X) (hc0 : bytesT8 X.m 0x8005d398 = 0x8005d1b8#64)
    (hc1 : bytesT8 X.m 0x8005d200 = 0x80032b0c#64) (hc2 : bytesT2 X.m 0x8005e678 = 0x2009#16)
    (hc3 : bytesT8 X.m 0x8005e680 = 0x0#64) (hc4 : bytesT8 X.m 0x8005e678 = 0x12009#64) :
    Triple (SegSt 0x8003587c#64 (Lua.Vm.AtF.Swsetup_r.r0 X) (ArmPay X.m X.o))
      (SegSt 0x80049a2c#64 (Lua.Vm.AtF.Swsetup_r.r2 X) (ArmPay (Lua.Vm.AtF.Swsetup_r.m1 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Swsetup_r h acc until [0x80049a2c]
  exact ⟨_, acc, h⟩

theorem sws_run1 (X : FCx) (hX : Lua.Vm.AtF.Swsetup_r.Ok X) (hc5 : bytesT8 X.m (X.n 0 - 32) = 0x8005e668#64)
    (hc6 : bytesT2 X.m 0x8005e678 = 0x2889#16) (hc7 : bytesT4 X.m 0x8005e688 = 0x400#32)
    (hc8 : bytesT8 X.m (X.n 0 - 8) = X.b 0) (hg_6 : (bytesT8 X.m (0x8005e680) == 0x0#64) = false) :
    Triple (SegSt 0x80035920#64 (Lua.Vm.AtF.Swsetup_r.r3 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.Swsetup_r.r5 X) (ArmPay (Lua.Vm.AtF.Swsetup_r.m2 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Swsetup_r h acc
  exact ⟨_, acc, h⟩

theorem sws_m1 (X : FCx) (hX : Lua.Vm.AtF.Swsetup_r.Ok X) :
    Agree (fun a => Rng (X.n 0 - 8) 8 a ∨ Rng (X.n 0 - 32) 8 a) X.m (Lua.Vm.AtF.Swsetup_r.m1 X) ∧
      bytesT8 (Lua.Vm.AtF.Swsetup_r.m1 X) (X.n 0 - 32) = 0x8005e668#64 ∧
      bytesT8 (Lua.Vm.AtF.Swsetup_r.m1 X) (X.n 0 - 8) = X.b 0 := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.Swsetup_r.m1]; fs_off
  all_goals simp only [Lua.Vm.AtF.Swsetup_r.m1]; fat_rd

theorem sws_m2 (X : FCx) :
    Agree (fun a => Rng (stdoutFile + 12) 4 a ∨ Rng (stdoutFile + 40) 4 a) X.m (Lua.Vm.AtF.Swsetup_r.m2 X) ∧
      bytesT4 (Lua.Vm.AtF.Swsetup_r.m2 X) 0x8005e674 = 0#32 ∧
      bytesT4 (Lua.Vm.AtF.Swsetup_r.m2 X) 0x8005e690 = 0#32 - 1024#32 := by
  have : stdoutFile = 0x8005e668 := rfl
  refine ⟨fun a ha => ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.Swsetup_r.m2]; fs_off
  all_goals simp only [Lua.Vm.AtF.Swsetup_r.m2]; fat_rd; decide

/-- **`__swsetup_r(_REENT, stdout)`** after `__sinit` on `std()`'s `stdout`
(`_flags` `__SORD | __SWR | __SLBF`, file 1, no buffer; htif.c's tables
before `fs_init`): `0` returned, `stdout` set up (`StdoutSet`), given
`_malloc_r`'s summary. -/
theorem swsetup_sum (hM : MallocR_Statement) (sp top brk : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : heapEnd + 32 + 2048 + 32 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (himp : bytesT8 m symImpurePtr = BitVec.ofNat 64 symImpureData)
    (hcl : bytesT8 m (symImpureData + reentCleanupOff) = BitVec.ofNat 64 symCleanupStdio)
    (hfl : bytesT2 m (stdoutFile + 16) = 0x2009#16) (hfile : bytesT2 m (stdoutFile + 18) = 1#16)
    (hfl8 : bytesT8 m (stdoutFile + 16) = 0x12009#64) (hbase : bytesT8 m (stdoutFile + 24) = 0#64)
    (hrd : bytesT4 m symFsReady = 0#32) (hheap : HeapAt m top brk chunks bins)
    (hroom : brk + 1024 + 16384 ≤ heapEnd) :
    Triple (SegSt 0x8003587c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' buf top' brk' chunks' bins', wrRet r sp 0 f m' o c ∧
        SwsetupPost m m' sp buf brk chunks top' brk' chunks' bins') := by
  intro c h
  fs_nums
  have hX0 : Lua.Vm.AtF.Swsetup_r.Ok (smbX sp 0 r f m o) := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  obtain ⟨c0, s0, h⟩ := sws_run0 (smbX sp 0 r f m o) hX0 himp hcl hfl hbase hfl8 c (h.repin (by pins_of h))
  obtain ⟨k1, fp1, ra1⟩ := sws_m1 (smbX sp 0 r f m o) hX0
  have k1' : Agree (fun a => Rng (sp - 8) 8 a ∨ Rng (sp - 32) 8 a) m (Lua.Vm.AtF.Swsetup_r.m1 (smbX sp 0 r f m o)) :=
    k1
  have hcall : SegSt 0x80049a2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (sp - 32) 0x80035920#64 f)
      (ArmPay (Lua.Vm.AtF.Swsetup_r.m1 (smbX sp 0 r f m o)) o) c0 := by
    simp only [Lua.Vm.AtF.Swsetup_r.r2, show (smbX sp 0 r f m o).n 0 - 32 = sp - 32 from rfl] at h
    exact h.repin (by pins_of h)
  have nk : ∀ a, (a + 32 < sp ∨ sp ≤ a) → (Lua.Vm.AtF.Swsetup_r.m1 (smbX sp 0 r f m o))[a]? = m[a]? :=
    fun a ha => k1' a (by simp only [Rng, not_or, not_and]; omega)
  obtain ⟨c1, s1, m1, buf, top', brk', chunks', bins', hr1, P⟩ :=
    smakebuf_sum hM (sp - 32) top brk chunks bins 0x80035920#64 f _ o (by decide) (by omega) (by omega)
      (by omega) ((AtF.bT2_congr fun i _ => nk _ (by omega)).trans hfl)
      ((AtF.bT2_congr fun i _ => nk _ (by omega)).trans hfile)
      ((AtF.bT4_congr fun i _ => nk _ (by omega)).trans hrd)
      (hheap.congr fun a ha => k1'.get (by simp only [HeapReads] at ha; rg_simp; omega)) hroom c0 hcall
  have hb0 := P.lo; have hb1 := P.hi; have hb2 := P.heap.brk_le
  let X1 := smbX sp buf r f m1 o
  have hX1 : Lua.Vm.AtF.Swsetup_r.Ok X1 := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  have kq : ∀ a, sp - 32 ≤ a → a < sp → m1[a]? = (Lua.Vm.AtF.Swsetup_r.m1 (smbX sp 0 r f m o))[a]? := by
    intro a h1 h2
    by_cases hw : MallocW chunks a
    · exact absurd (hw.coarse) (by simp only [MallocGlobal, Arena]; omega)
    · exact P.agree a (by simp only [hw, false_or]; simp only [FsGlobal, Below, Rng, StdoutW]; omega)
  simp only [voidRet] at hr1
  obtain ⟨c2, s2, h2⟩ := sws_run1 X1 hX1
    ((AtF.bT8_congr (x := sp - 32) fun i _ => kq _ (by omega) (by omega)).trans fp1) P.flags P.size
    ((AtF.bT8_congr (x := sp - 8) fun i _ => kq _ (by omega) (by omega)).trans ra1)
    (by rw [show (0x8005e680 : Nat) = stdoutFile + 24 from rfl, P.base,
          show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]
        simp only [decide_eq_false_iff_not]; omega)
    c1 (hr1.repin (by pins_of hr1))
  obtain ⟨k2, w2, l2⟩ := sws_m2 X1
  refine ⟨_, s0.trans (s1.trans s2), Lua.Vm.AtF.Swsetup_r.m2 X1, buf, top', brk', chunks', bins',
    h2.repin (by pins_of h2), ⟨⟨?_, ?_, w2, ?_, ?_, l2, ?_, ?_⟩, ⟨?_, P.brk_le, P.lo, by omega, ?_, P.fresh, P.kept⟩, ?_⟩⟩
  · exact (k2.b2 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.flags
  · exact (k2.b8 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.p
  · exact (k2.b8 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.base
  · exact (k2.b4 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.size
  · exact (k2.b4 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.ready
  · exact (k2.b4 fun i _ => by simp only [Rng, not_or, not_and]; omega).trans P.console
  · exact P.heap.congr fun a ha => k2.get (by simp only [HeapReads] at ha; simp only [Rng, not_or, not_and]; omega)
  · obtain ⟨sz, h1, h2⟩ := P.block; exact ⟨sz, h1, by omega⟩
  · intro a ha
    by_cases hw : MallocW chunks a
    · exact absurd (.inr (.inl hw)) ha
    · refine ((k1'.trans P.agree).trans k2) a fun hr => ha ?_
      simp only [hw, false_or, or_false] at hr ⊢
      simp only [FsGlobal, Below, Rng, StdoutW] at hr ⊢
      omega

end Lua.Vm.Sim.Kit
