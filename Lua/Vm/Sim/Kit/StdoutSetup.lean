import Lua.Vm.Sim.Kit.SfvFirst
import Lua.Vm.Sim.Kit.Fwrite
import Lua.Vm.AtF.FwriteSetup

/-!
# The first `fwrite` from the boot state (lane F1-10)

`fwrite(src, 1, n, stdout)` → `_fwrite_r` at the first write: `CHECK_INIT`
calls `__sinit` (`sinit_boot`), then the lock and `ORIENT`, then
`__sfvwrite_r` (`sfvwrite_first`: `__swsetup_r` → `__smakebuf_r` →
`_fstat_r`, `_malloc_r`, `_isatty_r`; the line-buffered loop), then the
unlock. Three roots (`Lua/Vm/AtF/FwriteSetup.lean`). `StdoutSetup_Statement`
follows from `MallocR_Statement` (`stdoutSetup_of_malloc`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (Config Steps)

theorem b2_lo_of_b4 {m : Mem} {a : Nat} {x : BitVec 32} (h : bytesT4 m a = x) :
    bytesT2 m a = x.extractLsb' 0 16 := by
  subst h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [bytesT2, bytesT4, BitVec.append_eq, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have : i < 8 ∨ (8 ≤ i ∧ i < 16) := by omega
  rcases this with h | h <;> simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_true, Bool.true_and,
    hi] <;> congr 1 <;> omega

theorem zero_b4 {m : Mem} {a n : Nat} (h : ZeroAt m a n) {x : Nat} (h1 : a ≤ x) (h2 : x + 4 ≤ a + n) :
    bytesT4 m x = 0#32 := by
  have e : ∀ i, i < 4 → m[x + i]? = some 0 := fun i hi => by
    have := h (x + i - a) (by omega); rwa [show a + (x + i - a) = x + i by omega] at this
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega)
  simp only [Nat.add_zero] at e0
  simp only [bytesT4, e0, e1, e2, e3, Option.getD_some]; decide

/-- What `__sinit` writes outside its frame: the three `FILE`s, `__cleanup`,
`__stdio_exit_handler`. -/
def SinitW (a : Nat) : Prop :=
  Rng symSf (3 * fileSize) a ∨ Rng (symImpureData + reentCleanupOff) 8 a ∨ Rng symStdioExitHandler 8 a

/-- The context of `fwrite`'s roots. -/
abbrev fwsX (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, src, n] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] M o

theorem fws_run0 (X : FCx) (hX : Lua.Vm.AtF.FwriteSetup.Ok X) (hc0 : bytesT8 X.m 0x8005d398 = 0x8005d1b8#64)
    (hc1 : bytesT8 X.m 0x8005d200 = 0x0#64) :
    Triple (SegSt 0x800342e4#64 (Lua.Vm.AtF.FwriteSetup.r0 X) (ArmPay X.m X.o))
      (SegSt 0x80032ed0#64 (Lua.Vm.AtF.FwriteSetup.r2 X) (ArmPay (Lua.Vm.AtF.FwriteSetup.m2 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.FwriteSetup h acc until [0x80032ed0]
  exact ⟨_, acc, h⟩

theorem fws_run1 (X : FCx) (hX : Lua.Vm.AtF.FwriteSetup.Ok X)
    (hc2 : bytesT8 X.m (X.n 0 - 104) = BitVec.ofNat 64 (X.n 2)) (hc3 : bytesT4 X.m 0x8005e718 = 0x0#32)
    (hc4 : bytesT2 X.m 0x8005e678 = 0x9#16) :
    Triple (SegSt 0x800342cc#64 (Lua.Vm.AtF.FwriteSetup.r3 X) (ArmPay X.m X.o))
      (SegSt 0x80033b50#64 (Lua.Vm.AtF.FwriteSetup.r5 X) (ArmPay (Lua.Vm.AtF.FwriteSetup.m5 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.FwriteSetup h acc until [0x80033b50]
  exact ⟨_, acc, h⟩

theorem fws_run2 (X : FCx) (hX : Lua.Vm.AtF.FwriteSetup.Ok X)
    (hc2 : bytesT8 X.m (X.n 0 - 104) = BitVec.ofNat 64 (X.n 2)) (hc3 : bytesT4 X.m 0x8005e718 = 0x0#32)
    (hc5 : bytesT2 X.m 0x8005e678 = 0x2889#16) (hc6 : bytesT8 X.m (X.n 0 - 8) = X.b 0)
    (hc7 : bytesT8 X.m (X.n 0 - 16) = X.b 1) (hc8 : bytesT8 X.m (X.n 0 - 24) = X.b 2)
    (hc9 : bytesT8 X.m (X.n 0 - 32) = X.b 3) (hc10 : bytesT8 X.m (X.n 0 - 40) = X.b 4) :
    Triple (SegSt 0x800341f8#64 (Lua.Vm.AtF.FwriteSetup.r6 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.FwriteSetup.r8 X) (ArmPay X.m X.o)) := by
  intro c h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.FwriteSetup h acc
  exact ⟨_, acc, h⟩

/-- The entry root's stores: the frame and the uio in `[sp - 112, sp)`. -/
structure FwsM2 (M : Mem) (X : FCx) : Prop where
  ra : bytesT8 M (X.n 0 - 8) = X.b 0
  s0 : bytesT8 M (X.n 0 - 16) = X.b 1
  s1 : bytesT8 M (X.n 0 - 24) = X.b 2
  s2 : bytesT8 M (X.n 0 - 32) = X.b 3
  s3 : bytesT8 M (X.n 0 - 40) = X.b 4
  resid : bytesT8 M (X.n 0 - 56) = BitVec.ofNat 64 (X.n 2)
  iov : bytesT8 M (X.n 0 - 72) = BitVec.ofNat 64 (X.n 0 - 88)
  len : bytesT8 M (X.n 0 - 80) = BitVec.ofNat 64 (X.n 2)
  base : bytesT8 M (X.n 0 - 88) = BitVec.ofNat 64 (X.n 1)
  n : bytesT8 M (X.n 0 - 104) = BitVec.ofNat 64 (X.n 2)

theorem fws_m2 (X : FCx) (hX : Lua.Vm.AtF.FwriteSetup.Ok X) :
    Agree (Below (X.n 0) 112) X.m (Lua.Vm.AtF.FwriteSetup.m2 X) ∧ FwsM2 (Lua.Vm.AtF.FwriteSetup.m2 X) X := by
  have := hX.sp_lo
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Below, not_and] at ha
    simp only [Lua.Vm.AtF.FwriteSetup.m2]; fs_off
  all_goals simp only [Lua.Vm.AtF.FwriteSetup.m2]; fat_rd

/-- Root 1's stores: `_flags2`, `_flags` (`ORIENT`), the saved `n`. -/
theorem fws_m5 (X : FCx) (hX : Lua.Vm.AtF.FwriteSetup.Ok X) :
    Agree (fun a => Rng (X.n 0 - 104) 8 a ∨ Rng (stdoutFile + 176) 4 a ∨ Rng (stdoutFile + 16) 2 a) X.m
      (Lua.Vm.AtF.FwriteSetup.m5 X) ∧
      bytesT2 (Lua.Vm.AtF.FwriteSetup.m5 X) 0x8005e678 = 0x2009#16 ∧
      bytesT4 (Lua.Vm.AtF.FwriteSetup.m5 X) 0x8005e718 = 0#32 ∧
      bytesT8 (Lua.Vm.AtF.FwriteSetup.m5 X) (X.n 0 - 104) = BitVec.ofNat 64 (X.n 2) := by
  have := hX.sp_lo
  have : stdoutFile = 0x8005e668 := rfl
  refine ⟨fun a ha => ?_, ?_, ?_, ?_⟩
  · simp only [Rng, not_or, not_and] at ha
    simp only [Lua.Vm.AtF.FwriteSetup.m5]; fs_off
  all_goals simp only [Lua.Vm.AtF.FwriteSetup.m5]; fat_rd; try decide


/-- A read off the set-up's regions, by `omega`. -/
macro "ssr" : tactic => `(tactic| (
  simp only [FsGlobal, MallocGlobal, Arena, Below, Rng, StdoutW, SinitW, HeapReads, not_or, not_and]; omega))

/-- **What `_fwrite_r` hands `__sfvwrite_r` at the first write**: `stdout`
fresh, the uio on its stack, its frame. -/
structure FwsMid (m M : Mem) (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (o : Array String) : Prop where
  fresh : StdoutFresh M
  uio : SfvUio M (sp - 72) (sp - 88) src n
  frame : FwsM2 M (fwsX sp src n r f m o)
  agree : Agree (fun a => SinitW a ∨ Below sp 176 a) m M

/-- **`fwrite` at the first write, up to `__sfvwrite_r`**: the entry,
`__sinit`, the lock, `ORIENT`. -/
theorem fws_pre (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e7d8 + 64 + 112 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hB : StdioBoot m) (hfs : bytesT4 m symFsReady = 0#32) :
    Triple (SegSt 0x800342e4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M, SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 (sp - 72)⟩] (sp - 112)
        0x800341f8#64 (fwFrame f n)) (ArmPay M o) c ∧ FwsMid m M sp src n r f o) := by
  intro c h
  fs_nums
  stdio_nums
  have : symImpurePtr = 0x8005d398 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  let X0 := fwsX sp src n r f m o
  have hX0 : Lua.Vm.AtF.FwriteSetup.Ok X0 := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hc0 : bytesT8 X0.m 0x8005d398 = 0x8005d1b8#64 := bytesT8_of_rd64 hB.impure_ptr
  have hc1 : bytesT8 X0.m 0x8005d200 = 0x0#64 := bytesT8_of_rd64 hB.cleanup
  obtain ⟨c0, s0, h0⟩ := fws_run0 X0 hX0 hc0 hc1 c (h.repin (by pins_of h))
  obtain ⟨k2, F2⟩ := fws_m2 X0 hX0
  have k2' : Agree (Below sp 112) m (Lua.Vm.AtF.FwriteSetup.m2 X0) := k2
  have hcall : SegSt 0x80032ed0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩] (sp - 112)
      0x800342cc#64 (fwFrame f n)) (ArmPay (Lua.Vm.AtF.FwriteSetup.m2 X0) o) c0 := by
    simp only [Lua.Vm.AtF.FwriteSetup.r2, show X0.n 0 - 112 = sp - 112 from rfl] at h0
    exact h0.repin (by pins_of h0)
  obtain ⟨c1, s1, m1, hv1, SP⟩ := sinit_boot (sp - 112) 0x800342cc#64 (fwFrame f n) _ o (by decide)
    (by omega) (by omega) (by omega)
    ((k2'.b8 (a := symImpureData + reentCleanupOff) fun i _ => by ssr).trans (bytesT8_of_rd64 hB.cleanup))
    ((k2'.b8 (a := symStdioExitHandler) fun i _ => by ssr).trans (bytesT8_of_rd64 hB.exit_handler)) c0 hcall
  have kS : Agree (fun a => Below (sp - 112) 64 a ∨ SinitW a) (Lua.Vm.AtF.FwriteSetup.m2 X0) m1 := by
    intro a ha
    simp only [Below, SinitW, Rng, not_or, not_and] at ha
    exact SP.keep a (by omega) (by omega) (by omega) (by omega)
  let X1 := fwsX sp src n r f m1 o
  have hX1 : Lua.Vm.AtF.FwriteSetup.Ok X1 := ⟨hX0.sp_lo, hX0.sp_hi, hX0.sp_al, hX0.ra⟩
  simp only [voidRet] at hv1
  have hc2 : bytesT8 m1 (sp - 104) = BitVec.ofNat 64 n := (kS.b8 fun i _ => by ssr).trans F2.n
  have hc4 : bytesT2 m1 0x8005e678 = 0x9#16 := by
    rw [b2_lo_of_b4 (a := 0x8005e678) SP.stdout.flags]; decide
  obtain ⟨c2, s2, h2⟩ := fws_run1 X1 hX1 hc2 SP.stdout.flags2 hc4 c1 (hv1.repin (by pins_of hv1))
  obtain ⟨k5, fl5, f25, n5⟩ := fws_m5 X1 hX1
  have k5' : Agree (fun a => Rng (sp - 104) 8 a ∨ Rng (stdoutFile + 176) 4 a ∨ Rng (stdoutFile + 16) 2 a) m1
      (Lua.Vm.AtF.FwriteSetup.m5 X1) := k5
  have k15 := kS.trans k5'
  have hcall2 : SegSt 0x80033b50#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x12, BitVec.ofNat 64 (sp - 72)⟩] (sp - 112)
      0x800341f8#64 (fwFrame f n)) (ArmPay (Lua.Vm.AtF.FwriteSetup.m5 X1) o) c2 := by
    simp only [Lua.Vm.AtF.FwriteSetup.r5, show X1.n 0 - 112 = sp - 112 from rfl,
      show X1.n 0 - 72 = sp - 72 from rfl] at h2
    exact h2.repin (by pins_of h2)
  have hfr : StdoutFresh (Lua.Vm.AtF.FwriteSetup.m5 X1) := by
    refine ⟨?_, ?_, fl5, ?_, ?_, ?_, ?_, ?_, f25, ?_⟩
    · exact (k15.b8 (a := symImpurePtr) fun i _ => by ssr).trans
        ((k2'.b8 (a := symImpurePtr) fun i _ => by ssr).trans (bytesT8_of_rd64 hB.impure_ptr))
    · exact (k5'.b8 (a := symImpureData + reentCleanupOff) fun i _ => by ssr).trans SP.cleanup
    · rw [k5'.b2 (a := stdoutFile + 18) fun i _ => by ssr]
      rw [show stdoutFile + 18 = stdoutFile + 16 + 2 from rfl, b2_hi_of_b4 SP.stdout.flags]; decide
    · rw [k5'.b4 (a := stdoutFile + 20) fun i _ => by ssr, SP.pad, k2'.b4 (a := stdoutFile + 20) fun i _ => by ssr]
      exact zero_b4 hB.files (by omega) (by simp only [symSfSize]; omega)
    · exact (k5'.b8 (a := stdoutFile + 24) fun i _ => by ssr).trans SP.stdout.base
    · exact (k5'.b8 (a := stdoutFile + 48) fun i _ => by ssr).trans SP.stdout.cookie
    · exact (k5'.b8 (a := stdoutFile + 64) fun i _ => by ssr).trans SP.stdout.write
    · exact (k15.b4 (a := symFsReady) fun i _ => by ssr).trans ((k2'.b4 (a := symFsReady) fun i _ => by ssr).trans hfs)
  have r8 : ∀ a, sp - 112 ≤ a → a + 8 ≤ sp → (a + 8 ≤ sp - 104 ∨ sp - 96 ≤ a) →
      bytesT8 (Lua.Vm.AtF.FwriteSetup.m5 X1) a = bytesT8 (Lua.Vm.AtF.FwriteSetup.m2 X0) a :=
    fun a h1 h2 h3 => k15.b8 fun i _ => by ssr
  have hio : SfvUio (Lua.Vm.AtF.FwriteSetup.m5 X1) (sp - 72) (sp - 88) src n := by
    refine ⟨(r8 (sp - 72) (by omega) (by omega) (by omega)).trans F2.iov, ?_, (r8 (sp - 88) (by omega) (by omega) (by omega)).trans F2.base, ?_⟩
    · rw [show sp - 72 + 16 = sp - 56 by omega]; exact (r8 (sp - 56) (by omega) (by omega) (by omega)).trans F2.resid
    · rw [show sp - 88 + 8 = sp - 80 by omega]; exact (r8 (sp - 80) (by omega) (by omega) (by omega)).trans F2.len
  have hfm : FwsM2 (Lua.Vm.AtF.FwriteSetup.m5 X1) X0 :=
    ⟨(r8 (sp - 8) (by omega) (by omega) (by omega)).trans F2.ra, (r8 (sp - 16) (by omega) (by omega) (by omega)).trans F2.s0,
     (r8 (sp - 24) (by omega) (by omega) (by omega)).trans F2.s1, (r8 (sp - 32) (by omega) (by omega) (by omega)).trans F2.s2,
     (r8 (sp - 40) (by omega) (by omega) (by omega)).trans F2.s3, (r8 (sp - 56) (by omega) (by omega) (by omega)).trans F2.resid,
     (r8 (sp - 72) (by omega) (by omega) (by omega)).trans F2.iov, (r8 (sp - 80) (by omega) (by omega) (by omega)).trans F2.len,
     (r8 (sp - 88) (by omega) (by omega) (by omega)).trans F2.base, n5⟩
  refine ⟨_, s0.trans (s1.trans s2), Lua.Vm.AtF.FwriteSetup.m5 X1, hcall2, hfr, hio, hfm, ?_⟩
  exact (k2'.trans k15).mono fun a ha => by
    simp only [Below, Rng, SinitW] at ha ⊢
    omega

/-- **What the first `fwrite` leaves**: `stdout` set up holding `pend'`,
`out ++ pend' = (the n bytes at src)`; the heap block `buf` granted at the
set-up's memory `M` (the region the set-up wrote); then the loop's keep. -/
structure SetupPost (m M m' : Mem) (sp src n buf brk : Nat) (chunks : List Chunk) (top' brk' : Nat)
    (chunks' : List Chunk) (bins' : Nat → List Nat) (out pend' : List (BitVec 8)) : Prop where
  stdout : StdoutAt m' buf pend'
  up : StdioUp m'
  out : out ++ pend' = bytesAt m src n
  grant : HeapGrant chunks 1024 buf brk M top' brk' chunks' bins'
  agree : Agree (fun a => FsGlobal a ∨ MallocW chunks a ∨ SinitW a ∨ Below sp 1536 a) m M
  keep : SfvKeep M m' (sp - 112) buf (sp - 72)
  src_buf : src + n ≤ buf ∨ buf + 1024 ≤ src

/-- **The first `fwrite(src, 1, n, stdout)`** from the boot state
(`StdioBoot`, `MemfsBoot`, the heap with room for the buffer), `n ≥ 1`, the
`n` bytes at `src` apart from what the set-up writes. -/
def StdoutSetup_Statement : Prop :=
  ∀ (sp src n top brk : Nat) (chunks : List Chunk) (bins : Nat → List Nat) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String),
    StdioBoot m → MemfsBoot m → HeapAt (Vsa.Densify.fillZeroMem m) top brk chunks bins →
    r.toNat % 4 = 0 → sp ≤ 2 ^ 32 → sp % 16 = 0 → heapEnd + 8192 ≤ sp → brk + 1024 + 16384 ≤ heapEnd →
    1 ≤ n → errnoAddr + 4 ≤ src → src + n + 4096 ≤ sp → (src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src) →
    (∀ a, src ≤ a → a < src + n → ¬ FsGlobal a ∧ ¬ MallocW chunks a ∧ ¬ SinitW a) →
    Triple (SegSt 0x800342e4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 src⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x13, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M m' out pend' buf top' brk' chunks' bins', wrRet r sp n f m' (pushes o out) c ∧
        SetupPost m M m' sp src n buf brk chunks top' brk' chunks' bins' out pend')

/-- **The first `fwrite`**, given `_malloc_r`'s summary. -/
theorem stdoutSetup_of_malloc (hM : MallocR_Statement) : StdoutSetup_Statement := by
  intro sp src n top brk chunks bins r f m o hB hMf hheap hra hhi hal hlo hroom hn hsl hsh hsf hsrc c h
  have q : heapEnd + 4096 ≤ sp - 112 ∧ 0x8005e7d8 + 64 + 112 ≤ sp := by
    obtain ⟨H, hH⟩ : ∃ H, heapEnd = H := ⟨_, rfl⟩
    have : H = 0x87800000 := hH ▸ rfl
    rw [hH] at hlo ⊢; omega
  fs_nums
  stdio_nums
  have : symSf = 0x8005e5b0 := rfl
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have hfs : bytesT4 m symFsReady = 0#32 := bytesT4_of_rd32 hMf.ready
  obtain ⟨c1, s1, M5, h1, mid⟩ := fws_pre sp src n r f m o hra q.2 hhi hal hB hfs c h
  have hH5 : HeapAt (Vsa.Densify.fillZeroMem M5) top brk chunks bins :=
    hheap.congr fun a ha => fill_congr <| mid.agree.get (by simp only [HeapReads] at ha; ssr)
  obtain ⟨c2, s2, M, m', out, pend', buf, top', brk', chunks', bins', hret, FW⟩ :=
    sfvwrite_first hM (sp - 112) (sp - 72) (sp - 88) src n top brk chunks bins 0x800341f8#64 (fwFrame f n) M5 o
      (by decide) q.1 (by omega) (by omega) mid.fresh hH5 hroom mid.uio (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hn hsl (by omega) hsf (fun a h1 h2 => ⟨(hsrc a h1 h2).1, (hsrc a h1 h2).2.1⟩)
      c1 h1
  have kc : Agree (fun a => FsGlobal a ∨ (MallocGlobal a ∨ Arena a) ∨ Below (sp - 112) 1312 a ∨ StdoutW a) M5 M :=
    FW.agree.mono fun a ha => by
      rcases ha with h | h | h
      · exact .inl h
      · exact .inr (.inl h.coarse)
      · exact .inr (.inr h)
  have rd : ∀ a, sp - 112 ≤ a → a + 8 ≤ sp → (a + 8 ≤ sp - 56 ∨ sp - 48 ≤ a) →
      bytesT8 m' a = bytesT8 M5 a := fun a h1 h2 h3 =>
    (bytesT8_congrT fun i _ => FW.keep.keep_hi _ (by omega) (by omega)).trans (kc.b8 fun i _ => by ssr)
  let X2 := fwsX sp src n r f m' (pushes o out)
  have hX2 : Lua.Vm.AtF.FwriteSetup.Ok X2 := ⟨show _ ≤ sp by omega, hhi, hal, hra⟩
  simp only [wrRet] at hret
  obtain ⟨c3, s3, h3⟩ := fws_run2 X2 hX2 ((rd (sp - 104) (by omega) (by omega) (by omega)).trans mid.frame.n)
    FW.up.flags2' FW.stdout.flags' ((rd (sp - 8) (by omega) (by omega) (by omega)).trans mid.frame.ra)
    ((rd (sp - 16) (by omega) (by omega) (by omega)).trans mid.frame.s0) ((rd (sp - 24) (by omega) (by omega) (by omega)).trans mid.frame.s1)
    ((rd (sp - 32) (by omega) (by omega) (by omega)).trans mid.frame.s2) ((rd (sp - 40) (by omega) (by omega) (by omega)).trans mid.frame.s3)
    c2 (hret.repin (by pins_of hret))
  refine ⟨c3, s1.trans (s2.trans s3), M, m', out, pend', buf, top', brk', chunks', bins',
    h3.repin (by pins_of h3), ⟨FW.stdout, FW.up, ?_, FW.grant, ?_, FW.keep, FW.src_buf⟩⟩
  · rw [FW.out]
    refine bytesAt_congr fun i hi => ?_
    have hx := hsrc (src + i) (by omega) (by omega)
    simp only [bytesT1]
    rw [mid.agree (src + i) fun hr => by
      rcases hr with h | h
      · exact hx.2.2 h
      · simp only [Below] at h; omega]
  · intro a ha
    by_cases hw : MallocW chunks a
    · exact absurd (.inr (.inl hw)) ha
    · refine (mid.agree.trans FW.agree) a fun hr => ha ?_
      simp only [hw, false_or, or_false] at hr ⊢
      simp only [FsGlobal, Below, Rng, StdoutW, SinitW] at hr ⊢
      omega

end Lua.Vm.Sim.Kit
