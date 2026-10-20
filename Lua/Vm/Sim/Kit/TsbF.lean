import Lua.Vm.Sim.Kit.FltFmt
import Lua.Vm.Sim.Kit.Strspn
import Lua.Vm.Sim.Kit.PushfI
import Lua.Num.Fmt14gFacts
import Lua.Vm.AtF.TsbF

/-!
# `tostringbuff` on a float (lane F1-25)

`tostringbuff`'s float part (`tostringbuff.part.0.isra.0`, `0x8001142c`):
`lua_number2str` = `snprintf(buf, 44, "%.14g", n)` (a call node: the named
premise `FloatToStr_Statement`, a bignum computation `BigRun`), then
`buff[strspn(buff, "-0123456789")] == '\0'` (`strspn_sum`) and, when the
string looks like an integer, `lua_getlocaledecpoint()` (compiled to `'.'`)
and `'0'`. Its at-lemmas are generated (`Lua/Vm/AtF/TsbF.lean`): the entry,
the returns from `snprintf` (`S`) and `strspn` (`P`). The bytes are the model's
`tostringbuff` (`tsbBytes_eq`: `strspn` reaches the terminator exactly when
every byte is a sign or a digit).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The model's bytes -/

/-- `tostringbuff` of a double, as bytes. -/
def tsbBytes (x : BitVec 64) : List (BitVec 8) := (Lua.Num.tostringbuffBits x).map fun c => BitVec.ofNat 8 c.toNat

/-- A byte converted to `BitVec 8` reads back as itself. -/
theorem u8_toNat (c : UInt8) : (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt c.toNat_lt

/-- `strspn` reaches the end exactly when every byte is in its set. -/
theorem spanLen_eq_length (l : List (BitVec 8)) : spanLen l = l.length ↔ l.all spnIn = true := by
  induction l with
  | nil => simp [spanLen]
  | cons c cs ih =>
    simp only [spanLen, List.length_cons, List.all_cons, Bool.and_eq_true]
    cases h : spnIn c
    · simp
    · simp only [if_true, Nat.add_right_cancel_iff, true_and]; exact ih

/-- **`tostringbuff`'s bytes** from `%.14g`'s: `".0"` appended when `strspn`
reaches the terminator. -/
theorem tsbBytes_eq (x : BitVec 64) :
    tsbBytes x = if spanLen (g14Bytes x) = (g14Bytes x).length then g14Bytes x ++ [0x2e#8, 0x30#8]
      else g14Bytes x := by
  have hc : ∀ c : UInt8, spnIn (BitVec.ofNat 8 c.toNat) = (c == 45 || (48 ≤ c && c ≤ 57)) := by
    intro c
    simp only [spnIn, u8_toNat]
    have h1 : (c == 45) = (c.toNat == 45) := by
      cases h : c == 45 <;> cases h' : c.toNat == 45 <;> simp_all [UInt8.ext_iff] <;> omega
    have h2 : ((48 : UInt8) ≤ c) = (48 ≤ c.toNat) := by
      apply propext; rw [UInt8.le_iff_toNat_le]; simp
    have h3 : (c ≤ (57 : UInt8)) = (c.toNat ≤ 57) := by
      apply propext; rw [UInt8.le_iff_toNat_le]; simp
    rw [h1]; simp only [h2, h3]
  rw [spanLen_eq_length]
  simp only [tsbBytes, g14Bytes, Lua.Num.tostringbuffBits, Lua.Num.tostringbuff, Lua.Num.fmt14gBits,
    List.all_map, Function.comp_def, hc]
  split <;> simp

/-- `%.14g`'s bytes are none zero. -/
theorem g14Bytes_nz (x : BitVec 64) : ∀ j (h : j < (g14Bytes x).length), (g14Bytes x)[j] ≠ 0#8 := by
  intro j hj he
  simp only [g14Bytes, List.getElem_map] at he
  have hm := List.getElem_mem (l := Lua.Num.fmt14gBits x) (by simpa [g14Bytes] using hj)
  have := Lua.Num.fmt14g_ne_zero _ _ _ hm
  have e := congrArg BitVec.toNat he
  rw [u8_toNat] at e
  exact this e

/-! ## `.rodata` -/

/-- Bytes of `.rodata`. -/
theorem rod_bytes {m : Mem} (h : RodataRead m) {a n : Nat} (h1 : Image.rodataBase ≤ a)
    (h2 : a + n ≤ Image.rodataBase + Image.rodataSize) :
    bytesAt m a n = (List.range n).map fun i => Image.rodataByte (a - Image.rodataBase + i) := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  have := h (a - Image.rodataBase + i) (by simp at hi; omega)
  rwa [show Image.rodataBase + (a - Image.rodataBase + i) = a + i by omega] at this

/-- `"%.14g"` in `.rodata`. -/
theorem g14Fmt_rod {m : Mem} (h : RodataRead m) : bytesAt m 0x8004f3d8 6 = g14Fmt := by
  rw [rod_bytes h (by decide) (by decide)]; decide

/-- `"-0123456789"` in `.rodata`. -/
theorem spnSet_rod {m : Mem} (h : RodataRead m) : bytesAt m 0x8004f3e0 12 = spnSetBytes := by
  rw [rod_bytes h (by decide) (by decide)]; decide

/-- `.rodata` at a memory agreeing on it. -/
theorem RodataRead.congr_rod {m M : Mem} (h : RodataRead m)
    (hk : ∀ a, Image.rodataBase ≤ a → a < Image.rodataBase + Image.rodataSize → bytesT1 M a = bytesT1 m a) :
    RodataRead M := fun o ho => by rw [hk _ (by omega) (by omega)]; exact h o ho

/-! ## The run -/

/-- A context of `tostringbuff`'s rows: `sp`, the buffer, the count, `strspn`'s
answer; the caller's frame, the double. -/
@[at_row] abbrev tsX (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (x : BitVec 64) (M : Mem) (o : Array String) :
    FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, x] M o

/-- **`tostringbuff`'s inputs**: the stack above the heap, the buffer in the
caller's frame, `snprintf`'s static words and `.rodata`, the heap, the
bignums and the room for `_dtoa_r`'s allocations. -/
structure TsbIn (m : Mem) (sp buf : Nat) (r : BitVec 64) (H : HeapIx) (B : Nat → Prop) : Prop where
  sp_lo : heapEnd + 16384 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  b_lo : sp ≤ buf
  b_hi : buf + 44 ≤ 2 ^ 32
  stat : FmtStatic m
  rod : RodataRead m
  heap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins
  room : H.brk + dtoaRoom ≤ heapEnd
  big : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m
  big_in : ∀ a, B a → InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd

/-- What `tostringbuff` may write besides the allocator's: its callees'
frames and its own below `sp`, the buffer. -/
def TsbFr (sp buf a : Nat) : Prop := Below sp 8256 a ∨ Rng buf 44 a

/-- **What `tostringbuff` leaves**: its count (one to twenty-three bytes), the
bytes at `buf`, a bignum computation within `dtoaRoom`. -/
structure TsbPost (sp buf : Nat) (x : BitVec 64) (m m' : Mem) (H H' : HeapIx) (B B' : Nat → Prop) : Prop where
  len_lo : 1 ≤ (tsbBytes x).length
  len_hi : (tsbBytes x).length ≤ 23
  bytes : bytesAt m' buf (tsbBytes x).length = tsbBytes x
  big : BigRun (TsbFr sp buf) m m' H H' B B' dtoaRoom

/-- `snprintf`'s frame (`tostringbuff`'s `s0`, `s1` at the call). -/
abbrev tsSnFr (buf : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨f.s0, BitVec.ofNat 64 buf, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- `strspn`'s frame. -/
abbrev tsSpFr (buf n : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 n, BitVec.ofNat 64 buf, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- A store in the stack frame is off the heap's footprint. -/
theorem tsbFr_hi {sp buf a : Nat} (hsp : heapEnd + 16384 ≤ sp) (hb : sp ≤ buf) (h : TsbFr sp buf a) :
    heapEnd + 32 ≤ a := by
  simp only [TsbFr, Below, Rng] at h; omega

/-- **`tostringbuff`'s float part** from `snprintf`'s summary (the named
premise `FloatToStr_Statement`) and `strspn`'s: the model's `tostringbuff`
bytes at `buf` (`tsbBytes`), their count returned, a bignum computation. -/
theorem tsb_sum (hF : FloatToStr_Statement) (sp buf : Nat) (x r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (H : HeapIx) (B : Nat → Prop) (hI : TsbIn m sp buf r H B) :
    Triple (SegSt 0x8001142c#64 (callPre [⟨Register.x10, x⟩, ⟨Register.x11, BitVec.ofNat 64 buf⟩] sp r f)
        (ArmPay m o))
      (fun c => ∃ m' H' B', wrRet r sp (tsbBytes x).length f m' o c ∧ TsbPost sp buf x m m' H H' B B') := by
  intro c h
  have hs1 := hI.sp_lo; have hs2 := hI.sp_hi; have hs3 := hI.sp_al; have hra := hI.ra
  have hb1 := hI.b_lo; have hb2 := hI.b_hi
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hX : Lua.Vm.AtF.TsbF.Ok (tsX [sp, buf] r f x m o) := by fcx_ok
  have h : SegSt 0x8001142c#64 (Lua.Vm.AtF.TsbF.r0 (tsX [sp, buf] r f x m o))
      (ArmPay (tsX [sp, buf] r f x m o).m (tsX [sp, buf] r f x m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TsbF h acc until [0x80034de0]
  -- the frame's stores
  generalize hM0 : Lua.Vm.AtF.TsbF.m0 (tsX [sp, buf] r f x m o) = M0 at h
  have k0 : ∀ a, (a + 24 < sp ∨ sp ≤ a) → bytesT1 M0 a = bytesT1 m a := by
    intro a ha; rw [← hM0]
    simp only [Lua.Vm.AtF.TsbF.m0, tsX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8]
  have w8 : bytesT8 M0 (sp - 8) = r := by
    rw [← hM0]; simp only [Lua.Vm.AtF.TsbF.m0, tsX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw8_wm8, fw8_same]
  have w16 : bytesT8 M0 (sp - 16) = f.s0 := by
    rw [← hM0]; simp only [Lua.Vm.AtF.TsbF.m0, tsX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw8_wm8, fw8_same]
  have w24 : bytesT8 M0 (sp - 24) = f.s1 := by
    rw [← hM0]; simp only [Lua.Vm.AtF.TsbF.m0, tsX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw8_wm8, fw8_same]
  have hBh : ∀ a, B a → a < heapEnd := fun a ha => (hI.big_in a ha).2.2
  have hF0 : ∀ a, ¬ TsbFr sp buf a → bytesT1 M0 a = bytesT1 m a := fun a ha =>
    k0 a (by simp only [TsbFr, Below, Rng, not_or, not_and, Nat.not_lt] at ha; omega)
  have lowS : ∀ a, a < 0x8005e720 → bytesT1 M0 a = bytesT1 m a := fun a ha => k0 a (.inl (by omega))
  -- `snprintf`'s inputs at the call
  have hIn : FltFmtIn M0 (sp - 32) buf 0x8004f3d8 0x80011458#64 H B := {
    fmtb := (bytesAt_congr fun j hj => lowS _ (by omega)).trans (g14Fmt_rod hI.rod)
    f_lo := by decide, f_hi := by decide, ra := by decide
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, b_lo := by omega, b_hi := hb2
    stat := hI.stat.congr lowS
    rod := hI.rod.congr_rod fun a h1 h2 => lowS a (by have : Image.rodataBase + Image.rodataSize = 0x8005c6a8 := rfl; omega)
    heap := (BigRun.ofFrame (F := TsbFr sp buf) hI.heap hI.big hBh (fun a ha => tsbFr_hi hs1 hb1 ha) hF0).heap
    room := hI.room
    big := hI.big.trans fun a ha => hF0 a fun hf => by
      have := tsbFr_hi hs1 hb1 hf
      rcases ha with hb' | hr
      · have := hBh a hb'; omega
      · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr; omega
    big_in := hI.big_in }
  fcx_unfold at h
  obtain ⟨c2, s2, M1, H1, B1, hret, hP⟩ := hF (sp - 32) buf 0x8004f3d8 x 0x80011458#64 (tsSnFr buf f) M0 o H B hIn
    _ (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s2
  have hl1 := hP.len_lo; have hl2 := hP.len_hi
  generalize hn : (g14Bytes x).length = n at hl1 hl2 hret
  -- `M1` keeps the frame and `.rodata`
  have kS : ∀ a, a < heapStart → ¬ MallocGlobal a → ¬ ReentWord a → bytesT1 M1 a = bytesT1 M0 a :=
    fun a h1 h2 h3 => hP.big.keep_static hBh h1 h2 h3 fun hf => by
      simp only [G14Fr, Below, Rng] at hf; omega
  have kF : ∀ a, sp - 32 ≤ a → a < sp → bytesT1 M1 a = bytesT1 M0 a := fun a h1 h2 => hP.big.keep a fun hw => by
    rcases hw with hw | hw | hw | hw
    · rcases hw with hg | ⟨-, hh, -⟩
      · have := hg.lt; omega
      · omega
    · have := hBh a hw; omega
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hw; omega
    · simp only [G14Fr, Below, Rng] at hw; omega
  have rod1 : RodataRead M1 := (hI.rod.congr_rod fun a h1 h2 => lowS a (by
      have : Image.rodataBase + Image.rodataSize = 0x8005c6a8 := rfl; omega)).congr_rod fun a h1 h2 => by
    have : Image.rodataBase + Image.rodataSize = 0x8005c6a8 := rfl
    have : Image.rodataBase = 0x8004ecc8 := rfl
    refine kS a (by omega) (fun hg => ?_) (fun hr => ?_)
    · have : symMallocAv = 0x8005c6d0 := rfl
      have : symMallocSbrkBase = 0x8005d388 := rfl
      have : symBrk = 0x8005d3b8 := rfl
      have : symMallocMallinfo = 0x8005e560 := rfl
      have : errnoAddr = 0x8005d408 := rfl
      simp only [MallocGlobal] at hg; omega
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr; omega
  -- `S`: on to `strspn`
  have hXS : Lua.Vm.AtF.TsbF.Ok_S (tsX [sp, buf, n] r f x M1 o) := by fcx_ok
  simp only [wrRet] at hret
  have h : SegSt 0x80011458#64 (Lua.Vm.AtF.TsbF.r2 (tsX [sp, buf, n] r f x M1 o))
      (ArmPay (tsX [sp, buf, n] r f x M1 o).m (tsX [sp, buf, n] r f x M1 o).o) c2 := by
    fcx_unfold; exact hret.repin (by pins_of hret)
  fat_run Lua.Vm.AtF.TsbF h acc until [0x800368dc]
  fcx_unfold at h
  have hSp : SpnIn M1 buf (g14Bytes x) := {
    bytes := hP.bytes
    nz := g14Bytes_nz x
    s_lo := by omega
    s_hi := by omega
    set := spnSet_rod rod1 }
  obtain ⟨c3, s3, hret3⟩ := strspn_sum (sp - 32) buf 0x8001146c#64 (tsSpFr buf n f) M1 o (g14Bytes x) hSp
    (by omega) (by decide) _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; rw [← hn]; exact h.repin (by pins_of h))
  have acc := acc.trans s3
  have hk := spanLen_le (g14Bytes x)
  generalize hk' : spanLen (g14Bytes x) = k at hk hret3
  rw [hn] at hk
  -- `P`: the byte at `buf + k`, the suffix
  have hXP : Lua.Vm.AtF.TsbF.Ok_P (tsX [sp, buf, n, k] r f x M1 o) := by fcx_ok
  simp only [wrRet] at hret3
  have h : SegSt 0x8001146c#64 (Lua.Vm.AtF.TsbF.r4 (tsX [sp, buf, n, k] r f x M1 o))
      (ArmPay (tsX [sp, buf, n, k] r f x M1 o).m (tsX [sp, buf, n, k] r f x M1 o).o) c3 := by
    fcx_unfold; exact hret3.repin (by pins_of hret3)
  have hc0 : bytesT8 (tsX [sp, buf, n, k] r f x M1 o).m ((tsX [sp, buf, n, k] r f x M1 o).n 0 - 8) =
      (tsX [sp, buf, n, k] r f x M1 o).b 0 :=
    show bytesT8 M1 (sp - 8) = r from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w8
  have hc1 : bytesT8 (tsX [sp, buf, n, k] r f x M1 o).m ((tsX [sp, buf, n, k] r f x M1 o).n 0 - 16) =
      (tsX [sp, buf, n, k] r f x M1 o).b 1 :=
    show bytesT8 M1 (sp - 16) = f.s0 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w16
  have hc2 : bytesT8 (tsX [sp, buf, n, k] r f x M1 o).m ((tsX [sp, buf, n, k] r f x M1 o).n 0 - 24) =
      (tsX [sp, buf, n, k] r f x M1 o).b 2 :=
    show bytesT8 M1 (sp - 24) = f.s1 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w24
  have hg := zb_bne0 (bytesT1 M1 (buf + k))
  have hbig := hP.big.mono (F' := TsbFr sp buf) (fun a ha => by
    simp only [G14Fr, TsbFr, Below, Rng] at ha ⊢; omega) (Nat.le_refl _)
  have hbig0 := BigRun.frame_before hI.heap hI.big hBh (fun a ha => tsbFr_hi hs1 hb1 ha) hF0 hbig
  have hbytesB := hP.bytes
  rw [hn] at hbytesB
  by_cases hkn : k = n
  · -- every byte a sign or a digit: `".0"`
    subst hkn
    have hz : bytesT1 M1 (buf + k) = 0#8 := by
      have := bytesAt_get hbytesB (j := k) (by omega)
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hn])]; simp [hn]
    simp only [hz, decide_true, Bool.not_true] at hg
    fat_run Lua.Vm.AtF.TsbF h acc
    fcx_unfold at h
    have ht : tsbBytes x = g14Bytes x ++ [0x2e#8, 0x30#8] := by rw [tsbBytes_eq, if_pos (hk'.trans hn.symm |>.trans rfl)]
    have hlen : (tsbBytes x).length = k + 2 := by rw [ht]; simp [hn]
    refine ⟨_, acc, _, H1, B1, ?_, ?_⟩
    · rw [hlen]; exact h.repin (by pins_of h)
    · refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [hlen, ht]
        apply List.ext_getElem (by simp [bytesAt, hn])
        intro j h1 h2
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        by_cases hj : j < k
        · simp (disch := omega) only [fw1_ins]
          have := bytesAt_get hbytesB (j := j) (by omega)
          rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hn]; exact hj),
            List.getElem?_eq_getElem (by rw [hn]; exact hj), Option.getD_some,
            List.getElem_append_left (by rw [hn]; exact hj)]
        · rw [List.getElem_append_right (by rw [hn]; omega)]
          simp only [List.length_append, List.length_cons, List.length_nil, hn] at h1 h2 ⊢
          have : j = k ∨ j = k + 1 := by omega
          rcases this with rfl | rfl
          · simp (disch := omega) only [fw1_ins]
            rw [fw1_same (by omega)]; decide
          · rw [fw1_same (by omega)]; decide
      · refine hbig0.frame_after hBh (fun a ha => tsbFr_hi hs1 hb1 ha) fun a ha => ?_
        simp only [TsbFr, Below, Rng, not_or, not_and, Nat.not_lt] at ha
        simp (disch := omega) only [fw1_ins]
  · -- a byte outside the set: no suffix
    have hz : bytesT1 M1 (buf + k) ≠ 0#8 := by
      have := bytesAt_get hbytesB (j := k) (by omega)
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hn]; omega),
        List.getElem?_eq_getElem (by rw [hn]; omega), Option.getD_some]
      exact g14Bytes_nz x k (by rw [hn]; omega)
    simp only [hz, decide_false, Bool.not_false] at hg
    fat_run Lua.Vm.AtF.TsbF h acc
    fcx_unfold at h
    have ht : tsbBytes x = g14Bytes x := by rw [tsbBytes_eq, if_neg (by rw [hk', hn]; exact hkn)]
    have hlen : (tsbBytes x).length = n := by rw [ht, hn]
    refine ⟨_, acc, _, H1, B1, ?_, ?_⟩
    · rw [hlen]; exact h.repin (by pins_of h)
    · refine ⟨by omega, by omega, ?_, hbig0⟩
      rw [hlen, ht]
      apply List.ext_getElem (by simp [bytesAt, hn])
      intro j h1 h2
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      have := bytesAt_get hbytesB (j := j) (by simp [bytesAt] at h1; omega)
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h2),
        List.getElem?_eq_getElem (by simpa using h2), Option.getD_some]

end Lua.Vm.Sim.Kit
