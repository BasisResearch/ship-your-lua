import Lua.Vm.Sim.Kit.IntFmtSum
import Lua.Vm.Sim.Kit.PushfI
import Lua.Vm.Sim.Kit.AtSubw
import Lua.Vm.AtF.SnprintfP.Runs

/-!
# `lua_pointer2str`: `snprintf(buf, 32, "%p", p)` on `print`'s address (lane F1-24)

`luaO_pushvfstring`'s `'p'` conversion on F1's one light C function: its
address `0x80022f18` (`ValRepr.print`) as `%p` prints it, `"0x80022f18"`.
Over the at-lemmas of `Lua/Vm/AtF/SnprintfP` (`gen_lua_at.py --fn
snprintf/p`): `_svfprintf_r`'s prologue (the root `F`, as for `"%lld"`), the
format's walk to the `'p'` conversion (the root `C`), the hex digits of the
literal pointer unrolled, the `0x` prefix and the digits written by
`__ssprint_r` (two `memmove`s, `memmove_sum`: the roots after them), the
format's end, `snprintf`'s `'\0'` and return. Every root's context is `SnG.X`
(`Kit/IntFmt.lean`, the pointer a literal: `SnG.i` unused); the root facts are
named structures as for `"%lld"` (`FacC`, `FacQ1`, `FacQ2`, `SnSave … 0x20`),
proven by forwarding (`sn_rd`, `sn_rd2`, `MoveOut`) or carried by an agreement
off the run's writes (`snWk`, `snWd`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- `print`'s address as `%p` prints it: `"0x80022f18"`. -/
def ptrBytes : List (BitVec 8) :=
  [0x30#8, 0x78#8, 0x38#8, 0x30#8, 0x30#8, 0x32#8, 0x32#8, 0x66#8, 0x31#8, 0x38#8]

/-- The `.rodata` words the `'p'` conversion reads: the conversion switch's
word for `'p'`, the digits of `xdigs_lower` it uses. -/
structure PtrRod (m : Mem) : Prop where
  jt_p : bytesT4 m 0x80055604 = 0xfffee784#32
  x0 : bytesT1 m 0x80051b70 = 0x30#8
  x1 : bytesT1 m 0x80051b71 = 0x31#8
  x2 : bytesT1 m 0x80051b72 = 0x32#8
  x8 : bytesT1 m 0x80051b78 = 0x38#8
  xf : bytesT1 m 0x80051b7f = 0x66#8

theorem ptrRod_of {m : Mem} (h : RodataRead m) : PtrRod m := by
  have e : ∀ a, Image.rodataBase ≤ a → a < Image.rodataBase + Image.rodataSize →
      bytesT1 m a = Image.rodataByte (a - Image.rodataBase) := fun a h1 h2 => by
    have := h (a - Image.rodataBase) (by omega)
    rwa [show Image.rodataBase + (a - Image.rodataBase) = a by omega] at this
  have hb : Image.rodataBase = 0x8004ecc8 := rfl
  have hs : Image.rodataSize = 55776 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0x80055604 : Nat) = Image.rodataBase + 0x693c by decide, rod4 h _ (by decide)]; decide
  all_goals (rw [e _ (by omega) (by omega)]; decide)

/-- `PtrRod` at a memory agreeing below the stack. -/
theorem PtrRod.congr {m M : Mem} (h : PtrRod m) (hk : ∀ a, a < 0x8005e720 → bytesT1 M a = bytesT1 m a) :
    PtrRod M where
  jt_p := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.jt_p
  x0 := (hk _ (by omega)).trans h.x0
  x1 := (hk _ (by omega)).trans h.x1
  x2 := (hk _ (by omega)).trans h.x2
  x8 := (hk _ (by omega)).trans h.x8
  xf := (hk _ (by omega)).trans h.xf

/-- **`lua_pointer2str`'s call** (`snprintf(buf, 32, "%p", p)` from
`luaO_pushvfstring`): the format `"%p"` in `.rodata`, the stack, the buffer
(in the caller's frame above `sp`, or well below it), the static words. -/
structure PtrFmtIn (m : Mem) (sp buf fmt : Nat) (r : BitVec 64) : Prop where
  fmtb : bytesAt m fmt 3 = [0x25#8, 0x70#8, 0#8]
  f_lo : 0x80000000 ≤ fmt
  f_hi : fmt + 5 ≤ 0x8005c6c0
  ra : r.toNat % 4 = 0
  sp_lo : 0x8005e720 + 8192 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  b_lo : 0x8005e720 ≤ buf
  b_ap : buf + 44 + 4096 ≤ sp ∨ sp ≤ buf
  b_hi : buf + 44 ≤ 2 ^ 32
  stat : FmtStatic m
  rod : PtrRod m

/-- The run's facts on its fixed data. -/
abbrev SnG.InP (G : SnG) (m : Mem) : Prop := PtrFmtIn m G.sp G.buf G.fmt G.r

/-- The `'p'` conversion's root memory: `_svfprintf_r`'s format scan after
the prologue. -/
@[reducible, at_row] def SnG.MP (G : SnG) (m : Mem) : Mem :=
  Lua.Vm.AtF.SnprintfP.m15 (G.X {} (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m)))

/-- The `'p'` conversion's context. -/
abbrev SnG.XP (G : SnG) (m : Mem) : FCx := G.X {} (G.MP m)

/-- The static words in a memory agreeing with another off the run's writes. -/
theorem FmtStatic.agree {m M : Mem} {sp buf : Nat} (hs : FmtStatic m) (ha : Agree (snWkN sp buf) m M)
    (hsp : 0x8005e720 + 8192 ≤ sp) (hb : 0x8005e720 ≤ buf) : FmtStatic M :=
  hs.congr fun a h => ha.t1 (a := a) (by simp only [snWkN]; omega)

/-- `PtrRod` in a memory agreeing with another off the run's writes. -/
theorem PtrRod.agree {m M : Mem} {sp buf : Nat} (hs : PtrRod m) (ha : Agree (snWkN sp buf) m M)
    (hsp : 0x8005e720 + 8192 ≤ sp) (hb : 0x8005e720 ≤ buf) : PtrRod M :=
  hs.congr fun a h => ha.t1 (a := a) (by simp only [snWkN]; omega)

/-- The format's bytes. -/
theorem PtrFmtIn.fmt_at {m : Mem} {sp buf fmt : Nat} {r : BitVec 64} (h : PtrFmtIn m sp buf fmt r) :
    bytesT1 m fmt = 0x25#8 ∧ bytesT1 m (fmt + 1) = 0x70#8 ∧ bytesT1 m (fmt + 2) = 0x0#8 := by
  have e := h.fmtb
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, Nat.add_zero] at e
  obtain ⟨e0, e1, e2, -⟩ := e
  exact ⟨e0, e1, e2⟩

/-- The format's bytes in a memory agreeing with the entry's. -/
theorem fmtP_of {G : SnG} {m M : Mem} (h : G.InP m) (ha : Agree (snWk G) m M) :
    bytesT1 M G.fmt = 0x25#8 ∧ bytesT1 M (G.fmt + 1) = 0x70#8 ∧ bytesT1 M (G.fmt + 2) = 0x0#8 := by
  have := h.sp_lo; have := h.b_lo; have := h.f_hi
  obtain ⟨e0, e1, e2⟩ := h.fmt_at
  refine ⟨?_, ?_, ?_⟩ <;> rw [ha.t1 (by simp only [snWk, snWkN]; omega)] <;> assumption

/-! ## From the entry to the `'p'` conversion -/

theorem agreeP_E (G : SnG) (m : Mem) (h : G.InP m) :
    Agree (snWk G) m (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m)) := by
  have := h.sp_lo
  fmt_agree

theorem agreeP_F (G : SnG) (m : Mem) (h : G.InP m) :
    Agree (snWk G) (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m)) (G.MP m) := by
  have := h.sp_lo
  fmt_agree

/-- The flags word `snprintf` stored (`_flags = __SWR | __SSTR`, `_file = -1`). -/
theorem flagsP_F (G : SnG) (m : Mem) (h : G.InP m) :
    bytesT2 (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m)) (G.sp - 248) = 0x208#16 := by
  have := h.sp_lo
  sn_unfold; fat_rd
  rw [fw2_ins2 (by omega) rfl]; decide

/-- **From the entry to the `'p'` conversion's root** (`run_E`, `run_F`). -/
theorem snpP_toC (G : SnG) (m : Mem) (hin : G.InP m) (c : Config)
    (h : SegSt 0x80034de0#64 (Lua.Vm.AtF.SnprintfP.r0 (G.X0 m)) (ArmPay (G.X0 m).m (G.X0 m).o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80043c48#64 (Lua.Vm.AtF.SnprintfP.r30 (G.XP m))
      (ArmPay (G.XP m).m (G.XP m).o) c' := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have hs := hin.stat
  obtain ⟨c1, s1, h1⟩ := Lua.Vm.AtF.SnprintfP.Runs.run_E (G.X0 m) (by sn_ok) (by sn_unfold; exact hs.impure)
    (by sn_unfold; exact hs.decpt) (by sn_unfold; exact hs.dotw) (by sn_unfold; exact hs.dot0)
    (by sn_unfold; exact hs.dot1) c h
  have ha := agreeP_E G m hin
  have hs1 := hs.agree ha hin.sp_lo hin.b_lo
  have hr1 := hin.rod.agree ha hin.sp_lo hin.b_lo
  obtain ⟨f0, f1, -⟩ := fmtP_of hin ha
  have h1' : SegSt 0x80042ec0#64 (Lua.Vm.AtF.SnprintfP.r16 (G.X {} (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m))))
      (ArmPay (G.X {} (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m))).m (G.X0 m).o) c1 := by
    sn_unfold at h1 ⊢; exact h1.repin (by pins_of h1)
  have hX1 : Lua.Vm.AtF.SnprintfP.Ok_F (G.X {} (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m))) := by
    constructor <;> simp only [SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] <;> omega
  obtain ⟨c2, s2, h2⟩ := Lua.Vm.AtF.SnprintfP.Runs.run_F (G.X {} (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m))) hX1
    (by sn_unfold; exact flagsP_F G m hin) (by sn_unfold; exact hs1.mbtowc) (by sn_unfold; exact hs1.mbmax)
    (by sn_unfold; exact f0) (by sn_unfold; exact f1) (by sn_unfold; exact hr1.jt_p) c1 h1'
  refine ⟨c2, s1.trans s2, ?_⟩
  sn_unfold at h2 ⊢; exact h2.repin (by pins_of h2)

/-! ## The frame `_svfprintf_r` restores -/

theorem agreeP_F2 (G : SnG) (m : Mem) (h : G.InP m) :
    Agree (fun a => G.sp ≤ a + 4096 ∧ a + 296 < G.sp) (Lua.Vm.AtF.SnprintfP.m12 (G.X0 m)) (G.MP m) := by
  have := h.sp_lo
  fmt_agree

theorem snSaveAP_C (G : SnG) (m : Mem) (h : G.InP m) : SnSaveA G (G.MP m) := by
  have := h.sp_lo
  constructor <;> sn_rd

theorem snSaveBP_C (G : SnG) (m : Mem) (h : G.InP m) : SnSaveB G 0x20#64 (G.MP m) := by
  have := h.sp_lo
  have hfl : bytesT2 (G.MP m) (G.sp - 248) = 0x208#16 :=
    ((agreeP_F2 G m h).b2 fun i _ => by omega).trans (flagsP_F G m h)
  refine ⟨?_, hfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sn_rd

theorem snSaveP_C (G : SnG) (m : Mem) (h : G.InP m) : SnSave G 0x20#64 (G.MP m) :=
  ⟨snSaveAP_C G m h, snSaveBP_C G m h⟩

/-! ## The `'p'` conversion: the hex digits, the `0x` prefix's `memmove` -/

/-- **What the `'p'` conversion's path reads** of its root memory. -/
structure FacC (G : SnG) (M : Mem) : Prop where
  ap : bytesT8 M (G.sp - 840) = BitVec.ofNat 64 (G.sp - 40)
  ptr : bytesT8 M (G.sp - 40) = 0x80022f18#64
  resid : bytesT8 M (G.sp - 624) = 0x0#64
  cnt : bytesT4 M (G.sp - 632) = 0x0#32
  ret : bytesT8 M (G.sp - 848) = 0x0#64
  fp : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)
  iov : bytesT8 M (G.sp - 640) = BitVec.ofNat 64 (G.sp - 512)
  w : bytesT4 M (G.sp - 252) = 0x1f#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf

theorem facC (G : SnG) (m : Mem) (h : G.InP m) : FacC G (G.MP m) := by
  have := h.sp_lo
  constructor <;> sn_rd

/-- The conversion's stores are writes after the conversion. -/
theorem agreeP_CX (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfP.m34 X) := by fmt_agree3

/-- **The `'p'` conversion, to `memmove` of the `0x` prefix** (`run_C`). -/
theorem snpP_mv1 (G : SnG) (m : Mem) (hin : G.InP m) (c : Config)
    (h : SegSt 0x80043c48#64 (Lua.Vm.AtF.SnprintfP.r30 (G.XP m)) (ArmPay (G.XP m).m (G.XP m).o) c) :
    ∃ c2 M1, Steps c c2 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfP.r33 (G.X {} M1)) (ArmPay (G.X {} M1).m (G.X {} M1).o) c2 ∧
      MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.XP m)) M1 G.buf (G.sp - 696) 2 := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  obtain ⟨fap, fptr, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := facC G m hin
  have ha : Agree (snWk G) m (G.MP m) := (agreeP_E G m hin).tr (agreeP_F G m hin)
  have hr := hin.rod.agree ha hin.sp_lo hin.b_lo
  obtain ⟨c1, s1, h1⟩ := Lua.Vm.AtF.SnprintfP.Runs.run_C (G.XP m) (by sn_ok) (by sn_u1; exact fap)
    (by sn_u1; exact fptr) (by sn_u1; exact hr.x8) (by sn_u1; exact hr.x1) (by sn_u1; exact hr.xf)
    (by sn_u1; exact hr.x2) (by sn_u1; exact hr.x0) (by sn_u1; exact fres) (by sn_u1; exact fcnt)
    (by sn_u1; exact fret) (by sn_u1; exact ffp) (by sn_u1; exact fiov) (by sn_u1; exact fw) (by sn_u1; exact fp) c h
  obtain ⟨c2, s2, M1, hr2, hmv⟩ := memmove_sum (G.sp - 992) G.buf (G.sp - 696) 2 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfP.m34 (G.XP m)) G.o
    ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega, by rfl⟩ c1
    (h1.repin (by
      simp only [Lua.Vm.AtF.SnprintfP.r32, SnG.XP, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h1
      pins_of h1))
  refine ⟨c2, M1, s1.trans s2, ?_, hmv⟩
  dsimp only [mmRet] at hr2
  refine hr2.repin ?_
  simp only [Lua.Vm.AtF.SnprintfP.r33, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr2

/-! ## The digits' `memmove` -/

/-- What the root after the prefix's `memmove` reads. -/
structure FacQ1 (G : SnG) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x1f#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 512)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = 0xa#64
  e632 : bytesT4 M (G.sp - 632) = 0x1#32
  e488 : bytesT8 M (G.sp - 488) = 0x8#64
  e496 : bytesT8 M (G.sp - 496) = BitVec.ofNat 64 (G.sp - 524)

theorem facQ1 (G : SnG) (MP : Mem) (F : FacC G MP) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) M1 G.buf (G.sp - 696) 2) : FacQ1 G M1 := by
  obtain ⟨fap, fptr, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- **From the prefix's `memmove` to the digits'** (`run_Q1`). -/
theorem snpP_mv2 (G : SnG) (m : Mem) (hin : G.InP m) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.XP m)) M1 G.buf (G.sp - 696) 2) (c2 : Config)
    (hQ : SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfP.r33 (G.X {} M1)) (ArmPay (G.X {} M1).m (G.X {} M1).o) c2) :
    ∃ c3 M2, Steps c2 c3 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfP.r36 (G.X {} M2)) (ArmPay (G.X {} M2).m (G.X {} M2).o) c3 ∧
      MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8 := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := facQ1 G (G.MP m) (facC G m hin) (by omega) (by omega) (by omega) M1 hmv
  obtain ⟨c3, s3, h3⟩ := Lua.Vm.AtF.SnprintfP.Runs.run_Q1 (G.X {} M1) (by sn_ok) (by sn_u1; exact a1)
    (by sn_u1; exact a2) (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5) (by sn_u1; exact a6)
    (by sn_u1; exact a7) (by sn_u1; exact a8) (by sn_u1; exact a9) c2 hQ
  obtain ⟨c4, s4, M2, hr, hmv2⟩ := memmove_sum (G.sp - 992) (G.buf + 2) (G.sp - 524) 8 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) G.o
    ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega, by rfl⟩ c3
    (h3.repin (by
      simp only [Lua.Vm.AtF.SnprintfP.r35, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h3
      pins_of h3))
  refine ⟨c4, M2, s3.trans s4, ?_, hmv2⟩
  dsimp only [mmRet] at hr
  refine hr.repin ?_
  simp only [Lua.Vm.AtF.SnprintfP.r36, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr

/-! ## The return -/

/-- What the root after the digits' `memmove` reads that the `'p'`
conversion's path stored (`__ssprint_r`'s and `__ssputs_r`'s saved words,
`_svfprintf_r`'s slots), at the root after the prefix's `memmove`. -/
structure FacQ1b (G : SnG) (M : Mem) : Prop where
  e880 : bytesT8 M (G.sp - 880) = 0x8005d1b8#64
  e896 : bytesT8 M (G.sp - 896) = 0x10#64
  e904 : bytesT8 M (G.sp - 904) = 0x25#64
  e912 : bytesT8 M (G.sp - 912) = 0xfffffffffffffff7#64
  e920 : bytesT8 M (G.sp - 920) = BitVec.ofNat 64 (G.sp - 512)
  e872 : bytesT8 M (G.sp - 872) = 0x80043ea4#64
  e888 : bytesT8 M (G.sp - 888) = 0x8005cff0#64
  e832 : bytesT8 M (G.sp - 832) = 0x0#64
  e864 : bytesT8 M (G.sp - 864) = BitVec.ofNat 64 (G.fmt + 2)
  e848 : bytesT8 M (G.sp - 848) = 0xa#64

theorem facQ1b (G : SnG) (MP : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) M1 G.buf (G.sp - 696) 2) : FacQ1b G M1 := by
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- What the root after the digits' `memmove` reads of `__ssprint_r`'s and
`__ssputs_r`'s frames, the uio and `_svfprintf_r`'s slots. -/
structure FacQ2a (G : SnG) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x1d#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 (G.buf + 2)
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 496)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = 0x8#64

theorem facQ2a (G : SnG) (M1 : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8) : FacQ2a G M2 := by
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem facQ2b (G : SnG) (M1 : Mem) (F : FacQ1b G M1) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8) : FacQ1b G M2 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem agreeP_Q1X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfP.m38 X) := by fmt_agree3

theorem agreeP_Q2X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfP.m44 X) := by fmt_agree3

/-! ### The bytes at the buffer -/

/-- The low byte of a halfword store. -/
theorem fw1_wm2_lo {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x = a) :
    bytesT1 (writeMap2 m a d) x = d.extractLsb' 0 8 := by
  subst h
  simp only [writeMap2, bytesT1]
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp), Std.ExtHashMap.getElem?_insert_self]
  rfl

/-- The high byte of a halfword store. -/
theorem fw1_wm2_hi {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x = a + 1) :
    bytesT1 (writeMap2 m a d) x = d.extractLsb' 8 8 := by
  subst h
  simp only [writeMap2, bytesT1]
  rw [Std.ExtHashMap.getElem?_insert_self]
  rfl

/-- **The `0x` prefix at the buffer** (the first `memmove` of the `'p'`
conversion's `ox`). -/
theorem ptrP_pre (G : SnG) (MP M1 M2 : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) M1 G.buf (G.sp - 696) 2)
    (hmv2 : MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8) :
    bytesT1 M2 G.buf = 0x30#8 ∧ bytesT1 M2 (G.buf + 1) = 0x78#8 := by
  have hS : 4096 ≤ G.sp := by omega
  have k : ∀ j, j < 2 → bytesT1 M2 (G.buf + j) =
      bytesT1 (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) (G.sp - 696 + j) := by
    intro j hj
    rw [hmv2.rd1 (by omega), ← hmv.moved j hj]
    simp only [Lua.Vm.AtF.SnprintfP.m38, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
  have e0 := k 0 (by omega)
  have e1 := k 1 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1]
  simp only [Lua.Vm.AtF.SnprintfP.m34, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins]
  rw [fw1_wm2_lo rfl, fw1_wm2_hi rfl]
  exact ⟨by decide, by decide⟩

/-- **The hex digits at the buffer** (the second `memmove`, of the digits
the conversion stored below `sp - 516`). -/
theorem ptrP_dig (G : SnG) (MP M1 M2 : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) M1 G.buf (G.sp - 696) 2)
    (hmv2 : MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8) :
    ∀ j, j < 8 → bytesT1 M2 (G.buf + 2 + j) = ptrBytes.getD (j + 2) 0 := by
  have hS : 4096 ≤ G.sp := by omega
  intro j hj
  rw [hmv2.moved j hj]
  have k : bytesT1 (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) (G.sp - 524 + j) =
      bytesT1 (Lua.Vm.AtF.SnprintfP.m34 (G.X {} MP)) (G.sp - 524 + j) := by
    simp only [Lua.Vm.AtF.SnprintfP.m38, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
    exact hmv.rd1 (by omega)
  rw [k]
  simp only [Lua.Vm.AtF.SnprintfP.m34, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins,
      Lua.Vm.Sim.AtF.fw1_same, Lua.Vm.Sim.AtF.fw1_wm2]; decide)

/-- **What `snprintf(buf, 32, "%p", print)` concludes**: `wrRet` with `10`,
`"0x80022f18"` and the `'\0'` at the buffer, the memory kept off the stack
window and the buffer. -/
def SnPostP (G : SnG) (m : Mem) (c : Config) : Prop :=
  ∃ m', wrRet G.r G.sp 10 G.f m' G.o c ∧ bytesAt m' G.buf 11 = ptrBytes ++ [0#8] ∧
    ∀ a, (a + 4096 ≤ G.sp ∨ G.sp ≤ a) → (a < G.buf ∨ G.buf + 44 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- The buffer's eleven bytes at the return's memory. -/
theorem ptrP_bytes (G : SnG) (M2 : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf)
    (hpre : bytesT1 M2 G.buf = 0x30#8 ∧ bytesT1 M2 (G.buf + 1) = 0x78#8)
    (hdig : ∀ j, j < 8 → bytesT1 M2 (G.buf + 2 + j) = ptrBytes.getD (j + 2) 0) :
    bytesAt (Lua.Vm.AtF.SnprintfP.m44 (G.X {} M2)) G.buf 11 = ptrBytes ++ [0#8] := by
  have k : ∀ j, j < 10 → bytesT1 (Lua.Vm.AtF.SnprintfP.m44 (G.X {} M2)) (G.buf + j) = bytesT1 M2 (G.buf + j) := by
    intro j hj
    simp only [Lua.Vm.AtF.SnprintfP.m44, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_wm2,
      Lua.Vm.Sim.AtF.fw1_ins]
  have k10 : bytesT1 (Lua.Vm.AtF.SnprintfP.m44 (G.X {} M2)) (G.buf + 10) = 0#8 := by
    simp only [Lua.Vm.AtF.SnprintfP.m44, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [Lua.Vm.Sim.AtF.fw1_same rfl]; decide
  have d : ∀ j, 2 ≤ j → j < 10 → bytesT1 M2 (G.buf + j) = ptrBytes.getD j 0 := fun j h1 h2 => by
    have := hdig (j - 2) (by omega)
    rwa [show G.buf + 2 + (j - 2) = G.buf + j by omega, show j - 2 + 2 = j by omega] at this
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, Nat.add_zero]
  rw [show G.buf = G.buf + 0 from rfl, k 0 (by omega), k 1 (by omega), k 2 (by omega), k 3 (by omega),
    k 4 (by omega), k 5 (by omega), k 6 (by omega), k 7 (by omega), k 8 (by omega), k 9 (by omega), k10,
    d 2 (by omega) (by omega), d 3 (by omega) (by omega), d 4 (by omega) (by omega), d 5 (by omega) (by omega),
    d 6 (by omega) (by omega), d 7 (by omega) (by omega), d 8 (by omega) (by omega),
    d 9 (by omega) (by omega), Nat.add_zero, hpre.1, hpre.2]
  rfl

/-- **From the digits' `memmove` to the return** (`run_Q2`). -/
theorem snpP_ret (G : SnG) (m : Mem) (hin : G.InP m) (M1 M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfP.m34 (G.XP m)) M1 G.buf (G.sp - 696) 2)
    (hmv2 : MoveOut (Lua.Vm.AtF.SnprintfP.m38 (G.X {} M1)) M2 (G.buf + 2) (G.sp - 524) 8) (c3 : Config)
    (hQ : SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfP.r36 (G.X {} M2)) (ArmPay (G.X {} M2).m (G.X {} M2).o) c3) :
    ∃ c', Steps c3 c' ∧ SnPostP G m c' := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have F1b := facQ1b G (G.MP m) (by omega) (by omega) (by omega) M1 hmv
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := facQ2a G M1 (by omega) (by omega) (by omega) M2 hmv2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := facQ2b G M1 F1b (by omega) (by omega) (by omega) M2 hmv2
  have ag1 : Agree (snWd G) (G.MP m) M2 :=
    ((((agreeP_CX (G.XP m) hin.sp_lo).tr (agree_move (G := G) hmv (by omega) (by omega))).tr
      (agreeP_Q1X (G.X {} M1) hin.sp_lo)).tr (agree_move (G := G) hmv2 (by omega) (by omega)))
  obtain ⟨⟨v2, v3, v4, v5, v7, v8, v9, v10, v11⟩, ⟨vfp, vfl, v6, vra, vs0, vs1, cs1, cra, cs0⟩⟩ :=
    (snSaveP_C G m hin).congr ag1 (by omega) (by omega)
  have agk : Agree (snWk G) m M2 :=
    ((agreeP_E G m hin).tr (agreeP_F G m hin)).tr (snWd_snWk ag1 (by omega))
  have st := hin.stat.agree agk hin.sp_lo hin.b_lo
  obtain ⟨-, -, f2⟩ := fmtP_of hin agk
  obtain ⟨c4, s4, h4⟩ := Lua.Vm.AtF.SnprintfP.Runs.run_Q2 (G.X {} M2) (by sn_ok)
    (by sn_u1; exact a1) (by sn_u1; exact a2) (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5)
    (by sn_u1; exact a6) (by sn_u1; exact b1) (by sn_u1; exact b2) (by sn_u1; exact b3) (by sn_u1; exact b4)
    (by sn_u1; exact b5) (by sn_u1; exact b6) (by sn_u1; exact b7) (by sn_u1; exact b8) (by sn_u1; exact b9)
    (by sn_u1; exact st.mbtowc) (by sn_u1; exact st.mbmax) (by sn_u1; exact f2) (by sn_u1; exact vfp)
    (by sn_u1; exact vfl) (by sn_u1; exact v2) (by sn_u1; exact v3) (by sn_u1; exact v4) (by sn_u1; exact v5)
    (by sn_u1; exact v7) (by sn_u1; exact v8) (by sn_u1; exact v9) (by sn_u1; exact v10) (by sn_u1; exact v11)
    (by sn_u1; exact vra) (by sn_u1; exact vs0) (by sn_u1; exact b10) (by sn_u1; exact vs1) (by sn_u1; exact v6)
    (by sn_u1; exact cs0) (by sn_u1; exact cra) (by sn_u1; exact cs1) c3 hQ
  have ag2 : Agree (snWd G) M2 _ := agreeP_Q2X (G.X {} M2) hin.sp_lo
  refine ⟨c4, s4, Lua.Vm.AtF.SnprintfP.m44 (G.X {} M2), ?_,
    ptrP_bytes G M2 (by omega) (by omega) (ptrP_pre G (G.MP m) M1 M2 (by omega) (by omega) hmv hmv2)
      (ptrP_dig G (G.MP m) M1 M2 (by omega) (by omega) hmv hmv2), ?_⟩
  · dsimp only [wrRet]
    refine h4.repin ?_
    simp only [Lua.Vm.AtF.SnprintfP.r38, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] at h4
    pins_of h4
  · intro a h1 h2
    exact (agk.tr (snWd_snWk ag2 (by omega))).t1 (by simp only [snWk, snWkN]; omega)

/-! ## The summary -/

/-- **`lua_pointer2str` on `print`** (lane F1-24): `snprintf(buf, 32, "%p",
0x80022f18)` writes `"0x80022f18"` and a `'\0'` at `buf`, returns `10`, and
keeps every byte off the stack window and the buffer. -/
theorem snprintfP_sum (sp buf fmt : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hin : PtrFmtIn m sp buf fmt r) :
    Triple (SegSt 0x80034de0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 buf⟩, ⟨Register.x11, BitVec.ofNat 64 32⟩,
        ⟨Register.x12, BitVec.ofNat 64 fmt⟩, ⟨Register.x13, 0x80022f18#64⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 10 f m' o c ∧ bytesAt m' buf 11 = ptrBytes ++ [0#8] ∧
        ∀ a, (a + 4096 ≤ sp ∨ sp ≤ a) → (a < buf ∨ buf + 44 ≤ a) → bytesT1 m' a = bytesT1 m a) := by
  intro c h
  simp only [callPre, List.cons_append, List.nil_append] at h
  obtain ⟨a4, ha4⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 14 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x14, a4⟩ :: _) h ⟨ha4, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 15 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x15, a5⟩ :: _) h ⟨ha5, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a6, ha6⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 16 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x16, a6⟩ :: _) h ⟨ha6, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a7, ha7⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 17 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x17, a7⟩ :: _) h ⟨ha7, Vsa.Sim.SegSt.pins h⟩
  let G : SnG := ⟨sp, buf, fmt, 0#64, r, f, a4, a5, a6, a7, o⟩
  have hin' : G.InP m := hin
  have h0 : SegSt 0x80034de0#64 (Lua.Vm.AtF.SnprintfP.r0 (G.X0 m)) (ArmPay (G.X0 m).m (G.X0 m).o) c := by
    refine h.repin ?_
    simp only [Lua.Vm.AtF.SnprintfP.r0, SnG.X0, SnG.X, G, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    pins_of h
  obtain ⟨c1, s1, h1⟩ := snpP_toC G m hin' c h0
  obtain ⟨c2, M1, s2, h2, hmv⟩ := snpP_mv1 G m hin' c1 h1
  obtain ⟨c3, M2, s3, h3, hmv2⟩ := snpP_mv2 G m hin' M1 hmv c2 h2
  obtain ⟨c4, s4, h4⟩ := snpP_ret G m hin' M1 M2 hmv hmv2 c3 h3
  exact ⟨c4, s1.trans (s2.trans (s3.trans s4)), h4⟩

end Lua.Vm.Sim.Kit
