import Lua.Vm.Sim.Kit.IntFmt

/-!
# `IntegerToStr_Statement` from the root runs (lane F1-FMT)

The runs of `Kit/IntFmt.lean` composed: each root's context is `SnG.X` over
the memory the previous root's run left (a store chain over the previous
root memory, or `memmove`'s result through its `MoveOut`). The facts a root
reads are named structures (`FacF`, `FacD`, `SnSave`, …), each proven from
the previous memory by forwarding (`fat_rd`) or carried by an agreement off
the run's writes (`Agree`, `snWk`: the stack window and the buffer; `snWd`:
what is written after the `'d'` conversion).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- The run's facts on its fixed data (the statement's `IntFmtIn`). -/
abbrev SnG.In (G : SnG) (m : Mem) : Prop := IntFmtIn m G.sp G.buf G.fmt G.r

/-- The entry context. -/
abbrev SnG.X0 (G : SnG) (m : Mem) : FCx := G.X {} m

/-- The `'d'` conversion's root memory: `_svfprintf_r`'s format scan after
the prologue. -/
@[reducible] def SnG.MD (G : SnG) (m : Mem) : Mem :=
  Lua.Vm.AtF.SnprintfLld.m15 (G.X {} (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m)))

/-- What a run writes: `snprintf`'s and its callees' frames (the 4 KiB below
`sp`) and the buffer. -/
def snWk (G : SnG) (a : Nat) : Prop := (G.sp ≤ a + 4096 ∧ a < G.sp) ∨ (G.buf ≤ a ∧ a < G.buf + 44)

/-- What a run writes after the `'d'` conversion: `__ssprint_r`'s and
`__ssputs_r`'s frames, `_svfprintf_r`'s slots but its saved registers, `fp`
and the format cursor, `fp->_p` and `_w`, the buffer. -/
def snWd (G : SnG) (a : Nat) : Prop :=
  (G.sp ≤ a + 1000 ∧ a + 866 < G.sp) ∨ (G.sp ≤ a + 864 ∧ a + 856 < G.sp) ∨
    (G.sp ≤ a + 848 ∧ a + 500 < G.sp) ∨ (G.sp ≤ a + 264 ∧ a + 248 < G.sp) ∨ (G.buf ≤ a ∧ a < G.buf + 44)

/-- A run's contexts and memories unfolded to the chains over the entry's. -/
macro "sn_unfold" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [SnG.MD, SnG.X0, SnG.X, at_row, abiCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] $[$loc]?)

/-- **A read of a run's memory**: the chains unfolded, the load forwarded
(`fat_rd`) onto the facts in context, a ground store's data evaluated. -/
macro "sn_rd" : tactic => `(tactic| (sn_unfold; fat_rd; try decide))

/-- **A store chain off a region**: every store of the (unfolded) chain lies
in the region (`omega` per store). -/
macro "fmt_agree" : tactic => `(tactic| (
  intro x hx
  simp only [snWk, snWd, not_or, not_and, Nat.not_lt] at hx
  sn_unfold
  simp (disch := omega) only [getElem?_writeMap8_out, getElem?_writeMap4_out, getElem?_writeMap2_out,
    Lua.Vm.Sim.AtF.ins_out]))

/-- The format's bytes. -/
theorem SnG.In.fmt_at {G : SnG} {m : Mem} (h : G.In m) :
    bytesT1 m G.fmt = 0x25#8 ∧ bytesT1 m (G.fmt + 1) = 0x6c#8 ∧ bytesT1 m (G.fmt + 2) = 0x6c#8 ∧
      bytesT1 m (G.fmt + 3) = 0x64#8 ∧ bytesT1 m (G.fmt + 4) = 0x0#8 := by
  have e := h.fmtb
  simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.cons.injEq, Nat.add_zero] at e
  obtain ⟨e0, e1, e2, e3, e4, -⟩ := e
  exact ⟨e0, e1, e2, e3, e4⟩

/-- The entry's stores (`snprintf`, `_svfprintf_r`'s prologue, `memset`) are
in the stack window. -/
theorem agree_E (G : SnG) (m : Mem) (h : G.In m) :
    Agree (snWk G) m (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m)) := by
  have := h.sp_lo
  fmt_agree

/-- The static words in a memory agreeing with the entry's off the run's
writes. -/
theorem stat_of {G : SnG} {m M : Mem} (h : G.In m) (ha : Agree (snWk G) m M) : FmtStatic M := by
  have := h.sp_lo; have := h.b_lo; have hs := h.stat
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ha.b8 fun i _ => by simp only [snWk]; omega).trans hs.impure
  · exact (ha.b8 fun i _ => by simp only [snWk]; omega).trans hs.decpt
  · exact (ha.b8 fun i _ => by simp only [snWk]; omega).trans hs.dotw
  · exact (ha.t1 (by simp only [snWk]; omega)).trans hs.dot0
  · exact (ha.t1 (by simp only [snWk]; omega)).trans hs.dot1
  · exact (ha.b8 fun i _ => by simp only [snWk]; omega).trans hs.mbtowc
  · exact (ha.t1 (by simp only [snWk]; omega)).trans hs.mbmax
  · exact (ha.b4 fun i _ => by simp only [snWk]; omega).trans hs.jt_l
  · exact (ha.b4 fun i _ => by simp only [snWk]; omega).trans hs.jt_d

/-- The format's bytes in a memory agreeing with the entry's. -/
theorem fmt_of {G : SnG} {m M : Mem} (h : G.In m) (ha : Agree (snWk G) m M) :
    bytesT1 M G.fmt = 0x25#8 ∧ bytesT1 M (G.fmt + 1) = 0x6c#8 ∧ bytesT1 M (G.fmt + 2) = 0x6c#8 ∧
      bytesT1 M (G.fmt + 3) = 0x64#8 ∧ bytesT1 M (G.fmt + 4) = 0x0#8 := by
  have := h.sp_lo; have := h.b_lo; have := h.f_hi
  obtain ⟨e0, e1, e2, e3, e4⟩ := h.fmt_at
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [ha.t1 (by simp only [snWk]; omega)] <;> assumption

theorem agree_F (G : SnG) (m : Mem) (h : G.In m) :
    Agree (snWk G) (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m)) (G.MD m) := by
  have := h.sp_lo
  fmt_agree

/-- **What the `'d'` conversion's paths read** of its root memory. -/
structure FacD (G : SnG) (M : Mem) : Prop where
  ap : bytesT8 M (G.sp - 840) = BitVec.ofNat 64 (G.sp - 40)
  i : bytesT8 M (G.sp - 40) = G.i
  s760 : bytesT8 M (G.sp - 760) = 0x0#64
  sgn : bytesT1 M (G.sp - 697) = 0x0#8
  resid : bytesT8 M (G.sp - 624) = 0x0#64
  cnt : bytesT4 M (G.sp - 632) = 0x0#32
  ret : bytesT8 M (G.sp - 848) = 0x0#64
  fp : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)
  iov : bytesT8 M (G.sp - 640) = BitVec.ofNat 64 (G.sp - 512)
  w : bytesT4 M (G.sp - 252) = 0x2b#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf

theorem facD (G : SnG) (m : Mem) (h : G.In m) : FacD G (G.MD m) := by
  have := h.sp_lo
  constructor <;> sn_rd

/-- A root's context facts (`Ok_*`) from the run's facts. -/
macro "sn_ok" : tactic => `(tactic| (constructor <;> (try sn_unfold) <;> first | assumption | omega))

/-- A halfword read over the two bytes of a word store `simp` split. -/
theorem fw2_ins2 {m : Mem} {a x y : Nat} {b0 b1 : BitVec 8} (hx : x = a + 1) (hy : y = a) :
    bytesT2 ((m.insert a b0).insert x b1) y = b1.append b0 := by
  subst hx; subst hy
  simp only [bytesT2]
  rw [Std.ExtHashMap.getElem?_insert_self, Std.ExtHashMap.getElem?_insert, if_neg (by simp),
    Std.ExtHashMap.getElem?_insert_self]
  simp only [Option.getD_some]

/-- The flags word `snprintf` stored (`_flags = __SWR | __SSTR`, `_file = -1`). -/
theorem flags_F (G : SnG) (m : Mem) (h : G.In m) :
    bytesT2 (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m)) (G.sp - 248) = 0x208#16 := by
  have := h.sp_lo
  sn_unfold; fat_rd
  rw [fw2_ins2 (by omega) rfl]; decide

/-- **From the entry to the `'d'` conversion's root** (`run_E`, `run_F`). -/
theorem snp_toD (G : SnG) (m : Mem) (hin : G.In m) (c : Config)
    (h : SegSt 0x80034de0#64 (Lua.Vm.AtF.SnprintfLld.r0 (G.X0 m)) (ArmPay (G.X0 m).m (G.X0 m).o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.X {} (G.MD m)))
      (ArmPay (G.X {} (G.MD m)).m (G.X {} (G.MD m)).o) c' := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have hs := hin.stat
  obtain ⟨c1, s1, h1⟩ := run_E (G.X0 m) (by sn_ok) (by sn_unfold; exact hs.impure)
    (by sn_unfold; exact hs.decpt) (by sn_unfold; exact hs.dotw) (by sn_unfold; exact hs.dot0)
    (by sn_unfold; exact hs.dot1) c h
  have ha := agree_E G m hin
  have hs1 := stat_of hin ha
  obtain ⟨f0, f1, f2, f3, -⟩ := fmt_of hin ha
  have h1' : SegSt 0x80042ec0#64 (Lua.Vm.AtF.SnprintfLld.r16 (G.X {} (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m))))
      (ArmPay (G.X {} (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m))).m (G.X0 m).o) c1 := by
    sn_unfold at h1 ⊢; exact h1.repin (by pins_of h1)
  have hX1 : Lua.Vm.AtF.SnprintfLld.Ok_F (G.X {} (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m))) := by
    constructor <;> simp only [SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] <;> omega
  obtain ⟨c2, s2, h2⟩ := run_F (G.X {} (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m))) hX1
    (by sn_unfold; exact flags_F G m hin) (by sn_unfold; exact hs1.mbtowc) (by sn_unfold; exact hs1.mbmax)
    (by sn_unfold; exact f0) (by sn_unfold; exact f1) (by sn_unfold; exact hs1.jt_l) (by sn_unfold; exact f2)
    (by sn_unfold; exact f3) (by sn_unfold; exact hs1.jt_d) c1 h1'
  refine ⟨c2, s1.trans s2, ?_⟩
  sn_unfold at h2 ⊢; exact h2.repin (by pins_of h2)

/-! ## The frame `_svfprintf_r` restores, and the agreements after the conversion -/

/-- **The registers `_svfprintf_r` saved** after the `'d'` conversion's root
(its format scan's stores). -/
structure SnSaveA (G : SnG) (M : Mem) : Prop where
  s2 : bytesT8 M (G.sp - 304) = G.f.s2
  s3 : bytesT8 M (G.sp - 312) = G.f.s3
  s4 : bytesT8 M (G.sp - 320) = G.f.s4
  s5 : bytesT8 M (G.sp - 328) = G.f.s5
  s7 : bytesT8 M (G.sp - 344) = G.f.s7
  s8 : bytesT8 M (G.sp - 352) = G.f.s8
  s9 : bytesT8 M (G.sp - 360) = G.f.s9
  s10 : bytesT8 M (G.sp - 368) = G.f.s10
  s11 : bytesT8 M (G.sp - 376) = G.f.s11

/-- **The words `snprintf` and `_svfprintf_r`'s prologue stored** that the
return reads. -/
structure SnSaveB (G : SnG) (M : Mem) : Prop where
  fp : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)
  flags : bytesT2 M (G.sp - 248) = 0x208#16
  s6 : bytesT8 M (G.sp - 336) = G.f.s6
  vra : bytesT8 M (G.sp - 280) = 0x80034e58#64
  vs0 : bytesT8 M (G.sp - 288) = 0x2c#64
  vs1 : bytesT8 M (G.sp - 296) = 0x8005d1b8#64
  cs1 : bytesT8 M (G.sp - 72) = G.f.s1
  cra : bytesT8 M (G.sp - 56) = G.r
  cs0 : bytesT8 M (G.sp - 64) = G.f.s0

/-- **The frame the return reads**, on every memory after the `'d'`
conversion (none of it in `snWd`). -/
structure SnSave (G : SnG) (M : Mem) : Prop where
  a : SnSaveA G M
  b : SnSaveB G M

/-- The format scan's stores (`_svfprintf_r`'s saves, its slots) are below
`snprintf`'s `FILE`. -/
theorem agree_F2 (G : SnG) (m : Mem) (h : G.In m) :
    Agree (fun a => G.sp ≤ a + 4096 ∧ a + 296 < G.sp) (Lua.Vm.AtF.SnprintfLld.m12 (G.X0 m)) (G.MD m) := by
  have := h.sp_lo
  fmt_agree

theorem snSaveA_D (G : SnG) (m : Mem) (h : G.In m) : SnSaveA G (G.MD m) := by
  have := h.sp_lo
  constructor <;> sn_rd

theorem snSaveB_D (G : SnG) (m : Mem) (h : G.In m) : SnSaveB G (G.MD m) := by
  have := h.sp_lo
  have hfl : bytesT2 (G.MD m) (G.sp - 248) = 0x208#16 :=
    ((agree_F2 G m h).b2 fun i _ => by omega).trans (flags_F G m h)
  refine ⟨?_, hfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sn_rd

theorem snSave_D (G : SnG) (m : Mem) (h : G.In m) : SnSave G (G.MD m) :=
  ⟨snSaveA_D G m h, snSaveB_D G m h⟩

theorem SnSave.congr {G : SnG} {M M' : Mem} (h : SnSave G M) (ha : Agree (snWd G) M M')
    (hs : 0x8005e720 + 8192 ≤ G.sp) (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) : SnSave G M' where
  a := {
    s2 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s2
    s3 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s3
    s4 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s4
    s5 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s5
    s7 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s7
    s8 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s8
    s9 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s9
    s10 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s10
    s11 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.a.s11 }
  b := {
    fp := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.fp
    flags := (ha.b2 fun i _ => by simp only [snWd]; omega).trans h.b.flags
    s6 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.s6
    vra := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.vra
    vs0 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.vs0
    vs1 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.vs1
    cs1 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.cs1
    cra := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.cra
    cs0 := (ha.b8 fun i _ => by simp only [snWd]; omega).trans h.b.cs0 }

/-- `memmove`'s keep as an agreement. -/
theorem MoveOut.agree {m M : Mem} {D S t : Nat} (h : MoveOut m M D S t) :
    Agree (fun a => D ≤ a ∧ a < D + t) m M := fun a ha => h.keep a (by omega)

/-- A copy into the buffer is a write after the conversion. -/
theorem agree_move {G : SnG} {m M : Mem} {D S t : Nat} (h : MoveOut m M D S t) (h1 : G.buf ≤ D)
    (h2 : D + t ≤ G.buf + 44) : Agree (snWd G) m M :=
  h.agree.mono fun a ha => by simp only [snWd]; omega

theorem snWd_snWk {G : SnG} {M M' : Mem} (h : Agree (snWd G) M M') (hs : 1000 ≤ G.sp) :
    Agree (snWk G) M M' :=
  h.mono fun a ha => by
    simp only [snWd, snWk] at ha ⊢
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨by omega, by omega⟩
    · exact .inl ⟨by omega, by omega⟩
    · exact .inl ⟨by omega, by omega⟩
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr ⟨h1, h2⟩

/-- A digit's byte (`addiw a0, a0, 48; sb a0, …`). -/
theorem digit_byte (q : BitVec 64) (hq : q.toNat < 10) :
    stData 1 (sign_extend (m := 64) (Sail.BitVec.extractLsb (q + sign_extend (m := 64) (0x030#12)) 31 0)) =
      digB q.toNat := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < 10 ∧ q = BitVec.ofNat 64 k := ⟨q.toNat, hq, by simp⟩
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Lua.Vm.Sim.Kit
