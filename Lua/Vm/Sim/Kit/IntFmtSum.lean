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

/-- The `'d'` conversion's context. -/
abbrev SnG.XD (G : SnG) (m : Mem) : FCx := G.X {} (G.MD m)

/-- What a run writes: `snprintf`'s and its callees' frames (the 4 KiB below
`sp`) and the buffer. -/
def snWkN (sp buf a : Nat) : Prop := (sp < a + 4096 ∧ a < sp) ∨ (buf ≤ a ∧ a < buf + 44)
abbrev snWk (G : SnG) : Nat → Prop := snWkN G.sp G.buf

/-- What a run writes after the `'d'` conversion: `__ssprint_r`'s and
`__ssputs_r`'s frames, `_svfprintf_r`'s slots but its saved registers, `fp`
and the format cursor, `fp->_p` and `_w`, the buffer. -/
def snWdN (sp buf a : Nat) : Prop :=
  (sp ≤ a + 1000 ∧ a + 856 < sp) ∨ (sp ≤ a + 848 ∧ a + 400 < sp) ∨
    (sp ≤ a + 264 ∧ a + 248 < sp) ∨ (buf ≤ a ∧ a < buf + 44)
abbrev snWd (G : SnG) : Nat → Prop := snWdN G.sp G.buf

/-- A run's contexts and memories unfolded to the chains over the entry's. -/
macro "sn_unfold" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [SnG.MD, SnG.X0, SnG.X, at_row, abiCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] $[$loc]?)

/-- **A read of a run's memory**: the chains unfolded, the load forwarded
(`fat_rd`) onto the facts in context, a ground store's data evaluated. -/
macro "sn_rd" : tactic => `(tactic| (sn_unfold; fat_rd; try decide))

theorem Agree.st8 {R : Nat → Prop} {M m : Mem} {a : Nat} {d : BitVec (8 * 8)} (h : Agree R M m)
    (hR : ∀ j, j < 8 → R (a + j)) : Agree R M (writeMap8 m a d) := fun x hx => by
  rw [getElem?_writeMap8_out m a d x (by
    rcases Nat.lt_or_ge x a with h1 | h1
    · exact .inl h1
    · refine .inr (Nat.not_lt.1 fun h2 => hx ?_)
      have := hR (x - a) (by omega); rwa [Nat.add_sub_cancel' h1] at this)]
  exact h x hx
theorem Agree.st4 {R : Nat → Prop} {M m : Mem} {a : Nat} {d : BitVec (8 * 4)} (h : Agree R M m)
    (hR : ∀ j, j < 4 → R (a + j)) : Agree R M (writeMap4 m a d) := fun x hx => by
  rw [getElem?_writeMap4_out m a d x (by
    rcases Nat.lt_or_ge x a with h1 | h1
    · exact .inl h1
    · refine .inr (Nat.not_lt.1 fun h2 => hx ?_)
      have := hR (x - a) (by omega); rwa [Nat.add_sub_cancel' h1] at this)]
  exact h x hx
theorem Agree.st1 {R : Nat → Prop} {M m : Mem} {a : Nat} {d : BitVec 8} (h : Agree R M m)
    (hR : R a) : Agree R M (m.insert a d) := fun x hx => by
  rw [Lua.Vm.Sim.AtF.ins_out m a d x (by
    rcases Nat.lt_or_ge x a with h1 | h1
    · exact .inl h1
    · refine .inr (Nat.not_lt.1 fun h2 => hx ?_)
      rwa [show x = a by omega])]
  exact h x hx

/-- **A store chain in a region** (store by store: each store's bytes in the
region, by `omega` on its offsets). -/
macro "fmt_agree2" : tactic => `(tactic| (
  sn_unfold
  repeat (first | with_reducible exact Agree.refl _ _ | with_reducible apply Agree.st8 | with_reducible apply Agree.st4 | with_reducible apply Agree.st1)
  all_goals first
    | exact Agree.refl _ _
    | (intro j hj; simp only [snWd, snWk, snWdN, snWkN]; omega)
    | (simp only [snWd, snWk, snWdN, snWkN]; omega)))

/-- **A store chain off a region**: every store of the (unfolded) chain lies
in the region (`omega` per store). -/
macro "fmt_agree" : tactic => `(tactic| (
  intro x hx
  simp only [snWk, snWd, snWkN, snWdN, not_or, not_and, Nat.not_lt] at hx
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
  · exact (ha.b8 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.impure
  · exact (ha.b8 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.decpt
  · exact (ha.b8 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.dotw
  · exact (ha.t1 (by simp only [snWk, snWkN]; omega)).trans hs.dot0
  · exact (ha.t1 (by simp only [snWk, snWkN]; omega)).trans hs.dot1
  · exact (ha.b8 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.mbtowc
  · exact (ha.t1 (by simp only [snWk, snWkN]; omega)).trans hs.mbmax
  · exact (ha.b4 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.jt_l
  · exact (ha.b4 fun i _ => by simp only [snWk, snWkN]; omega).trans hs.jt_d

/-- The format's bytes in a memory agreeing with the entry's. -/
theorem fmt_of {G : SnG} {m M : Mem} (h : G.In m) (ha : Agree (snWk G) m M) :
    bytesT1 M G.fmt = 0x25#8 ∧ bytesT1 M (G.fmt + 1) = 0x6c#8 ∧ bytesT1 M (G.fmt + 2) = 0x6c#8 ∧
      bytesT1 M (G.fmt + 3) = 0x64#8 ∧ bytesT1 M (G.fmt + 4) = 0x0#8 := by
  have := h.sp_lo; have := h.b_lo; have := h.f_hi
  obtain ⟨e0, e1, e2, e3, e4⟩ := h.fmt_at
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [ha.t1 (by simp only [snWk, snWkN]; omega)] <;> assumption

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
macro "sn_ok" : tactic => `(tactic| (constructor <;>
  simp only [SnG.XD, SnG.X0, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] <;> omega))

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
    s2 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s2
    s3 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s3
    s4 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s4
    s5 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s5
    s7 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s7
    s8 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s8
    s9 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s9
    s10 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s10
    s11 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.a.s11 }
  b := {
    fp := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.fp
    flags := (ha.b2 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.flags
    s6 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.s6
    vra := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.vra
    vs0 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.vs0
    vs1 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.vs1
    cs1 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.cs1
    cra := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.cra
    cs0 := (ha.b8 fun i _ => by simp only [snWd, snWdN]; omega).trans h.b.cs0 }

/-- `memmove`'s keep as an agreement. -/
theorem MoveOut.agree {m M : Mem} {D S t : Nat} (h : MoveOut m M D S t) :
    Agree (fun a => D ≤ a ∧ a < D + t) m M := fun a ha => h.keep a (by omega)

/-- A copy into the buffer is a write after the conversion. -/
theorem agree_move {G : SnG} {m M : Mem} {D S t : Nat} (h : MoveOut m M D S t) (h1 : G.buf ≤ D)
    (h2 : D + t ≤ G.buf + 44) : Agree (snWd G) m M :=
  h.agree.mono fun a ha => by simp only [snWd, snWdN]; omega

theorem snWd_snWk {G : SnG} {M M' : Mem} (h : Agree (snWd G) M M') (hs : 1000 ≤ G.sp) :
    Agree (snWk G) M M' :=
  h.mono fun a ha => by
    simp only [snWd, snWk, snWdN, snWkN] at ha ⊢
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
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

/-- Agreements off one region compose. -/
theorem Agree.tr {R : Nat → Prop} {m m1 m2 : Mem} (h1 : Agree R m m1) (h2 : Agree R m1 m2) : Agree R m m2 :=
  (h1.trans h2).mono fun _ h => h.elim id id

/-- A read of a run's memory down to the `'d'` conversion's root memory
(`SnG.MD` kept folded: its facts, `FacD`/`SnSave`, in context). -/
macro "sn_rd1" : tactic => `(tactic| (
  simp only [SnG.XD, SnG.X0, SnG.X, at_row, abiCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  fat_rd; try decide))

/-- **What `IntegerToStr_Statement` concludes** of a run. -/
def SnPost (G : SnG) (m : Mem) (c : Config) : Prop :=
  ∃ m', wrRet G.r G.sp (intBytes G.i).length G.f m' G.o c ∧
    bytesAt m' G.buf ((intBytes G.i).length + 1) = intBytes G.i ++ [0#8] ∧
    ∀ a, (a + 4096 ≤ G.sp ∨ G.sp ≤ a) → (a < G.buf ∨ G.buf + 44 ≤ a) → bytesT1 m' a = bytesT1 m a

/-- `intBytes` of a one-digit non-negative `i`. -/
theorem intBytes_one {i : BitVec 64} (hp : zopz0zKzJ_s i (0x0#64) = true) (hs : zopz0zI_u (0x9#64) i = false) :
    intBytes i = [digB i.toNat] ∧ i.toNat < 10 := by
  have hi : 0 ≤ i.toInt := by
    simp only [zopz0zKzJ_s, decide_eq_true_eq] at hp; simpa using hp
  have h9 : i.toNat ≤ 9 := by
    have e : BitVec.toNatInt (0x9#64 : BitVec 64) = 9 := by decide
    unfold zopz0zI_u at hs
    rw [e, decide_eq_false_iff_not] at hs
    simp only [BitVec.toNatInt, Int.ofNat_eq_coe] at hs
    omega
  refine ⟨?_, by omega⟩
  rw [intBytes_eq, magOf, if_neg (by omega), if_neg (by omega), List.nil_append, decBytes_lt (by omega)]

theorem MoveOut.rd4 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a + 4 ≤ D ∨ D + t ≤ a) :
    bytesT4 M a = bytesT4 m a := bT4_congr fun _ _ => h.keep _ (by omega)
theorem MoveOut.rd2 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a + 2 ≤ D ∨ D + t ≤ a) :
    bytesT2 M a = bytesT2 m a := bT2_congr fun _ _ => h.keep _ (by omega)

/-- A context's atoms unfolded, its memory kept. -/
macro "sn_u1" : tactic => `(tactic|
  simp only [SnG.XD, SnG.X0, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ])

set_option hygiene false in
/-- A read past a `memmove` (`hmv`, off the copy) down to the run's memories. -/
macro "sn_mv" : tactic => `(tactic| (
  sn_u1
  first
  | (rw [MoveOut.rd8 hmv (by omega)])
  | (rw [MoveOut.rd4 hmv (by omega)])
  | (rw [MoveOut.rd2 hmv (by omega)])
  | (rw [MoveOut.rd1 hmv (by omega)])
  sn_rd1))

/-- **A root path's stores in the writes after the conversion** (over a
generic context: its root memory is the base of the chain). -/
macro "fmt_agree3" : tactic => `(tactic| (
  simp only [at_row]
  repeat (first | with_reducible exact Agree.refl _ _ | with_reducible apply Agree.st8 | with_reducible apply Agree.st4 | with_reducible apply Agree.st1)
  all_goals first
    | (intro j hj; simp only [snWdN]; omega)
    | (simp only [snWdN]; omega)))

theorem agree_Dp1X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m27 X) := by fmt_agree3

theorem agree_Dp1 (G : SnG) (m : Mem) (h : G.In m) :
    Agree (snWd G) (G.MD m) (Lua.Vm.AtF.SnprintfLld.m27 (G.XD m)) := agree_Dp1X (G.XD m) h.sp_lo

theorem agree_Qp1X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m33 X) := by fmt_agree3

theorem agree_Qp1 (G : SnG) (M : Mem) (h : 0x8005e720 + 8192 ≤ G.sp) :
    Agree (snWd G) M (Lua.Vm.AtF.SnprintfLld.m33 (G.X {} M)) := agree_Qp1X (G.X {} M) h

/-- **A non-negative one-digit `i`, to `memmove` of its digit** (`run_Dp1`). -/
theorem snp_p1_mv (G : SnG) (m : Mem) (hin : G.In m)
    (hp : zopz0zKzJ_s G.i (0x0#64) = true) (hs : zopz0zI_u (0x9#64) G.i = false) (c : Config)
    (h : SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m)) (ArmPay (G.XD m).m (G.XD m).o) c) :
    ∃ c2 M1, Steps c c2 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r40 (G.X {} M1)) (ArmPay (G.X {} M1).m (G.X {} M1).o) c2 ∧
      MoveOut (Lua.Vm.AtF.SnprintfLld.m27 (G.XD m)) M1 G.buf (G.sp - 517) 1 := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := facD G m hin
  obtain ⟨c1, s1, h1⟩ := run_Dp1 (G.XD m) (by sn_ok) (by sn_u1; exact fap) (by sn_u1; exact fi)
    (by sn_u1; exact hp) (by sn_u1; exact hs) (by sn_u1; exact fsgn) (by sn_u1; exact fres)
    (by sn_u1; exact fcnt) (by sn_u1; exact fret) (by sn_u1; exact ffp) (by sn_u1; exact fiov)
    (by sn_u1; exact fw) (by sn_u1; exact fp) c h
  obtain ⟨c2, s2, M1, hr, hmv⟩ := memmove_sum (G.sp - 992) G.buf (G.sp - 517) 1 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfLld.m27 (G.XD m)) G.o
    ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega, by rfl⟩ c1
    (h1.repin (by
      simp only [Lua.Vm.AtF.SnprintfLld.r39, SnG.XD, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h1
      pins_of h1))
  refine ⟨c2, M1, s1.trans s2, ?_, hmv⟩
  dsimp only [mmRet] at hr
  refine hr.repin ?_
  simp only [Lua.Vm.AtF.SnprintfLld.r40, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr

/-- What the root after the digit's `memmove` reads of `__ssprint_r`'s and
`__ssputs_r`'s frames, the uio and `_svfprintf_r`'s slots. -/
structure FacQp1a (G : SnG) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x2b#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 512)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = 0x1#64
  e880 : bytesT8 M (G.sp - 880) = 0x8005d1b8#64
  e896 : bytesT8 M (G.sp - 896) = 0x10#64

structure FacQp1b (G : SnG) (M : Mem) : Prop where
  e904 : bytesT8 M (G.sp - 904) = 0x25#64
  e912 : bytesT8 M (G.sp - 912) = 0xfffffffffffffffe#64
  e920 : bytesT8 M (G.sp - 920) = BitVec.ofNat 64 (G.sp - 512)
  e872 : bytesT8 M (G.sp - 872) = 0x80043ea4#64
  e888 : bytesT8 M (G.sp - 888) = 0x8005cff0#64
  e832 : bytesT8 M (G.sp - 832) = 0x0#64
  e864 : bytesT8 M (G.sp - 864) = BitVec.ofNat 64 (G.fmt + 4)
  e848 : bytesT8 M (G.sp - 848) = 0x1#64

/-! ### Forwarding a stack read through stack stores (`S - k`, literal `k`):
the separations decided on the literals -/

theorem fwS8_wm8 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 8)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 8 ≤ k2 ∨ k2 + 8 ≤ k1) :
    bytesT8 (writeMap8 m (S - k1) d) (S - k2) = bytesT8 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw8_wm8 (by omega)
theorem fwS8_wm4 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 4)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 8 ≤ k2 ∨ k2 + 4 ≤ k1) :
    bytesT8 (writeMap4 m (S - k1) d) (S - k2) = bytesT8 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw8_wm4 (by omega)
theorem fwS8_wm2 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 2)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 8 ≤ k2 ∨ k2 + 2 ≤ k1) :
    bytesT8 (writeMap2 m (S - k1) d) (S - k2) = bytesT8 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw8_wm2 (by omega)
theorem fwS8_ins {m : Mem} {S k1 k2 : Nat} {d : BitVec 8} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 8 ≤ k2 ∨ k2 + 1 ≤ k1) :
    bytesT8 (m.insert (S - k1) d) (S - k2) = bytesT8 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw8_ins (by omega)
theorem fwS4_wm8 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 8)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 4 ≤ k2 ∨ k2 + 8 ≤ k1) :
    bytesT4 (writeMap8 m (S - k1) d) (S - k2) = bytesT4 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw4_wm8 (by omega)
theorem fwS4_wm4 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 4)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 4 ≤ k2 ∨ k2 + 4 ≤ k1) :
    bytesT4 (writeMap4 m (S - k1) d) (S - k2) = bytesT4 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw4_wm4 (by omega)
theorem fwS4_wm2 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 2)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 4 ≤ k2 ∨ k2 + 2 ≤ k1) :
    bytesT4 (writeMap2 m (S - k1) d) (S - k2) = bytesT4 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw4_wm2 (by omega)
theorem fwS4_ins {m : Mem} {S k1 k2 : Nat} {d : BitVec 8} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 4 ≤ k2 ∨ k2 + 1 ≤ k1) :
    bytesT4 (m.insert (S - k1) d) (S - k2) = bytesT4 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw4_ins (by omega)
theorem fwS2_wm8 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 8)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 2 ≤ k2 ∨ k2 + 8 ≤ k1) :
    bytesT2 (writeMap8 m (S - k1) d) (S - k2) = bytesT2 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw2_wm8 (by omega)
theorem fwS2_wm4 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 4)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 2 ≤ k2 ∨ k2 + 4 ≤ k1) :
    bytesT2 (writeMap4 m (S - k1) d) (S - k2) = bytesT2 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw2_wm4 (by omega)
theorem fwS2_wm2 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 2)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 2 ≤ k2 ∨ k2 + 2 ≤ k1) :
    bytesT2 (writeMap2 m (S - k1) d) (S - k2) = bytesT2 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw2_wm2 (by omega)
theorem fwS2_ins {m : Mem} {S k1 k2 : Nat} {d : BitVec 8} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 2 ≤ k2 ∨ k2 + 1 ≤ k1) :
    bytesT2 (m.insert (S - k1) d) (S - k2) = bytesT2 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw2_ins (by omega)
theorem fwS1_wm8 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 8)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 1 ≤ k2 ∨ k2 + 8 ≤ k1) :
    bytesT1 (writeMap8 m (S - k1) d) (S - k2) = bytesT1 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw1_wm8 (by omega)
theorem fwS1_wm4 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 4)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 1 ≤ k2 ∨ k2 + 4 ≤ k1) :
    bytesT1 (writeMap4 m (S - k1) d) (S - k2) = bytesT1 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw1_wm4 (by omega)
theorem fwS1_wm2 {m : Mem} {S k1 k2 : Nat} {d : BitVec (8 * 2)} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 1 ≤ k2 ∨ k2 + 2 ≤ k1) :
    bytesT1 (writeMap2 m (S - k1) d) (S - k2) = bytesT1 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw1_wm2 (by omega)
theorem fwS1_ins {m : Mem} {S k1 k2 : Nat} {d : BitVec 8} (hS : 4096 ≤ S) (h1 : k1 ≤ 4096)
    (h2 : k2 ≤ 4096) (h : k1 + 1 ≤ k2 ∨ k2 + 1 ≤ k1) :
    bytesT1 (m.insert (S - k1) d) (S - k2) = bytesT1 m (S - k2) :=
  Lua.Vm.Sim.AtF.fw1_ins (by omega)

/-- **A read of a stack slot through a chain of stack stores** down to the
root memory, rewritten by the facts in context (`*`): the separations on
the literal offsets (`decide`), `sp ≥ 4096` by `assumption`. -/
macro "sn_rd2" : tactic => `(tactic| (
  simp only [SnG.X, at_row, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := first | assumption | decide | rfl) only [fwS8_wm8, fwS8_wm4, fwS8_wm2, fwS8_ins, fwS4_wm8, fwS4_wm4, fwS4_wm2, fwS4_ins, fwS2_wm8, fwS2_wm4, fwS2_wm2, fwS2_ins, fwS1_wm8, fwS1_wm4, fwS1_wm2, fwS1_ins,
    Lua.Vm.Sim.AtF.fw8_same, Lua.Vm.Sim.AtF.fw4_same, Lua.Vm.Sim.AtF.fw2_same, Lua.Vm.Sim.AtF.fw1_same, *]
  try decide))

set_option hygiene false in
/-- A read past a `memmove` (`hmv`, off the copy). -/
macro "sn_mv2" : tactic => `(tactic| (
  simp (disch := omega) only [MoveOut.rd8 hmv, MoveOut.rd4 hmv, MoveOut.rd2 hmv, MoveOut.rd1 hmv]
  sn_rd2))

theorem facQp1a (G : SnG) (MD : Mem) (F : FacD G MD) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m27 (G.X {} MD)) M1 G.buf (G.sp - 517) 1) : FacQp1a G M1 := by
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem facQp1b (G : SnG) (MD : Mem) (F : FacD G MD) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hbl : 0x8005e720 ≤ G.buf) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m27 (G.X {} MD)) M1 G.buf (G.sp - 517) 1) : FacQp1b G M1 := by
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- **A non-negative one-digit `i`, from the digit's `memmove` to the
return** (`run_Qp1`): `wrRet` with `1`, the digit and the `'\0'` at the
buffer, the memory kept off the run's writes. -/
theorem snp_p1_ret (G : SnG) (m : Mem) (hin : G.In m)
    (hp : zopz0zKzJ_s G.i (0x0#64) = true) (hs : zopz0zI_u (0x9#64) G.i = false) (M1 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m27 (G.XD m)) M1 G.buf (G.sp - 517) 1) (c2 : Config)
    (hQ : SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r40 (G.X {} M1)) (ArmPay (G.X {} M1).m (G.X {} M1).o) c2) :
    ∃ c', Steps c2 c' ∧ SnPost G m c' := by
  have := hin.sp_lo; have := hin.sp_hi; have := hin.sp_al; have := hin.ra; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have FD := facD G m hin
  have ag1 : Agree (snWd G) (G.MD m) M1 := (agree_Dp1 G m hin).tr (agree_move (G := G) hmv (by omega) (by omega))
  obtain ⟨⟨v2, v3, v4, v5, v7, v8, v9, v10, v11⟩, ⟨vfp, vfl, v6, vra, vs0, vs1, cs1, cra, cs0⟩⟩ :=
    (snSave_D G m hin).congr ag1 (by omega) (by omega)
  have agk : Agree (snWk G) m M1 :=
    ((agree_E G m hin).tr (agree_F G m hin)).tr (snWd_snWk ag1 (by omega))
  have st := stat_of hin agk
  obtain ⟨-, -, -, -, f4⟩ := fmt_of hin agk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := facQp1a G (G.MD m) FD (by omega) (by omega) (by omega) M1 hmv
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := facQp1b G (G.MD m) FD (by omega) (by omega) (by omega) M1 hmv
  obtain ⟨c3, s3, h3⟩ := run_Qp1 (G.X {} M1) (by sn_ok)
    (by sn_u1; exact a1) (by sn_u1; exact a2) (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5)
    (by sn_u1; exact a6) (by sn_u1; exact a7) (by sn_u1; exact a8) (by sn_u1; exact b1) (by sn_u1; exact b2)
    (by sn_u1; exact b3) (by sn_u1; exact b4) (by sn_u1; exact b5) (by sn_u1; exact b6) (by sn_u1; exact b7)
    (by sn_u1; exact st.mbtowc) (by sn_u1; exact st.mbmax) (by sn_u1; exact f4) (by sn_u1; exact vfp)
    (by sn_u1; exact vfl) (by sn_u1; exact v2) (by sn_u1; exact v3) (by sn_u1; exact v4) (by sn_u1; exact v5)
    (by sn_u1; exact v7) (by sn_u1; exact v8) (by sn_u1; exact v9) (by sn_u1; exact v10) (by sn_u1; exact v11)
    (by sn_u1; exact vra) (by sn_u1; exact vs0) (by sn_u1; exact b8) (by sn_u1; exact vs1) (by sn_u1; exact v6)
    (by sn_u1; exact cs0) (by sn_u1; exact cra) (by sn_u1; exact cs1) c2 hQ
  obtain ⟨hib, hlt⟩ := intBytes_one hp hs
  have hd : bytesT1 M1 G.buf = digB G.i.toNat := by
    have e := hmv.moved 0 (by omega)
    simp only [Nat.add_zero] at e
    rw [e]
    simp only [SnG.XD, SnG.X, at_row, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    have hS : 4096 ≤ G.sp := by omega
    simp (disch := first | assumption | decide | rfl) only [fwS1_wm8, fwS1_wm4, fwS1_wm2, fwS1_ins,
      Lua.Vm.Sim.AtF.fw1_same]
    exact digit_byte G.i hlt
  have ag2 := agree_Qp1 G M1 (by omega)
  refine ⟨c3, s3, Lua.Vm.AtF.SnprintfLld.m33 (G.X {} M1), ?_, ?_, ?_⟩
  · rw [hib]
    dsimp only [wrRet]
    refine h3.repin ?_
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    simp only [Lua.Vm.AtF.SnprintfLld.r42, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] at h3
    pins_of h3
  · rw [hib]
    simp only [bytesAt, List.length_cons, List.length_nil, Nat.zero_add, List.range_succ, List.range_zero,
      List.nil_append, List.map_cons, List.map_nil, List.map_append, List.cons_append, Nat.add_zero]
    have k0 : bytesT1 (Lua.Vm.AtF.SnprintfLld.m33 (G.X {} M1)) G.buf = bytesT1 M1 G.buf := by
      simp only [Lua.Vm.AtF.SnprintfLld.m33, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins]
    have k1 : bytesT1 (Lua.Vm.AtF.SnprintfLld.m33 (G.X {} M1)) (G.buf + 1) = 0#8 := by
      simp only [Lua.Vm.AtF.SnprintfLld.m33, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      rw [Lua.Vm.Sim.AtF.fw1_same rfl]; decide
    rw [k0, hd, k1]
  · intro a h1 h2
    exact (agk.tr (snWd_snWk ag2 (by omega))).t1 (by simp only [snWk, snWkN]; omega)

end Lua.Vm.Sim.Kit
