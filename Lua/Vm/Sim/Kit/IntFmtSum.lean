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
def snWk (G : SnG) (a : Nat) : Prop := (G.sp - 4096 ≤ a ∧ a < G.sp) ∨ (G.buf ≤ a ∧ a < G.buf + 44)

/-- What a run writes after the `'d'` conversion: `__ssprint_r`'s and
`__ssputs_r`'s frames, `_svfprintf_r`'s slots but its saved registers, `fp`
and the format cursor, `fp->_p` and `_w`, the buffer. -/
def snWd (G : SnG) (a : Nat) : Prop :=
  (G.sp - 1000 ≤ a ∧ a < G.sp - 866) ∨ (G.sp - 864 ≤ a ∧ a < G.sp - 856) ∨
    (G.sp - 848 ≤ a ∧ a < G.sp - 500) ∨ (G.sp - 264 ≤ a ∧ a < G.sp - 248) ∨ (G.buf ≤ a ∧ a < G.buf + 44)

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

end Lua.Vm.Sim.Kit
