import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Arms

/-!
# `OP_EQ` by the direct kit (round-3 bake-off, held-out case)

`Protect(cond = luaV_equalobj(L, s2v(ra), rb))`, then `docondjump`: the
`savestate` stores (`Scratch`), the call node `equalobj_sum` (M5), and the two
exits of `docondjump` (skip, `donextjump`). Two long strings are excluded
(`EqShort`): `abstractions/bakeoff3/KIT.md` records why the relation cannot
support that path.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `ci->u.l.trap` read through the `Scratch` stores. -/
theorem Core.trap_at {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {a : Nat} (ha : a = w.ci + 40) : bytesT4 c.σ.mem a = 0 := by
  subst ha; exact hc.trap

/-- An instruction word read through `Scratch` stores. -/
theorem Core.fetch_scratch {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {m : Mem} (h : ∀ x, ¬ Scratch w x → m[x]? = c.σ.mem[x]?) {pc : Nat} {ins : Word}
    (hf : p.fetch pc = some ins) : bytesT4 m (w.code + 4 * pc) = ins := by
  have hlt := fetch_lt hf
  refine (bytesT4_congr fun i hi => h _ fun hs => ?_).trans (hc.fetch hf)
  exact hc.ranges.code_out _ (by omega) (by omega) (.inr (.inr hs))

/-- `R[A]` and `R[B]` are not both long strings (the path `KIT.md` excludes). -/
def EqShort (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  ¬ (slotTag c.σ.mem (w.slot ins.a) = 84#8 ∧ slotTag c.σ.mem (w.slot ins.b) = 84#8)

/-- The frame `luaV_equalobj` keeps, read off the call site. -/
macro "kframe?" : term => `(KFrame.mk _ _ _ _ _ _ _ _ _ _ _)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [kraw_eq])

theorem eq_skip : ArmBody .EQ fun p c s w ins => EqShort p c s w ins ∧ ¬ FltAB p s ins ∧
    ∀ va vb, s.regs ins.a = some va → s.regs ins.b = some vb → ins.k ≠ decide (va = vb) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hl, hN, hkk⟩ => by
  kit_setup 0x8001c690
  rcases hnj : nextJump p s.pc with _ | t <;> simp [hnj] at hk htop
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  have hnfa := notFlt_of_reg (fun h => hN (.inl h)) hba
  have hnfb := notFlt_of_reg (fun h => hN (.inr h)) hbb
  have hk2 : ¬ decide (va = vb) = ins.k := fun e => hkk va vb hba hbb e.symm
  simp [Opnd.fill, δ, Value.rawEq_of_notFlt hnfa hnfb, VState.apply, writeDefs, KEdge.kills,
    Value.isFalse, hk2] at hk
  subst hk
  kit_run h0 acc until [0x8001b780]
  have hro : RodataRead c.σ.mem := hc.rodata
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (equalobj_sum _ _ (w.slot ins.a) (w.slot ins.b) w.sp kframe? _ _
      ⟨RodataRead.wm8 (RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch))
          (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch),
        by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
        by kit_disch⟩
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hva)
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hvb) hnfa hnfb
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl))
  have hg : ((if ins.k then 1#64 else 0#64) != (if va = vb then 1#64 else 0#64)) = true := by
    by_cases he : va = vb <;> cases hkb : ins.k <;> simp_all
  kit_run h0 acc
  have hLci := hr.L_sep_ci; simp only [stateSize, ciSize] at hLci
  simp (disch := kit_disch) only [bytesT4_wm8_out] at h0
  simp (disch := kit_disch) only [Core.trap_at hc] at h0
  simp only [trap_zero] at h0
  exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩

theorem eq_take : ArmBody .EQ fun p c s w ins => EqShort p c s w ins ∧ ¬ FltAB p s ins ∧
    ∀ va vb, s.regs ins.a = some va → s.regs ins.b = some vb → ins.k = decide (va = vb) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hl, hN, hkk⟩ => by
  kit_setup 0x8001c690
  rcases hnj : nextJump p s.pc with _ | t <;> simp [hnj] at hk htop
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  have hnfa := notFlt_of_reg (fun h => hN (.inl h)) hba
  have hnfb := notFlt_of_reg (fun h => hN (.inr h)) hbb
  have hk2 : decide (va = vb) = ins.k := (hkk va vb hba hbb).symm
  simp [Opnd.fill, δ, Value.rawEq_of_notFlt hnfa hnfb, VState.apply, writeDefs, KEdge.kills,
    Value.isFalse, hk2] at hk
  subst hk
  obtain ⟨ni, hni, hjt⟩ : ∃ ni, p.fetch (s.pc + 1) = some ni ∧ jumpTo (s.pc + 2) ni.sj = some t := by
    simp only [nextJump, Option.bind_eq_some_iff] at hnj; exact hnj
  have hlt1 := fetch_lt hni
  have hjt' := jumpTo_eq hjt
  have hsj : ni.sj < 2 ^ 25 := by
    simp only [Word.sj, Word.ax, Word.field, Word.offsetSJ]; have := ni.isLt; omega
  kit_run h0 acc until [0x8001b780]
  have hro : RodataRead c.σ.mem := hc.rodata
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (equalobj_sum _ _ (w.slot ins.a) (w.slot ins.b) w.sp kframe? _ _
      ⟨RodataRead.wm8 (RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch))
          (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch),
        by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
        by kit_disch⟩
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hva)
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hvb) hnfa hnfb
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl))
  have hg : ((if ins.k then 1#64 else 0#64) != (if va = vb then 1#64 else 0#64)) = false := by
    rw [← hk2]; by_cases he : va = vb <;> simp [he]
  clear hkk hk2
  kit_run h0 acc
  have hLci := hr.L_sep_ci; simp only [stateSize, ciSize] at hLci
  simp (disch := kit_disch) only [bytesT4_wm8_out] at h0
  simp (disch := kit_disch) only [Core.trap_at hc] at h0
  simp only [trap_zero] at h0
  rw [nextjump_pc ?_ (Core.fetch_scratch hc (by kit_frame) hni) hjt (by kit_disch) (by kit_disch)] at h0
  · exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩
  · kit_disch

/-- **`OP_EQ` but two long strings or a float**: both exits of `docondjump`. -/
theorem eq_short : ArmBody .EQ fun p c s w ins => EqShort p c s w ins ∧ ¬ FltAB p s ins :=
    fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hl, hN⟩ => by
  by_cases hk : ∀ va vb, s.regs ins.a = some va → s.regs ins.b = some vb → ins.k = decide (va = vb)
  · exact eq_take hS hA hf hop hstep ⟨hl, hN, hk⟩
  · refine eq_skip hS hA hf hop hstep ⟨hl, hN, fun va vb ha hb e => hk fun va' vb' ha' hb' => ?_⟩
    rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; exact e

/-- **`sim_EQ` from the long-string path**: `OP_EQ` off its float paths holds as soon as the
run with two long strings in `R[A]`, `R[B]` (`luaS_eqlngstr` → `memcmp`) is
supplied; `abstractions/bakeoff3/KIT.md` records why `VmRel` cannot supply it
(a string's bytes are described in the complement `w.mo` only, and nothing
places them outside the window, where the machine's `memcmp` reads them). -/
theorem sim_EQ_of_long (hlong : ArmBody .EQ fun p c s w ins => ¬ EqShort p c s w ins) :
    SimArmOn .EQ fun p s ins => ¬ FltAB p s ins :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hN =>
    (Classical.em (EqShort p c s w ins)).elim (fun hl => eq_short hS hA hf hop hstep ⟨hl, hN⟩)
      (hlong hS hA hf hop hstep)

end Lua.Vm.Sim.Kit
