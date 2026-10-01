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

/-- `R[A]` and `R[B]` are not both long strings (the path `KIT.md` excludes). -/
def EqShort (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  ¬ (slotTag c.σ.mem (w.slot ins.a) = 84#8 ∧ slotTag c.σ.mem (w.slot ins.b) = 84#8)

/-- The frame `luaV_equalobj` keeps, read off the call site. -/
macro "kframe?" : term => `(KFrame.mk _ _ _ _ _ _ _ _ _ _ _)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [kraw_eq])

set_option hygiene false in
/-- `OP_EQ` up to `luaV_equalobj`'s return (`0x8001c6c4`), with `hkk` the
kernel's choice of edge. -/
local macro "eq_call" : tactic => `(tactic| (
  rcases hnj : nextJump p s.pc with _ | t <;> simp [hnj] at hk htop
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse] at hk
  kit_run h0 acc until [0x8001b780]
  simp (disch := decide) only [slot_addr] at h0
  have hro : RodataRead c.σ.mem := hc.rodata
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (equalobj_sum _ _ (w.slot ins.a) (w.slot ins.b) w.sp kframe? _ _
      ⟨RodataRead.wm8 (RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch))
          (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch),
        by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
        by kit_disch⟩
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hva)
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hvb)
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl))
  kit_run h0 acc
  simp (disch := kit_disch) only [bytesT4_wm8_out, hc.trap_at, trap_zero] at h0))

theorem eq_skip : ArmBody .EQ fun p c s w ins => EqShort p c s w ins ∧
    ∀ va vb, s.regs ins.a = some va → s.regs ins.b = some vb → ins.k ≠ decide (va = vb) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hl, hkk⟩ => by
  kit_setup 0x8001c690
  rcases hnj : nextJump p s.pc with _ | t <;> simp [hnj] at hk htop
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  have hk2 : ¬ decide (va = vb) = ins.k := fun e => hkk va vb hba hbb e.symm
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, hk2] at hk
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
      (by simp (disch := kit_disch) only [slotTag_wm8, slotVal_wm8]; exact hvb)
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl))
  have hg : ((if ins.k then 1#64 else 0#64) != (if va = vb then 1#64 else 0#64)) = true := by
    by_cases he : va = vb <;> cases hkb : ins.k <;> simp_all
  kit_run h0 acc
  simp (disch := kit_disch) only [bytesT4_wm8_out] at h0
  simp (disch := kit_disch) only [Core.trap_at hc] at h0
  simp only [trap_zero] at h0
  exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩

end Lua.Vm.Sim.Kit
