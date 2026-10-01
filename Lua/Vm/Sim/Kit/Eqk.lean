import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Sim.Kit.Cond
import Lua.Vm.Arms

/-!
# `OP_EQK` by the direct kit (lane KIT-2)

`cond = luaV_rawequalobj(s2v(ra), &k[B])` (`luaV_equalobj(NULL, …)`, no
`savestate`), then `docondjump` (`kit_cond`). The constant is read through
`0(sp)` (`Core.kptr`) and represented in memory (`Core.kconst`); the call
node is `equalobj_sum`. As for `OP_EQ`, two long strings are the premise of
`sim_EQK_of_long`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `ld a5,0(sp)`: the constant array `k` (`Core.kptr`). -/
theorem Core.kptr_ld {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {a : Nat} (ha : a = w.sp) :
    sign_extend (m := 64) (bytesT8 c.σ.mem a : BitVec (8 * 8)) = BitVec.ofNat 64 w.k := by
  subst ha; rw [sext64_id]; exact hc.kptr

/-- `R[A]` and `K[B]` are not both long strings. -/
def EqkShort (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  ¬ (slotTag c.σ.mem (w.slot ins.a) = 84#8 ∧
    slotTag c.σ.mem (w.k + stackValueSize * ins.b) = 84#8)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_norm $h) => `(tactic| simp (disch := kit_disch) only [Core.kptr_ld hc] at $h:ident)

local macro_rules
  | `(tactic| kit_val) => `(tactic| (
      try simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      apply BitVec.eq_of_toNat_eq; slot_arith))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [kraw_eq, bne_ite_prop])

theorem eqk_short : ArmBody .EQK EqkShort := fun {p} hS {c s s' w ins} hA hf hop hstep hl => by
  kit_setup 0x8001c850
  rcases hkv : kval p ins.b with _ | vk <;> simp [hkv] at hk htop
  kit_nj
  kit_bound hAt ins.a
  have hkb := kval_lt hkv
  have hk_top := hr.k_top; have hk_lo := hr.k_lo; have hk_al := hr.k_al
  simp only [stackValueSize, cStackBudget, RuntimeData.spEntry] at hk_top
  kit_reg hba va hva ins.a
  have hvk := hc.kconst hkv
  kit_run h0 acc until [0x8001b780]
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (equalobj_sum _ _ (w.slot ins.a) (w.k + stackValueSize * ins.b) w.sp ⟨_, _, _, _, _, _, _, _, _, _, _⟩ _ _
      ⟨hc.rodata, by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
        by kit_disch, by kit_disch⟩ hva hvk hl)
  kit_cond decide (va = vk)

/-- **`sim_EQK` from the long-string path** (`R[A]` and `K[B]` both long
strings: `luaS_eqlngstr` → `memcmp`), as `sim_EQ_of_long`. -/
theorem sim_EQK_of_long (hlong : ArmBody .EQK fun p c s w ins => ¬ EqkShort p c s w ins) :
    SimArm .EQK :=
  sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep =>
    (Classical.em (EqkShort p c s w ins)).elim (eqk_short hS hA hf hop hstep)
      (hlong hS hA hf hop hstep)

end Lua.Vm.Sim.Kit
