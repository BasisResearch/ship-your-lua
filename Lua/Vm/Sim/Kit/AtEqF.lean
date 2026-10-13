import Lua.Vm.Sim.Kit.AtCond
import Lua.Vm.Sim.Kit.EqualobjF

/-!
# `luaV_equalobj`'s float call node at a row (lane F1-F4: `OP_EQ`, `OP_EQK`)

The call at-lemma of `OP_EQ_F`/`OP_EQK_F` (`scripts/gen_lua_at.py`): the
summary `equalobj_flt_sum` (`Kit/EqualobjF.lean`) applied at the row, its
answer as the location `.lit (if Value.rawEq (vOf X .a) … then 1 else 0)`,
the callee frames `[sp - 160, sp)` the log entry `clob` with content
`eqfMem` (`memPatch_eqf`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout

/-- The value of register field `f` (`nil` when it is none). -/
def vOf (X : Cx) (f : Fld) : Value := (X.s.regs (f.den X)).getD .nil

/-- The constant `K[B]` (`nil` when it is none). -/
def kvOf (X : Cx) : Value := (kval X.p X.ins.b).getD .nil

theorem vOf_eq {X : Cx} {f : Fld} {j : Nat} {v : Value} (h : X.s.regs j = some v) (hj : f.den X = j) :
    vOf X f = v := by
  subst hj; simp [vOf, h]

theorem kvOf_eq {X : Cx} {v : Value} (h : kval X.p X.ins.b = some v) : kvOf X = v := by
  simp [kvOf, h]

/-- The callee frames patched with what `eqfMem` holds there: `eqfMem`. -/
theorem memPatch_eqf {M : Mem} {r s0 : BitVec 64} {n1 n2 sp : Nat} (hs : 160 ≤ sp) :
    memPatch M (eqfMem r s0 n1 n2 sp M) (sp - 160) 160 = eqfMem r s0 n1 n2 sp M :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch]
    split
    · rfl
    · exact (eqfMem_out hs (by omega)).symm

/-- `.rodata` through `Scratch` stores. -/
theorem rodata_scr {X : Cx} (hX : X.Ok) {m : Mem} (hm : ScrFrame X m) : RodataRead m := fun o ho => by
  have hc := hX.core
  have hr := hc.ranges
  have := rodata_below_tohost
  have hsp := hr.sp_eq
  simp only [RuntimeData.spEntry, execFrame] at hsp
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hb : ¬ Scratch X.w (Image.rodataBase + o) := by
    have := hr.ci_lo; have := hr.L_lo
    simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget]; omega
  simp only [bytesT1, hm _ hb]; exact hc.rodata o ho

/-- **`luaV_equalobj(L, R[A], v2)` on a float at a row**: two represented
values at `n1 = R[A]`'s slot and `n2` (a register slot or `K[B]`), the
answer `Value.rawEq`'s as 0/1, the callee frames patched (`eqfMem`). -/
theorem eqf_at {X : Cx} (hX : X.Ok) (hfl : FloorSpec) {m : Mem} (hm : ScrFrame X m) {n1 n2 : Nat}
    {v1 v2 : Value}
    (hv1 : ValRepr X.w.mo X.w.ι (slotTag m n1) (slotVal m n1) v1)
    (hv2 : ValRepr X.w.mo X.w.ι (slotTag m n2) (slotVal m n2) v2) (hf : ¬ (v1.NotFlt ∧ v2.NotFlt))
    (h1 : tohostAddr + 16 ≤ n1) (h1' : n1 + 16 ≤ RuntimeData.spEntry - cStackBudget)
    (h2 : tohostAddr + 16 ≤ n2) (h2' : n2 + 16 ≤ RuntimeData.spEntry - cStackBudget)
    (L r : BitVec 64) (hra : r.toNat % 4 = 0) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 X.w.sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if v1.rawEq v2 then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 X.w.sp⟩ ::
        f.pins) (ArmPay (memPatch m (eqfMem r f.s0 n1 n2 X.w.sp m) (X.w.sp - 160) 160) o)) := by
  have hr := hX.core.ranges
  have hsp := hr.sp_eq
  simp only [RuntimeData.spEntry, cStackBudget, execFrame] at hsp h1' h2'
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  rw [memPatch_eqf (by omega)]
  exact equalobj_flt_sum hfl L r n1 n2 X.w.sp f m o
    ⟨rodata_scr hX hm, hra, by omega, by omega, by omega, h1, by omega, h2, by omega⟩ hv1 hv2 hf

/-- A register's representation read through `Scratch` stores (`slot_scr`). -/
theorem stack_scr {X : Cx} (hX : X.Ok) {m : Mem} (hm : ScrFrame X m) {j : Nat} {v : Value}
    (hj : j < X.p.maxstacksize) (hv : X.s.regs j = some v) :
    ValRepr X.w.mo X.w.ι (slotTag m (X.w.slot j)) (slotVal m (X.w.slot j)) v := by
  obtain ⟨e1, e2⟩ := slot_scr hX hm hj
  rw [e1, e2]; exact hX.core.stack j v hj hv

set_option hygiene false in
/-- The slot facts `eqf_at` takes: above the HTIF mailbox, below the C stack. -/
macro "eqf_room" : tactic => `(tactic| (
  have hr := hX.core.ranges
  have := hr.slots_top; have := hr.base_lo; have := hr.k_top; have := hr.k_lo
  simp only [stackValueSize, RelPtrs.slot, Fld.den, Word.a, Word.b, Word.field,
    Nat.shiftRight_eq_div_pow] at *
  first | omega | (have := kval_lt hky; omega)))

set_option hygiene false in
/-- **`at_eqf`**: the `OP_EQ` float call lemma's proof (after `at_open`): the
call node `eqf_at` at the row, the answer as the location over `vOf`, the
return row and memory (the `clob` of `eqfMem`) by `at_pins`/`at_mem`. -/
macro "at_eqf" : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (eqf_at hX hfl (by at_scr) (stack_scr hX (by at_scr) hs_a0 hsa) (stack_scr hX (by at_scr) hs_b0 hsb)
      hfab (by eqf_room) (by eqf_room) (by eqf_room) (by eqf_room) _ _ (by decide)
      (Lua.Vm.Sim.KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _)
  rw [← vOf_eq (X := X) (f := .a) hsa (by fld_eq), ← vOf_eq (X := X) (f := .b) hsb (by fld_eq)] at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
  · at_pins h
  · at_mem))

set_option hygiene false in
/-- **`at_eqkf`**: `OP_EQK`'s (`K[B]`'s representation, `Core.kconst`). -/
macro "at_eqkf" : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (eqf_at hX hfl (fun _ _ => rfl) (stack_scr hX (fun _ _ => rfl) hs_a0 hsa) (hX.core.kconst hky)
      hfab (by eqf_room) (by eqf_room) (by eqf_room) (by eqf_room) _ _ (by decide)
      (Lua.Vm.Sim.KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _)
  rw [← vOf_eq (X := X) (f := .a) hsa (by fld_eq), ← kvOf_eq (X := X) (v := vb) (by simpa only [Word.b, Word.field, Nat.shiftRight_eq_div_pow] using hky)] at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
  · at_pins h
  · at_mem))

/-- The callee frames' contents at a row (`at_mem`'s `clob` content): the
same `eqfMem`, its slot arguments in another field form. -/
macro_rules | `(tactic| at_eq_ext) => `(tactic|
  (simp only [Word.a, Word.b, Word.field, Nat.shiftRight_eq_div_pow, Nat.add_zero, Loc.den]; done))

end Lua.Vm.Sim.At
