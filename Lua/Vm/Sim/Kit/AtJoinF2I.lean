import Lua.Vm.Sim.Kit.AtFltLt
import Lua.Vm.Sim.Kit.FltValLt

/-!
# `luaV_flttointeger`'s chain on the join route (lane F2)

`op_order` on an integer outside `l_intfitsf` and a float (`LTintfloat`,
`LEintfloat`, `LTfloatint`, `LEfloatint`): the machine calls `floor`
(`FloorSpec`), compares `n` with it (`__eqdf2`), adds `1.0` for `F2Iceil`,
range-checks against the `.rodata` constants `(double)LUA_MININTEGER` and
`-(double)LUA_MININTEGER`, converts by `__fixdfdi` and compares integers;
out of range it compares the float with `0`.

The leaf (`at_atoms`) decides this over pair atoms as before, with three
additions, all rewrites of the `at_atom_simp` set:

* **the value equation as a conditional**: `__fixdfdi`'s result compared
  with an integer is the model's `toInt64` compared, under the range atom
  `minIntF ≤ g` (`slt_fixR`/`slt_fixL`, from A-INC's `fixdfdi_model`); off
  it, an opaque residue (`fixOut`) the path never reads;
* the kernel's chain restated with `bif` over the same atoms
  (`ltIntFloat_f2i`, …), so the leaf splits only `docondjump`'s test;
* the integer compares themselves are residual Boolean atoms (`at_atoms`
  generalises a `decide` neither a pair atom nor `k` decides), oriented as
  `<` (`decide_int_le`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `__fixdfdi`'s result off its range atom: never read by a path that
reaches the integer compare (the machine checks the range first). -/
@[irreducible] def fixOut (x : BitVec 64) : BitVec 64 := Lua.Vm.Fn.Fixdfdi.S x

/-- **`i < (long long)g`** on the machine, under the range atom. -/
@[at_atom_simp] theorem slt_fixR (i x : BitVec 64) :
    zopz0zI_s i (Lua.Vm.Fn.Fixdfdi.S x) =
      if Float.Model.le minIntF (F64.toModel x) = true
      then decide (i.toInt < (F64.toModel x).toInt64.toBitVec.toInt) else zopz0zI_s i (fixOut x) := by
  by_cases h : Float.Model.le minIntF (F64.toModel x) = true
  · rw [if_pos h, fixdfdi_model x h, slt_toInt]
  · rw [if_neg h]; unfold fixOut; rfl

/-- **`(long long)g < i`** on the machine, under the range atom. -/
@[at_atom_simp] theorem slt_fixL (i x : BitVec 64) :
    zopz0zI_s (Lua.Vm.Fn.Fixdfdi.S x) i =
      if Float.Model.le minIntF (F64.toModel x) = true
      then decide ((F64.toModel x).toInt64.toBitVec.toInt < i.toInt) else zopz0zI_s (fixOut x) i := by
  by_cases h : Float.Model.le minIntF (F64.toModel x) = true
  · rw [if_pos h, fixdfdi_model x h, slt_toInt]
  · rw [if_neg h]; unfold fixOut; rfl

/-- The integer compares oriented as `<`. -/
@[at_atom_simp] theorem decide_int_le (a b : Int) : decide (a ≤ b) = !decide (b < a) := by
  by_cases h : b < a
  · simp [h, Int.not_le.mpr h]
  · simp [h, Int.not_lt.mp h]

/-- `sext.w` of an `slt` answer (`docondjump`'s test on the integer compare
or the `f > 0` fallback): the answer as `0`/`1`. -/
@[at_atom_simp] theorem sext_slt (b : Bool) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (zero_extend (m := 64) (bool_to_bit b) + 0x0#64) 31 0) = if b then 1#64 else 0#64 := by
  cases b <;> decide

attribute [at_atom_simp] bne_ite' rod_min rod_max rod_one toModel_min toModel_max toModel_one sext_ite

/-! ## The kernel's chain over the same atoms -/

/-- `LTintfloat` off `l_intfitsf` (`F2Iceil`). -/
theorem ltIntFloat_f2i {i : BitVec 64} (h : intfitsf i = false) (f : Float.Model) :
    ltIntFloat i f =
      bif Float.Model.beq f (floor f) then
        (bif Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg
         then decide (i.toInt < (floor f).toInt64.toBitVec.toInt) else Float.Model.lt zero f)
      else
        (bif Float.Model.le minIntF ((floor f).add (.ofNat 1)) &&
            Float.Model.lt ((floor f).add (.ofNat 1)) minIntF.neg
         then decide (i.toInt < ((floor f).add (.ofNat 1)).toInt64.toBitVec.toInt)
         else Float.Model.lt zero f) := by
  unfold ltIntFloat flttointeger numberToInteger
  simp only [h, Bool.false_eq_true, ite_false]
  cases hb : Float.Model.beq f (floor f) <;>
  cases hc : (Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg) <;>
  cases hd : (Float.Model.le minIntF ((floor f).add (.ofNat 1)) &&
    Float.Model.lt ((floor f).add (.ofNat 1)) minIntF.neg) <;> simp_all

/-- `LEintfloat` off `l_intfitsf` (`F2Ifloor`). -/
theorem leIntFloat_f2i {i : BitVec 64} (h : intfitsf i = false) (f : Float.Model) :
    leIntFloat i f =
      bif Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg
      then decide (i.toInt ≤ (floor f).toInt64.toBitVec.toInt) else Float.Model.lt zero f := by
  unfold leIntFloat flttointeger numberToInteger
  simp only [h, Bool.false_eq_true, ite_false]
  cases hb : Float.Model.beq f (floor f) <;>
  cases hc : (Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg) <;> simp_all

/-- `LTfloatint` off `l_intfitsf` (`F2Ifloor`). -/
theorem ltFloatInt_f2i {i : BitVec 64} (h : intfitsf i = false) (f : Float.Model) :
    ltFloatInt f i =
      bif Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg
      then decide ((floor f).toInt64.toBitVec.toInt < i.toInt) else Float.Model.lt f zero := by
  unfold ltFloatInt flttointeger numberToInteger
  simp only [h, Bool.false_eq_true, ite_false]
  cases hb : Float.Model.beq f (floor f) <;>
  cases hc : (Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg) <;> simp_all

/-- `LEfloatint` off `l_intfitsf` (`F2Iceil`). -/
theorem leFloatInt_f2i {i : BitVec 64} (h : intfitsf i = false) (f : Float.Model) :
    leFloatInt f i =
      bif Float.Model.beq f (floor f) then
        (bif Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg
         then decide ((floor f).toInt64.toBitVec.toInt ≤ i.toInt) else Float.Model.lt f zero)
      else
        (bif Float.Model.le minIntF ((floor f).add (.ofNat 1)) &&
            Float.Model.lt ((floor f).add (.ofNat 1)) minIntF.neg
         then decide (((floor f).add (.ofNat 1)).toInt64.toBitVec.toInt ≤ i.toInt)
         else Float.Model.lt f zero) := by
  unfold leFloatInt flttointeger numberToInteger
  simp only [h, Bool.false_eq_true, ite_false]
  cases hb : Float.Model.beq f (floor f) <;>
  cases hc : (Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg) <;>
  cases hd : (Float.Model.le minIntF ((floor f).add (.ofNat 1)) &&
    Float.Model.lt ((floor f).add (.ofNat 1)) minIntF.neg) <;> simp_all

/-- `op_order`'s f2i class with the integer in `R[A]` (`LTintfloat`, `LEintfloat`). -/
def F2IL (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ i x n, s.regs ins.a = some (.int i) ∧ s.regs ins.b = some (.flt x n) ∧ intfitsf i = false

/-- `op_order`'s f2i class with the integer in `R[B]` (`LTfloatint`, `LEfloatint`). -/
def F2IR (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ i x n, s.regs ins.a = some (.flt x n) ∧ s.regs ins.b = some (.int i) ∧ intfitsf i = false

/-- The f2i paths from their two classes. -/
theorem armBody_f2i {o : OpCode} (hl : ArmBody o F2IL) (hr : ArmBody o F2IR) : ArmBody o FltF2I :=
  fun {_} hS {_ _ _ _ _} hA hf hop hstep hT =>
    hT.elim (hl hS hA hf hop hstep) (hr hS hA hf hop hstep)

set_option hygiene false in
/-- The float register `j` (`hq : regs j = flt`) by its view and the integer
register `k` (`hi : regs k = int`) by its tag. -/
macro "f2i_regs " j:term "," hq:ident "," k:term "," hi:ident : tactic => `(tactic| (
  flt_reg_s $j, (⟨x, n, $hq⟩ : FltReg s $j)
  kit_reg hr v hv $k
  rw [$hi:ident] at hr; cases hr
  obtain ⟨htn, rfl⟩ := hv.tag_of_int))

set_option hygiene false in
/-- **`at_jf2i pc NS side`**: an f2i class of `op_order` (`hT : F2IL`,
side `L`: the integer in `R[A]`; `F2IR`, side `R`): the integer operand by
its tag, the float by its view, the kernel's chain restated over the atoms
(`*_f2i`), `.rodata` read at the entry (`hrod`), then `at_walk NS`. -/
syntax "at_jf2i " num ident ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| at_jf2i $pc:num $ns:ident $side:ident) => do
    let regs ← if side.getId == `L then `(tactic| f2i_regs ins.b, hb, ins.a, ha)
      else `(tactic| f2i_regs ins.a, ha, ins.b, hb)
    `(tactic| (
      kit_setup $pc
      kit_nj
      kit_bound hAt ins.a; kit_bound hBt ins.b
      flt_views
      have hrod := hc.rodata
      obtain ⟨i, x, n, ha, hb, hfit⟩ := hT
      $regs:tactic
      simp [Opnd.fill, δ, Value.toNum?, ltNum, leNum] at hk
      simp only [ltIntFloat_f2i hfit, leIntFloat_f2i hfit, ltFloatInt_f2i hfit, leFloatInt_f2i hfit] at hk
      at_walk $ns))

end Lua.Vm.Sim.At
