import Lua.Vm.Sim.Kit.AtFltLt
import Lua.Vm.Sim.Kit.FltValLt

/-!
# `luaV_flttointeger`'s chain on the join route (lane F2)

`op_order` on an integer outside `l_intfitsf` and a float (`LTintfloat`,
`LEintfloat`, `LTfloatint`, `LEfloatint`): the machine calls `floor`
(`FloorSpec`, `floorSpec_proved`), compares `n` with it (`__eqdf2`), adds `1.0` for `F2Iceil`,
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

/-- `F2Ieq`'s test (`luaV_flttointeger`: integral and in range). -/
abbrev f2iOk (f : Float.Model) : Bool :=
  Float.Model.beq f (floor f) && Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg

/-- `F2Ieq`'s integer. -/
abbrev f2iVal (f : Float.Model) : BitVec 64 := (floor f).toInt64.toBitVec

attribute [at_atom_simp] f2iOk f2iVal

/-- `luaV_tointegerns(F2Ieq)` (the bitwise arms) over the atoms: integral
and in range, or no integer. An `if`, so the leaf splits it as the kernel's
outcome. -/
theorem flttointeger_eq (f : Float.Model) :
    flttointeger f .eq = if f2iOk f = true then some (f2iVal f) else none := by
  unfold flttointeger numberToInteger
  cases hb : Float.Model.beq f (floor f) <;>
  cases hc : (Float.Model.le minIntF (floor f) && Float.Model.lt (floor f) minIntF.neg) <;> simp_all

/-- **`luaO_rawarith`'s bitwise case on a float operand** (`op_bitwise`'s
`tointegerns`), over the atoms: the integer result, or the fall-through. -/
theorem rawArith_bit_fi {o : Op} (ho : o = .band ∨ o = .bor ∨ o = .bxor ∨ o = .shl ∨ o = .shr)
    (x : Float.Model) (j : BitVec 64) :
    rawArith o (.flt x) (.int j) = if f2iOk x = true then .ofInt (intarith o (f2iVal x) j) else .fail := by
  have h : rawArith o (.flt x) (.int j) = match flttointeger x .eq, some j with
      | some i, some j => .ofInt (intarith o i j) | _, _ => .fail := by
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [h, flttointeger_eq]
  by_cases hc : f2iOk x = true <;> simp only [hc, ↓reduceIte] <;> rfl

theorem rawArith_bit_if {o : Op} (ho : o = .band ∨ o = .bor ∨ o = .bxor ∨ o = .shl ∨ o = .shr)
    (i : BitVec 64) (y : Float.Model) :
    rawArith o (.int i) (.flt y) = if f2iOk y = true then .ofInt (intarith o i (f2iVal y)) else .fail := by
  have h : rawArith o (.int i) (.flt y) = match some i, flttointeger y .eq with
      | some i, some j => .ofInt (intarith o i j) | _, _ => .fail := by
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [h, flttointeger_eq]
  by_cases hc : f2iOk y = true <;> simp only [hc, ↓reduceIte] <;> rfl

theorem rawArith_bit_ff {o : Op} (ho : o = .band ∨ o = .bor ∨ o = .bxor ∨ o = .shl ∨ o = .shr)
    (x y : Float.Model) :
    rawArith o (.flt x) (.flt y) =
      if f2iOk x = true then (if f2iOk y = true then .ofInt (intarith o (f2iVal x) (f2iVal y)) else .fail)
      else .fail := by
  have h : rawArith o (.flt x) (.flt y) = match flttointeger x .eq, flttointeger y .eq with
      | some i, some j => .ofInt (intarith o i j) | _, _ => .fail := by
    rcases ho with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [h, flttointeger_eq, flttointeger_eq]
  by_cases hc : f2iOk x = true <;> by_cases hd : f2iOk y = true <;> simp only [hc, hd, ↓reduceIte] <;> rfl

set_option hygiene false in
/-- **`at_fact`**: a Boolean fact of the path (`P = true`) from its fork
facts, by the leaf's decision (`at_atoms` on its negation). -/
macro "at_fact" : tactic => `(tactic| (
  apply Classical.byContradiction; intro hq_fact
  simp only [Bool.not_eq_true] at hq_fact
  at_atoms))

/-- A stored integer whose payload is the kernel's (by an equation). -/
theorem _root_.Lua.Vm.Sim.ValRepr.int_eq {mo : Mem} {ι : Strs} {x y : BitVec 64} (h : x = y) :
    ValRepr mo ι (BitVec.ofNat 8 vNumInt) x (.int y) := h ▸ .int

/-- `not` (`xori -1`) as the complement. -/
theorem xor_ones (x : BitVec 64) : x ^^^ 0xffffffffffffffff#64 = ~~~x := by
  rw [show (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]

set_option hygiene false in
/-- **A stored integer converted from a float** (`luaV_tointegerns`'s
`(lua_Integer)f`): `__fixdfdi`'s result is the model's `toInt64` under the
path's range fact (`at_fact`, `fixdfdi_model`). -/
macro_rules | `(tactic| at_new_ext) => `(tactic| (
  refine ValRepr.int_eq ?_
  simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, xor_ones]
  simp (disch := at_fact) only [fixdfdi_model]
  simp (disch := assumption) only [at_fspec, Loc.den, Fld.den, Nat.add_zero, f2iVal, hxm, true_and, and_true,
    BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm]
  done))

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

set_option hygiene false in
/-- **`at_junary pc NS`**: a one-register `setR` kernel on a float `R[B]`
(`hT : FltB`; `OP_UNM`, `OP_BNOT`): its view, `δ` evaluated (`tointegerns`
over the atoms, `flttointeger_eq`), then `at_walk NS`. -/
macro "at_junary " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  simp [setR, Opnd.ports] at htop hk
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  have hrod := hc.rodata
  flt_reg_s ins.b, hT
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, flttointeger_eq] at hk
  try subst hk
  at_walk $ns))

/-! ## One declaration per operand class (heavy arms) -/

/-- The per-operand view of register `r` as a state predicate: `0` a float,
`1` an integer, `2` no number (or no value: the kernel has no `Step`). -/
def RegCls : Nat → State → Nat → Prop
  | 0, s, r => FltReg s r
  | 1, s, r => ∃ i, s.regs r = some (.int i)
  | _, s, r => ¬ FltReg s r ∧ ¬ ∃ i, s.regs r = some (.int i)

/-- An arm body from its three classes of the register `k ins`. -/
theorem armBody_cls {o : OpCode} {P : State → Word → Prop} (k : Word → Nat)
    (h0 : ArmBody o fun _ _ s _ ins => P s ins ∧ RegCls 0 s (k ins))
    (h1 : ArmBody o fun _ _ s _ ins => P s ins ∧ RegCls 1 s (k ins))
    (h2 : ArmBody o fun _ _ s _ ins => P s ins ∧ RegCls 2 s (k ins)) :
    ArmBody o fun _ _ s _ ins => P s ins :=
  fun {_} hS {_ s _ _ ins} hA hf hop hstep hP => by
  by_cases e0 : RegCls 0 s (k ins)
  · exact h0 hS hA hf hop hstep ⟨hP, e0⟩
  by_cases e1 : RegCls 1 s (k ins)
  · exact h1 hS hA hf hop hstep ⟨hP, e1⟩
  exact h2 hS hA hf hop hstep ⟨hP, e0, e1⟩

/-- An arm's float paths from the two operands' (`FltBC`, `FltAB`, …: one
declaration each). -/
theorem sim_on_or {o : OpCode} {P Q : Proto → State → Word → Prop} (ho : o.toNat < Arms.jtEntries)
    (hP : ArmBody o fun p _ s _ ins => P p s ins) (hQ : ArmBody o fun p _ s _ ins => Q p s ins) :
    SimArmOn o fun p s ins => P p s ins ∨ Q p s ins :=
  sim_arm_on ho fun {_} hS {_ _ _ _ _} hA hf hop hstep (hT : _ ∨ _) =>
    Or.elim hT (hP hS hA hf hop hstep) (hQ hS hA hf hop hstep)

set_option hygiene false in
/-- `R[k]` by its per-operand view, the class `hK : RegCls cls s k` keeping
one of the three goals (the others refuted by the register's value). -/
macro "num_cls " k:term "," hn:ident : tactic => `(tactic| (
  num_reg $k, $hn
  all_goals try (simp [RegCls, FltReg, hr] at hK; done)))

set_option hygiene false in
/-- **`at_jbit pc NS j k`**: `op_bitwise`'s float case with `R[j]` a float
and `R[k]` of one class (`hT : FltReg s j ∧ RegCls cls s k`): the float by
its view, `R[k]` by its per-operand view (`num_cls`), the kernel's
`tointegerns` over the atoms (`rawArith_bit_*`), then `at_walk NS`; a stored
integer is `__fixdfdi`'s under the range fact (`at_new_ext`). One
declaration per (float operand, class) (`sim_on_or`, `armBody_cls`). -/
macro "at_jbit " pc:num ns:ident j:term "," k:term : tactic => `(tactic| (
  obtain ⟨hT, hK⟩ := hT
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  have hrod := hc.rodata
  flt_reg_q x $j, hT
  num_cls $k, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp (disch := decide) [Value.toNum?, BinOp.toOp, rawArith_bit_fi, rawArith_bit_if, rawArith_bit_ff,
      Res.ofInt, intarith, Value.ofNum, VState.apply, writeDefs, KEdge.kills] at hk
    at_walk $ns))

/-- **`bitwise_flt_arm name OP pc NS`**: an `op_bitwise` arm's float paths
as one declaration per (float operand, the other's class) (`at_jbit`), and
`name : SoftFloatSpec → SimArmOn OP FltBC` from them. -/
syntax "bitwise_flt_arm " ident term:max num ident : command

set_option hygiene false in
macro_rules
  | `(bitwise_flt_arm $nm $op $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let one (side cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let (j, k) ← if side == "b" then pure ((← `(ins.b)), (← `(ins.c))) else pure ((← `(ins.c)), (← `(ins.b)))
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_{side}{cls}") (hsf : SoftFloatSpec) :
          ArmBody $op fun _ _ s _ ins => FltReg s $j ∧ RegCls $n s $k :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jbit $pc $ns $j, $k)
    let cmds ← ["b", "c"].flatMap (fun side => ["0", "1", "2"].map (side, ·)) |>.mapM fun (side, cls) => one side cls
    let fin ← `(theorem $nm (hsf : SoftFloatSpec) : SimArmOn $op FltBC :=
        sim_on_or (by decide)
          (armBody_cls (·.c) ($(mk "_b0") hsf) ($(mk "_b1") hsf) ($(mk "_b2") hsf))
          (armBody_cls (·.b) ($(mk "_c0") hsf) ($(mk "_c1") hsf) ($(mk "_c2") hsf)))
    return Lean.mkNullNode (cmds.toArray.push fin)

end Lua.Vm.Sim.At
