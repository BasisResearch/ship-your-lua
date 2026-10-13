import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.Sim.Kit.AtFmod

/-!
# `luai_nummod` on the join route (lane F1-F7)

`op_arithf(K)`'s `luai_nummod(L, a, b, m)` is

  `m = fmod(a, b); if ((m > 0) ? b < 0 : (m < 0 && b != m)) m += b;`

compiled as libm `fmod` (the call node `FmodR`: the reference `SfRef.fmod`,
its `errno` store at `x % 0.0` a second log window, `Kit/AtFmod.lean`),
`__gedf2(m, 0)`, `__ledf2(b, 0)` (or `__ledf2(m, 0)`, `__gedf2(b, 0)`) and
`__adddf3(m, b)`. The kernel's `Lua.Num.nummod` reads the same comparisons
of the model (`Float.Model.ofNat 0` is the leaf atoms' `Lua.Num.zero`,
`fmod`'s model `SfRef.fmod_model`); the stored float is `fmod`'s canonical
datum (`FmodR.S_bits`) or the sum's (`F64.add_eq_model`).

The arms are `at_jarith`/`at_jarithK` (`Kit/AtJoinOps.lean`) on
`sim_arm_onE`: a path through `fmod` ends at `AtFinE` (`Kit/AtErrno.lean`),
the relation at the pointers after the `errno` store.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (Config Steps)

/-- `luai_nummod`'s zero is the leaf atoms' (`toModel_zero`). -/
theorem ofNat_zero_eq : Float.Model.ofNat 0 = Lua.Num.zero := by decide +kernel

attribute [at_atom_simp] ofNat_zero_eq SfRef.fmod_model

set_option hygiene false in
/-- A stored float computed by `luai_nummod`: `fmod`'s result (its canonical
datum, `FmodR.S_bits`) or its sum with the divisor (`__adddf3`). -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.FmodR.S_bits,
        Lua.Vm.Fn.Adddf3.S, Lua.Vm.Fn.Floatdidf.S, F64.add_eq_model, toModel_toBits, toModel_ofInt, ofI,
        hxm, true_and, and_true, ofNat_zero_eq, SfRef.fmod_model, Lua.Num.nummod]
      done))

set_option hygiene false in
/-- **`at_jmod pc NS`**: `op_arithf`'s `luai_nummod` (`hT : FltBC`): the
per-operand views as `at_jarith`'s, the kernel's `Lua.Num.nummod` unfolded
and left in `hk`, so that the leaf splits its comparisons (`at_leaf`) and
refutes the side the path's forks contradict (`at_atoms`). -/
macro "at_jmod " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  refine hT.elim (fun hq => ?fb) (fun hq => ?fc)
  case' fb => flt_reg_q x ins.b, hq; num_reg ins.c, hn
  case' fc => flt_reg_q x ins.c, hq; num_reg ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.nummod] at hk
    at_walk $ns))

set_option hygiene false in
/-- **`at_jmodK pc NS`**: `at_jmod` with the constant `K[C]` (`at_jarithK`'s views). -/
macro "at_jmodK " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  refine hT.elim (fun hq => ?fb) (fun hq => ?fk)
  case' fb => flt_reg_q x ins.b, hq; num_k hn
  case' fk => flt_k_q x, hq; num_reg ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.nummod] at hk
    at_walk $ns))

/-! ## One declaration per operand class, the pointers free after the run -/

/-- **An arm's run under `Q` that may move the pointers** (`ArmBody` with the
relation at any pointers after it: an `errno` store). -/
def ArmBodyE (o : OpCode) (Q : Proto → Config → State → RelPtrs → Word → Prop) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs} {ins : Word},
    ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
    Q p c s w ins → ∃ c' w', Steps c c' ∧ VmRelAt p c' s' w'

/-- `armBody_cls` for `ArmBodyE`. -/
theorem armBodyE_cls {o : OpCode} {P : State → Word → Prop} (k : Word → Nat)
    (h0 : ArmBodyE o fun _ _ s _ ins => P s ins ∧ RegCls 0 s (k ins))
    (h1 : ArmBodyE o fun _ _ s _ ins => P s ins ∧ RegCls 1 s (k ins))
    (h2 : ArmBodyE o fun _ _ s _ ins => P s ins ∧ RegCls 2 s (k ins)) :
    ArmBodyE o fun _ _ s _ ins => P s ins :=
  fun {_} hS {_ s _ _ ins} hA hf hop hstep hP => by
  by_cases e0 : RegCls 0 s (k ins)
  · exact h0 hS hA hf hop hstep ⟨hP, e0⟩
  by_cases e1 : RegCls 1 s (k ins)
  · exact h1 hS hA hf hop hstep ⟨hP, e1⟩
  exact h2 hS hA hf hop hstep ⟨hP, e0, e1⟩

/-- `sim_on_or` for `ArmBodyE` (`sim_arm_onE`). -/
theorem sim_on_orE {o : OpCode} {P Q : Proto → State → Word → Prop} (ho : o.toNat < Arms.jtEntries)
    (hP : ArmBodyE o fun p _ s _ ins => P p s ins) (hQ : ArmBodyE o fun p _ s _ ins => Q p s ins) :
    SimArmOn o fun p s ins => P p s ins ∨ Q p s ins :=
  sim_arm_onE ho fun {_} hS {_ _ _ _ _} hA hf hop hstep (hT : _ ∨ _) =>
    Or.elim hT (hP hS hA hf hop hstep) (hQ hS hA hf hop hstep)

set_option hygiene false in
/-- **`at_jmod1 pc NS j k`**: `at_jmod` with `R[j]` a float and `R[k]` of
one class (`hT : FltReg s j ∧ RegCls cls s k`, `num_cls`). -/
macro "at_jmod1 " pc:num ns:ident j:term "," k:term : tactic => `(tactic| (
  obtain ⟨hT, hK⟩ := hT
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  flt_reg_q x $j, hT
  num_cls $k, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.nummod] at hk
    at_walk $ns))

/-- **`mod_flt_arm name OP pc NS`**: `OP_MOD`'s float paths as one
declaration per (float operand, the other's class) (`at_jmod1`), and
`name : SimArmOn OP FltBC` from them. -/
syntax "mod_flt_arm " ident term:max num ident : command

set_option hygiene false in
macro_rules
  | `(mod_flt_arm $nm $op $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let one (side cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let (j, k) ← if side == "b" then pure ((← `(ins.b)), (← `(ins.c))) else pure ((← `(ins.c)), (← `(ins.b)))
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_{side}{cls}") :
          ArmBodyE $op fun _ _ s _ ins => FltReg s $j ∧ RegCls $n s $k :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jmod1 $pc $ns $j, $k)
    let cmds ← ["b", "c"].flatMap (fun side => ["0", "1", "2"].map (side, ·)) |>.mapM fun (side, cls) => one side cls
    let fin ← `(theorem $nm : SimArmOn $op FltBC :=
        sim_on_orE (by decide)
          (armBodyE_cls (·.c) $(mk "_b0") $(mk "_b1") $(mk "_b2"))
          (armBodyE_cls (·.b) $(mk "_c0") $(mk "_c1") $(mk "_c2")))
    return Lean.mkNullNode (cmds.toArray.push fin)

/-! ## `OP_MODK`: the constant's classes -/

/-- The per-operand view of the constant `K[i]`: `0` a float, `1` an
integer, `2` no number. -/
def KCls : Nat → Proto → Nat → Prop
  | 0, p, i => FltK p i
  | 1, p, i => ∃ n, kval p i = some (.int n)
  | _, p, i => ¬ FltK p i ∧ ¬ ∃ n, kval p i = some (.int n)

/-- An arm body from the three classes of the constant `K[k ins]`. -/
theorem armBodyE_kcls {o : OpCode} {P : Proto → State → Word → Prop} (k : Word → Nat)
    (h0 : ArmBodyE o fun p _ s _ ins => P p s ins ∧ KCls 0 p (k ins))
    (h1 : ArmBodyE o fun p _ s _ ins => P p s ins ∧ KCls 1 p (k ins))
    (h2 : ArmBodyE o fun p _ s _ ins => P p s ins ∧ KCls 2 p (k ins)) :
    ArmBodyE o fun p _ s _ ins => P p s ins :=
  fun {p} hS {_ s _ _ ins} hA hf hop hstep hP => by
  by_cases e0 : KCls 0 p (k ins)
  · exact h0 hS hA hf hop hstep ⟨hP, e0⟩
  by_cases e1 : KCls 1 p (k ins)
  · exact h1 hS hA hf hop hstep ⟨hP, e1⟩
  exact h2 hS hA hf hop hstep ⟨hP, e0, e1⟩

set_option hygiene false in
/-- `K[C]` by its per-operand view, the class `hK : KCls cls p C` keeping one
of the three goals. -/
macro "num_kcls " hn:ident : tactic => `(tactic| (
  num_k $hn
  all_goals try (simp [KCls, FltK, hkv] at hK; done)))

set_option hygiene false in
/-- **`at_jmodKb pc NS`**: `OP_MODK` with `R[B]` a float and `K[C]` of one
class (`hT : FltReg s B ∧ KCls cls p C`). -/
macro "at_jmodKb " pc:num ns:ident : tactic => `(tactic| (
  obtain ⟨hT, hK⟩ := hT
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  flt_reg_q x ins.b, hT
  num_kcls hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.nummod] at hk
    at_walk $ns))

set_option hygiene false in
/-- **`at_jmodKk pc NS`**: `OP_MODK` with `K[C]` a float and `R[B]` of one
class (`hT : FltK p C ∧ RegCls cls s B`). -/
macro "at_jmodKk " pc:num ns:ident : tactic => `(tactic| (
  obtain ⟨hT, hK⟩ := hT
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  flt_k_q x, hT
  num_cls ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.nummod] at hk
    at_walk $ns))

/-- **`modk_flt_arm name OP pc NS`**: `OP_MODK`'s float paths as one
declaration per (float operand, the other's class), and `name : SimArmOn OP
FltBK` from them. -/
syntax "modk_flt_arm " ident term:max num ident : command

set_option hygiene false in
macro_rules
  | `(modk_flt_arm $nm $op $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let oneB (cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_b{cls}") :
          ArmBodyE $op fun p _ s _ ins => FltReg s ins.b ∧ KCls $n p ins.c :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jmodKb $pc $ns)
    let oneK (cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_k{cls}") :
          ArmBodyE $op fun p _ s _ ins => FltK p ins.c ∧ RegCls $n s ins.b :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jmodKk $pc $ns)
    let cb ← ["0", "1", "2"].mapM oneB
    let ck ← ["0", "1", "2"].mapM oneK
    let fin ← `(theorem $nm : SimArmOn $op FltBK :=
        sim_on_orE (by decide)
          (armBodyE_kcls (·.c) $(mk "_b0") $(mk "_b1") $(mk "_b2"))
          (armBodyE_cls (·.b) $(mk "_k0") $(mk "_k1") $(mk "_k2")))
    return Lean.mkNullNode ((cb ++ ck).toArray.push fin)

end Lua.Vm.Sim.At
