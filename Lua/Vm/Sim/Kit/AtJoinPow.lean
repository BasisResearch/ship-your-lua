import Lua.Vm.Sim.Kit.AtJoinMod
import Lua.Vm.Sim.Kit.AtJoinMul
import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.Sim.Kit.AtPow

/-!
# `luai_numpow` on the join route (lane F1-21)

`op_arithf(K)`'s `luai_numpow(L, a, b)` is `b == 2 ? a*a : pow(a, b)`
(`llimits.h:339-342`), compiled as `__eqdf2(b, 2.0)` (the `.rodata` word
`0x8005c468`, `rod_two`), then `__muldf3(a, a)` or libm `pow(a, b)` (the call
node `PowQ`, `Kit/AtPow.lean`: its `errno` stores a second log window, the
close `AtFinE`). The kernel's `Lua.Num.numpow` tests `Float.Model.beq b two`,
the same comparison of the model (`toModel_two`); it is left in `hk`, so the
leaf splits it and refutes the side the path's `__eqdf2` fork contradicts.

`OP_POW` and `OP_POWK` have no integer case (`rawArith .pow`: always the
float), so their arms are every path (`at_jarithA`'s views): `at_jpow1`,
`at_jpowK1`, one declaration per class of `R[B]` (`pow_arm`, `powk_arm`).

**Signalling NaNs.** `pow`'s level (b) (`PowQ.spec`) holds on quiet operands
only: `Float.Model` has no signalling NaN, and the ELF's `pow(sNaN, ±0)` and
`pow(1, sNaN)` are a NaN where the model's are `1`. The relation admits a
float register or constant with a signalling payload (`ValRepr.flt` holds of
every bit pattern), so the arms are proved on the states whose float operands
are quiet (`PowQuiet`, `PowKQuiet`: a predicate of the machine's memory, so
`SimArmOnM`, not `SimArmOn`); the other states are `FloatArms`' fields.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (Config Steps StepsN)

/-- **An arm's simulation on the states where a machine-level `Q` holds**
(`Q` over the program, the machine's memory at the fetch head, the relation's
pointers and the instruction): `SimArmOn` for a path family the bytecode
state does not determine (a float operand's payload bits). -/
def SimArmOnM (o : OpCode) (Q : Proto → Mem → RelPtrs → Word → Prop) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs}, VmRelAt p c s w →
    ∀ {ins : Word}, p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      Q p c.σ.mem w ins → ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'

/-- **An arm from its two machine-level path families**: off `Q`, and on `Q`. -/
theorem SimArmOnM.split {o : OpCode} {Q : Proto → Mem → RelPtrs → Word → Prop}
    (h₁ : SimArmOnM o fun p m w ins => ¬ Q p m w ins) (h₂ : SimArmOnM o Q) : SimArm o :=
  fun {p} hS {c s _} hR {ins} hf hop hstep => by
    obtain ⟨w, hR⟩ := hR
    exact (Classical.em (Q p c.σ.mem w ins)).elim (h₂ hS hR hf hop hstep) (h₁ hS hR hf hop hstep)

/-- A slot whose tag is the float tag holds a quiet payload (not a signalling
NaN; `Lua.Vm.Fn.PowR.NotSNaN`). -/
def QuietAt (m : Mem) (a : Nat) : Prop :=
  slotTag m a = BitVec.ofNat 8 vNumFlt → Lua.Vm.Fn.PowR.NotSNaN (slotVal m a)

/-- Two operand slots quiet. -/
def QuietOps (m : Mem) (a b : Nat) : Prop := QuietAt m a ∧ QuietAt m b

theorem QuietOps.l {m : Mem} {a b : Nat} (h : QuietOps m a b)
    (ht : slotTag m a = BitVec.ofNat 8 vNumFlt) : Lua.Vm.Fn.PowR.NotSNaN (slotVal m a) := h.1 ht

theorem QuietOps.r {m : Mem} {a b : Nat} (h : QuietOps m a b)
    (ht : slotTag m b = BitVec.ofNat 8 vNumFlt) : Lua.Vm.Fn.PowR.NotSNaN (slotVal m b) := h.2 ht

/-- `OP_POW`'s operands `R[B]`, `R[C]` quiet. -/
def PowQuiet (_p : Proto) (m : Mem) (w : RelPtrs) (ins : Word) : Prop :=
  QuietOps m (w.slot ins.b) (w.slot ins.c)

/-- `OP_POWK`'s operands `R[B]`, `K[C]` quiet. -/
def PowKQuiet (_p : Proto) (m : Mem) (w : RelPtrs) (ins : Word) : Prop :=
  QuietOps m (w.slot ins.b) (w.k + 16 * ins.c)

namespace At

open Lua.Vm.Sim.Kit Lua.Num

/-- `luai_numpow`'s `2.0` (`.rodata` at `0x8005c468`). -/
theorem rod_two {m : Mem} (h : RodataRead m) : bytesT8 m 2147861608 = 0x4000000000000000#64 := by
  have := rod8 h (2147861608 - Image.rodataBase) (by decide)
  rw [show Image.rodataBase + (2147861608 - Image.rodataBase) = 2147861608 by decide] at this
  rw [this]; decide

theorem toModel_two : F64.toModel 0x4000000000000000#64 = Lua.Num.Pow.two := by decide +kernel

attribute [at_atom_simp] rod_two toModel_two

set_option hygiene false in
/-- One operand of `pow`'s call quiet: `__floatdidf`'s result
(`PowQ.notSNaN_ofInt`), or a float register's or constant's payload by the
arm's `hQ` and its tag fact. -/
macro "pow_q1" : tactic => `(tactic| (
  simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.Floatdidf.S]
  first
    | exact Lua.Vm.Fn.PowQ.notSNaN_ofInt _
    | exact QuietOps.l hQo (by assumption)
    | exact QuietOps.r hQo (by assumption)))

/-- The discharger of `pow`'s conditional level (b) (`gen_lua_at.py`
`FSPEC_HYP`): its premise and the context by `assumption`, the guard by
`pow_q1`. -/
macro "pow_disch" : tactic => `(tactic| first
  | assumption
  | (apply Lua.Vm.Fn.PowQ.Q.mk <;> pow_q1))

set_option hygiene false in
/-- A stored float computed by `pow` (after `__floatdidf` for an integer
operand): `PowQ.spec`'s canonical datum of `Lua.Num.pow`. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := pow_disch) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.PowQ.S,
        Lua.Vm.Fn.Floatdidf.S, toModel_ofInt, ofI, true_and, and_true]
      done))

set_option hygiene false in
/-- The kernel on the two views (`hn`, `hn'`): `rawArith`, `numpow` unfolded
and left in `hk` (the leaf splits `beq b two`), then `at_walk NS`. -/
macro "at_jpow_both " ns:ident : tactic => `(tactic| (
  all_goals
    simp only [Opnd.fill, fastArith, hn, hn'] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, Lua.Num.numpow] at hk
    at_walk $ns))

/-- **The arm skeleton on a machine-level path family whose run may store
`errno`** (`sim_arm_onE`): dispatch keeps the memory (`dispatchM`), so `Q` is
read at the arm's entry. -/
theorem sim_arm_onEM {o : OpCode} {Q : Proto → Mem → RelPtrs → Word → Prop} (ho : o.toNat < Arms.jtEntries)
    (body : ArmBodyE o fun p c _ w ins => Q p c.σ.mem w ins) : SimArmOnM o Q := by
  intro p hS c s s' w hR ins hf hop hstep hQ
  have hnum := opNum_of_op? hop
  obtain ⟨c1, hs1, hlt1, hA, hm⟩ := dispatchM hR hf (by rw [hnum]; exact ho)
  obtain ⟨c', w', hs, hR'⟩ := body hS hA hf hop hstep (show Q p c1.σ.mem w ins by rw [hm]; exact hQ)
  exact sim_of_run (w := w') ⟨c', hs1.trans hs, Nat.lt_of_lt_of_le hlt1 hs.steps_le, hR'⟩

/-- `armBodyE_cls` over a predicate of the whole context (`PowQuiet` reads
the memory). -/
theorem armBodyE_cls3 {o : OpCode} {P : Proto → Config → State → RelPtrs → Word → Prop} (k : Word → Nat)
    (h0 : ArmBodyE o fun p c s w ins => P p c s w ins ∧ RegCls 0 s (k ins))
    (h1 : ArmBodyE o fun p c s w ins => P p c s w ins ∧ RegCls 1 s (k ins))
    (h2 : ArmBodyE o fun p c s w ins => P p c s w ins ∧ RegCls 2 s (k ins)) :
    ArmBodyE o P :=
  fun {_} hS {_ s _ _ ins} hA hf hop hstep hP => by
  by_cases e0 : RegCls 0 s (k ins)
  · exact h0 hS hA hf hop hstep ⟨hP, e0⟩
  by_cases e1 : RegCls 1 s (k ins)
  · exact h1 hS hA hf hop hstep ⟨hP, e1⟩
  exact h2 hS hA hf hop hstep ⟨hP, e0, e1⟩

set_option hygiene false in
/-- **`at_jpow1 pc NS`**: `op_arithf`'s `luai_numpow` (`OP_POW`) with `R[B]` of
one class (`hT : PowQuiet … ∧ RegCls cls s B`, `num_cls`) and `R[C]` by its
per-operand view (`at_jarithA`'s), `.rodata` at the entry (`hrod`), the quiet
operands as `hQo`, the kernel's `numpow` left in `hk`. -/
macro "at_jpow1 " pc:num ns:ident : tactic => `(tactic| (
  obtain ⟨hQ, hK⟩ := hT
  have hQo : QuietOps c.σ.mem _ _ := hQ
  kit_setup $pc
  have hrod := hc.rodata
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  num_cls ins.b, hn
  all_goals at_keep_tags
  all_goals num_reg ins.c, hn'
  at_jpow_both $ns))

set_option hygiene false in
/-- **`at_jpowK1 pc NS`**: `at_jpow1` with the constant `K[C]` (`OP_POWK`,
`hT : PowKQuiet … ∧ RegCls cls s B`; `at_jarithAK`'s views). -/
macro "at_jpowK1 " pc:num ns:ident : tactic => `(tactic| (
  obtain ⟨hQ, hK⟩ := hT
  have hQo : QuietOps c.σ.mem _ _ := hQ
  kit_setup $pc
  kitk_const
  have hrod := hc.rodata
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  num_cls ins.b, hn
  all_goals at_keep_tags
  all_goals num_k hn'
  at_jpow_both $ns))

/-- **`pow_arm name OP Q pc NS`** (`Q` `PowQuiet`) and **`powk_arm …`** (`Q`
`PowKQuiet`): `luai_numpow`'s arm as one declaration per class of `R[B]`
(`at_jpow1`, `at_jpowK1`), and `name : SimArmOnM OP Q` from them, given
`__ieee754_pow`'s level (b). -/
syntax "pow_arm " ident term:max ident num ident : command
syntax "powk_arm " ident term:max ident num ident : command

set_option hygiene false in
macro_rules
  | `(pow_arm $nm $op $q $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let one (cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_b{cls}") (hpw : Lua.Vm.Fn.PowR.Ieee754PowSpec_Statement) :
          ArmBodyE $op fun p c s w ins => $q p c.σ.mem w ins ∧ RegCls $n s ins.b :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jpow1 $pc $ns)
    let cmds ← ["0", "1", "2"].mapM one
    let fin ← `(theorem $nm (hpw : Lua.Vm.Fn.PowR.Ieee754PowSpec_Statement) : SimArmOnM $op $q :=
        sim_arm_onEM (by decide)
          (armBodyE_cls3 (·.b) ($(mk "_b0") hpw) ($(mk "_b1") hpw) ($(mk "_b2") hpw)))
    return Lean.mkNullNode (cmds.toArray.push fin)
  | `(powk_arm $nm $op $q $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let one (cls : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let n := Lean.Syntax.mkNumLit cls
      `(theorem $(mk s!"_b{cls}") (hpw : Lua.Vm.Fn.PowR.Ieee754PowSpec_Statement) :
          ArmBodyE $op fun p c s w ins => $q p c.σ.mem w ins ∧ RegCls $n s ins.b :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jpowK1 $pc $ns)
    let cmds ← ["0", "1", "2"].mapM one
    let fin ← `(theorem $nm (hpw : Lua.Vm.Fn.PowR.Ieee754PowSpec_Statement) : SimArmOnM $op $q :=
        sim_arm_onEM (by decide)
          (armBodyE_cls3 (·.b) ($(mk "_b0") hpw) ($(mk "_b1") hpw) ($(mk "_b2") hpw)))
    return Lean.mkNullNode (cmds.toArray.push fin)

end At

end Lua.Vm.Sim
