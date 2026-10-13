import Lua.Vm.Sim.Kit.AtJoinInt
import Lua.Vm.Sim.Kit.Shift

/-!
# The shifts with a float operand on the join route (lane F3)

`OP_SHL`/`OP_SHR`/`OP_SHLI`/`OP_SHRI` with a float operand: the operand
through `luaV_tointegerns(F2Ieq)` (`floor`, `__eqdf2`, the range,
`__fixdfdi`), then `luaV_shiftl` inlined: two branches on the amount and
one RV64 shift (`Kit/Shift.lean`). When the amount is the converted float,
the machine branches on `__fixdfdi`'s value; those branches are **residual
atoms**, not pair atoms:

* the kernel's `shiftl`/`shiftr` is restated as an `if` over the very
  `Bool`s the machine tests (`shiftl_m`, `shiftr_m`: `bltz`, `blt 63`,
  `blt -63` on the amount; `shiftr_K`: `bltu`/`bgeu` on the field `C`), from
  `Kit/Shift.lean`'s per-branch equations, so `at_leaf` splits the kernel
  where the machine forks;
* on the machine side a test of `__fixdfdi`'s result (or its negation, the
  amount of `OP_SHR`) is the model's `toInt64` tested, under the range atom
  (`slt_fixL`/`slt_fixR` of `Kit/AtJoinF2I.lean`, `slt_negfixL`/`R` here);
  on the kernel side the same test of `toInt64` is the same `decide`
  (`slt_i64L`/`R`, `slt_negi64L`/`R`): one residual atom for both;
* the field `C`'s tests are `decide`s on `C` (`ult_c`, `uge_c`);
* the stored integer: `__fixdfdi`'s under the path's range fact
  (`fixdfdi_model` by `at_fact`), the immediate `sC` as `addiw` (`sc_eq`).

The arms: `SHLI`/`SHRI` by `at_jshiftI pc NS`, `SHL`/`SHR` by
`bitwise_flt_arm` with `shiftl_m`/`shiftr_m` as local simp lemmas (one
declaration per (float operand, the other's class)).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-! ## The kernel's shift on the machine's tests -/

theorem msb_slt (y : BitVec 64) : y.msb = zopz0zI_s y 0x0#64 := by
  simp [zopz0zI_s, BitVec.msb_eq_toInt]

/-- A selection on a machine test, opaque to `split` and `simp`: the kernel's
value keeps the shift's tests until the path's fork facts decide them
(`at_kfork`, `bsel_true`/`bsel_false`), so `at_leaf` never splits the kernel
where the machine already chose. -/
@[irreducible] def bsel {α : Type} (b : Bool) (x y : α) : α := cond b x y

theorem bsel_true {α : Type} (x y : α) : bsel true x y = x := by unfold bsel; rfl
theorem bsel_false {α : Type} (x y : α) : bsel false x y = y := by unfold bsel; rfl

/-- **`luaV_shiftl x y`** on the machine's tests of a register amount `y`
(`OP_SHL`, `OP_SHLI`). -/
theorem shiftl_m (x y : BitVec 64) : Lua.Num.shiftl x y =
    bsel (zopz0zI_s y 0x0#64)
      (bsel (zopz0zI_s y 0xffffffffffffffc1#64) 0x0#64
        (shift_bits_right x (Sail.BitVec.extractLsb (wsub 0x0#64 y) 5 0)))
      (bsel (zopz0zI_s 0x3f#64 y) 0x0#64 (shift_bits_left x (Sail.BitVec.extractLsb y 5 0))) := by
  have hm := msb_slt y
  cases h1 : zopz0zI_s y 0x0#64 <;> rw [h1] at hm <;> simp only [bsel_true, bsel_false]
  · cases h3 : zopz0zI_s 0x3f#64 y <;> simp only [bsel_true, bsel_false]
    · exact shiftlC_run hm h3 x
    · exact shiftlC_big hm h3 x
  · cases h2 : zopz0zI_s y 0xffffffffffffffc1#64 <;> simp only [bsel_true, bsel_false]
    · exact shiftlC_neg_run hm h2 x
    · exact shiftlC_neg_big hm h2 x

/-- **`luaV_shiftr x y`** on the machine's tests of the amount `0 - y`
(`OP_SHR`). -/
theorem shiftr_m (x y : BitVec 64) : Lua.Num.shiftr x y =
    bsel (zopz0zI_s (0x0#64 - y) 0x0#64)
      (bsel (zopz0zI_s (0x0#64 - y) 0xffffffffffffffc1#64) 0x0#64
        (shift_bits_right x (Sail.BitVec.extractLsb y 5 0)))
      (bsel (zopz0zI_s 0x3f#64 (0x0#64 - y)) 0x0#64
        (shift_bits_left x (Sail.BitVec.extractLsb (0x0#64 - y) 5 0))) := by
  have hm := msb_slt (0x0#64 - y)
  cases h1 : zopz0zI_s (0x0#64 - y) 0x0#64 <;> rw [h1] at hm <;> simp only [bsel_true, bsel_false]
  · cases h3 : zopz0zI_s 0x3f#64 (0x0#64 - y) <;> simp only [bsel_true, bsel_false]
    · exact shiftrC_run hm h3 x
    · exact shiftrC_big hm h3 x
  · cases h2 : zopz0zI_s (0x0#64 - y) 0xffffffffffffffc1#64 <;> simp only [bsel_true, bsel_false]
    · exact shiftrC_neg_run hm h2 x
    · exact shiftrC_neg_big hm h2 x

/-- **`luaV_shiftr x sC`** on the machine's tests of the field `C`
(`OP_SHRI`). -/
theorem shiftr_K (x : BitVec 64) (w : Word) : Lua.Num.shiftr x (BitVec.ofInt 64 w.sc) =
    bsel (zopz0zI_u 0x7f#64 (BitVec.ofNat 64 w.c))
      (bsel (zopz0zI_u 0xbe#64 (BitVec.ofNat 64 w.c)) 0x0#64
        (shift_bits_right x
          (Sail.BitVec.extractLsb (wsub 0x0#64 (wsub 0x7f#64 (BitVec.ofNat 64 w.c))) 5 0)))
      (bsel (zopz0zKzJ_u 0x3f#64 (BitVec.ofNat 64 w.c)) 0x0#64
        (shift_bits_left x (Sail.BitVec.extractLsb (wsub 0x7f#64 (BitVec.ofNat 64 w.c)) 5 0))) := by
  cases h1 : zopz0zI_u 0x7f#64 (BitVec.ofNat 64 w.c) <;> simp only [bsel_true, bsel_false]
  · cases h2 : zopz0zKzJ_u 0x3f#64 (BitVec.ofNat 64 w.c) <;> simp only [bsel_true, bsel_false]
    · exact shiftrK_run h1 h2 x
    · exact shiftrK_big h1 h2 x
  · cases h2 : zopz0zI_u 0xbe#64 (BitVec.ofNat 64 w.c) <;> simp only [bsel_true, bsel_false]
    · exact shiftrK_neg_run h1 h2 x
    · exact shiftrK_neg_big h1 h2 x

/-! ## Residual atoms: the amount's tests -/

-- The amount `0 - y` as the kernel's simp set leaves it (`-y`), on both sides.
attribute [at_atom_simp] BitVec.zero_sub

/-- `0 - (long long)g` tested, under the range atom (`OP_SHR`'s amount). -/
@[at_atom_simp] theorem slt_negfixL (i x : BitVec 64) :
    zopz0zI_s (-Lua.Vm.Fn.Fixdfdi.S x) i =
      if Float.Model.le minIntF (F64.toModel x) = true
      then decide ((-(F64.toModel x).toInt64.toBitVec).toInt < i.toInt)
      else zopz0zI_s (-fixOut x) i := by
  by_cases h : Float.Model.le minIntF (F64.toModel x) = true
  · rw [if_pos h, fixdfdi_model x h, slt_toInt]
  · rw [if_neg h]; unfold fixOut; rfl

@[at_atom_simp] theorem slt_negfixR (i x : BitVec 64) :
    zopz0zI_s i (-Lua.Vm.Fn.Fixdfdi.S x) =
      if Float.Model.le minIntF (F64.toModel x) = true
      then decide (i.toInt < (-(F64.toModel x).toInt64.toBitVec).toInt)
      else zopz0zI_s i (-fixOut x) := by
  by_cases h : Float.Model.le minIntF (F64.toModel x) = true
  · rw [if_pos h, fixdfdi_model x h, slt_toInt]
  · rw [if_neg h]; unfold fixOut; rfl

/-- The kernel's test of a converted integer (`f2iVal`), as the machine's. -/
@[at_atom_simp] theorem slt_i64L (m : Float.Model) (i : BitVec 64) :
    zopz0zI_s m.toInt64.toBitVec i = decide (m.toInt64.toBitVec.toInt < i.toInt) := slt_toInt _ _

@[at_atom_simp] theorem slt_i64R (m : Float.Model) (i : BitVec 64) :
    zopz0zI_s i m.toInt64.toBitVec = decide (i.toInt < m.toInt64.toBitVec.toInt) := slt_toInt _ _

@[at_atom_simp] theorem slt_negi64L (m : Float.Model) (i : BitVec 64) :
    zopz0zI_s (-m.toInt64.toBitVec) i =
      decide ((-m.toInt64.toBitVec).toInt < i.toInt) := slt_toInt _ _

@[at_atom_simp] theorem slt_negi64R (m : Float.Model) (i : BitVec 64) :
    zopz0zI_s i (-m.toInt64.toBitVec) =
      decide (i.toInt < (-m.toInt64.toBitVec).toInt) := slt_toInt _ _

/-- The field `C`'s tests (`OP_SHRI`) as `decide`s on `C`. -/
@[at_atom_simp] theorem ult_c127 (w : Word) :
    zopz0zI_u 0x7f#64 (BitVec.ofNat 64 w.c) = decide (127 < w.c) :=
  ult_ofNat 127 w.c (by decide) (c_lt w)

@[at_atom_simp] theorem ult_c190 (w : Word) :
    zopz0zI_u 0xbe#64 (BitVec.ofNat 64 w.c) = decide (190 < w.c) :=
  ult_ofNat 190 w.c (by decide) (c_lt w)

@[at_atom_simp] theorem uge_c63 (w : Word) :
    zopz0zKzJ_u 0x3f#64 (BitVec.ofNat 64 w.c) = decide (w.c ≤ 63) :=
  uge_ofNat 63 w.c (by decide) (c_lt w)

/-! ## The kernel's tests decided by the fork facts -/

open Lean Elab Tactic Meta in
/-- **`at_kfork`**: on the side the close takes, the kernel's value (in `hk`)
tests the shift's amount as the machine did: the path's fork facts (`hf_*`)
are put in the residual atoms' form (`at_atom_simp`, the call sites'
`at_fspec`, the payload model `hxm`), the range atom of a test of
`__fixdfdi`'s value decided by the kernel's own side facts (`hqc`: `F2Ieq`
held), and the kernel's tests rewritten by them, leaving the value of the
path the machine took; the kernel's split tests of the amount are cleared. -/
elab "at_kfork" : tactic => withMainContext do
  let mut ns : Array Ident := #[]
  let mut ks : Array Ident := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let nm := d.userName.toString
    let isF := nm.startsWith "hf_"
    unless isF || nm.startsWith "hqc" do continue
    unless ← Meta.isProp (← instantiateMVars d.type) do continue
    let n := mkIdent (← mkFreshUserName `kf)
    let src ← Term.exprToSyntax (mkFVar d.fvarId)
    evalTactic (← `(tactic| have $n:ident := $src))
    if isF then ns := ns.push n else ks := ks.push n
  if ns.isEmpty then throwError "at_kfork: no fork facts"
  -- the kernel's side facts as conjunctions of atoms (`f2iOk` unfolded)
  unless ks.isEmpty do
    evalTactic (← `(tactic| try simp only [at_atom_simp, Bool.and_eq_true] at $ks*))
  let ms ← withMainContext do
    let mut ms : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    for k in ks do ms := ms.push (← `(Lean.Parser.Tactic.simpLemma| $k:ident))
    if ((← getLCtx).findFromUserName? `hxm).isSome then
      ms := ms.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent `hxm):ident))
    return ms
  evalTactic (← `(tactic| try simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, Aff.den,
    Aff.sum, Atom.den, Nat.one_mul, Nat.zero_add, Nat.sub_zero, at_fspec, at_atom_simp, ite_true,
    eq_self_iff_true,
    $ms,*] at $ns*))
  let ls ← withMainContext do
    ns.filterMapM fun n => do
      if ((← getLCtx).findFromUserName? n.getId).isSome then
        return some (← `(Lean.Parser.Tactic.simpLemma| $n:ident))
      return none
  evalTactic (← `(tactic| try simp only [at_atom_simp, $ls,*, bsel_true, bsel_false, Bool.false_eq_true,
    eq_self_iff_true, sc_eq] at $(mkIdent `hk):ident))
  for n in ns ++ ks do
    evalTactic (← `(tactic| try clear $n:ident))
  -- the kernel's split tests of the amount (`hq`: the close never reads them;
  -- the closers' `simp_all` would evaluate their 64-bit literals)
  withMainContext do
    let mut fs : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let nm := d.userName.toString
      unless nm.startsWith "hq" && !nm.startsWith "hqc" do continue
      let t ← instantiateMVars d.type
      if (t.find? fun e => e.isConstOf ``zopz0zI_s || e.isConstOf ``zopz0zI_u ||
          e.isConstOf ``zopz0zKzJ_u).isSome then fs := fs.push d.fvarId
    if !fs.isEmpty then
      replaceMainGoal [← (← getMainGoal).tryClearMany fs]

/-- A shift's tests in the kernel decided by the path's forks. -/
macro_rules | `(tactic| at_leaf_ext) => `(tactic| at_kfork)

set_option hygiene false in
/-- The shifts' leaves closed before any refutation is tried: on a wrong side
the close fails at its fin lemma's key or pc. -/
macro_rules
  | `(tactic| at_leaf_first $ns) => `(tactic| (
    try (simp only [Lua.Num.Res.val.injEq, Lua.Num.Numeral.int.injEq] at hq; cases hq)
    try at_kfork
    simp [VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_close $ns h0 acc))

/-! ## The stored integer -/

set_option hygiene false in
/-- **A shifted integer** (`sll`/`srl` of a converted float or by a
converted amount): `__fixdfdi`'s result is the model's `toInt64` under the
path's range fact (`at_fact`), `subw` is `wsub`, `sC` is `addiw c, -127`. -/
macro_rules | `(tactic| at_new_ext) => `(tactic| (
  refine ValRepr.int_eq ?_
  simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Aff.den, Aff.sum, Atom.den,
    Nat.one_mul, Nat.zero_add, Nat.sub_zero]
  simp (disch := at_fact) only [fixdfdi_model]
  simp (disch := assumption) only [at_fspec, Loc.den, Fld.den, Nat.add_zero, f2iVal, hxm, wsub, sc_eq,
    BitVec.zero_sub]
  done))

set_option hygiene false in
/-- `at_new` for the shifts: the stored slot's affine immediate unfolded
(`addiw c, -127`), the value matched at reducible transparency only (a
default `exact .int` would unfold `__fixdfdi`'s value against `toInt64`),
else the stored-integer rule above. -/
macro_rules
  | `(tactic| at_new) => `(tactic| (
  intro e he v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  all_goals rcases he with he | he <;>
  ( try subst he
    try simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den, Aff.den, Aff.sum, Atom.den, Nat.one_mul,
      Nat.zero_add, Nat.sub_zero, BitVec.zero_sub] at hv ⊢
    try simp at hv
    try subst hv
    try simp only [stData_three_lit, stData_three_n]
    first | (with_reducible exact .int) | at_new_ext)))

/-! ## One declaration per `F2Ieq` outcome -/

/-- The float in register `r` converts (`ok = true`, `luaV_flttointeger`'s
`F2Ieq` holds) or not: the kernel's `tointegerns` outcome as a state
predicate. -/
def F2IC (ok : Bool) (r : Nat) (s : State) : Prop :=
  ∃ x n, s.regs r = some (.flt x n) ∧ f2iOk x = ok

/-- An arm body from its two `F2Ieq` outcomes of the float register `r ins`. -/
theorem armBody_f2ic {o : OpCode} {P : State → Word → Prop} (r : Word → Nat)
    (h1 : ArmBody o fun _ _ s _ ins => P s ins ∧ F2IC true (r ins) s)
    (h0 : ArmBody o fun _ _ s _ ins => P s ins ∧ F2IC false (r ins) s)
    (hP : ∀ {s ins}, P s ins → FltReg s (r ins)) :
    ArmBody o fun _ _ s _ ins => P s ins :=
  fun {_} hS {_ s _ _ ins} hA hf hop hstep hp => by
  obtain ⟨x, n, hx⟩ := hP hp
  cases hb : f2iOk x
  · exact h0 hS hA hf hop hstep ⟨hp, x, n, hx, hb⟩
  · exact h1 hS hA hf hop hstep ⟨hp, x, n, hx, hb⟩

set_option hygiene false in
/-- **`at_jshiftI pc NS`**: `OP_SHLI`/`OP_SHRI` on a float `R[B]` of one
`F2Ieq` outcome (`hT : FltReg s ins.b ∧ F2IC ok ins.b s`): `R[B]` by its
view, the outcome as the fact `hqc_cls` (read by `at_atoms`, `at_kfork`),
the kernel's `tointegerns` over the atoms (`rawArith_bit_fi`/`_if`) decided
by it and its shift on the machine's tests (`shiftl_m`, `shiftr_K`), then
`at_walk NS`. -/
macro "at_jshiftI " pc:num ns:ident : tactic => `(tactic| (
  obtain ⟨hT, hcls⟩ := hT
  kit_setup $pc
  try simp [immC, Opnd.ports] at htop
  try simp only [immC, Opnd.ports] at hk
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  have hrod := hc.rodata
  flt_reg_q x ins.b, hT
  obtain ⟨x', n', hst', hqc_cls⟩ := hcls
  rw [hst] at hst'; cases hst'
  simp only [Opnd.fill, fastArith] at hk
  simp (disch := decide) [Value.toNum?, BinOp.toOp, rawArith_bit_fi, rawArith_bit_if, Res.ofInt,
    intarith, Value.ofNum, VState.apply, KEdge.kills, shiftl_m, shiftr_K, hqc_cls] at hk
  at_walk $ns))

/-- **`shift_flt_arm name OP pc NS`**: a shift arm with a float `R[B]` as
one declaration per `F2Ieq` outcome (`at_jshiftI`), and
`name : SoftFloatSpec → FloorSpec → SimArmOn OP FltB` from them. -/
syntax "shift_flt_arm " ident term:max num ident : command

set_option hygiene false in
macro_rules
  | `(shift_flt_arm $nm $op $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let one (ok : String) : Lean.MacroM (Lean.TSyntax `command) := do
      let b ← if ok == "1" then `(true) else `(false)
      `(theorem $(mk s!"_{ok}") (hsf : SoftFloatSpec) (hfl : FloorSpec) :
          ArmBody $op fun _ _ s _ ins => FltReg s ins.b ∧ F2IC $b ins.b s :=
        fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jshiftI $pc $ns)
    let fin ← `(theorem $nm (hsf : SoftFloatSpec) (hfl : FloorSpec) : SimArmOn $op FltB :=
        sim_arm_on (by decide) (armBody_f2ic (·.b) ($(mk "_1") hsf hfl) ($(mk "_0") hsf hfl) id))
    return Lean.mkNullNode #[← one "1", ← one "0", fin]

set_option hygiene false in
/-- **`at_jshift2 pc NS j k (post)`**: `OP_SHL`/`OP_SHR` with `R[j]` a float
of one `F2Ieq` outcome and `R[k]` of one class (`hT : (FltReg s j ∧ RegCls
cls s k) ∧ F2IC ok j s`): `at_jbit`'s set-up with the outcome as the fact
`hqc_cls` (and `post`'s `hqc_cls2`, the other float's outcome), the kernel's
shift on the machine's tests (`shiftl_m`, `shiftr_m`), then `at_walk NS`. -/
macro "at_jshift2 " pc:num ns:ident j:term:max "," k:term:max "(" post:tacticSeq ")" : tactic => `(tactic| (
  obtain ⟨⟨hT, hK⟩, hcls⟩ := hT
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  have hrod := hc.rodata
  flt_reg_q x $j, hT
  obtain ⟨x', n', hst', hqc_cls⟩ := hcls
  rw [hst] at hst'; cases hst'
  num_cls $k, hn
  all_goals
    ($post)
    simp only [Opnd.fill, fastArith, hn] at hk
    simp (disch := decide) [Value.toNum?, BinOp.toOp, rawArith_bit_fi, rawArith_bit_if, rawArith_bit_ff,
      Res.ofInt, intarith, Value.ofNum, VState.apply, writeDefs, KEdge.kills, shiftl_m, shiftr_m,
      hqc_cls, hqc_cls2] at hk
    at_walk $ns))

set_option hygiene false in
/-- `at_jshift2` with `R[k]` a float too, of one `F2Ieq` outcome (`hT : (… ∧
RegCls 0 s k) ∧ F2IC ok j s) ∧ F2IC ok' k s`: `hqc_cls2`). -/
macro "at_jshift2f " pc:num ns:ident j:term "," k:term : tactic => `(tactic| (
  obtain ⟨hT, hcls2⟩ := hT
  at_jshift2 $pc $ns $j, $k (
    obtain ⟨y', m', hsty, hqc_cls2⟩ := hcls2
    rw [hr] at hsty; cases hsty)))

/-- **`shift2_flt_arm name OP pc NS`**: `OP_SHL`/`OP_SHR`'s float paths as
one declaration per (float operand and its `F2Ieq` outcome, the other's
class, and its outcome if a float) (`at_jshift2`, `at_jshift2f`), and
`name : SoftFloatSpec → FloorSpec → SimArmOn OP FltBC` from them
(`armBody_f2ic`, `armBody_cls`, `sim_on_or`). -/
syntax "shift2_flt_arm " ident term:max num ident : command

set_option hygiene false in
macro_rules
  | `(shift2_flt_arm $nm $op $pc $ns) => do
    let mk (s : String) : Lean.Ident := Lean.mkIdent (nm.getId.appendAfter s)
    let regs (side : String) : Lean.MacroM (Lean.Term × Lean.Term) := do
      if side == "b" then pure ((← `(ins.b)), (← `(ins.c))) else pure ((← `(ins.c)), (← `(ins.b)))
    let bool (ok : String) : Lean.MacroM Lean.Term := if ok == "1" then `(true) else `(false)
    let mut cmds : Array (Lean.TSyntax `command) := #[]
    for side in ["b", "c"] do
      let (j, k) ← regs side
      -- the other an integer or no number: one declaration per outcome of `R[j]`
      for cls in ["1", "2"] do
        for ok in ["1", "0"] do
          let n := Lean.Syntax.mkNumLit cls
          cmds := cmds.push (← `(theorem $(mk s!"_{side}{cls}_{ok}") (hsf : SoftFloatSpec)
              (hfl : FloorSpec) :
              ArmBody $op fun _ _ s _ ins => (FltReg s $j ∧ RegCls $n s $k) ∧ F2IC $(← bool ok) $j s :=
            fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
              at_jshift2 $pc $ns $j, $k (have hqc_cls2 : True := trivial)))
      -- the other a float: per outcome of each
      for ok in ["1", "0"] do
        for ok' in ["1", "0"] do
          cmds := cmds.push (← `(theorem $(mk s!"_{side}0_{ok}{ok'}") (hsf : SoftFloatSpec)
              (hfl : FloorSpec) :
              ArmBody $op fun _ _ s _ ins =>
                ((FltReg s $j ∧ RegCls 0 s $k) ∧ F2IC $(← bool ok) $j s) ∧ F2IC $(← bool ok') $k s :=
            fun {p} hS {c s s' w ins} hA hf hop hstep hT => by at_jshift2f $pc $ns $j, $k))
    let cl (side cls : String) : Lean.MacroM Lean.Term := do
      let (j, _) ← regs side
      `(armBody_f2ic (fun ins => $j) ($(mk s!"_{side}{cls}_1") hsf hfl) ($(mk s!"_{side}{cls}_0") hsf hfl)
          (fun h => h.1))
    let cl0 (side : String) : Lean.MacroM Lean.Term := do
      let (j, k) ← regs side
      let half (ok : String) : Lean.MacroM Lean.Term :=
        `(armBody_f2ic (fun ins => $k) ($(mk s!"_{side}0_{ok}1") hsf hfl) ($(mk s!"_{side}0_{ok}0") hsf hfl)
            (fun h => h.1.2))
      `(armBody_f2ic (fun ins => $j) $(← half "1") $(← half "0") (fun h => h.1))
    let fin ← `(theorem $nm (hsf : SoftFloatSpec) (hfl : FloorSpec) : SimArmOn $op FltBC :=
        sim_on_or (by decide)
          (armBody_cls (·.c) $(← cl0 "b") $(← cl "b" "1") $(← cl "b" "2"))
          (armBody_cls (·.b) $(← cl0 "c") $(← cl "c" "1") $(← cl "c" "2")))
    return Lean.mkNullNode (cmds.push fin)

end Lua.Vm.Sim.At
