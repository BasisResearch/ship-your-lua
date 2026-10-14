import Lua.Vm.Sim.Kit.TointF
import Lua.Vm.Sim.Kit.AtFloat

/-!
# FORPREP's coercions as call nodes at a row (lane F1-F8)

The call at-lemmas of `OP_FORPREP_TI`/`OP_FORPREP_C*` (`scripts/gen_lua_at.py`):

* `luaV_tointeger(R[A+1], sp + 40, mode)` on a float limit
  (`toint_flt_sum`, `Kit/TointF.lean`), as two variants on whether
  `flttointeger` converts (`tiOk`, the run's fork `hg_ti`): `a0 = 1` and
  `*q` the integer (`tiv`), or `a0 = 0`; the callee frames
  `[sp - 192, sp)` the log entry `clob` with content `tifW'`;
* `luaV_tonumber_(R[A+k], q)` on an integer (`tonum_int_sum`): `a0 = 1`, `*q`
  the converted float (`__floatdidf`), the callee frames `[sp - 80, sp)` a
  `clob` with content `toniW`.

The operand is read through the path's stores (`hv`, by `at_eq`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-- `luaV_tointeger(v, &i, mode)` on a float `v` converts (`flttointeger`). -/
def tiOk (md : Nat) (v : BitVec 64) : Bool := (flttointeger (F64.toModel v) (tifMode md)).isSome

/-- … and the integer it stores. -/
def tiv (md : Nat) (v : BitVec 64) : BitVec 64 := (flttointeger (F64.toModel v) (tifMode md)).getD 0

theorem tifRes_cx {md : Nat} {r : BitVec 64} {n q sp : Nat} {f : HFrame} {M : Mem} {o : Array String}
    {v : BitVec 64} (hv : slotVal M n = v) :
    tifRes md (tifCx r n q sp f M o) = flttointeger (F64.toModel v) (tifMode md) := by
  rw [← hv]; rfl

/-- **`luaV_tointeger` on a float that converts**, at a call. -/
theorem tif_ok_at {md : Nat} (hmd : md = 1 ∨ md = 2) {n q sp : Nat} {r : BitVec 64} {f : HFrame}
    {M : Mem} {o : Array String} (hx : TifCtx M n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (ht : slotTag M n = 19#8) {v : BitVec 64} (hv : slotVal M n = v)
    (hok : tiOk md v = true) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 md⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay M o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
        (ArmPay (writeMap8 (memPatch M (tifW' md r f.s0 f.s1 n q sp M) (sp - 192) 192) q
          (sdData_val (tiv md v))) o)) := by
  have hr := tifRes_cx (md := md) (r := r) (q := q) (sp := sp) (f := f) (o := o) hv
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hok
  have e1 : tifRes md (tifCx r n q sp f M o) = some (tiv md v) := by
    rw [hr, hi]; simp only [tiv, hi, Option.getD_some]
  have := toint_flt_sum hmd n q sp r f M o hx hsp hgp ht
  rw [tifMem_some e1, e1, tifW_eq] at this
  exact this

/-- **`luaV_tointeger` on a float that does not convert**, at a call. -/
theorem tif_no_at {md : Nat} (hmd : md = 1 ∨ md = 2) {n q sp : Nat} {r : BitVec 64} {f : HFrame}
    {M : Mem} {o : Array String} (hx : TifCtx M n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (ht : slotTag M n = 19#8) {v : BitVec 64} (hv : slotVal M n = v)
    (hno : tiOk md v = false) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 md⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay M o))
      (SegSt r (⟨Register.x10, 0#64⟩ :: f.pins)
        (ArmPay (memPatch M (tifW' md r f.s0 f.s1 n q sp M) (sp - 192) 192) o)) := by
  have hr := tifRes_cx (md := md) (r := r) (q := q) (sp := sp) (f := f) (o := o) hv
  have e1 : tifRes md (tifCx r n q sp f M o) = none := by
    rw [hr]; simpa only [tiOk, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using hno
  have := toint_flt_sum hmd n q sp r f M o hx hsp hgp ht
  rw [tifMem_none e1, e1, tifW_eq] at this
  exact this

/-- **`luaV_tonumber_` on an integer**, at a call. -/
theorem toni_at {n q sp : Nat} {r : BitVec 64} {f : HFrame} {M : Mem} {o : Array String}
    (hx : TifCtx M n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (ht : slotTag M n = 3#8) {v : BitVec 64} (hv : slotVal M n = v) :
    Triple (SegSt 0x8001ab58#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x1, r⟩ :: f.pins) (ArmPay M o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
        (ArmPay (writeMap8 (memPatch M (toniW r n q sp M) (sp - 80) 80) q
          (sdData_val (Lua.Vm.Fn.Floatdidf.S v))) o)) := by
  have := tonum_int_sum n q sp r f M o hx hsp hgp ht
  rw [hv] at this
  exact this

end Lua.Vm.Sim.Kit

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Lua.Num

/-! ## The integer loop's conversion facts (`OP_FORPREP_TI`) -/

/-- `bgtz` on `__gedf2(a, b)`: `b < a`. -/
theorem bgtz_gedf2 (a b : BitVec 64) : zopz0zI_s (0#64) (Lua.Vm.Fn.Gedf2.S a b) = F64.lt b a := by
  have h := blez_gedf2 a b
  unfold zopz0zKzJ_s at h; unfold zopz0zI_s
  cases e : F64.lt b a <;> simp_all

theorem flt_tif_some {md : Nat} {b : BitVec 64} (h : tiOk md b = true) :
    flttointeger (F64.toModel b) (tifMode md) = some (tiv md b) := by
  unfold tiOk at h; unfold tiv
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
  rw [hi]; rfl

theorem flt_tif_none {md : Nat} {b : BitVec 64} (h : tiOk md b = false) :
    flttointeger (F64.toModel b) (tifMode md) = none := by
  unfold tiOk at h
  simpa only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using h

theorem tifMode_1 : tifMode 1 = .floor := rfl
theorem tifMode_2 : tifMode 2 = .ceil := rfl

/-- No integer exceeds `LUA_MAXINTEGER`. -/
theorem not_gt_maxInt (x : BitVec 64) : ¬ (x.toInt > maxInt.toInt) := by
  have := BitVec.toInt_lt (x := x)
  have e : maxInt.toInt = 2 ^ 63 - 1 := by decide
  omega

/-- No integer is below `LUA_MININTEGER`. -/
theorem not_lt_minInt (x : BitVec 64) : ¬ (x.toInt < minInt.toInt) := by
  have := BitVec.le_toInt (x := x)
  have e : minInt.toInt = -2 ^ 63 := by decide
  omega


open Lean Elab Tactic Meta in
/-- `.rodata` through the path's stores above the HTIF mailbox: each store
peeled by the lemma of its head symbol, the entry's fact (`hc.rodata`) last
(`at_rod` tries the entry's fact at every store, a costly failed
unification on a long log). -/
partial def tifRod : TacticM Unit := withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget))
  let m := t.appArg!
  if m.isAppOf ``writeMap8 then
    evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.wm8 ?_ (by kit_disch)))
    tifRod
  else if m.isAppOf ``Std.ExtHashMap.insert then
    evalTactic (← `(tactic| refine Lua.Vm.Sim.At.RodataRead.ins ?_ (by kit_disch)))
    tifRod
  else if m.isAppOf ``memPatch then
    evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.patch ?_ (by kit_disch)))
    tifRod
  else
    evalTactic (← `(tactic| exact $(mkIdent `hc).rodata))

elab "tif_rod" : tactic => tifRod

set_option hygiene false in
/-- The context facts of a coercion's call (`TifCtx`): `.rodata` through the
path's stores, the rest from the arm's ranges. -/
macro "tif_ctx" : tactic => `(tactic|
  (refine ⟨by tif_rod, by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
    by kit_disch, by kit_disch, by kit_disch⟩))

/-- **`at_tif f k md ok|no`**: `luaV_tointeger`'s float call lemma's proof
(after `at_open`): the variant's summary at the row, the operand `R[f+k]`
read through the path's stores, the guard `hg_ti`. -/
syntax "at_tif " ident num num ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| at_tif $fl:ident $k:num $md:num $v:ident) =>
    let lem := if v.getId == `ok then Lean.mkIdent ``Lua.Vm.Sim.Kit.tif_ok_at else Lean.mkIdent ``Lua.Vm.Sim.Kit.tif_no_at
    `(tactic| (
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
      ($lem (md := $md) (by decide) (sp := X.w.sp) (f := hframe?) (by tif_ctx) (by rfl) (by rfl) (by at_pre ht)
        (v := slotVal X.c.σ.mem (X.w.slot (X.ins.$fl + $k))) (by at_eq)
        (by simpa only [Loc.den, Fld.den] using hg_ti))
    refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
    · at_pins h
    · at_mem))

/-- **`at_toni f k`**: `luaV_tonumber_`'s integer call lemma's proof (after
`at_open` and the dead registers' pins). -/
syntax "at_toni " ident num : tactic

set_option hygiene false in
macro_rules
  | `(tactic| at_toni $fl:ident $k:num) => do
    -- the slot in the row's form (`Nat.add_zero` applied)
    let j ← if k.getNat == 0 then `(X.ins.$fl) else `(X.ins.$fl + $k)
    `(tactic| (
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
      (Lua.Vm.Sim.Kit.toni_at (sp := X.w.sp) (f := hframe?) (by tif_ctx) (by rfl) (by rfl) (by at_pre ht)
        (v := slotVal X.c.σ.mem (X.w.slot $j)) (by at_eq))
    refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
    · at_pins h
    · at_mem))

open Lean Elab Tactic Meta in
/-- Generalise the outermost `memPatch` subterm of the goal (a callee's
frame and everything below it in the log) to an opaque memory, when the
goal's loads are all answered by newer stores. -/
elab "gen_patch" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (·.isAppOfArity ``Lua.Vm.Sim.memPatch 4) | throwError "gen_patch: none"
  let stx ← Term.exprToSyntax e
  evalTactic (← `(tactic| generalize $stx:term = M₀))

set_option hygiene false in
/-- **`at_fin_withG fr, kp`**: `at_fin_with`, its stored slots read first past
newer stores only (`gen_patch`: the log below a callee's frame is opaque, a
shallower term for the forwarding), else through the whole log. -/
macro "at_fin_withG " fr:term "," kp:term : tactic => `(tactic| (
  have hfr := $fr
  have hkp := $kp
  at_facts hX
  have hseg := Vsa.Sim.SegSt.repin (L' := []) h trivial
  at_unfold at h
  refine ⟨hseg, at_fin_pins, hfr, ?_, ?_, hkp, ?_⟩
  all_goals try at_unfold
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Loc.den, stData_zext]
    repeat' apply And.intro
    all_goals first | (gen_patch; at_eq) | at_eq
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Loc.den]
    repeat' apply And.intro
    all_goals first | (gen_patch; at_eq) | at_eq
  at_fin_bound))

end Lua.Vm.Sim.At
