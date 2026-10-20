import Lua.Vm.Sim.Kit.AtFltForprepTI
import Lua.Vm.Sim.Kit.AtFltForprepS

/-!
# `FpCoerce_Statement` from its non-integer string classes (lanes F1-F8, F1-F9)

`FORPREP`'s coerced classes (`FpCoerce`: neither three integers nor three
floats) by the control values' types:

* a value that is neither a number nor a string: the kernel is stuck
  (`forLimit`/`tonumber` fail), so the class is empty;
* integers and floats only: the integer loop with a float limit (`fp_ti`,
  `Kit/AtFltForprepTI.lean`) or a float loop with integer values (`fp_c*`,
  `Kit/AtFltForprepC.lean`);
* strings that `luaO_str2num` reads as integers (`str2int`), with integers
  and floats: the integer loop with a string limit (`fp_sISI`) or a float
  loop (`fp_s*`, `Kit/AtFltForprepS.lean`, lane F1-F9);
* a string `str2int` rejects: `FpStrFlt_Statement` (open: `luaO_str2num`
  falls to `l_str2d`, `strpbrk`, `l_str2dloc` → newlib `strtod`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`FORPREP` with a string control value**: `init`, `limit` or `step` a
string (the coerced classes `luaO_str2num` serves). -/
def FpStr (p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ForCoerce p s ins ∧ ∃ k, k < 3 ∧ ∃ x, s.regs (ins.a + k) = some (.str x)

/-- `FORPREP` with a string control value (lane F1-F8): proved from
`FpStrFlt_Statement` (`fpStr_of`). -/
def FpStr_Statement : Prop := ArmBody .FORPREP FpStr

/-- **`FORPREP` with a float numeral among its control values**: every string
among `init`, `limit`, `step` is a numeral (`str2number`; a string that is
none leaves the kernel stuck), and one of them is no integer numeral
(`l_str2int` rejects it, so `str2number` reads it by `str2d`: a decimal or
hex float). -/
structure FpStrFlt (p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop where
  coerce : ForCoerce p s ins
  flt : ∃ k, k < 3 ∧ ∃ x, s.regs (ins.a + k) = some (.str x) ∧ (str2int x).isSome = false
  num : ∀ k, k < 3 → ∀ x, s.regs (ins.a + k) = some (.str x) → (str2number x).isSome = true

/-- **Open (lane F1-F9): `FORPREP` with a float numeral string.** The machine
converts it by `luaV_tonumber_` or, for an integer loop's limit,
`luaV_tointeger`: `luaO_str2num`'s `l_str2int` fails (`0x80011998`, its exits
to `0x80011b5c`), and `l_str2d` runs `strpbrk(s, ".xXnN")`, `l_str2dloc` →
`strtod` → newlib `_strtod_l` (`0x800309b4`, 1601 instructions: the locale's
decimal point, the digit loops, the exact fast path through `__floatunsidf`
and `__muldf3`/`__divdf3` on `tens`, the bignum path through `_Balloc` →
`_calloc_r` and `errno` on overflow, `__gethex` for hex floats); then
`luaV_tonumber_`'s float result (tag `19`, stored as read) or
`luaV_tointeger`'s `luaV_flttointeger` on it (`0x8001ae98`). -/
def FpStrFlt_Statement : Prop := ArmBody .FORPREP FpStrFlt

/-- Three cases of a register offset below 3. -/
theorem fp_num3 {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, k < 3 → P k
  | 0, _ => h0
  | 1, _ => h1
  | 2, _ => h2
  | _ + 3, h => absurd h (by omega)

/-- **`OP_FORPREP`'s integer loop with a float limit, every path.** -/
theorem fp_ti : ArmBody .FORPREP (FpCls false true false) := fun {p} hS {c s s' w ins} hA hf hop hstep hcl => by
  have h := fun {q : BitVec 64 → BitVec 64 → BitVec 64 → Prop} (b : ArmBody .FORPREP (TiQ q))
      (hq : FpQ q p c s w ins) => b hS hA hf hop hstep ⟨hq, hcl⟩
  simp only [FpQ] at h
  generalize slotVal c.σ.mem (w.slot ins.a) = i at h
  generalize slotVal c.σ.mem (w.slot (ins.a + 1)) = l at h
  generalize slotVal c.σ.mem (w.slot (ins.a + 2)) = st at h
  by_cases hst : st = 0#64
  · exact h ti_zero hst
  by_cases hpos : 0 < st.toInt
  · cases hok : tiOk 1 l
    · cases hz : Float.Model.lt zero (F64.toModel l)
      · exact h ti_up_none ⟨hst, hpos, hok, hz⟩
      · exact h ti_up_clip ⟨hst, hpos, hok, hz⟩
    · by_cases hgt : (tiv 1 l).toInt < i.toInt
      · exact h ti_up_skip ⟨hst, hpos, hok, hgt⟩
      · exact h ti_up_run ⟨hst, hpos, hok, hgt⟩
  · cases hok : tiOk 2 l
    · cases hz : Float.Model.lt zero (F64.toModel l)
      · exact h ti_down_clip ⟨hst, hpos, hok, hz⟩
      · exact h ti_down_none ⟨hst, hpos, hok, hz⟩
    · by_cases hlt : i.toInt < (tiv 2 l).toInt
      · exact h ti_down_skip ⟨hst, hpos, hok, hlt⟩
      · exact h ti_down_run ⟨hst, hpos, hok, hlt⟩

set_option hygiene false in
open Lean Elab Tactic Meta in
/-- **The class of a coerced `FORPREP`** from the registers' values (`h0`,
`h1`, `h2`: `s.regs (A + k) = some v`): a stuck kernel (another type: `hk`
refuted), each string split on whether `l_str2int` reads it (`hi<k>`); with
all of them read, the class's theorem; else each string split on whether it
is a numeral (`hn<k>`: none leaves the kernel stuck), and `hflt`. -/
partial def fpDispatch : TacticM Unit := withMainContext do
  let cls (k : Nat) : TacticM (Char × Option Expr) := do
    let n := Name.mkSimple s!"h{k}"
    let some d := (← getLCtx).findFromUserName? n | throwError "fp_dispatch: no {n}"
    let t ← whnfR (← instantiateMVars d.type)
    let some (_, _, r) := t.eq? | throwError "fp_dispatch: {n}"
    let v := r.appArg!
    return if v.isAppOf ``Value.int then ('I', none) else if v.isAppOf ``Value.flt then ('F', none)
      else if v.isAppOf ``Value.str then ('S', some v.appArg!) else ('O', none)
  let cs := [← cls 0, ← cls 1, ← cls 2]
  let ks := cs.map (·.1)
  let k := String.ofList ks
  if ks.contains 'O' then
    evalTactic (← `(tactic| (simp [Value.tonumber?, Value.tonum?, forLimit] at hk; done)))
    return
  let has (n : String) : TacticM Bool := return ((← getLCtx).findFromUserName? (Name.mkSimple n)).isSome
  -- a split of the main goal on `e`, each side dispatched on
  let split (h : Ident) (e : Term) : TacticM Unit := do
    evalTactic (← `(tactic| cases $h:ident : $e))
    let gs ← getUnsolvedGoals
    let mut out := []
    for g in gs do
      setGoals [g]
      fpDispatch
      out := out ++ (← getUnsolvedGoals)
    setGoals out
  -- a string not yet split on `l_str2int`
  for i in [0:3] do
    if let ('S', some x) := cs[i]! then
      unless ← has s!"hi{i}" do
        split (mkIdent (Name.mkSimple s!"hi{i}")) (← `((Lua.Num.str2int $(← Term.exprToSyntax x)).isSome))
        return
  let rejected ← (List.range 3).filterM fun i => do
    if ks[i]! != 'S' then return false
    let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"hi{i}") | return false
    let some (_, _, r) := (← instantiateMVars d.type).eq? | return false
    return r.isConstOf ``Bool.false
  if let some i0 := rejected.head? then
    -- a string not yet split on being a numeral
    for i in [0:3] do
      if let ('S', some x) := cs[i]! then
        unless ← has s!"hn{i}" do
          split (mkIdent (Name.mkSimple s!"hn{i}")) (← `(Lua.Num.str2number $(← Term.exprToSyntax x)))
          return
    -- a string no numeral: the kernel is stuck
    let st ← (List.range 3).filterM fun i => do
      if ks[i]! != 'S' then return false
      let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"hn{i}") | return false
      let some (_, _, r) := (← instantiateMVars d.type).eq? | return false
      return r.isAppOf ``Option.none
    if let some i := st.head? then
      let hn := mkIdent (Name.mkSimple s!"hn{i}")
      evalTactic (← `(tactic| (simp [Value.tonumber?, Value.tonum?, forLimit, $hn:ident] at hk; done)))
      return
    -- the open class: a float numeral among numerals
    let num (i : Nat) : TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
      let hreg := mkIdent (Name.mkSimple s!"h{i}")
      if ks[i]! == 'S' then
        let hn := mkIdent (Name.mkSimple s!"hn{i}")
        `(tacticSeq| intro x hx; simp only [Nat.add_zero, $hreg:ident, Option.some.injEq, Value.str.injEq] at hx
                     subst hx; simp [$hn:ident])
      else `(tacticSeq| intro x hx; simp only [Nat.add_zero, $hreg:ident] at hx; cases hx)
    let ki := Syntax.mkNumLit (toString i0)
    let hreg := mkIdent (Name.mkSimple s!"h{i0}")
    let hi := mkIdent (Name.mkSimple s!"hi{i0}")
    evalTactic (← `(tactic| exact hflt hS hA hf hop hstep ⟨hN, ⟨$ki, by decide, _, $hreg, $hi⟩,
      fp_num3 (by $(← num 0)) (by $(← num 1)) (by $(← num 2))⟩))
    return
  let pf (i : Nat) : TacticM Term := do
    let hreg := mkIdent (Name.mkSimple s!"h{i}")
    match ks[i]! with
    | 'S' => `(⟨_, $hreg, $(mkIdent (Name.mkSimple s!"hi{i}"))⟩)
    | _ => `(by simp [ClsReg, NumCls, IntReg, FltReg, $hreg:ident])
  let stx ← if k == "III" then `(tactic| exact absurd ⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩⟩ hN)
    else if k == "FFF" then `(tactic| exact absurd ⟨⟨_, _, h0⟩, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ h3)
    else
      let thm := mkIdent <| if k == "IFI" then `fp_ti else if ks.contains 'S' then Name.mkSimple s!"fp_s{k}"
        else Name.mkSimple s!"fp_c{k}"
      `(tactic| exact $thm hS hA hf hop hstep ⟨$(← pf 0), $(← pf 1), $(← pf 2)⟩)
  evalTactic stx

elab "fp_dispatch" : tactic => fpDispatch

/-- **`FpCoerce_Statement` from the strings `l_str2int` rejects**: the number
classes (`fp_ti`, `fp_c*`) and the string integer numerals (`fp_sISI`,
`fp_s*`) are proved, the others stuck. -/
theorem fpCoerce_of_flt (hflt : FpStrFlt_Statement) : FpCoerce_Statement := by
  intro p hS c s s' w ins hA hf hop hstep ⟨hN, h3⟩
  have hk := (kstep_iff _ _).1 hstep
  simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, forprepK] at hk
  rcases h0 : s.regs ins.a with _ | v0 <;> try simp [h0] at hk
  rcases h1 : s.regs (ins.a + 1) with _ | v1 <;> try simp [h1] at hk
  rcases h2 : s.regs (ins.a + 2) with _ | v2 <;> try simp [h2] at hk
  rcases v0 with _ | _ | _ | _ | x0 | _ <;> rcases v1 with _ | _ | _ | _ | x1 | _ <;>
    rcases v2 with _ | _ | _ | _ | x2 | _
  all_goals fp_dispatch

/-- **`FpStr_Statement` from the float numeral strings.** -/
theorem fpStr_of (hflt : FpStrFlt_Statement) : FpStr_Statement := by
  intro p hS c s s' w ins hA hf hop hstep h
  refine fpCoerce_of_flt hflt hS hA hf hop hstep ⟨h.1, fun ⟨h0, h1, h2⟩ => ?_⟩
  obtain ⟨k, hk, x, hx⟩ := h.2
  obtain ⟨_, _, e0⟩ := h0; obtain ⟨_, _, e1⟩ := h1; obtain ⟨_, _, e2⟩ := h2
  rcases k with _ | _ | _ | k
  · rw [Nat.add_zero, e0] at hx; cases hx
  · rw [e1] at hx; cases hx
  · rw [e2] at hx; cases hx
  · omega

/-- **`FpCoerce_Statement` from the string classes** (lane F1-F8's form). -/
theorem fpCoerce_of (hstr : FpStr_Statement) : FpCoerce_Statement := by
  refine fpCoerce_of_flt ?_
  intro p hS c s s' w ins hA hf hop hstep h
  obtain ⟨k, hk, x, hx, _⟩ := h.flt
  exact hstr hS hA hf hop hstep ⟨h.coerce, k, hk, x, hx⟩

end Lua.Vm.Sim.At
