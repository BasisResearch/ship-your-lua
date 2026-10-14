import Lua.Vm.Sim.Kit.AtFltForprepTI

/-!
# `FpCoerce_Statement` from its string classes (lane F1-F8)

`FORPREP`'s coerced classes (`FpCoerce`: neither three integers nor three
floats) by the control values' types:

* a value that is neither a number nor a string: the kernel is stuck
  (`forLimit`/`tonumber` fail), so the class is empty;
* integers and floats only: the integer loop with a float limit (`fp_ti`,
  `Kit/AtFltForprepTI.lean`) or a float loop with integer values (`fp_c*`,
  `Kit/AtFltForprepC.lean`);
* a string among them: `FpStr_Statement` (open: `luaV_tonumber_` and
  `luaV_tointeger` on a string call `luaO_str2num` → `l_str2int`,
  `strpbrk`, `l_str2dloc` → `strtod`).
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

/-- **Open (lane F1-F8): `FORPREP` with a string control value.** The machine
converts it by `luaV_tonumber_` (`0x8001ab58`: `l_strton` → `luaO_str2num`)
or, for an integer loop's limit, `luaV_tointeger` (`0x8001ade8`: the same
`luaO_str2num`, then `luaV_tointegerns`); `luaO_str2num` runs `l_str2int`'s
loops and, failing that, `strpbrk`, `l_str2dloc` → newlib `strtod`
(`_strtod_l`, whose bignum and hex paths allocate through `_Balloc`). -/
def FpStr_Statement : Prop := ArmBody .FORPREP FpStr

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
`h1`, `h2`: `s.regs (A + k) = some v`): a string's (`hstr`), a stuck kernel
(another type: `hk` refuted), or the number class's theorem. -/
elab "fp_dispatch" : tactic => withMainContext do
  let cls (n : Name) : TacticM Char := do
    let some d := (← getLCtx).findFromUserName? n | throwError "fp_dispatch: no {n}"
    let t ← whnfR (← instantiateMVars d.type)
    let some (_, _, r) := t.eq? | throwError "fp_dispatch: {n}"
    let v := r.appArg!
    return if v.isAppOf ``Value.int then 'I' else if v.isAppOf ``Value.flt then 'F'
      else if v.isAppOf ``Value.str then 'S' else 'O'
  let ks := [← cls `h0, ← cls `h1, ← cls `h2]
  let k := String.mk ks
  let stx ← if ks.contains 'O' then
      `(tactic| (simp [Value.tonumber?, Value.tonum?, forLimit] at hk; done))
    else if ks[0]! == 'S' then `(tactic| exact hstr hS hA hf hop hstep ⟨hN, 0, by decide, _, h0⟩)
    else if ks[1]! == 'S' then `(tactic| exact hstr hS hA hf hop hstep ⟨hN, 1, by decide, _, h1⟩)
    else if ks[2]! == 'S' then `(tactic| exact hstr hS hA hf hop hstep ⟨hN, 2, by decide, _, h2⟩)
    else if k == "III" then `(tactic| exact absurd ⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩⟩ hN)
    else if k == "FFF" then `(tactic| exact absurd ⟨⟨_, _, h0⟩, ⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ h3)
    else
      let thm := mkIdent <| if k == "IFI" then `fp_ti else Name.mkSimple s!"fp_c{k}"
      `(tactic| exact $thm hS hA hf hop hstep ⟨by simp [NumCls, IntReg, FltReg, h0],
          by simp [NumCls, IntReg, FltReg, h1], by simp [NumCls, IntReg, FltReg, h2]⟩)
  evalTactic stx

/-- **`FpCoerce_Statement` from the string classes**: the number classes are
proved (`fp_ti`, `fp_c*`), the others stuck. -/
theorem fpCoerce_of (hstr : FpStr_Statement) : FpCoerce_Statement := by
  intro p hS c s s' w ins hA hf hop hstep ⟨hN, h3⟩
  have hk := (kstep_iff _ _).1 hstep
  simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, forprepK] at hk
  rcases h0 : s.regs ins.a with _ | v0 <;> try simp [h0] at hk
  rcases h1 : s.regs (ins.a + 1) with _ | v1 <;> try simp [h1] at hk
  rcases h2 : s.regs (ins.a + 2) with _ | v2 <;> try simp [h2] at hk
  rcases v0 with _ | _ | _ | _ | x0 | _ <;> rcases v1 with _ | _ | _ | _ | x1 | _ <;>
    rcases v2 with _ | _ | _ | _ | x2 | _
  all_goals fp_dispatch

end Lua.Vm.Sim.At
