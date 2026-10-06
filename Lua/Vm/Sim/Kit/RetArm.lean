import Lua.Vm.Sim.Kit.RetTail

/-!
# `OP_RETURN` from the arm to `ccall` (lane F1-4)

The arm at `0x8001c360` (lvm.c `OP_RETURN`, `n = B - 1`, `k`, `C`) on every
path the machine can take: `B = 0` (`n` from `L->top`) or not, `k` (then
`L->top` raised to `ci->top` or not, `luaF_close` with nothing open, the
trap reload) or not, `C` (`ci->func` moved back by `nextraargs + C`) or not;
then `L->top = ra + n` and `luaD_poscall` (`ret_tail`). Each branch is split
on its guard (`kit_split`), not decided from the instruction: every path
returns into `ccall` with the memory in agreement with the head's off the
return path's words (`AtCcall`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **The `luaF_close` call node** at `OP_RETURN`'s call site, from the
agreement: nothing open (`HeadReads`), `tbclist < base` (`RetCx`). -/
theorem ret_close_call {p : Proto} {w : RelPtrs} {m0 M : Mem} {o : Array String} {c0 c : Config}
    {L : List Pin} (hX : RetCx p w m0) (acc : Steps c0 c)
    (h : SegSt 0x8000c224#64 L (ArmPay M o) c) (hM : RAgree w m0 M) (f : RFrame)
    (v12 v13 : BitVec 64)
    (hL : PinsHold c.σ (⟨Register.x10, BitVec.ofNat 64 w.L⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 w.base⟩ :: ⟨Register.x12, v12⟩ :: ⟨Register.x13, v13⟩ ::
        ⟨Register.x1, 0x8001c3d0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 w.sp⟩ :: f.pins)) :
    ∃ c', Steps c0 c' ∧ SegSt 0x8001c3d0#64 (⟨Register.x2, BitVec.ofNat 64 w.sp⟩ :: f.pins)
      (ArmPay (fcMem M w.sp f 0x8001c3d0#64) o) c' := by
  have hr := hX.ranges
  have hR := hX.reads
  have hb := hX.tbc_lt
  ret_facts hr
  have hx : FcCx w.L w.base w.sp w.rt.stack 0x8001c3d0#64 M :=
    { ra := by decide
      sp_lo := by omega
      sp_hi := by omega
      sp_al := by omega
      L_lo := by omega
      L_hi := by simp only [stateSize]; omega
      lvl_hi := by simp only [RelPtrs.base, stackValueSize]; omega
      lt := hb
      open_ := by rw [hM.bytesT8 (hr.nd_L (by decide) (by decide))]; exact hR.openupval
      tbc := by rw [hM.bytesT8 (hr.nd_L (by decide) (by decide))]; exact hR.tbclist }
  exact h.call acc hL (fclose_sum hx f v12 v13 o)

/-- **The tail** from the `luaD_poscall` call site, from the agreement. -/
theorem ret_tail_at {p : Proto} {w : RelPtrs} {m0 M : Mem} {o : Array String} {c0 c : Config}
    {L : List Pin} (hX : RetCx p w m0) (acc : Steps c0 c)
    (h : SegSt 0x8001c784#64 L (ArmPay M o) c) (hM : RAgree w m0 M)
    (q9 q18 q19 q20 q21 q24 q25 q27 : BitVec 64)
    (hL : PinsHold c.σ (pcRow w q9 q18 q19 q20 q21 q24 q25 q27)) :
    ∃ c', Steps c0 c' ∧ AtCcall w m0 o c' := by
  obtain ⟨c', hs, hq⟩ := ret_tail hX hM q9 q18 q19 q20 q21 q24 q25 q27 o c (h.repin hL)
  exact ⟨c', acc.trans hs, hq⟩

/-- A dirty store's side goal. -/
macro "ret_dirty" : tactic => `(tactic| first
    | exact RetDirty.func (by assumption) | exact RetDirty.savedpc (by assumption)
    | exact RetDirty.nres (by assumption) | exact RetDirty.top (by assumption)
    | exact RetDirty.lci (by assumption)
    | exact RetDirty.nCcalls (by assumption) | exact RetDirty.errorJmp (by assumption)
    | exact RetDirty.errfunc (by assumption)
    | (apply RetDirty.below <;> (try simp only [cStackBudget, RuntimeData.spEntry]) <;> omega))

open Lean Elab Tactic Meta in
/-- **`ret_agree`**: the agreement of a store chain over the head memory,
store by store, dispatched on the store's head symbol (no unfolding of the
chain); each store's bytes dirty (`ret_dirty`). -/
partial def retAgree : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let x := t.appArg!
  if x.isAppOf ``Vsa.Sim.writeMap8 then
    evalTactic (← `(tactic| refine RAgree.wm8 ?_ _ (fun i hi => ?_)))
    let gs ← getGoals
    setGoals [gs[1]!]
    evalTactic (← `(tactic| ret_dirty))
    setGoals [gs[0]!]
    retAgree
  else if x.isAppOf ``Vsa.Sim.writeMap4 then
    evalTactic (← `(tactic| refine RAgree.wm4 ?_ _ (fun i hi => ?_)))
    let gs ← getGoals
    setGoals [gs[1]!]
    evalTactic (← `(tactic| ret_dirty))
    setGoals [gs[0]!]
    retAgree
  else if x.isAppOf ``fcMem then
    evalTactic (← `(tactic| unfold fcMem))
    retAgree
  else if x.isAppOf ``pcMem then
    evalTactic (← `(tactic| unfold pcMem))
    retAgree
  else
    evalTactic (← `(tactic| exact RAgree.refl _ _))

elab "ret_agree" : tactic => retAgree

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    sext64_id, sdData_id] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | kit_hyp
      | decide)

/-! ## The rows between the phases

`sp`, `gp`, `L`, `ci` and `base` are pinned; the other registers hold some
values (the instruction's fields, `n`, `ra`, …), which no later phase needs:
every branch on them is split, not decided. -/

abbrev rowFix (w : RelPtrs) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 w.L⟩, ⟨Register.x23, BitVec.ofNat 64 w.ci⟩,
   ⟨Register.x25, BitVec.ofNat 64 w.base⟩]

/-- The free registers of a row inside the arm. -/
abbrev rowVar (q9 q18 q19 q20 q21 q22 q24 q26 q27 : BitVec 64) : List Pin :=
  [⟨Register.x9, q9⟩, ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩,
   ⟨Register.x21, q21⟩, ⟨Register.x22, q22⟩, ⟨Register.x24, q24⟩, ⟨Register.x26, q26⟩,
   ⟨Register.x27, q27⟩]

/-- **A state of the arm at `pc`**: the fixed registers, some values for the
others, the memory in agreement with the head's. -/
def RAt (w : RelPtrs) (m0 : Mem) (o : Array String) (pc : BitVec 64) (c : Config) : Prop :=
  ∃ M q9 q18 q19 q20 q21 q22 q24 q26 q27, RAgree w m0 M ∧
    SegSt pc (rowFix w ++ rowVar q9 q18 q19 q20 q21 q22 q24 q26 q27) (ArmPay M o) c

/-- **At the `luaF_close` call** (`0x8000c224`): its arguments too. -/
def RAtClose (w : RelPtrs) (m0 : Mem) (o : Array String) (c : Config) : Prop :=
  ∃ M q9 q18 q19 q20 q21 q22 q24 q26 q27 v12 v13, RAgree w m0 M ∧
    SegSt 0x8000c224#64 (⟨Register.x10, BitVec.ofNat 64 w.L⟩ :: ⟨Register.x11, BitVec.ofNat 64 w.base⟩ ::
      ⟨Register.x12, v12⟩ :: ⟨Register.x13, v13⟩ :: ⟨Register.x1, 0x8001c3d0#64⟩ ::
      (rowFix w ++ rowVar q9 q18 q19 q20 q21 q22 q24 q26 q27)) (ArmPay M o) c

set_option hygiene false in
/-- Close a phase at a row: the agreement through the phase's stores, the pins. -/
macro "ret_close" : tactic => `(tactic| (
  refine ⟨_, acc, _, _, _, _, _, _, _, _, _, _, hM.trans (by ret_agree), h.repin (by pins_of h)⟩))

set_option hygiene false in
macro "ret_closeC" : tactic => `(tactic| (
  refine ⟨_, acc, _, _, _, _, _, _, _, _, _, _, _, _, hM.trans (by ret_agree),
    h.repin (by pins_of h)⟩))

set_option hygiene false in
macro "ret_closeR" : tactic => `(tactic| (
  refine ⟨_, acc, .inr ⟨_, _, _, _, _, _, _, _, _, _, hM.trans (by ret_agree),
    h.repin (by pins_of h)⟩⟩))

set_option hygiene false in
macro "ret_closeL" : tactic => `(tactic| (
  refine ⟨_, acc, .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, hM.trans (by ret_agree),
    h.repin (by pins_of h)⟩⟩))

/-- **Phase 1**: `n = B - 1` (or `L->top - ra` for `B = 0`), to `0x8001c398`. -/
theorem ret_p1 {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) (hop : ins.opNum = 70) :
    ∃ c', Steps c c' ∧ RAt w c.σ.mem c.σ.sailOutput 0x8001c398#64 c' := by
  have hr := hA.core.ranges
  have h := hA.seg (pc := 0x8001c360#64) (by rw [hop]; decide)
  have acc := Steps.refl c
  have hM := RAgree.refl w c.σ.mem
  ret_facts hr
  simp only [armPins] at h
  kit_split h
  all_goals kit_run h acc until [0x8001c398]
  all_goals ret_close

/-- **Phase 2**: `savepc`; with `k`, `nres`, `L->top` raised to `ci->top` or
not, to the `luaF_close` call; without, to `0x8001c3dc`. -/
theorem ret_p2 {p : Proto} {w : RelPtrs} {m0 : Mem} {o : Array String} (hX : RetCx p w m0) :
    Triple (RAt w m0 o 0x8001c398#64) (fun c => RAtClose w m0 o c ∨ RAt w m0 o 0x8001c3dc#64 c) := by
  rintro c ⟨M, q9, q18, q19, q20, q21, q22, q24, q26, q27, hM, h⟩
  have acc := Steps.refl c
  have hr := hX.ranges
  ret_facts hr
  simp only [rowFix, rowVar, List.cons_append, List.nil_append] at h
  kit_split h
  all_goals kit_run h acc until [0x8001c3a8, 0x8001c3dc]
  all_goals first
    | ret_closeR
    | (kit_split h
       all_goals kit_run h acc until [0x8000c224]
       all_goals ret_closeL)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | kit_hyp
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, fcMem,
          bytesT4_wm8_out'', hTr, sext32_zero]; decide))

/-- **Phase 3**: the `luaF_close` call node, the trap reload (`trap = 0`), to
`0x8001c3dc`. -/
theorem ret_p3 {p : Proto} {w : RelPtrs} {m0 : Mem} {o : Array String} (hX : RetCx p w m0) :
    Triple (RAtClose w m0 o) (RAt w m0 o 0x8001c3dc#64) := by
  rintro c ⟨M, q9, q18, q19, q20, q21, q22, q24, q26, q27, v12, v13, hM, h⟩
  have acc := Steps.refl c
  have hr := hX.ranges
  have hTr := (tailMem hX hM).trap
  ret_facts hr
  simp only [rowFix, rowVar, List.cons_append, List.nil_append] at h
  obtain ⟨_, acc, h⟩ := ret_close_call hX acc h hM
    ⟨BitVec.ofNat 64 symGlobalPointer, BitVec.ofNat 64 w.L, q9, q18, q19, q20, q21, q22,
      BitVec.ofNat 64 w.ci, q24, BitVec.ofNat 64 w.base, q26, q27⟩ v12 v13 (by pins_of h)
  try simp only [RFrame.pins] at h
  kit_run h acc until [0x8001c3dc]
  ret_close

/-- **Phase 4**: `C` (`ci->func` moved back by `nextraargs + C`) or not,
`L->top = ra + n`, then the tail (`ret_tail`). -/
theorem ret_p4 {p : Proto} {w : RelPtrs} {m0 : Mem} {o : Array String} (hX : RetCx p w m0) :
    Triple (RAt w m0 o 0x8001c3dc#64) (AtCcall w m0 o) := by
  rintro c ⟨M, q9, q18, q19, q20, q21, q22, q24, q26, q27, hM, h⟩
  have acc := Steps.refl c
  have hr := hX.ranges
  ret_facts hr
  simp only [rowFix, rowVar, List.cons_append, List.nil_append] at h
  kit_split h
  all_goals kit_run h acc until [0x8001c784]
  all_goals exact ret_tail_at hX acc h (hM.trans (by ret_agree)) _ _ _ _ _ _ _ _ (by pins_of h)

/-- **`OP_RETURN`, every path, to `ccall`** (`AtCcall`): phases 1–4. -/
theorem ret_RETURN {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) (hop : ins.opNum = 70) :
    ∃ c', Steps c c' ∧ AtCcall w c.σ.mem c.σ.sailOutput c' := by
  have hX := hA.core.retCx
  obtain ⟨c1, h1, q1⟩ := ret_p1 hA hop
  obtain ⟨c2, h2, q2⟩ := ret_p2 hX c1 q1
  rcases q2 with q2 | q2
  · obtain ⟨c3, h3, q3⟩ := ret_p3 hX c2 q2
    obtain ⟨c4, h4, q4⟩ := ret_p4 hX c3 q3
    exact ⟨c4, h1.trans (h2.trans (h3.trans h4)), q4⟩
  · obtain ⟨c4, h4, q4⟩ := ret_p4 hX c2 q2
    exact ⟨c4, h1.trans (h2.trans h4), q4⟩

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | kit_hyp
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          bytesT2_wm8_out', bytesT4_wm8_out'', hT.hook, hT.nres, sext32_zero, sext16_zero]; decide))

/-- **`OP_RETURN0`** (`0x8001c2bc`): no hooks, `L->ci = ci->previous`,
`L->top = base - 1`, no result to fill (`ci->nresults = 0`), then
`CIST_FRESH` (`ret_fresh`). -/
theorem ret_RETURN0 {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) (hop : ins.opNum = 71) :
    ∃ c', Steps c c' ∧ AtCcall w c.σ.mem c.σ.sailOutput c' := by
  have hX := hA.core.retCx
  have hr := hX.ranges
  have hT := tailMem hX (RAgree.refl w c.σ.mem)
  have h := hA.seg (pc := 0x8001c2bc#64) (by rw [hop]; decide)
  have acc := Steps.refl c
  have hM := RAgree.refl w c.σ.mem
  ret_facts hr
  simp only [armPins] at h
  kit_run h acc until [0x8001c274]
  obtain ⟨c', hs, hq⟩ := ret_fresh hX (hM.trans (by ret_agree)) _ _ _ _ _ _ _ _ _ _
    (h.repin (by pins_of h))
  exact ⟨c', acc.trans hs, hq⟩

/-- **`OP_RETURN1`** (`0x8001c24c`): no hooks, `L->ci = ci->previous`, no
result kept (`ci->nresults = 0`), `L->top = base - 1`, then `CIST_FRESH`. -/
theorem ret_RETURN1 {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) (hop : ins.opNum = 72) :
    ∃ c', Steps c c' ∧ AtCcall w c.σ.mem c.σ.sailOutput c' := by
  have hX := hA.core.retCx
  have hr := hX.ranges
  have hT := tailMem hX (RAgree.refl w c.σ.mem)
  have h := hA.seg (pc := 0x8001c24c#64) (by rw [hop]; decide)
  have acc := Steps.refl c
  have hM := RAgree.refl w c.σ.mem
  ret_facts hr
  simp only [armPins] at h
  kit_run h acc until [0x8001c274]
  obtain ⟨c', hs, hq⟩ := ret_fresh hX (hM.trans (by ret_agree)) _ _ _ _ _ _ _ _ _ _
    (h.repin (by pins_of h))
  exact ⟨c', acc.trans hs, hq⟩

end Lua.Vm.Sim.Ret
