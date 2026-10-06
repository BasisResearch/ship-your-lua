import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.Cond
import Lua.Vm.Sim.Kit.LstrcmpPro
import Lua.Vm.Sim.Kit.EqLong
import Lua.Vm.Sim.Kit.Objlen

/-!
# `docondjump` and the string call node on the location-list route (lane F1-2)

The test arms (`EQ`, `EQK`, `LT`, `LE`, …) end in `lvm.c`'s `docondjump`:
`updatetrap` (`lw t6, 40(s7)`), the `k` bit (`srliw 15; andi 1`) against the
test, then `pc += 2` or `donextjump` (the following `OP_JMP`'s `sJ`). Their
values have closed forms stated here once, as rules of `at_eq`'s extension
point `at_eq_ext` (`Kit/At.lean`), so `gen_lua_at.py` emits them as
locations over the context (`.lit <term over X>`):

* the `k` bit: `if X.ins.k then 1 else 0` (`kraw_eq`);
* the `trap` reload: `0` (`trap_ld`, `trap_sx`, `Core.trap` through the
  `Scratch` stores);
* `donextjump`'s target: `code + 4 * jmpPc X` (`jmp_at`, `nextjump_pc`);
* `l_strcmp`'s answer, observed by the instruction after the call (`slti 1`
  for `OP_LE`, `srliw 31` for `OP_LT`): `if ¬ lexLt b a then 1 else 0`
  (`obs_le`), `if lexLt a b then 1 else 0` (`obs_lt`), over the strings the
  registers hold (`sOf`). The call node is `lstr_sum` (`lstrcmp_sum` at the
  row, the strings live by `Core.str_at`) and the generated call lemma runs
  on through the observing segment (`at_lstr`); the return memory is
  `l_strcmp`'s six saves (`lsMem`), stores of the log.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.Kit
open Vsa.Machine (MState Config Steps StepsN)

/-! ## Values over the context -/

/-- The string register `f` holds (`[]` when it holds none). -/
def sOf (X : Cx) (f : Fld) : List UInt8 :=
  match X.s.regs (f.den X) with
  | some (.str s) => s
  | _ => []

theorem sOf_eq {X : Cx} {f : Fld} {j : Nat} {x : List UInt8} (h : X.s.regs j = some (.str x))
    (hj : f.den X = j) : sOf X f = x := by
  subst hj; simp [sOf, h]

/-- `sOf_eq`'s field side condition (after `at_facts`' field normal form). -/
macro "fld_eq" : tactic => `(tactic|
  simp only [Fld.den, Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow, Nat.add_zero])

/-- A register bound over the instruction's fields in either form. -/
macro "fld_omega" : tactic => `(tactic|
  (simp only [Fld.den, Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow] at *; omega))

/-- A `donextjump` lies before a `JMP`. -/
theorem jmp_lt {X : Cx} (hj : (nextJump X.p X.s.pc).isSome = true) : X.s.pc + 1 < X.p.code.length := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hj
  simp only [nextJump, Option.bind_eq_some_iff] at ht
  obtain ⟨ni, hni, _⟩ := ht
  exact fetch_lt hni

/-- `donextjump`'s target (`nextJump`; `0` when the kernel has none). -/
def jmpPc (X : Cx) : Nat := (nextJump X.p X.s.pc).getD 0

/-- The run's memory agrees with the entry memory outside `Scratch` (the
`savestate` stores, the callee frames below `sp`). -/
abbrev ScrFrame (X : Cx) (m : Mem) : Prop := ∀ a, ¬ Scratch X.w a → m[a]? = X.c.σ.mem[a]?

set_option hygiene false in
/-- `ScrFrame` of a log of `Scratch` stores (after `at_open`). -/
macro "at_scr" : tactic => `(tactic| (
  intro x hx
  simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget, not_or,
    not_and, Nat.not_lt] at hx
  simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]))

/-- The run's memory agrees with the entry memory outside `Scratch` and the
register slots (an arm's stores, a callee's frame and its stores of `R[A]`). -/
abbrev WinFrame (X : Cx) (m : Mem) : Prop :=
  ∀ a, ¬ Scratch X.w a → ¬ Slots X.p X.w a → m[a]? = X.c.σ.mem[a]?

set_option hygiene false in
/-- `WinFrame` of a log of `Scratch` and slot stores (after `at_open`). -/
macro "at_win" : tactic => `(tactic| (
  intro x hx hx'
  simp only [Scratch, Slots, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget, not_or,
    not_and, Nat.not_lt, stackValueSize] at hx hx'
  simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]))

/-! ## `updatetrap` -/

/-- `lw t6, 40(s7)`: `ci->u.l.trap`, read through `Scratch` stores. -/
theorem trap_ld {X : Cx} (hX : X.Ok) {m : Mem} (hm : WinFrame X m) {a : Nat} (ha : a = X.w.ci + 40) :
    sign_extend (m := 64) (bytesT4 m a : BitVec (8 * 4)) = 0#64 := by
  have hc := hX.core
  have hr := hc.ranges
  have := hr.L_sep_ci; have := hr.ci_top; have := hr.sp_eq; have := hr.L_lo; have := hr.ci_sep
  simp only [ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame, stackValueSize] at *
  have e : bytesT4 m a = 0 := by
    subst ha
    refine (bytesT4_congr fun i hi => hm _ (fun hs => ?_) fun hs => ?_).trans hc.trap
    · simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget] at hs
      omega
    · simp only [Slots, stackValueSize] at hs; omega
  rw [e]; decide

/-- `sext.w s5, t6` after the reload. -/
theorem trap_sx {X : Cx} (hX : X.Ok) {m : Mem} (hm : WinFrame X m) {a : Nat} (ha : a = X.w.ci + 40) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (bytesT4 m a : BitVec (8 * 4)))
      + sign_extend (m := 64) (0x000#12)) 31 0) = 0#64 := by
  rw [trap_ld hX hm ha]; decide

/-! ## `donextjump` -/

/-- **`donextjump`'s target**: the following `OP_JMP`'s `sJ`, read through
`Scratch` stores, relative to `pc + 2`. -/
theorem jmp_at {X : Cx} (hX : X.Ok) (hj : (nextJump X.p X.s.pc).isSome = true) {m : Mem} (hm : WinFrame X m)
    {a : Nat} (ha : a = X.w.code + 4 * (X.s.pc + 1)) :
    BitVec.ofNat 64 (X.w.code + 4 * (X.s.pc + 1)) + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) (bytesT4 m a : BitVec (8 * 4))) 31 0) (0x07#5)))
      + ((sign_extend (m := 64) ((0xff000#20) +++ 0x000#12)) + sign_extend (m := 64) (0x002#12)))
      (Sail.BitVec.extractLsb (0x02#6) 5 0) = BitVec.ofNat 64 (X.w.code + 4 * jmpPc X) := by
  have hc := hX.core
  have hr := hc.ranges
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hj
  have ht' := ht
  simp only [nextJump, Option.bind_eq_some_iff] at ht'
  obtain ⟨ni, hni, hjt⟩ := ht'
  have e : jmpPc X = t := by simp [jmpPc, ht]
  rw [e]
  have hlt1 := fetch_lt hni
  have hjt' := jumpTo_eq hjt
  have hsj : ni.sj < 2 ^ 25 := by
    simp only [Word.sj, Word.ax, Word.field, Word.offsetSJ]; have := ni.isLt; omega
  have := hr.code_hi
  have hw : bytesT4 m (X.w.code + 4 * (X.s.pc + 1)) = ni :=
    (bytesT4_congr fun i hi => hm _ (fun hs => hr.code_out _ (by omega) (by omega) (.inr (.inr hs)))
      fun hs => hr.code_out _ (by omega) (by omega) (.inl hs)).trans (hc.fetch hni)
  exact nextjump_pc ha hw hjt (by omega) (by omega)

/-! ## `l_strcmp`'s call node at a row -/

/-- **`l_strcmp` at a row**: two string registers' payloads in `a0`, `a1`;
the strings are live (`Core.str_at`) in any memory exact outside `Scratch`. -/
theorem lstr_sum {X : Cx} (hX : X.Ok) {m : Mem} (hm : ScrFrame X m) {ja jb : Nat}
    (hja : ja < X.p.maxstacksize) (hjb : jb < X.p.maxstacksize) {x y : List UInt8}
    (hx : X.s.regs ja = some (.str x)) (hy : X.s.regs jb = some (.str y)) (r : BitVec 64)
    (hra : r.toNat % 4 = 0) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x8001a704#64 (⟨Register.x10, slotVal X.c.σ.mem (X.w.slot ja)⟩ ::
        ⟨Register.x11, slotVal X.c.σ.mem (X.w.slot jb)⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x2, BitVec.ofNat 64 X.w.sp⟩ :: f.pins) (ArmPay m o))
      (LsRet r X.w.sp f m o x y) := by
  have hc := hX.core
  have hr := hc.ranges
  have hva := hc.stack ja _ hja hx
  have hvb := hc.stack jb _ hjb hy
  have hsp := hr.sp_eq
  simp only [RuntimeData.spEntry, execFrame] at hsp
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have ro : RodataRead m := fun o ho => by
    have := rodata_below_tohost
    have hb : ¬ Scratch X.w (Image.rodataBase + o) := by
      have := hr.ci_lo; have := hr.L_lo
      simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget]; omega
    simp only [bytesT1, hm _ hb]; exact hc.rodata o ho
  have a1 := hc.str_at hva hm; have a2 := hc.str_at hvb hm
  simp only [RuntimeData.spEntry, cStackBudget, execFrame] at a1 a2
  have h := lstrcmp_sum (slotVal X.c.σ.mem (X.w.slot ja)).toNat (slotVal X.c.σ.mem (X.w.slot jb)).toNat x y r
    X.w.sp f m o ⟨ro, hra, by omega, by omega, by omega, ⟨a1.view, a1.apart.mono (by omega) (by omega)⟩,
      ⟨a2.view, a2.apart.mono (by omega) (by omega)⟩⟩
  simp only [lstrPre, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- **`OP_LE`'s observation** (`slti a0, a0, 1`): `¬ (b < a)`. -/
theorem obs_le {X : Cx} {v : BitVec 64} {x y : List UInt8} (hv : LsObs v x y) (hx : sOf X .a = x)
    (hy : sOf X .b = y) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s v (sign_extend (m := 64) (0x001#12)))) =
      if !lexLt (sOf X .b) (sOf X .a) then 1#64 else 0#64 := by
  rw [hv.le, hx, hy]; cases lexLt y x <;> decide

/-- **`OP_LT`'s observation** (`srliw a0, a0, 31`): `a < b`. -/
theorem obs_lt {X : Cx} {v : BitVec 64} {x y : List UInt8} (hv : LsObs v x y) (hx : sOf X .a = x)
    (hy : sOf X .b = y) :
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) (0x1f#5)) =
      if lexLt (sOf X .a) (sOf X .b) then 1#64 else 0#64 := by
  rw [srliw31, hv.neg, hx, hy]

set_option hygiene false in
open Lean Elab Tactic Meta in
/-- **`at_lstr seg obs`**: a call lemma's proof (after `at_open`): the
call node `lstr_sum` at the row, then the observing segment `seg` (the
answer `v` as the location `obs` states, from `LsObs`), the return row and
memory (`lsMem`'s saves) by `at_pins`/`at_mem`. -/
elab "at_lstr " seg:ident obs:ident : tactic => do
  let nm ← realizeGlobalConstNoOverload seg
  let args ← withMainContext <| Tactic.runTermElab (atSegArgs nm)
  let segT ← `($(mkIdent nm) $args*)
  evalTactic (← `(tactic| (
    obtain ⟨_, acc, ⟨⟨v, h, hv⟩⟩⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
      (lstr_sum hX (by at_scr) (by omega) (by omega) hsa hsb _ (by decide)
        (Lua.Vm.Sim.KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _)
    have e := $obs hv (sOf_eq hsa (by fld_eq)) (sOf_eq hsb (by fld_eq))
    dsimp only [Lua.Vm.Sim.Kit.RetAt] at h
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h) $segT
    exact ⟨_, acc, (Vsa.Sim.SegSt.repin h (by at_pins h)).mem_eq (by simp only [Lua.Vm.Sim.Kit.lsMem]; at_mem)⟩)))

/-! ## `luaV_equalobj`'s long-string call node at a row (`OP_EQK`) -/

/-- The string constant `K[B]` (`[]` when it is none). -/
def kOf (X : Cx) : List UInt8 :=
  match kval X.p X.ins.b with
  | some (.str s) => s
  | _ => []

theorem kOf_eq {X : Cx} {y : List UInt8} (h : kval X.p X.ins.b = some (.str y)) : kOf X = y := by
  simp [kOf, h]

/-- **`luaV_equalobj(NULL, R[A], K[B])` on two long strings at a row**: the
answer `δ .eq`'s as 0/1, the memory the entry's with `ra` saved below `sp`
(`eqo_long_ex`). -/
theorem lngeq_sum {X : Cx} (hX : X.Ok) {ja jb : Nat} (hja : ja < X.p.maxstacksize) {x y : List UInt8}
    (hx : X.s.regs ja = some (.str x)) (hky : kval X.p jb = some (.str y))
    (hta : slotTag X.c.σ.mem (X.w.slot ja) = 84#8)
    (htk : slotTag X.c.σ.mem (X.w.k + stackValueSize * jb) = 84#8)
    (L r : BitVec 64) (hra : r.toNat % 4 = 0) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x8001b780#64 (eqPre L r (X.w.slot ja) (X.w.k + stackValueSize * jb) X.w.sp f)
        (ArmPay X.c.σ.mem o))
      (RetAt r (BitVec.ofNat 64 X.w.sp) f (writeMap8 X.c.σ.mem (X.w.sp - 8) (sdData_val r)) o
        (if x = y then 1#64 else 0#64)) := by
  have hc := hX.core
  have hr := hc.ranges
  have hva := hc.stack ja _ hja hx
  have hvk := hc.kconst hky
  have hkb := kval_lt hky
  have hsp := hr.sp_eq; have := hr.slots_top; have := hr.k_top; have := hr.base_lo; have := hr.k_lo
  simp only [RuntimeData.spEntry, cStackBudget, execFrame, stackValueSize, RelPtrs.slot] at *
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  obtain ⟨_, e1, hl1⟩ := (hta ▸ hva).long_of_tag
  obtain ⟨_, e2, hl2⟩ := (htk ▸ hvk).long_of_tag
  cases e1; cases e2
  exact eqo_long_ex L r _ _ X.w.sp f _ o
    ⟨hc.rodata, hra, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    hta htk hl1 hl2 (hc.lng_pair hva hvk fun _ _ => rfl)

set_option hygiene false in
/-- **`at_eqk`**: the `OP_EQK` call lemma's proof (after `at_open`): the call
node `lngeq_sum` at the row, the answer as the location over `sOf`/`kOf`, the
return row and memory (`ra`'s save) by `at_pins`/`at_mem`. -/
macro "at_eqk" : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (lngeq_sum hX (by omega) hsa hky hta htk _ _ (by decide) (Lua.Vm.Sim.KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _)
  have e : (if x = y then 1#64 else 0#64) = if sOf X .a = kOf X then 1#64 else 0#64 := by
    rw [sOf_eq hsa (by fld_eq), kOf_eq (by simpa only [Word.b, Word.field, Nat.shiftRight_eq_div_pow] using hky)]
  dsimp only [Lua.Vm.Sim.Kit.RetAt] at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
  · at_pins h
  · at_mem))

/-! ## `luaV_objlen`'s call node at a row (`OP_LEN` on a string) -/

/-- A register slot read through `Scratch` stores. -/
theorem slot_scr {X : Cx} (hX : X.Ok) {m : Mem} (hm : ScrFrame X m) {j : Nat} (hj : j < X.p.maxstacksize) :
    slotTag m (X.w.slot j) = slotTag X.c.σ.mem (X.w.slot j) ∧
      slotVal m (X.w.slot j) = slotVal X.c.σ.mem (X.w.slot j) := by
  have hr := hX.core.ranges
  have := hr.ci_sep; have := hr.L_sep; have := hr.slots_top; have := hr.ci_top; have := hr.L_top
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget] at *
  have hs : ∀ i, i < 16 → ¬ Scratch X.w (X.w.slot j + i) := fun i hi h => by
    simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget, RelPtrs.slot,
      stackValueSize] at h
    omega
  refine ⟨?_, bytesT8_congr fun i hi => ?_⟩
  · simp only [slotTag, bytesT1, tvalueTagOff, hm _ (hs 8 (by omega))]
  · simp only [tvalueValOff, Nat.add_zero]; exact hm _ (hs i (by omega))

/-- **`luaV_objlen(L, R[A], R[B])` on a string at a row**: the integer `#y`
stored in `R[A]`, the memory `olMem` (`objlen_sum`). -/
theorem len_sum {X : Cx} (hX : X.Ok) {m : Mem} (hm : ScrFrame X m) {ja jb : Nat}
    (hja : ja < X.p.maxstacksize) (hjb : jb < X.p.maxstacksize) {y : List UInt8}
    (hy : X.s.regs jb = some (.str y)) (L r : BitVec 64) (hra : r.toNat % 4 = 0) (f : KFrame)
    (o : Array String) :
    Triple (SegSt 0x8001bae0#64 (olPre L r (X.w.slot ja) (X.w.slot jb) X.w.sp f) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 X.w.sp⟩ :: f.pins) (ArmPay (olMem m (X.w.slot ja) X.w.sp r y.length) o)) := by
  have hc := hX.core
  have hr := hc.ranges
  have hvb := hc.stack jb _ hjb hy
  have ⟨et, ev⟩ := slot_scr hX hm hjb
  have a2 := hc.str_at hvb hm
  have hsp := hr.sp_eq; have := hr.slots_top; have := hr.base_lo; have := hr.base_al
  simp only [RuntimeData.spEntry, cStackBudget, execFrame, stackValueSize, RelPtrs.slot] at *
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  exact objlen_sum L r _ _ X.w.sp f m o _ y
    ⟨hra, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      et.trans hvb.tag_eq, ev.trans (bv_ofNat_toNat _).symm, a2.view, a2.apart.mono (by omega) (by omega)⟩

set_option hygiene false in
/-- **`at_objlen`**: the `OP_LEN` call lemma's proof (after `at_open`): the
call node `len_sum` at the row, the length as the location over `sOf`, the
return row and memory (`olMem`) by `at_pins`/`at_mem`. -/
macro "at_objlen" : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
    (len_sum hX (by at_scr) (by fld_omega) (by fld_omega) hsb _ _ (by decide)
      (Lua.Vm.Sim.KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _)
  rw [← sOf_eq (f := .b) hsb (by fld_eq)] at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
  · at_pins h
  · simp only [Lua.Vm.Sim.Kit.olMem]; at_mem))

/-! ## The rules -/

open Lean Elab Tactic Meta in
/-- `at_eq_ext`'s rules, each tried only on its goal's shape (a cheap
syntactic test first: a failed `exact` would unify through `sign_extend`). -/
elab "at_eq_cond" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, r) := t.eq? | throwError "at_eq_cond: not an equation"
  let has (e : Expr) (n : Name) : Bool := (e.find? fun x => x.isConstOf n).isSome
  let tacs : Array (TSyntax `tactic) ←
    if has r ``lexLt || has r ``kOf then pure #[← `(tactic| with_reducible assumption)]
    else if l.isAppOf ``HAnd.hAnd && r.isAppOf ``ite then pure #[← `(tactic| exact kraw_eq _)]
    else if has r ``jmpPc then
      pure #[← `(tactic| exact jmp_at $(mkIdent `hX) (by assumption) (by at_win) (by kit_disch))]
    else if has l ``bytesT4 && has l ``sign_extend then
      -- `sext (lw …)` itself, or `sext.w` of it (`extractLsb`)
      if has l ``Sail.BitVec.extractLsb then
        pure #[← `(tactic| exact trap_sx $(mkIdent `hX) (by at_win) (by kit_disch))]
      else pure #[← `(tactic| exact trap_ld $(mkIdent `hX) (by at_win) (by kit_disch))]
    else throwError "at_eq_cond: no rule"
  for tac in tacs do
    let s ← saveState
    try
      evalTactic tac
      return
    catch _ => s.restore
  throwError "at_eq_cond: no rule closes"

macro_rules | `(tactic| at_eq_ext) => `(tactic| at_eq_cond)

set_option hygiene false in
macro_rules
  | `(tactic| at_pc_ext) => `(tactic| (simp only [jmpPc]; rw [hnj]; rfl))

end Lua.Vm.Sim.At
