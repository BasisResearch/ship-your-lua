import Lua.Vm.Sim.Kit.At
import Lua.Vm.Sim.Kit.AtFAttr
import Lua.Vm.Sim.Kit.Clzdi2
import Lua.Vm.Fn.Spec
import Lua.Vm.Fn.Floor
import Lua.Vm.Fn.Muldf3
import Lua.Vm.Fn.Divdf3

/-!
# The soft-float call nodes on the location-list route (lane float-m0, M1)

A float path of an arm calls libgcc's soft-float routines; their summaries
are `scripts/gen_lua_fn.py`'s (`Lua/Vm/Fn/*`, `sum`), keyed by entry pc. The
generated call at-lemmas (`scripts/gen_lua_at.py` `FCALLS`) apply them at
the row (`at_call`) with what this file supplies once:

* `at_fnSp`: the stack facts a framed helper's frame below `luaV_execute`'s
  `sp` needs (`FnSp`, from `Ranges.sp_eq`);
* `at_rod`: `.rodata` (`__clz_tab`) read through the path's stores
  (`Core.rodata` and the stores' addresses above the HTIF mailbox);
* `at_fsite_eq` (an `at_eq` extension): a call site's result `f<k> X` (or
  memory `k<k> X M`) against the summary's, by unfolding the site once
  (`at_fsite_delta`) and comparing the lifted function's arguments
  (`fn_congr*`), never the lifted function itself.

The call's result is the location `.fn f<k>`; a framed helper's frame is the
log entry `Ent.clob` with content `k<k>` (`memPatch`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout

/-- **A frame of up to 112 bytes below `luaV_execute`'s `sp`** (`FnSp`). -/
theorem at_fnSp {X : Cx} {F : Nat} (hX : X.Ok) (hF : F ≤ 112 := by decide) : FnSp X.w.sp F := by
  have := hX.core.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry] at this
  exact ⟨by have : tohostAddr = 0x8005c6c0 := rfl; omega, by omega, by omega⟩

/-- `.rodata` survives a byte store above the HTIF mailbox. -/
theorem RodataRead.ins {m : Mem} (h : RodataRead m) {a : Nat} {b : BitVec 8} (ha : tohostAddr ≤ a) :
    RodataRead (m.insert a b) := fun o ho => by
  have := Lua.Vm.Sim.rodata_below_tohost
  simp only [bytesT1, getElem?_insert_out (show Image.rodataBase + o ≠ a by omega)]
  exact h o ho

set_option hygiene false in
/-- **`.rodata` through the path's stores** (`Core.rodata` at the entry). -/
macro "at_rod" : tactic => `(tactic| (
  repeat (first
    | exact hc.rodata
    | (refine RodataRead.wm8 ?_ (by kit_disch))
    | (refine RodataRead.ins ?_ (by kit_disch))
    | (refine RodataRead.patch ?_ (by kit_disch)))))

theorem fn_congr2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := by subst ha hb; rfl

theorem fn_congr4 {α β γ δ ε : Type} (f : α → β → γ → δ → ε) {a a' : α} {b b' : β} {c c' : γ}
    {d d' : δ} (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') : f a b c d = f a' b' c' d' := by
  subst ha hb hc hd; rfl

theorem fn_congr5 {α β γ δ ε ζ : Type} (f : α → β → γ → δ → ε → ζ) {a a' : α} {b b' : β} {c c' : γ}
    {d d' : δ} {e e' : ε} (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e') :
    f a b c d e = f a' b' c' d' e' := by
  subst ha hb hc hd he; rfl

theorem fn_congr1 {α β : Type} (f : α → β) {a a' : α} (ha : a = a') : f a = f a' := by subst ha; rfl

theorem fn_congr6 {α β γ δ ε ζ η : Type} (f : α → β → γ → δ → ε → ζ → η) {a a' : α} {b b' : β}
    {c c' : γ} {d d' : δ} {e e' : ε} {z z' : ζ} (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d')
    (he : e = e') (hz : z = z') : f a b c d e z = f a' b' c' d' e' z' := by
  subst ha hb hc hd he hz; rfl

/-! ## A frame that stores the caller's saved registers (lane F1-F6) -/

/-- The caller's frame reduced to the registers a routine's memory stores
(`s0`–`s3`: `__divdf3`'s mid-body saves); the other fields are `0`. -/
def frame4 (s0 s1 s2 s3 : BitVec 64) : SFrame := ⟨0, s0, s1, s2, s3, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `__divdf3`'s frame reads only `s0`–`s3` of the caller's frame (the
lifted memory passes `g` through and stores `g.s0 … g.s3`): definitional. -/
theorem divdf3_Fm_frame4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (a b : BitVec 64) :
    Lua.Vm.Fn.Divdf3.Fm m s r g a b = Lua.Vm.Fn.Divdf3.Fm m s r (frame4 g.s0 g.s1 g.s2 g.s3) a b :=
  rfl

/-- **`__divdf3`'s summary with its frame over `frame4`** (`Divdf3.sum`):
the call node's memory `k<k>` is then a function of the row (`gen_lua_at.py`
`FRAME_G`), whatever the registers the caller leaves dead. -/
theorem divdf3_sumG (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 v11 : BitVec 64)
    (hs : FnSp s 112) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002de30#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Vm.Fn.Divdf3.F m s r v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Lua.Vm.Fn.Divdf3.Fm m s r (frame4 g.s0 g.s1 g.s2 g.s3) v10 v11) (s - 112) 112) o)) := by
  rw [← divdf3_Fm_frame4]
  exact Lua.Vm.Fn.Divdf3.sum m o s r g v10 v11 hs hr hrod

open Lean Elab Tactic Meta in
/-- A call site's definition (`Lua.Vm.At.<OP>.f<k>`, `….k<k>`). -/
def isFsite (n : Name) : Bool :=
  match n with
  | .str p s =>
    (`Lua.Vm.At).isPrefixOf p && s.length ≥ 2 && (s.front == 'f' || s.front == 'k') &&
      (s.drop 1).all Char.isDigit
  | _ => false

open Lean Elab Tactic Meta in
/-- **The call sites of the goal unfolded once** (a definitional step: no
equation lemma, whose generation would unfold the lifted function). -/
elab "at_fsite_delta" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (ty, l, r) := t.eq? | throwError "at_fsite_delta: not an equation"
  -- only a side's head: the sites inside the arguments stay folded
  let unfoldHead (e : Expr) : MetaM (Option Expr) := do
    let f := e.getAppFn
    unless f.isConst && isFsite f.constName! do return none
    return some (← deltaExpand e (· == f.constName!)).headBeta
  let l' ← unfoldHead l
  let r' ← unfoldHead r
  if l'.isNone && r'.isNone then throwError "at_fsite_delta: no call site at the head"
  let t' ← mkEq (l'.getD l) (r'.getD r)
  let _ := ty
  replaceMainGoal [← (← getMainGoal).replaceTargetDefEq t']

/-- **A call site's result or memory against the summary's** (`at_eq`'s
extension in a float arm): the site unfolded once (`at_fsite_delta`), then
the lifted function's arguments compared (each by `at_unfold` and `at_eq` or
`at_mem`). -/
macro "at_fsite_eq" : tactic => `(tactic| (
  at_fsite_delta
  first
    | (refine fn_congr6 _ ?_ ?_ ?_ ?_ ?_ ?_)
    | (refine fn_congr5 _ ?_ ?_ ?_ ?_ ?_)
    | (refine fn_congr4 _ ?_ ?_ ?_ ?_)
    | (refine fn_congr2 _ ?_ ?_)
    | (refine fn_congr1 _ ?_)
  all_goals first
    | with_reducible rfl
    | (at_unfold <;> first | with_reducible rfl | at_mem | at_eq)))

macro_rules | `(tactic| at_eq_ext) => `(tactic| at_fsite_eq)

/-- `__floatsidf`'s argument at a call site is canonical: a 32-bit result
(`addw`, `addiw`) sign-extended (`Lua.Vm.Fn.sext32_canon`). -/
macro "at_sext" : tactic => `(tactic|
  first | exact Lua.Vm.Fn.sext32_canon _ | (simp only [Loc.den]; exact Lua.Vm.Fn.sext32_canon _))

/-! ## `.rodata` constants (`auipc`; `ld`) -/

open Lean Elab Tactic Meta in
/-- **`at_ground`**: a ground address an `auipc` computes (`pc + (hi +++ 0)
+ lo`, a `.rodata` constant's) evaluated to its literal, by one `decide`;
fails when there is none. -/
elab "at_ground" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let cands := collectE (fun e => !e.hasFVar && !e.hasMVar && e.isAppOfArity ``HAdd.hAdd 6 &&
    (e.find? fun x => x.isAppOf ``HAppend.hAppend).isSome) t
  let some e := cands[0]? | throwError "at_ground: no ground address"
  let n ← unsafe evalExpr Nat (mkConst ``Nat) (← mkAppM ``BitVec.toNat #[e])
  let lit := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)
  let some pf ← proveBy (← mkEq e lit) (← `(tactic| decide)) | throwError "at_ground: {e}"
  let g ← getMainGoal
  let r ← g.rewrite (← g.getType) pf
  replaceMainGoal ((← g.replaceTargetEq r.eNew r.eqProof) :: r.mvarIds)

/-- The address normaliser on a `.rodata` constant's address. -/
macro_rules | `(tactic| at_addr) => `(tactic| (at_ground; at_addr))

/-- A load of a `.rodata` constant (`at_eq`): its address evaluated first. -/
macro_rules | `(tactic| at_eq_ext) => `(tactic| (at_ground; at_eq))

end Lua.Vm.Sim.At
