import Lua.Vm.Sim.Dispatch
import Lua.Vm.Sim.Close

/-!
# The KIT's machine runner (round-3 bake-off, contender KIT)

The arm proofs of the direct kit are written by hand; what they do not write
is the chaining of the generated `SegSt` segments (`Lua.Vm.Arms.seg_*`,
`scripts/gen_lua_arms.py`). This file supplies it once:

* `SegSt.run`: continue a run from a segment state through a segment whose
  pins are found in the current state (`pins_from`: every register of the
  segment's entry list is looked up by name in the current pin list, which
  also instantiates the segment's value parameters);
* `kit_run h acc`: from `h : SegSt pc L P c` (and `acc : Steps c₀ c`), run
  the generated segments that start at `pc`, choosing among a branch's two
  polarities by which one's side conditions `kit_side` discharges, until the
  fetch head `Lua.Vm.Arms.headPc` or a `stop` pc (a call node, M5) is reached.
  It picks the segment theorem by its name `seg_<pc>_<hi>[_t|_n]`, fills
  every value parameter with `_`, and every side condition with
  `(by kit_side)`: no per-arm glue is written.

`kit_side` is extensible (`macro_rules`): address side conditions
(`slot_arith`), and branch guards discharged from the arm's facts in context
(`kit_guard`: a guard lemma of `Lua/Vm/Sim/Close.lean` applied to each
hypothesis about a slot tag or a register's value representation, M2).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- Continue a run through a segment whose entry pins hold in the current
state. -/
theorem _root_.Vsa.Sim.SegSt.run {pc : BitVec 64} {L L' : List Pin} {P : MState → Prop}
    {c₀ c : Config} {Q : Config → Prop} (acc : Steps c₀ c) (h : SegSt pc L P c)
    (hL : PinsHold c.σ L') (seg : Triple (SegSt pc L' P) Q) : ∃ c', Steps c₀ c' ∧ Q c' :=
  let ⟨c', hs, hq⟩ := seg c ⟨h.good, h.pcAt, hL, h.minstret, h.tick, h.extra⟩
  ⟨c', acc.trans hs, hq⟩

/-- The fetch-head registers after dispatch (the segments' `KEEP` list). -/
def armPins (w : RelPtrs) (pc : Nat) (ins : Word) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 w.L⟩, ⟨Register.x9, BitVec.ofNat 64 (Arms.jtEntries - 1)⟩,
   ⟨Register.x18, BitVec.ofNat 64 vNumInt⟩,
   ⟨Register.x19, BitVec.ofNat 64 (w.code + 4 * (pc + 1))⟩,
   ⟨Register.x20, sign_extend (m := 64) ins⟩, ⟨Register.x21, 0#64⟩,
   ⟨Register.x23, BitVec.ofNat 64 w.ci⟩, ⟨Register.x24, BitVec.ofNat 64 Arms.jtBase⟩,
   ⟨Register.x25, BitVec.ofNat 64 w.base⟩, ⟨Register.x27, BitVec.ofNat 64 (w.code + 4 * pc)⟩]

/-- **The caller's frame across a helper call**: the fetch-head registers and
the arm temporaries `s6`, `s10` (the helper segments' carried pins,
`scripts/gen_lua_arms.py` `HELPERS`). -/
structure HFrame where
  (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64)

/-- The frame as pins. -/
def HFrame.pins (f : HFrame) : List Pin :=
  [⟨Register.x2, f.sp⟩, ⟨Register.x3, f.gp⟩, ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩,
   ⟨Register.x18, f.s2⟩, ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩,
   ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩,
   ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- The shift amount of `srli`/`slli … 1`. -/
abbrev sh1 : BitVec 6 := Sail.BitVec.extractLsb (0x01#6) 5 0

/-- A frame to be read off a call site's pins (`pins_of`). -/
macro "hframe?" : term => `(HFrame.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **The call rule (M5)**: at a helper's entry, run its summary `sum` (a
`Triple` from the entry pins to the return address), the pins found in the
current state. -/
theorem _root_.Vsa.Sim.SegSt.call {pc : BitVec 64} {L L' : List Pin} {P : MState → Prop}
    {c₀ c : Config} {Q : Config → Prop} (acc : Steps c₀ c) (h : SegSt pc L P c)
    (hL : PinsHold c.σ L') (sum : Triple (SegSt pc L' P) Q) : ∃ c', Steps c₀ c' ∧ Q c' :=
  h.run acc hL sum

/-- The fetch-head registers but `sp` (what `luaV_equalobj` keeps). -/
structure KFrame where
  (gp s0 s1 s2 s3 s4 s5 s7 s8 s9 s11 : BitVec 64)

def KFrame.pins (f : KFrame) : List Pin :=
  [⟨Register.x3, f.gp⟩, ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x18, f.s2⟩,
   ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x27, f.s11⟩]

/-- Re-pin a segment state (its pins looked up elsewhere). -/
theorem _root_.Vsa.Sim.SegSt.repin {pc : BitVec 64} {L L' : List Pin} {P : MState → Prop}
    {c : Config} (h : SegSt pc L P c) (hL : PinsHold c.σ L') : SegSt pc L' P c :=
  ⟨h.good, h.pcAt, hL, h.minstret, h.tick, h.extra⟩

/-- A segment state at a pc shown equal to another. -/
theorem _root_.Vsa.Sim.SegSt.at {pc pc' : BitVec 64} {L : List Pin} {P : MState → Prop}
    {c : Config} (h : SegSt pc L P c) (e : pc = pc') : SegSt pc' L P c := e ▸ h

/-- `addi sp, sp, -48` (`luaV_equalobj`'s frame). -/
theorem add_imm_m48 (n : Nat) :
    BitVec.ofNat 64 n + sign_extend (m := 64) (0xfd0#12) = BitVec.ofNat 64 (n + (2^64 - 48)) := by
  rw [show sign_extend (m := 64) (0xfd0#12) = BitVec.ofNat 64 (2^64 - 48) by decide,
    BitVec.ofNat_add_ofNat]

/-- `addi rd, rs, -k` (a negative 12-bit immediate, `0x800 ≤ k`): any
callee frame (`addi sp, sp, -80`, …). -/
theorem add_imm_neg (n k : Nat) (hk : 2048 ≤ k) (hk2 : k < 4096) :
    BitVec.ofNat 64 n + sign_extend (m := 64) (BitVec.ofNat 12 k) =
      BitVec.ofNat 64 (n + (2^64 - (4096 - k))) := by
  rw [show sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (2^64 - (4096 - k)) by
    apply BitVec.eq_of_toNat_eq
    simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat]
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
    rw [if_pos (by simp; omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega,
    BitVec.ofNat_add_ofNat]

/-- `slot_arith` as a `simp` discharger: one goal, and a failure is a failure
(no `all_goals`, whose error recovery would admit the goal). -/
macro "kit_disch" : tactic => `(tactic| (
  try simp (config := { decide := true }) only [extract_sext, field8, sext_shr, add_imm, shl_ofNat,
    add_imm_m48, add_imm_neg, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.add_zero, RelPtrs.slot,
    stackValueSize, Word.a, Word.b, Word.c, Word.bx, Word.field, ciTrapOff, and255,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  try simp (disch := omega) only [Nat.mod_eq_of_lt]
  first | done | omega))

/-- The bound of a pin's position. -/
macro "pin_len" : tactic =>
  `(tactic| (simp only [armPins, HFrame.pins, KFrame.pins, List.length_cons, List.length_nil]; omega))

/-- A register's pin, by name, from a pin list (the first 26 positions). -/
macro "pin_at " h:term : tactic => `(tactic| first
  | exact pinsHold_get $h 0 (by pin_len) | exact pinsHold_get $h 1 (by pin_len)
  | exact pinsHold_get $h 2 (by pin_len) | exact pinsHold_get $h 3 (by pin_len)
  | exact pinsHold_get $h 4 (by pin_len) | exact pinsHold_get $h 5 (by pin_len)
  | exact pinsHold_get $h 6 (by pin_len) | exact pinsHold_get $h 7 (by pin_len)
  | exact pinsHold_get $h 8 (by pin_len) | exact pinsHold_get $h 9 (by pin_len)
  | exact pinsHold_get $h 10 (by pin_len) | exact pinsHold_get $h 11 (by pin_len)
  | exact pinsHold_get $h 12 (by pin_len) | exact pinsHold_get $h 13 (by pin_len)
  | exact pinsHold_get $h 14 (by pin_len) | exact pinsHold_get $h 15 (by pin_len)
  | exact pinsHold_get $h 16 (by pin_len) | exact pinsHold_get $h 17 (by pin_len)
  | exact pinsHold_get $h 18 (by pin_len) | exact pinsHold_get $h 19 (by pin_len)
  | exact pinsHold_get $h 20 (by pin_len) | exact pinsHold_get $h 21 (by pin_len)
  | exact pinsHold_get $h 22 (by pin_len) | exact pinsHold_get $h 23 (by pin_len)
  | exact pinsHold_get $h 24 (by pin_len) | exact pinsHold_get $h 25 (by pin_len))

/-- A pin list, every register looked up by name in `h`. -/
macro "pins_from " h:term : tactic => `(tactic| (
  repeat' (first | exact (trivial : True) | refine ⟨?_, ?_⟩ | pin_at $h)))

/-- A pin's value shown equal to the one a segment or summary expects. -/
syntax "kit_val" : tactic
macro_rules | `(tactic| kit_val) => `(tactic| first
  | rfl
  | (simp only [List.getElem_cons_succ, List.getElem_cons_zero]
     simp (disch := decide) only [slot_addr]
     simp only [RelPtrs.slot, Word.a, Word.b, Word.c, Word.field, stackValueSize]))

open Lean Elab Tactic Meta in
/-- The elements of a list literal. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match_expr e with
  | List.cons _ a t => return #[a] ++ (← listElems t)
  | List.nil _ => return #[]
  | _ =>
    let e' ← whnfD e
    if e' == e then throwError "not a list literal: {e}" else listElems e'

open Lean Elab Tactic Meta in
/-- **`pins_of h`**: the goal's pin list, each register found by name in the
pin list of the segment state `h` (the index computed here, so each pin is
one `pinsHold_get`). -/
elab "pins_of " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "pins_of: no {h}"
  let src ← listElems ((← instantiateMVars ld.type).getAppArgs[1]!)
  let tgt ← instantiateMVars (← getMainTarget)
  let dst ← listElems tgt.getAppArgs[1]!
  let reg (p : Expr) : Expr := p.getAppArgs[2]!
  let mut parts : Array Term := #[]
  for q in dst do
    let some i := src.findIdx? (fun p => reg p == reg q)
      | throwError "pins_of: register {reg q} not pinned in {h}"
    -- an unknown value is the pin's own expression (not its whnf)
    let qv ← whnfR q.getAppArgs[3]!
    let pv ← whnfR src[i]!.getAppArgs[3]!
    if (← withReducible (isDefEq qv pv)) || (← isDefEq qv pv) then
      parts := parts.push (← `(pinsHold_get ($h).pins $(quote i) (by pin_len)))
    else
      -- a value in another normal form (an address as `slot`): `kit_val`
      parts := parts.push (← `(pin_eq (pinsHold_get ($h).pins $(quote i) (by pin_len)) (by kit_val)))
  parts := parts.push (← `(trivial))
  evalTactic (← `(tactic| exact ⟨$parts,*⟩))

open Lean Elab Tactic Meta in
/-- **`pin_of h`**: a goal `σ.regs.get? R = some _` from the pin of `R` in
the segment state `h`. -/
elab "pin_of " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "pin_of: no {h}"
  let src ← listElems ((← instantiateMVars ld.type).getAppArgs[1]!)
  let tgt ← instantiateMVars (← getMainTarget)
  let some lhs := (match_expr tgt with | Eq _ l _ => some l | _ => none)
    | throwError "pin_of: not an equation"
  let some i := src.findIdx? (fun p => (lhs.find? (· == p.getAppArgs[2]!)).isSome)
    | throwError "pin_of: no pin for {lhs}"
  -- an unknown value is the pin's own (not the list projection `L[i].2`)
  match_expr tgt with
  | Eq _ _ r => discard <| isDefEq r.appArg! src[i]!.getAppArgs[3]!
  | _ => pure ()
  evalTactic (← `(tactic| exact pinsHold_get ($h).pins $(quote i) (by pin_len)))

/-- The arm's normaliser of a segment state's pins after each step (extended
by `macro_rules`, e.g. a register's payload read back as `slotVal`). -/
syntax "kit_norm " ident : tactic
macro_rules | `(tactic| kit_norm $_h) => `(tactic| fail "no normaliser")

/-- An arm-specific guard closer, tried before the generic ones (extended by
`macro_rules`). -/
syntax "kit_guard_ext" : tactic
macro_rules | `(tactic| kit_guard_ext) => `(tactic| fail "no extension")

open Lean Elab Tactic Meta in
/-- The guard lemmas that apply to a hypothesis, by its shape: a slot's tag
equal to, or different from, a constant, or a register's representation
(never a float tag). -/
def guardLemmas (t : Expr) : MetaM (List Name) := do
  let t ← instantiateMVars t
  if t.isAppOf ``Lua.Vm.Sim.ValRepr then return [``guard_not_float, ``guard_not_float_f]
  match_expr t with
  | Eq _ l _ => return if l.isAppOf ``slotTag then [``guard_tag_eq, ``guard_tag_bne_f] else []
  | Not e =>
    match_expr e with
    | Eq _ l _ => return if l.isAppOf ``slotTag then [``guard_tag_ne, ``guard_tag_bne_t] else []
    | _ => return []
  | _ => return []

open Lean Elab Tactic Meta in
/-- **`kit_guard`**: a branch guard of a generated segment, from a fact in
context about a slot's tag or a register's representation (M2): the guard
lemma fitting each such hypothesis, the address equation by `slot_arith`. -/
elab "kit_guard" : tactic => withMainContext do
  -- a tag read through `Scratch` stores is the entry memory's
  withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
    try simp (disch := kit_disch) only [bytesT1_writeMap8_out]))
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let hyp := mkIdent ldecl.userName
    for l in ← guardLemmas ldecl.type do
      let s ← saveState
      try
        withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
          (apply $(mkIdent l) (h := $hyp) <;> first | decide | kit_disch)))
        if (← getUnsolvedGoals).isEmpty then return
        s.restore
      catch _ => s.restore
  throwError "kit_guard: no guard lemma applies"

open Lean in
/-- An address-range fact: a linear (dis)equation or order over `Nat`, or a
disjunction of them. -/
partial def natFact (t : Expr) : Bool :=
  match t.getAppFnArgs with
  | (``LE.le, #[ty, _, _, _]) | (``LT.lt, #[ty, _, _, _]) | (``Eq, #[ty, _, _])
  | (``Ne, #[ty, _, _]) => ty.isConstOf ``Nat
  | (``Or, #[a, b]) | (``And, #[a, b]) => natFact a && natFact b
  | (``Not, #[a]) => natFact a
  | _ => false

/-- The value facts `kit_bv` may use: small equations and disequations. -/
syntax "kit_bv_norm" : tactic
macro_rules | `(tactic| kit_bv_norm) => `(tactic| fail "no normaliser")

open Lean Elab Tactic Meta in
/-- **`kit_bv`**: a value guard (a helper's loop test, a sign test) from one
small fact in context, after the arm's normaliser `kit_bv_norm`. -/
elab "kit_bv" : tactic => withMainContext do
  let s0 ← saveState
  try withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| kit_bv_norm))
  catch _ => do s0.restore; throwError "kit_bv: no normaliser in scope"
  -- the normaliser may close a ground guard by itself
  if (← getUnsolvedGoals).isEmpty then return
  let s1 ← saveState
  try
    withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| (simp; done)))
    return
  catch _ => s1.restore
  let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail || ldecl.userName.hasMacroScopes then continue
    let t ← instantiateMVars ldecl.type
    unless ← Meta.isProp t do continue
    if t.getAppFn.isConst && [``Vsa.Sim.SegSt, ``Vsa.Machine.Steps, ``Lua.Vm.Sim.ArmAt, ``Lua.Vm.Sim.Core,
        ``Lua.Vm.Sim.Ranges, ``Lua.Bytecode.Step].contains t.getAppFn.constName! then continue
    -- a value fact, not an address-range fact over `Nat`
    if natFact t then continue
    facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent ldecl.userName):term))
  -- one `simp` with every value fact
  let s ← saveState
  try
    withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
      first | (simp only [$facts,*]; first | done | decide) | (simp [$facts,*]; done)))
  catch e => do
    s.restore
    throwError "kit_bv: no fact closes the side condition: {e.toMessageData}"

open Lean Elab Tactic Meta in
/-- **`kit_side`**: a side condition of a generated segment. A boolean
equation is a branch guard (`kit_guard_ext`, then `kit_guard`); anything
else is address arithmetic (`slot_arith`). -/
elab "kit_side" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isGuard := match_expr t with
    | Eq ty _ _ => ty.isConstOf ``Bool
    | _ => false
  if isGuard then
    withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| first | kit_guard_ext | kit_guard | kit_bv))
  else
    withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| first | kit_guard_ext | kit_disch | kit_bv))

open Lean Elab Tactic Meta

/-- Eight hex digits. -/
def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) '0') ++ s

/-- The generated segment theorems that start at `lo`. -/
def segCands (env : Environment) (lo : Nat) : List Name := Id.run do
  let mut out := []
  for k in [0:512] do
    let hi := lo + 4 * (k + 1)
    for suf in ["", "_t", "_n"] do
      let n := Name.mkStr (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "Lua") "Vm") "Arms")
        s!"seg_{hex8 lo}_{hex8 hi}{suf}"
      if env.contains n then out := out ++ [n]
  return out

/-- The argument syntax of a segment theorem: `_` for its values, memory and
console, `(by kit_side)` for each side condition. -/
def segArgs (n : Name) : TermElabM (Array Term) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut args := #[]
    for x in xs do
      let t ← inferType x
      if ← Meta.isProp t then args := args.push (← `((by kit_side)))
      else args := args.push (← `(_))
    return args

/-- The pc of a `SegSt` hypothesis, if a literal. -/
def segPc (ty : Expr) : MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``Vsa.Sim.SegSt 4 do return none
  match ← getBitVecValue? ty.getAppArgs[0]! with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- The branch guards (`hg_*`) of segment `n`, instantiated at the segment
state `hty`'s pins and payload, all discharged by `kit_side`: a cheap
pre-check that rejects the wrong polarity of a branch before the segment is
elaborated. -/
def guardsHold (hty : Expr) (n : Name) : TacticM Bool := withoutModifyingState do
  let ci ← getConstInfo n
  let names := ci.type.getForallBinderNames
  let (xs, _, body) ← forallMetaTelescope ci.type
  let pre := body.getAppArgs[0]!
  let src ← listElems hty.getAppArgs[1]!
  for q in ← listElems pre.getAppArgs[1]! do
    if let some p := src.find? (fun p => p.getAppArgs[2]! == q.getAppArgs[2]!) then
      discard <| isDefEq (← whnfR q.getAppArgs[3]!) (← whnfR p.getAppArgs[3]!)
  unless ← isDefEq pre.getAppArgs[2]! hty.getAppArgs[2]! do return true
  for x in xs, nm in names do
    unless nm.toString.startsWith "hg" do continue
    let ty ← instantiateMVars (← inferType x)
    if ty.hasExprMVar then return true
    let g ← mkFreshExprMVar ty
    try
      let gs ← withoutRecover <| Term.withoutErrToSorry <|
        Tactic.run g.mvarId! (evalTactic (← `(tactic| kit_side)))
      unless gs.isEmpty do return false
    catch _ => return false
  return true

/-- One run step: the first candidate segment at the current pc whose pins
and side conditions hold. -/
def kitStep (h acc : Ident) (lo : Nat) : TacticM Bool := do
  let cands := segCands (← getEnv) lo
  let mut errs : Array MessageData := #[]
  let hty ← withMainContext do
    let some ld := (← getLCtx).findFromUserName? h.getId | throwError "kit_run: no {h}"
    instantiateMVars ld.type
  for n in cands do
    if cands.length > 1 then
      unless ← withMainContext (guardsHold hty n) do
        errs := errs.push m!"{n}: a guard fails"
        continue
    let s ← saveState
    try
      let args ← Tactic.runTermElab (segArgs n)
      let seg ← `($(mkIdent n) $args*)
      withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
        obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (by pins_of $h) $seg))
      withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| try kit_norm $h))
      return true
    catch e =>
      errs := errs.push m!"{n}: {e.toMessageData}"
      s.restore
  if cands.isEmpty then return false
  throwError "kit_run: no segment at 0x{hex8 lo} applies:{indentD (MessageData.joinSep errs.toList "\n")}"

/-- **`kit_run h acc [stops]`**: run the generated segments from `h` until
the fetch head or one of the `stops` pcs. -/
syntax "kit_run " ident ident (" until " "[" num,* "]")? : tactic

elab_rules : tactic
  | `(tactic| kit_run $h:ident $acc:ident $[until [$ns,*]]?) => do
  let stopPcs : List Nat := match ns with
    | some ns => ns.getElems.toList.map (·.getNat)
    | none => []
  let head := 0x8001bfe4
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let pc ← withMainContext do
      let some ldecl := (← getLCtx).findFromUserName? h.getId
        | throwError "kit_run: no hypothesis {h}"
      segPc ldecl.type
    let some pc := pc | return    -- a computed pc (a return): the caller continues
    if pc == head || (fuel < 63 && stopPcs.contains pc) then return
    unless ← kitStep h acc pc do
      throwError "kit_run: no segment starts at 0x{hex8 pc}"
  throwError "kit_run: out of fuel"

end Lua.Vm.Sim
