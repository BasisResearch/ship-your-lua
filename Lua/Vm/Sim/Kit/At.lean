import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Sim.Kit.K
import Lua.Vm.Sim.Kit.AtAttr

/-!
# Location lists and segment-local discharge (round-4 bake-off, B-SEGLOCAL)

The kit (`Kit/Run.lean`) runs the generated `SegSt` segments inside the arm's
own declaration, so every load's separation and every branch guard is
re-proved per path, in the arm's heartbeat budget. This file states the arm's
machine state at every segment boundary in a **location-list** form (DWARF's
idea, R4-R1-5 #1) so that a segment can be proved **once, in its own
declaration** (R4-R2-2 #2), for every path through it:

* `Cx`: the arm context (`p c s w ins`) a location is read in, and `Cx.Ok`,
  its facts (the relation's `Core` and the fetch);
* `Loc`: what a register holds, as a function of the context: a fetch-head
  register (`sp`, `L`, `ci`, `base`, `pc d`, `insw`), an affine address
  (`nat`, over the atoms `Atom`), a slot's or `K[C]`'s tag or payload *in the
  entry memory* (`tag`, `val`, `ktag`, `kval`), and the operations the arms
  and their helpers compute (`add`, …, `srem`, `udiv`);
* `Ent`/`Log.den`: the path's stores, oldest last, over the entry memory (a
  spill cell is an `Ent.sd` at `sp + 16`, `luaV_tointeger`'s out-parameter an
  `Ent.sd` at `sp + 40`: a later load reads the stored location);
* `At X pc L M c`: the machine at `pc` with pins `L` (values `Loc.den X _`)
  and memory `Log.den X M`; `AtStep`: a run between two such rows.

A generated **at-lemma** (`scripts/gen_lua_at.py`, `Lua/Vm/At/*`) is an
`AtStep` between two rows, proved in its own declaration by `at_seg`: the
`SegSt` segment applied, its bus side conditions and branch guards
discharged there (the guard taken from the at-lemma's hypothesis about the
*locations*, which the arm closes from its path facts without reading
memory), and the post-pins and post-memory normalised to the next row. The
arm composes at-lemmas with `AtStep.seq` (by `at_run`, which picks each one by
pc and by its guards) and calls with generated call at-lemmas.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- **The arm context** a location is read in. -/
structure Cx where
  p : Proto
  c : Config
  s : State
  w : RelPtrs
  ins : Word

/-- The context's facts. -/
structure Cx.Ok (X : Cx) : Prop where
  core : Core X.p X.c X.s X.w
  fetch : X.p.fetch X.s.pc = some X.ins

/-- An instruction field (a slot label's atom). -/
inductive Fld | a | b | c
  deriving DecidableEq

def Fld.den (X : Cx) : Fld → Nat
  | .a => X.ins.a
  | .b => X.ins.b
  | .c => X.ins.c

/-- An atom of an affine address. -/
inductive Atom | base | k | sp | L | ci | code | pc | a | b | c | bx
  deriving DecidableEq

def Atom.den (X : Cx) : Atom → Nat
  | .base => X.w.base
  | .k => X.w.k
  | .sp => X.w.sp
  | .L => X.w.L
  | .ci => X.w.ci
  | .code => X.w.code
  | .pc => X.s.pc
  | .a => X.ins.a
  | .b => X.ins.b
  | .c => X.ins.c
  | .bx => X.ins.bx

/-- An affine address `Σ cᵢ·atomᵢ + add - sub`. -/
structure Aff where
  terms : List (Nat × Atom)
  add : Nat
  sub : Nat

def Aff.sum (X : Cx) : List (Nat × Atom) → Nat
  | [] => 0
  | t :: ts => t.1 * t.2.den X + Aff.sum X ts

def Aff.den (X : Cx) (e : Aff) : Nat := Aff.sum X e.terms + e.add - e.sub

/-- **A location**: a register's value as a function of the arm context. -/
inductive Loc
  | lit (v : BitVec 64)
  | sp | L | ci | base
  | pc (d : Nat)
  | insw
  | nat (e : Aff)
  | tag (f : Fld) (k : Nat)
  | val (f : Fld) (k : Nat)
  | ktag | kval
  | add (x y : Loc) | sub (x y : Loc) | xor (x y : Loc)
  | srem (x y : Loc) | sdiv (x y : Loc) | udiv (x y : Loc) | umod (x y : Loc)
  | snez (x : Loc)
  | cell (e : Aff)
  -- the bitwise and shift arms (`and`, `or`, `sll`, `srl`, `addiw`, `subw`/`negw`)
  | and (x y : Loc) | or (x y : Loc) | sll (x y : Loc) | srl (x y : Loc)
  | addw (x y : Loc) | subw (x y : Loc)
  /-- a value stated over the context (`Kit/AtCond.lean`: a call's answer,
  such as a string register's length), closed so a log may hold it -/
  | fn (f : Cx → BitVec 64)

/-- The value of a location. -/
def Loc.den (X : Cx) : Loc → BitVec 64
  | .lit v => v
  | .sp => BitVec.ofNat 64 X.w.sp
  | .L => BitVec.ofNat 64 X.w.L
  | .ci => BitVec.ofNat 64 X.w.ci
  | .base => BitVec.ofNat 64 X.w.base
  | .pc d => BitVec.ofNat 64 (X.w.code + 4 * (X.s.pc + d))
  | .insw => sign_extend (m := 64) X.ins
  | .nat e => BitVec.ofNat 64 (e.den X)
  | .tag f k => zero_extend (m := 64) (slotTag X.c.σ.mem (X.w.slot (f.den X + k)))
  | .val f k => slotVal X.c.σ.mem (X.w.slot (f.den X + k))
  | .ktag => zero_extend (m := 64) (slotTag X.c.σ.mem (X.w.k + 16 * X.ins.c))
  | .kval => slotVal X.c.σ.mem (X.w.k + 16 * X.ins.c)
  | .add x y => x.den X + y.den X
  | .sub x y => x.den X - y.den X
  | .xor x y => x.den X ^^^ y.den X
  | .srem x y => (x.den X).srem (y.den X)
  | .sdiv x y => (x.den X).sdiv (y.den X)
  | .udiv x y => x.den X / y.den X
  | .umod x y => x.den X % y.den X
  | .snez x => zero_extend (m := 64) (bool_to_bit (zopz0zI_u 0#64 (x.den X)))
  | .cell e => bytesT8 X.c.σ.mem (e.den X)
  | .and x y => x.den X &&& y.den X
  | .or x y => x.den X ||| y.den X
  | .sll x y => shift_bits_left (x.den X) (Sail.BitVec.extractLsb (y.den X) 5 0)
  | .srl x y => shift_bits_right (x.den X) (Sail.BitVec.extractLsb (y.den X) 5 0)
  | .addw x y => sign_extend (m := 64) (Sail.BitVec.extractLsb (x.den X + y.den X) 31 0)
  | .subw x y => sign_extend (m := 64)
      ((Sail.BitVec.extractLsb (x.den X) 31 0) - (Sail.BitVec.extractLsb (y.den X) 31 0))
  | .fn f => f X

/-- `snez`'s value. -/
theorem snez_eq (x : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u 0#64 x)) = if x = 0#64 then 0#64 else 1#64 := by
  by_cases h : x = 0#64
  · subst h; decide
  · have : 0 < x.toNat := Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq e)
    have e : zopz0zI_u 0#64 x = true := by
      unfold zopz0zI_u; simp only [Sail.BitVec.toNatInt]
      exact decide_eq_true (Int.ofNat_lt.mpr (by simpa using this))
    rw [e, if_neg h]; decide

/-- A store of the path. -/
inductive Ent
  | sd (a : Aff) (v : Loc)
  | sb (a : Aff) (v : Loc)

def Ent.app (X : Cx) (m : Mem) : Ent → Mem
  | .sd a v => writeMap8 m (a.den X) (sdData_val (v.den X))
  | .sb a v => m.insert (a.den X) (stData 1 (v.den X))

/-- **The path's memory**: its stores (newest first) over the entry memory. -/
def Log.den (X : Cx) : List Ent → Mem
  | [] => X.c.σ.mem
  | e :: es => e.app X (Log.den X es)

/-- **The machine at a row**: at `pc`, pins `L`, memory `Log.den X M`. -/
def At (X : Cx) (pc : BitVec 64) (L : List Pin) (M : List Ent) (c : Config) : Prop :=
  SegSt pc L (ArmPay (Log.den X M) X.c.σ.sailOutput) c

/-- **A run between two rows.** -/
def AtStep (X : Cx) (pc : BitVec 64) (L : List Pin) (M : List Ent) (pc' : BitVec 64)
    (L' : List Pin) (M' : List Ent) : Prop :=
  ∀ c, At X pc L M c → ∃ c', Steps c c' ∧ At X pc' L' M' c'

/-- **Composition by name**: the rows meet. -/
theorem AtStep.seq {X : Cx} {pc pc' pc'' : BitVec 64} {L L' L'' : List Pin} {M M' M'' : List Ent}
    (h₁ : AtStep X pc L M pc' L' M') (h₂ : AtStep X pc' L' M' pc'' L'' M'') :
    AtStep X pc L M pc'' L'' M'' := fun c h =>
  let ⟨c₁, s₁, h₁⟩ := h₁ c h
  let ⟨c₂, s₂, h₂⟩ := h₂ c₁ h₁
  ⟨c₂, s₁.trans s₂, h₂⟩

/-- A run continued by an at-lemma. -/
theorem At.run {X : Cx} {pc pc' : BitVec 64} {L L' : List Pin} {M M' : List Ent} {c₀ c : Config}
    (acc : Steps c₀ c) (h : At X pc L M c) (st : AtStep X pc L M pc' L' M') :
    ∃ c', Steps c₀ c' ∧ At X pc' L' M' c' :=
  let ⟨c', s, h'⟩ := st c h
  ⟨c', acc.trans s, h'⟩

/-! ## The arm's entry -/

/-- The fetch-head registers as a row (`armPins`). -/
@[at_row] abbrev headRow (X : Cx) : List Pin :=
  [⟨Register.x2, Loc.den X .sp⟩, ⟨Register.x3, Loc.den X (.lit (BitVec.ofNat 64 symGlobalPointer))⟩,
   ⟨Register.x8, Loc.den X .L⟩, ⟨Register.x9, Loc.den X (.lit (BitVec.ofNat 64 (Arms.jtEntries - 1)))⟩,
   ⟨Register.x18, Loc.den X (.lit (BitVec.ofNat 64 vNumInt))⟩, ⟨Register.x19, Loc.den X (.pc 1)⟩,
   ⟨Register.x20, Loc.den X .insw⟩, ⟨Register.x21, Loc.den X (.lit 0#64)⟩,
   ⟨Register.x23, Loc.den X .ci⟩, ⟨Register.x24, Loc.den X (.lit (BitVec.ofNat 64 Arms.jtBase))⟩,
   ⟨Register.x25, Loc.den X .base⟩, ⟨Register.x27, Loc.den X (.pc 0)⟩]

/-- **The arm's entry as a row.** -/
theorem At.entry {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) {pc : BitVec 64} (hpc : armTarget ins.opNum = pc) :
    At ⟨p, c, s, w, ins⟩ pc (headRow ⟨p, c, s, w, ins⟩) [] c :=
  hA.seg hpc

/-! ## Regions (the separation of a load from a store, once)

A load is forwarded through a store of the path by its *region*: the
register slots, the constant array, `ci->u.l.savedpc`, `L->top`,
`luaV_execute`'s C frame and the callee frames below it. Distinct regions are
disjoint (`Rgn.sep`, proved once from `Ranges`); within a region the offsets
are compared (`omega`). -/

inductive Rgn | slots | kArr | savedpc | ltop | cframe | below
  deriving DecidableEq

def Rgn.lo (w : RelPtrs) : Rgn → Nat
  | .slots => w.base
  | .kArr => w.k
  | .savedpc => w.ci + ciSavedpcOff
  | .ltop => w.L + stateTopOff
  | .cframe => w.sp
  | .below => RuntimeData.spEntry - cStackBudget

def Rgn.hi (p : Proto) (w : RelPtrs) : Rgn → Nat
  | .slots => w.base + stackValueSize * p.maxstacksize
  | .kArr => w.k + stackValueSize * p.k.length
  | .savedpc => w.ci + ciSavedpcOff + 8
  | .ltop => w.L + stateTopOff + 8
  | .cframe => w.sp + execFrame
  | .below => w.sp

/-- Two byte ranges apart. -/
def Sep (x n a m : Nat) : Prop := x + n ≤ a ∨ a + m ≤ x

/-- **Distinct regions are disjoint.** -/
theorem Rgn.sep {p : Proto} {w : RelPtrs} (hr : Ranges p w) {r r' : Rgn} (hne : r ≠ r')
    {x n a m : Nat} (hx : r.lo w ≤ x ∧ x + n ≤ r.hi p w) (ha : r'.lo w ≤ a ∧ a + m ≤ r'.hi p w)
    (hn : 0 < n) (hm : 0 < m) : Sep x n a m := by
  have ko := hr.k_out
  have := hr.k_sep; have := hr.ci_sep; have := hr.L_sep; have := hr.frame_sep
  have := hr.L_sep_ci; have := hr.L_top; have := hr.ci_top; have := hr.sp_eq; have := hr.k_top
  have := hr.slots_top
  simp only [Win, Slots, Scratch, RuntimeData.spEntry, cStackBudget, execFrame,
    ciSavedpcOff, stateTopOff, ciSize, stateSize, stackValueSize] at *
  unfold Sep
  refine Classical.byContradiction fun hc => ?_
  cases r <;> cases r' <;> simp only [Rgn.lo, Rgn.hi, ciSavedpcOff, stateTopOff, execFrame,
    stackValueSize, RuntimeData.spEntry, cStackBudget] at hx ha <;> first
    | exact hne rfl
    | omega
    | exact ko (max x a) (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)
    | exact ko (max x a) (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
    | exact ko (max x a) (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
    | exact ko (max x a) (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
    | exact ko (max x a) (by omega) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))

/-! ## Forwarding a load through a store -/

theorem ld8_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : Sep x 8 a 8) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x := bytesT8_wm8_out (by unfold Sep at h; omega)

theorem ld8_ins {m : Mem} {a x : Nat} {b : BitVec 8} (h : Sep x 8 a 1) :
    bytesT8 (m.insert a b) x = bytesT8 m x := bytesT8_ins (by unfold Sep at h; omega)

theorem ld1_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : Sep x 1 a 8) :
    bytesT1 (writeMap8 m a d) x = bytesT1 m x := bytesT1_writeMap8_out m a d (by unfold Sep at h; omega)

theorem ld1_ins {m : Mem} {a x : Nat} {b : BitVec 8} (h : Sep x 1 a 1) :
    bytesT1 (m.insert a b) x = bytesT1 m x := by
  simp only [bytesT1, getElem?_insert_out (show x ≠ a by unfold Sep at h; omega)]

theorem ld8_wm8_same {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x = a) :
    bytesT8 (writeMap8 m a d) x = d := by subst h; exact bytesT8_writeMap8 m x d

theorem ld1_ins_same {m : Mem} {a x : Nat} {b : BitVec 8} (h : x = a) :
    bytesT1 (m.insert a b) x = b := by subst h; simp [bytesT1]

/-- `ld 0(sp)`: the constant array (`Core.kptr`). -/
theorem kptr_at {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w) {x : Nat}
    (h : x = w.sp) : bytesT8 c.σ.mem x = BitVec.ofNat 64 w.k := h ▸ hc.kptr

/-! ## Congruences (the machine term against the location's value) -/

theorem guard_congr {α β γ : Type} {f : α → β → γ} {a a' : α} {b b' : β} {r : γ}
    (h : f a' b' = r) (ha : a = a') (hb : b = b') : f a b = r := by
  subst ha hb; exact h

theorem bin_congr {α β γ : Type} {f : α → β → γ} {a a' : α} {b b' : β}
    (ha : a = a') (hb : b = b') : f a b = f a' b' := by subst ha hb; rfl

theorem un_congr {α β : Type} {f : α → β} {a a' : α} (ha : a = a') : f a = f a' := by subst ha; rfl

theorem writeMap8_congr {m m' : Mem} {a a' : Nat} {d d' : BitVec (8 * 8)} (hm : m = m')
    (ha : a = a') (hd : d = d') : writeMap8 m a d = writeMap8 m' a' d' := by subst hm ha hd; rfl

theorem insert_congr {m m' : Mem} {a a' : Nat} {d d' : BitVec 8} (hm : m = m')
    (ha : a = a') (hd : d = d') : m.insert a d = m'.insert a' d' := by subst hm ha hd; rfl

/-- The unfolding of rows and logs. -/
macro "at_unfold" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [at_row, At, Loc.den, Fld.den, Aff.den, Aff.sum, Atom.den, Log.den, Ent.app,
    Nat.mul_one, Nat.one_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero] $[$loc]?)

set_option hygiene false in
/-- The context's numeric facts, for `kit_disch` (as `kit_setup`'s). -/
macro "at_facts " hX:ident : tactic => `(tactic| (
  have hc := ($hX).core
  have hr := hc.ranges
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hr.base_lo; have := hr.base_hi; have := hr.base_al; have := hr.ci_lo
  have := hr.ci_hi; have := hr.code_hi; have := hr.code_lo; have := fetch_lt ($hX).fetch
  have := X.ins.isLt; have := hr.L_lo; have := hr.ci_sep; have := hr.L_sep; have := hr.ci_top
  have := hr.L_top; have := hr.slots_top; have := hr.sp_eq; have := hr.L_al; have := hr.ci_al
  have := hr.k_lo; have := hr.k_hi; have := hr.k_al; have := hr.frame_sep; have := hr.k_top
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame,
    Word.a, Word.b, Word.c, Word.bx, Word.field, Nat.shiftRight_eq_div_pow] at *))

open Lean Elab Tactic Meta

/-- `decide` on a goal without free variables (never on a symbolic one). -/
elab "ground_decide" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then throwError "ground_decide: not ground"
  evalTactic (← `(tactic| decide))

/-- The region of a (normalised) address, by the pointer it is built on. -/
def rgnOf (e : Expr) : Option Name :=
  let has (n : Name) := (e.find? fun x => x.isConstOf n).isSome
  if has ``RelPtrs.k then some ``Rgn.kArr
  else if has ``RelPtrs.base || has ``RelPtrs.func then some ``Rgn.slots
  else if has ``RelPtrs.ci then some ``Rgn.savedpc
  else if has ``RelPtrs.L then some ``Rgn.ltop
  else if has ``RelPtrs.sp then
    (if (e.find? fun x => x.isAppOf ``HSub.hSub).isSome then some ``Rgn.below else some ``Rgn.cframe)
  else none

/-- The address normaliser of `kit_disch` (without its closer). -/
macro "at_addr" : tactic => `(tactic| (
  try simp (config := { decide := true }) only [extract_sext, field8, sext_shr, add_imm, shl_ofNat,
    add_imm_m48, imm_neg_add, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.add_zero, RelPtrs.slot,
    stackValueSize, Word.a, Word.b, Word.c, Word.bx, Word.field, Nat.shiftRight_eq_div_pow, and255]
  try simp (disch := omega) only [Nat.mod_eq_of_lt]))

/-- **`at_sep`**: `Sep x n a m` for a load against a store: the addresses
normalised, then the regions (`Rgn.sep`) or, in one region, the offsets. -/
elab "at_sep" : tactic => withMainContext do
  evalTactic (← `(tactic| at_addr))
  withMainContext do
  let t ← whnfR (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let args := t.getAppArgs
  unless t.isAppOfArity ``Sep 4 do throwError "at_sep: not a Sep goal: {t}"
  match rgnOf args[0]!, rgnOf args[2]! with
  | some r1, some r2 =>
    if r1 == r2 then evalTactic (← `(tactic| (unfold Sep; omega)))
    else evalTactic (← `(tactic| (
      refine Rgn.sep $(mkIdent `hr) (r := $(mkIdent r1)) (r' := $(mkIdent r2)) (by decide) ?_ ?_ (by decide) (by decide) <;>
      (simp only [Rgn.lo, Rgn.hi, ciSavedpcOff, stateTopOff, execFrame, stackValueSize,
        RuntimeData.spEntry, cStackBudget]; constructor <;> omega))))
  | _, _ => evalTactic (← `(tactic| (unfold Sep; omega)))

/-- The same function applied on both sides, with the same number of arguments. -/
def sameHead (l r : Expr) : Bool :=
  let lf := l.getAppFn; let rf := r.getAppFn
  lf.isConst && rf.isConst && lf.constName! == rf.constName! && l.getAppNumArgs == r.getAppNumArgs

/-- The subterms satisfying `p`, outermost first. -/
partial def collectE (p : Expr → Bool) (e : Expr) : Array Expr :=
  let here := if p e then #[e] else #[]
  match e with
  | .app f a => here ++ collectE p f ++ collectE p a
  | .lam _ t b _ | .forallE _ t b _ => here ++ collectE p t ++ collectE p b
  | .letE _ t v b _ => here ++ collectE p t ++ collectE p v ++ collectE p b
  | .mdata _ b => here ++ collectE p b
  | .proj _ _ b => here ++ collectE p b
  | _ => here

/-- Run a tactic on a fresh goal of type `ty`; its proof, if it closes. -/
def proveBy (ty : Expr) (tac : Syntax) : TacticM (Option Expr) := do
  let g ← mkFreshExprMVar ty
  let s ← saveState
  try
    let gs ← Tactic.run g.mvarId! (evalTactic tac)
    if gs.isEmpty then return some (← instantiateMVars g)
    s.restore; return none
  catch _ => s.restore; return none

/-- One load `bytesT1/bytesT8 M x` of the goal whose memory `M` is a store
(`writeMap8`/`insert`), forwarded through that store: past it (`at_sep`) or
reading it (`*_same`, `kit_disch`). -/
partial def atFwd1 : TacticM Bool := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let loads := collectE (fun e : Expr =>
    (e.isAppOfArity ``bytesT1 2 || e.isAppOfArity ``bytesT8 2) &&
    (e.appFn!.appArg!.isAppOfArity ``writeMap8 3 ||
      e.appFn!.appArg!.isAppOf ``Std.ExtHashMap.insert)) t
  for e in loads do
    let isB1 := e.isAppOfArity ``bytesT1 2
    let M := e.appFn!.appArg!
    let x := e.appArg!
    let isW8 := M.isAppOfArity ``writeMap8 3
    let (m, a, d) := if isW8 then (M.appFn!.appFn!.appArg!, M.appFn!.appArg!, M.appArg!)
      else (M.appFn!.appFn!.appArg!, M.appFn!.appArg!, M.appArg!)
    let n : Nat := if isB1 then 1 else 8
    let w : Nat := if isW8 then 8 else 1
    let out := if isB1 then (if isW8 then ``ld1_wm8 else ``ld1_ins)
      else (if isW8 then ``ld8_wm8 else ``ld8_ins)
    let sepTy ← mkAppM ``Sep #[x, mkNatLit n, a, mkNatLit w]
    let mut eq? : Option Expr := none
    if let some pf ← proveBy sepTy (← `(tactic| at_sep)) then
      eq? := some (← mkAppOptM out #[m, a, x, d, pf])
    else if (isB1 && !isW8) || (!isB1 && isW8) then
      let same := if isB1 then ``ld1_ins_same else ``ld8_wm8_same
      if let some pf ← proveBy (← mkEq x a) (← `(tactic| kit_disch)) then
        eq? := some (← mkAppOptM same #[m, a, x, d, pf])
    if let some eq := eq? then
      let g ← getMainGoal
      let r ← g.rewrite (← g.getType) eq
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      replaceMainGoal (g' :: r.mvarIds)
      return true
  return false

/-- Every load of the goal forwarded through the path's stores. -/
partial def atFwd : TacticM Unit := do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    unless ← atFwd1 do return

/-- **An extension point of `at_eq`** (tried first, before `rfl`): the rules
of a family of arms whose machine values have a closed form a library lemma
states once (`Kit/AtCond.lean`: `docondjump`'s `k` bit, the `trap` reload,
`donextjump`'s target, a call's observed answer). Fails by default. -/
syntax "at_eq_ext" : tactic
macro_rules | `(tactic| at_eq_ext) => `(tactic| fail "at_eq_ext")

/-- **`at_eq`**: a machine value equal to a location's (after `at_unfold`):
by the goal's shape, a load forwarded through the path's stores
(`ld*_wm8`/`ld*_ins` by `at_sep`, a hit by `*_same`), the constant array
(`kptr_at`), an operation's arguments (`bin_congr`/`un_congr`), or an address
(`toNat`, `kit_disch`). -/
partial def atEq : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, _, _) := t.eq? | throwError "at_eq: not an equation"
  -- an affine location left folded (a stored value computed from `C`)
  if (t.find? fun e => e.isConstOf ``Aff.den).isSome then
    evalTactic (← `(tactic| simp only [Aff.den, Aff.sum, Atom.den, Nat.one_mul, Nat.add_zero,
      Nat.sub_zero]))
    unless (← getUnsolvedGoals).isEmpty do atEq
    return
  let s0 ← saveState
  try
    evalTactic (← `(tactic| at_eq_ext))
    if (← getUnsolvedGoals).isEmpty then return
    s0.restore
  catch _ => s0.restore
  try
    evalTactic (← `(tactic| with_reducible rfl)); return
  catch _ => s0.restore
  if !t.hasFVar && !t.hasMVar then
    evalTactic (← `(tactic| decide)); return
  evalTactic (← `(tactic| try simp only [Vsa.Sim.sext_zero, BitVec.add_zero]))
  if (← getUnsolvedGoals).isEmpty then return
  let s0 ← saveState
  try
    evalTactic (← `(tactic| with_reducible rfl)); return
  catch _ => s0.restore
  withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isLoad (e : Expr) : Bool :=
    (e.find? fun x => x.isAppOf ``bytesT8 || x.isAppOf ``bytesT1 || x.isAppOf ``slotVal ||
      x.isAppOf ``slotTag).isSome
  -- every load forwarded through the path's stores, `0(sp)` read as `k`
  if isLoad t then
    let hc := mkIdent `hc
    evalTactic (← `(tactic| try simp only [sext64_id, slotVal, slotTag, tvalueValOff, tvalueTagOff,
      Nat.add_zero]))
    atFwd
    evalTactic (← `(tactic| (
      try simp (disch := kit_disch) only [kptr_at $hc]
      try simp only [sdData_id, sext64_id])))
    if (← getUnsolvedGoals).isEmpty then return
    let s1 ← saveState
    try
      evalTactic (← `(tactic| with_reducible rfl)); return
    catch _ => s1.restore
  withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, r) := t.eq? | throwError "at_eq: not an equation"
  let isLd (e : Expr) : Bool := e.isAppOf ``bytesT8 || e.isAppOf ``bytesT1 ||
    (e.getAppNumArgs > 0 && (e.appArg!.isAppOf ``bytesT1 || e.appArg!.isAppOf ``bytesT8))
  -- two loads from the entry memory: their addresses
  if isLd l && isLd r then
    let s1 ← saveState
    for tac in [← `(tactic| (with_reducible apply un_congr; kit_disch)),
                ← `(tactic| (with_reducible apply un_congr; with_reducible apply un_congr; kit_disch))] do
      try
        evalTactic tac
        if (← getUnsolvedGoals).isEmpty then return
        s1.restore
      catch _ => s1.restore
    -- a binary operation on loads (`and a4,a4,a3`): its operands, below
    unless sameHead l r && l.getAppNumArgs == 6 do
      throwError "at_eq: load not forwarded: {← ppGoal (← getMainGoal)}"
  -- an operation: congruence on its arguments
  if sameHead l r && l.getAppFn.constName! != ``BitVec.ofNat then
    let s2 ← saveState
    try
      evalTactic (← `(tactic| with_reducible refine bin_congr ?_ ?_))
      let gs ← getUnsolvedGoals
      for g in gs do
        setGoals [g]
        atEq
      return
    catch _ => s2.restore
    try
      evalTactic (← `(tactic| with_reducible refine un_congr ?_))
      atEq
      return
    catch _ => s2.restore
    -- an operand not in the last position (`extractLsb x 31 0`): congruence
    -- on every argument (no closing by `rfl`: never whnf a Sail term)
    if l.getAppFn.constName! == ``Sail.BitVec.extractLsb then
     try
      let gs ← (← getMainGoal).congrN 1 (closePre := false) (closePost := false)
      for g in gs do
        setGoals [g]
        atEq
      return
     catch _ => s2.restore
  -- an address
  try
    evalTactic (← `(tactic| (apply BitVec.eq_of_toNat_eq; kit_disch)))
  catch e =>
    throwError "at_eq: no rule: {e.toMessageData}\n{← ppGoal (← getMainGoal)}"

elab "at_eq" : tactic => atEq

/-- A guard of the segment from the at-lemma's guard about locations. -/
macro "at_guard " h:ident : tactic => `(tactic|
  (refine guard_congr (by at_unfold at $h:ident; exact $h) ?_ ?_ <;> at_eq))

/-- A store chain in two forms. -/
syntax "at_mem" : tactic
macro_rules
  | `(tactic| at_mem) => `(tactic| first
    | with_reducible rfl
    | (with_reducible refine writeMap8_congr ?_ ?_ ?_
       · at_mem
       · kit_disch
       · exact un_congr (by at_eq))
    | (with_reducible refine insert_congr ?_ ?_ ?_
       · at_mem
       · kit_disch
       · exact un_congr (by at_eq)))

/-- **`at_pins h`**: the goal's pin list (a row), each register found by name
in `h`'s pins, the value by `at_eq` where the forms differ. -/
elab "at_pins " h:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_pins: no {h}"
  let src ← listElems ((← instantiateMVars ld.type).getAppArgs[1]!)
  let tgt ← instantiateMVars (← getMainTarget)
  let dst ← listElems tgt.getAppArgs[1]!
  let reg (p : Expr) : Expr := p.getAppArgs[2]!
  let mut parts : Array Term := #[]
  for q in dst do
    let some i := src.findIdx? (fun p => reg p == reg q)
      | throwError "at_pins: register {reg q} not pinned in {h}"
    let qv ← whnfR q.getAppArgs[3]!
    let pv ← whnfR src[i]!.getAppArgs[3]!
    -- a failed check (e.g. `maxRecDepth` unfolding a large value) is a mismatch
    let st ← saveState
    let same ← tryCatchRuntimeEx (withReducible (isDefEq qv pv)) fun _ => do st.restore; pure false
    if same then
      parts := parts.push (← `(pinsHold_get ($h).pins $(quote i) (by pin_len)))
    else
      -- the pin's fact elaborated on its own first (elaborated against the
      -- row's value, `addiw`'s pin sends the unifier into a loop)
      parts := parts.push (← `((by
        have hh := pinsHold_get ($h).pins $(quote i) (by pin_len)
        exact pin_eq hh (by simp only [List.getElem_cons_succ, List.getElem_cons_zero, HFrame.pins]; at_eq))))
  -- the goal's pins as `get? r = some v`, one goal each (a projection
  -- `⟨r, v⟩.1`, or one term for all pins, lets the elaborator unify the pins'
  -- values structurally, at default transparency)
  evalTactic (← `(tactic| dsimp only [PinsHold]))
  let holes : Array Term ← parts.mapM fun _ => `(?_)
  let holes := holes.push (← `(trivial))
  evalTactic (← `(tactic| refine ⟨$holes,*⟩))
  let gs ← getUnsolvedGoals
  unless gs.length == parts.size do throwError "at_pins: {gs.length} goals for {parts.size} pins"
  for (g, part) in gs.zip parts.toList do
    setGoals [g]
    evalTactic (← `(tactic| exact $part))

/-- The argument syntax of a segment theorem for `at_seg`: `_` for values,
`(by at_guard hg_k)` for a guard `hg_k`, `(by kit_disch)` for the rest. -/
def atSegArgs (n : Name) : TermElabM (Array Term) := do
  let ci ← getConstInfo n
  let outer ← getLCtx
  forallTelescope ci.type fun xs _ => do
    let mut args := #[]
    for x in xs do
      let t ← inferType x
      let nm := (← x.fvarId!.getDecl).userName.toString
      if ← Meta.isProp t then
        if nm.startsWith "hg" then
          if outer.findFromUserName? (Name.mkSimple nm) |>.isSome then
            args := args.push (← `((by at_guard $(mkIdent (Name.mkSimple nm)))))
          else
            args := args.push (← `((by first | decide | (simp; done))))
        else if (t.find? fun e => e.isConstOf ``bytesT8).isSome then
          -- an address through a load in the segment (`ld a4,0(sp)`: `k`)
          args := args.push (← `((by
            (try simp (disch := kit_disch) only [kptr_at $(mkIdent `hc)])
            (try simp only [sext64_id])
            kit_disch)))
        else args := args.push (← `((by kit_disch)))
      else args := args.push (← `(_))
    return args

set_option hygiene false in
/-- The opening of an at-lemma's proof. -/
macro "at_open" : tactic => `(tactic| (
  intro c h
  at_facts hX
  at_unfold at h ⊢
  have acc := Vsa.Machine.Steps.refl c))

/-- **`at_seg seg`**: an at-lemma's proof: the segment `seg` applied at the
row, its side conditions discharged here, the post-state put in the next
row's form. -/
elab "at_seg " n:ident : tactic => do
  evalTactic (← `(tactic| at_open))
  let nm ← realizeGlobalConstNoOverload n
  let args ← withMainContext <| Tactic.runTermElab (atSegArgs nm)
  let seg ← `($(mkIdent nm) $args*)
  let h := mkIdent `h; let acc := mkIdent `acc
  evalTactic (← `(tactic|
    obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (by pins_of $h) $seg))
  -- the pins and the memory as goals of their own (inside one `exact` the
  -- pins' terms elaborate against the outer term's pending unification)
  evalTactic (← `(tactic| refine ⟨_, $acc, (Vsa.Sim.SegSt.repin $h ?_).mem_eq ?_⟩))
  evalTactic (← `(tactic| · at_pins $h))
  evalTactic (← `(tactic| · at_mem))

/-- A dead callee-saved register's pin (every GPR holds a value, `RegsOk`):
`s6`/`s10` in a helper's frame where the row has no location for them. -/
theorem _root_.Vsa.Sim.SegSt.pin22 {pc : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    {c : Vsa.Machine.Config} (h : SegSt pc L (ArmPay m o) c) :
    ∃ t, SegSt pc (⟨Register.x22, t⟩ :: L) (ArmPay m o) c := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h.armOk.gpr 22 (by decide) (by decide))
  exact ⟨t, h.repin ⟨ht, h.pins⟩⟩

theorem _root_.Vsa.Sim.SegSt.pin26 {pc : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    {c : Vsa.Machine.Config} (h : SegSt pc L (ArmPay m o) c) :
    ∃ t, SegSt pc (⟨Register.x26, t⟩ :: L) (ArmPay m o) c := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h.armOk.gpr 26 (by decide) (by decide))
  exact ⟨t, h.repin ⟨ht, h.pins⟩⟩

set_option hygiene false in
/-- **`at_call sum`**: a call at-lemma's proof, after `at_open` and the pins
of the registers the row leaves dead (`SegSt.pin5`, `pin22`, `pin26`): the
helper's summary `sum` (a call node, `SegSt.call`) at the row, the return
row and memory by `at_pins`/`at_mem`. -/
macro "at_call " sum:term : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h) $sum
  exact ⟨_, acc, (Vsa.Sim.SegSt.repin h (by at_pins h)).mem_eq (by at_mem)⟩))

/-- A helper's precondition about memory from the at-lemma's hypothesis
about the entry memory. -/
macro "at_pre " h:ident : tactic => `(tactic|
  (refine Eq.trans ?_ (by (try at_unfold at $h:ident); exact $h); at_eq))

/-! ## The close at the fetch head -/

/-- A register slot the path stored: field `f` plus `k`, the tag and
payload locations. -/
structure SlotW where
  f : Fld
  k : Nat
  t : Loc
  v : Loc

/-- The slot's register. -/
abbrev SlotW.j (X : Cx) (e : SlotW) : Nat := e.f.den X + e.k

/-- **At the fetch head**: the machine state, its pins for the successor
pc `pc'`, the memory's frame (outside the slots, `Scratch` and the C frame,
the entry memory), the stored slots `W` and the other slots unchanged. -/
structure AtFin (X : Cx) (M : List Ent) (W : List SlotW) (pc' : Nat) (c : Vsa.Machine.Config) : Prop where
  seg : SegSt Arms.headPc [] (ArmPay (Log.den X M) X.c.σ.sailOutput) c
  pins : Pins c.σ X.w pc'
  frame : ∀ x, ¬ Slots X.p X.w x → ¬ Scratch X.w x → ¬ CFrame X.w x → (Log.den X M)[x]? = X.c.σ.mem[x]?
  wtag : ∀ e ∈ W, slotTag (Log.den X M) (X.w.slot (e.j X)) = stData 1 (e.t.den X)
  wval : ∀ e ∈ W, slotVal (Log.den X M) (X.w.slot (e.j X)) = e.v.den X
  keep : ∀ x, Slots X.p X.w x → (∀ e ∈ W, x < X.w.slot (e.j X) ∨ X.w.slot (e.j X) + 16 ≤ x) →
    (Log.den X M)[x]? = X.c.σ.mem[x]?
  bound : ∀ e ∈ W, e.j X < X.p.maxstacksize

set_option hygiene false in
/-- **`at_fin`**: a fin lemma's proof: the pins by name (the pc by
`slot_arith`), the frame and the slots by forwarding through the log. -/
macro "at_fin" : tactic => `(tactic| (
  at_facts hX
  have hseg := Vsa.Sim.SegSt.repin (L' := []) h trivial
  at_unfold at h
  refine ⟨hseg, ⟨by pin_of h, by pin_of h, by pin_of h, by pin_of h,
    by pin_of h, by pin_of h, by pin_of h, by pin_of h, by pin_of h,
    pin_eq (by pin_of h) (by apply BitVec.eq_of_toNat_eq; slot_arith)⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try at_unfold
  · intro x h1 h2 h3
    simp only [Slots, Scratch, CFrame, RelPtrs.slot, ciSavedpcOff, stateTopOff, RuntimeData.spEntry,
      cStackBudget, execFrame, stackValueSize, not_or, not_and, Nat.not_lt] at h1 h2 h3
    try simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Loc.den]
    try refine ⟨?_, ?_⟩
    all_goals at_eq
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Loc.den]
    try refine ⟨?_, ?_⟩
    all_goals at_eq
  · intro x h1 h2
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Slots, RelPtrs.slot, stackValueSize, Word.a, Word.b, Word.c, Word.field,
      Nat.shiftRight_eq_div_pow] at h1 h2
    try simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      SlotW.j, Fld.den, Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow]
    try refine ⟨?_, ?_⟩
    all_goals omega))

/-- **The close**: the successor's registers `regs'` are the entry's but at
the stored slots `W`, each represented by its stored tag and payload. -/
theorem AtFin.close {X : Cx} (hX : X.Ok) {M : List Ent} {W : List SlotW} {pc' : Nat} {c : Vsa.Machine.Config}
    (hF : AtFin X M W pc' c) {regs' : Nat → Option Value}
    (hold : ∀ j, (∀ e ∈ W, j ≠ e.j X) → regs' j = X.s.regs j)
    (hnew : ∀ e ∈ W, ∀ v, regs' (e.j X) = some v →
      ValRepr X.w.mo X.w.ι (stData 1 (e.t.den X)) (e.v.den X) v) :
    VmRelAt X.p c ⟨pc', regs', X.s.out⟩ X.w := by
  have hc := hX.core
  refine ⟨hc.bleachF hF.seg rfl hF.pins hF.frame ?_, hF.seg.pcAt⟩
  refine hc.stack_of (fun j => ∃ e ∈ W, j = e.j X) (fun j hj => hold j fun e he h => hj ⟨e, he, h⟩)
    (fun x hx hW => hF.keep x hx fun e he => ?_) ?_
  · have := hW (e.j X) ⟨e, he, rfl⟩
    simp only [RelPtrs.slot, stackValueSize] at this ⊢; omega
  · rintro j v ⟨e, he, rfl⟩ _ hv
    rw [hF.wtag e he, hF.wval e he]
    exact hnew e he v hv

/-! ## The arm: a chain of at-lemmas -/

/-- The arm's closer of an at-lemma's hypothesis (a slot bound, a guard
about locations), extended per arm by `macro_rules`. -/
syntax "at_hyp" : tactic
macro_rules
  | `(tactic| at_hyp) => `(tactic| first
    | assumption
    | (simp only [Fld.den]; omega))

/-- The arguments of an at-lemma for `at_run`: `_` for the context,
`hX` for its facts, `(by at_hyp)` for the rest. -/
def atRunArgs (n : Name) : TermElabM (Array Term) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut args : Array Term := #[]
    for x in xs do
      let t ← inferType x
      unless (← x.fvarId!.getDecl).binderInfo.isExplicit do continue
      let nm := (← x.fvarId!.getDecl).userName.toString
      if nm == "hX" then args := args.push (mkIdent `hX)
      else if ← Meta.isProp t then args := args.push (← `((by at_hyp)))
      else args := args.push (← `(_))
    return args

/-- The pc of an `At` hypothesis. -/
def atPc (ty : Expr) : MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``At 5 do return none
  match ← getBitVecValue? ty.getAppArgs[1]! with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- The at-lemmas of namespace `ns` that may start at `pc`, by name: a
segment's `at_<pc>_<hi>[_t|_n][_k]`, and a call's `call_<ret>[_k]` where
`ret` is the row's return address (`ra`, a literal). -/
def atCands (ns : Name) (pc : Nat) (ret : Option Nat) : MetaM (List Name) := do
  let env ← getEnv
  let mut out := []
  let ks := ["", "_1", "_2", "_3", "_4", "_5", "_6", "_7"]
  for d in [0:96] do
    let hi := pc + 4 * (d + 1)
    for suf in ["", "_t", "_n"] do
      for k in ks do
        let n := ns ++ Name.mkSimple s!"at_{hex8 pc}_{hex8 hi}{suf}{k}"
        if env.contains n then out := out ++ [n]
  if let some r := ret then
    for k in ks do
      let n := ns ++ Name.mkSimple s!"call_{hex8 r}{k}"
      if env.contains n then out := out ++ [n]
  return out

/-- A row's or log's name (its head constant: `r3`, `headRow`, `m2`, `[]`). -/
def headName (e : Expr) : Name := e.getAppFn.constName?.getD .anonymous

/-- The (row, log) names of an `At` hypothesis. -/
def atKey (ty : Expr) : MetaM (Name × Name) := do
  let ty ← instantiateMVars ty
  return (headName ty.getAppArgs[2]!, headName ty.getAppArgs[3]!)

/-- The (row, log) names an at-lemma (`AtStep`) starts from, or a fin
lemma's `At` hypothesis has. -/
def lemmaKey (n : Name) : MetaM (Name × Name) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs body => do
    if body.isAppOfArity ``AtStep 7 then
      return (headName body.getAppArgs[2]!, headName body.getAppArgs[3]!)
    for x in xs.reverse do
      let t ← inferType x
      if t.isAppOfArity ``At 5 then
        return (headName t.getAppArgs[2]!, headName t.getAppArgs[3]!)
    return (.anonymous, .anonymous)

/-- The literal return address in an `At` row (`ra`'s pin), if any. -/
def atRet (ty : Expr) : MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``At 5 do return none
  let row ← whnfR ty.getAppArgs[2]!
  let pins ← try listElems row catch _ => return none
  for p in pins do
    if p.getAppArgs[2]!.isConstOf ``Register.x1 then
      let v := p.getAppArgs[3]!
      -- `Loc.den X (.lit r)`
      if v.isAppOfArity ``Loc.den 2 && v.appArg!.isAppOfArity ``Loc.lit 1 then
        if let some ⟨_, r⟩ ← getBitVecValue? v.appArg!.appArg! then return some r.toNat
  return none

/-- The entries of the error exits (`scripts/gen_lua_at.py` `ERRS`;
`errEntries_eq` checks them against `Lua/Vm/Layout.lean`): a run of the
at-lemmas stops there as at the fetch head. -/
def errEntryPcs : List Nat :=
  [0x800092cc, 0x80009438, 0x80009414, 0x80009468, 0x80009398, 0x800094c0, 0x800093e4, 0x80009530]

/-- **`at_run ns h acc`**: from `h : At X pc …`, apply the at-lemmas of `ns`
that start at the current pc (the first whose row matches and whose
hypotheses `at_hyp` closes), until the fetch head or an error exit's entry
(`errEntryPcs`). -/
elab "at_run " ns:ident h:ident acc:ident : tactic => do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let (pc, ret) ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_run: no {h}"
      return (← atPc ld.type, ← atRet ld.type)
    let some pc := pc | throwError "at_run: no pc"
    if pc == 0x8001bfe4 || errEntryPcs.contains pc then return
    let cands ← atCands ns.getId pc ret
    let mut done := false
    let mut errs : Array MessageData := #[]
    let key ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_run: no {h}"
      atKey ld.type
    for n in cands do
      unless (← lemmaKey n) == key do continue
      let s ← saveState
      try
        let args ← Tactic.runTermElab (atRunArgs n)
        let lem ← `($(mkIdent n) $args*)
        withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
          obtain ⟨_, $acc, $h⟩ := At.run $acc $h $lem))
        done := true
        break
      catch e =>
        errs := errs.push m!"{n}: {e.toMessageData}"
        s.restore
    unless done do
      throwError "at_run: no at-lemma at 0x{hex8 pc} applies:{indentD (MessageData.joinSep errs.toList "\n")}"
  throwError "at_run: out of fuel"

end Lua.Vm.Sim.At
