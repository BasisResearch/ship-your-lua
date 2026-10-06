import Lua.Vm.Sim.Kit.At
import Lua.Vm.Sim.Kit.Sflush

/-!
# Callee-context rows (lane F1-8)

The at-lemma rows of `Kit/At.lean` are stated over an *arm* context `Cx`
(`p c s w ins`): a location is a slot, `K[C]`, a fetch-head pointer. A C
callee (`fflush`, `_fwrite_r`, `__sfvwrite_r`, …) has none of these: its
entry pins are its arguments, `ra`, `sp`, `gp` and the caller's callee-saved
registers. Lane F1-6 therefore wrote one context macro and one pin normaliser
per helper (`wr_ctx`, `sfl_ctx`, `sfl_norm`, …). This file is the callee
version of the rows, so that `scripts/gen_lua_at.py --fn` generates a
helper's at-lemmas as it does an arm's:

* `FCx`: the values a callee's rows are stated over: Nat atoms `X.n i`
  (`sp`, pointer and count arguments: addresses are affine in them), opaque
  words `X.b i` (`ra`, the caller's `s0`–`s11`, data arguments), and the
  memory `X.m` and console `X.o` at the *root* the rows start from (the
  callee's entry, a loop head, or the return from a call whose effect is
  abstract: a fresh context `{X with m := m', o := o'}`, the atoms shared);
* a row is an `@[at_row]` abbreviation `r<k> (X : FCx) : List Pin`, a path's
  memory an abbreviation `m<k> (X : FCx) : Mem` (its stores over `X.m`), both
  printed by the generator in a canonical form (addresses `BitVec.ofNat 64`
  of a Nat term in the atoms, loads `bytesT<w> X.m a`);
* an at-lemma is a `Triple` between two rows, keyed by the entry pc of its
  segment, proved in its own declaration by `fat_seg` (the segment applied,
  its side conditions discharged here) and `fat_close` (the post-row by
  `at_pins`, the post-memory by `fat_mem`);
* the entry-memory facts a path relies on (a `FILE` field, a stack slot kept
  across a call) are hypotheses `bytesT<w> X.m a = v` of the at-lemmas that
  read them; `fat_rd` forwards every load through the path's stores to `X.m`
  (`fw*` lemmas, separations by `omega`) and rewrites it by these facts.

`fat_run` chains a function's at-lemmas from a row, by pc and row/memory
name, as `at_run` does an arm's.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.AtF

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **A callee's context**: the atoms its rows are stated over, and the
memory and console at the root. -/
structure FCx where
  /-- Nat atoms: `sp`, pointer and count arguments -/
  n : Nat → Nat
  /-- opaque words: `ra`, the caller's callee-saved registers, data arguments -/
  b : Nat → BitVec 64
  m : Mem
  o : Array String

/-- A context from lists of atoms. -/
abbrev FCx.mk' (ns : List Nat) (bs : List (BitVec 64)) (m : Mem) (o : Array String) : FCx :=
  ⟨fun i => ns.getD i 0, fun i => bs.getD i 0, m, o⟩

/-- **A C callee's context from its ABI entry** (`gen_lua_at.py`'s `abi_row`):
`sp` the Nat atom, `ra` and the caller's `s0`–`s11` the words. -/
abbrev abiCx (sp : Nat) (r : BitVec 64) (f : Kit.AbiFrame) (m : Mem) (o : Array String) : FCx :=
  ⟨fun _ => sp, fun i => [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11].getD i 0,
    m, o⟩

/-- The rows, memories and contexts unfolded to the summary's own terms. -/
macro "fcx_unfold" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp only [at_row, abiCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] $[$loc]?)

/-- **The row of a callee**: at `pc`, pins `L`, memory `M`, the root's console. -/
abbrev FAt (X : FCx) (pc : BitVec 64) (L : List Pin) (M : Mem) : Config → Prop :=
  SegSt pc L (ArmPay M X.o)

/-! ## Byte reads through stores -/

theorem bT1_congr {m m' : Mem} {x : Nat} (h : m[x]? = m'[x]?) : bytesT1 m x = bytesT1 m' x := by
  simp only [bytesT1, h]

theorem bT2_congr {m m' : Mem} {x : Nat} (h : ∀ i, i < 2 → m[x + i]? = m'[x + i]?) :
    bytesT2 m x = bytesT2 m' x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT2, h0, h1]

theorem bT4_congr {m m' : Mem} {x : Nat} (h : ∀ i, i < 4 → m[x + i]? = m'[x + i]?) :
    bytesT4 m x = bytesT4 m' x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4, h0, h1, h2, h3]

theorem bT8_congr {m m' : Mem} {x : Nat} (h : ∀ i, i < 8 → m[x + i]? = m'[x + i]?) :
    bytesT8 m x = bytesT8 m' x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT8, h0, h1, h2, h3, h4, h5, h6, h7]

theorem ins_out (m : Mem) (a : Nat) (b : BitVec 8) (x : Nat) (h : x < a ∨ a + 1 ≤ x) :
    (m.insert a b)[x]? = m[x]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-! The forwarding matrix: a `w`-byte load past a store (`wm8`, `wm4`, `wm2`,
`ins`), the side condition a separation over `Nat` (`omega`). -/

theorem fw1_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 1 ≤ a ∨ a + 8 ≤ x) :
    bytesT1 (writeMap8 m a d) x = bytesT1 m x := bT1_congr (getElem?_writeMap8_out m a d x (by omega))
theorem fw1_wm4 {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 1 ≤ a ∨ a + 4 ≤ x) :
    bytesT1 (writeMap4 m a d) x = bytesT1 m x := bT1_congr (getElem?_writeMap4_out m a d x (by omega))
theorem fw1_wm2 {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 1 ≤ a ∨ a + 2 ≤ x) :
    bytesT1 (writeMap2 m a d) x = bytesT1 m x := bT1_congr (getElem?_writeMap2_out m a d x (by omega))
theorem fw1_ins {m : Mem} {a x : Nat} {d : BitVec 8} (h : x + 1 ≤ a ∨ a + 1 ≤ x) :
    bytesT1 (m.insert a d) x = bytesT1 m x := bT1_congr (ins_out m a d x (by omega))

theorem fw2_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 2 ≤ a ∨ a + 8 ≤ x) :
    bytesT2 (writeMap8 m a d) x = bytesT2 m x :=
  bT2_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)
theorem fw2_wm4 {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 2 ≤ a ∨ a + 4 ≤ x) :
    bytesT2 (writeMap4 m a d) x = bytesT2 m x :=
  bT2_congr fun i _ => getElem?_writeMap4_out m a d _ (by omega)
theorem fw2_wm2 {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 2 ≤ a ∨ a + 2 ≤ x) :
    bytesT2 (writeMap2 m a d) x = bytesT2 m x :=
  bT2_congr fun i _ => getElem?_writeMap2_out m a d _ (by omega)
theorem fw2_ins {m : Mem} {a x : Nat} {d : BitVec 8} (h : x + 2 ≤ a ∨ a + 1 ≤ x) :
    bytesT2 (m.insert a d) x = bytesT2 m x :=
  bT2_congr fun i _ => ins_out m a d _ (by omega)

theorem fw4_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 4 ≤ a ∨ a + 8 ≤ x) :
    bytesT4 (writeMap8 m a d) x = bytesT4 m x :=
  bT4_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)
theorem fw4_wm4 {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 4 ≤ a ∨ a + 4 ≤ x) :
    bytesT4 (writeMap4 m a d) x = bytesT4 m x :=
  bT4_congr fun i _ => getElem?_writeMap4_out m a d _ (by omega)
theorem fw4_wm2 {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 4 ≤ a ∨ a + 2 ≤ x) :
    bytesT4 (writeMap2 m a d) x = bytesT4 m x :=
  bT4_congr fun i _ => getElem?_writeMap2_out m a d _ (by omega)
theorem fw4_ins {m : Mem} {a x : Nat} {d : BitVec 8} (h : x + 4 ≤ a ∨ a + 1 ≤ x) :
    bytesT4 (m.insert a d) x = bytesT4 m x :=
  bT4_congr fun i _ => ins_out m a d _ (by omega)

theorem fw8_wm8 {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bT8_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)
theorem fw8_wm4 {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 8 ≤ a ∨ a + 4 ≤ x) :
    bytesT8 (writeMap4 m a d) x = bytesT8 m x :=
  bT8_congr fun i _ => getElem?_writeMap4_out m a d _ (by omega)
theorem fw8_wm2 {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 8 ≤ a ∨ a + 2 ≤ x) :
    bytesT8 (writeMap2 m a d) x = bytesT8 m x :=
  bT8_congr fun i _ => getElem?_writeMap2_out m a d _ (by omega)
theorem fw8_ins {m : Mem} {a x : Nat} {d : BitVec 8} (h : x + 8 ≤ a ∨ a + 1 ≤ x) :
    bytesT8 (m.insert a d) x = bytesT8 m x :=
  bT8_congr fun i _ => ins_out m a d _ (by omega)

/-- The load of what was just stored, at the same width (the address in
another form, `omega`). -/
theorem fw8_same {m : Mem} {a x : Nat} {v : BitVec 64} (h : x = a) :
    bytesT8 (writeMap8 m a (sdData_val v)) x = v := by
  subst h; rw [bytesT8_writeMap8, sdData_id]
theorem fw4_same {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x = a) :
    bytesT4 (writeMap4 m a d) x = d := by subst h; exact Lua.Vm.Sim.Kit.bytesT4_wm4_self m x d
theorem fw2_same {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x = a) :
    bytesT2 (writeMap2 m a d) x = d := by subst h; exact Lua.Vm.Sim.Kit.bytesT2_writeMap2 m x d
theorem fw1_same {m : Mem} {a x : Nat} {d : BitVec 8} (h : x = a) :
    bytesT1 (m.insert a d) x = d := by subst h; simp [bytesT1]

/-- A fact about the root memory, at an address in another form. -/
theorem rd8_of {m : Mem} {a : Nat} {v : BitVec 64} (h : bytesT8 m a = v) {x : Nat} (e : x = a) :
    bytesT8 m x = v := e ▸ h
theorem rd4_of {m : Mem} {a : Nat} {v : BitVec 32} (h : bytesT4 m a = v) {x : Nat} (e : x = a) :
    bytesT4 m x = v := e ▸ h
theorem rd2_of {m : Mem} {a : Nat} {v : BitVec 16} (h : bytesT2 m a = v) {x : Nat} (e : x = a) :
    bytesT2 m x = v := e ▸ h
theorem rd1_of {m : Mem} {a : Nat} {v : BitVec 8} (h : bytesT1 m a = v) {x : Nat} (e : x = a) :
    bytesT1 m x = v := e ▸ h

/-! ## Tactics -/

open Lean Elab Tactic Meta

/-- The reader of a root-memory fact `bytesT<w> m a = v` (for `simp`). -/
def rdOf (ty : Expr) : Option Name :=
  match ty.eq? with
  | some (_, l, _) =>
    if l.isAppOfArity ``bytesT8 2 then some ``rd8_of
    else if l.isAppOfArity ``bytesT4 2 then some ``rd4_of
    else if l.isAppOfArity ``bytesT2 2 then some ``rd2_of
    else if l.isAppOfArity ``bytesT1 2 then some ``rd1_of
    else none
  | none => none

/-- **`fat_rd`**: every load of the goal forwarded through the path's stores
to the root memory (`fw*`, the separations by `omega`), and rewritten by the
root-memory facts in context; addresses normalised to `Nat` first. -/
elab "fat_rd" loc:(Lean.Parser.Tactic.location)? : tactic => withMainContext do
  let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    if let some r := rdOf (← instantiateMVars ld.type) then
      facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent r):ident $(mkIdent ld.userName):ident))
  -- one `simp`: a fact rewritten may expose an address to normalise, and a
  -- normalised address a load to forward
  evalTactic (← `(tactic| (
    simp (disch := omega) only [add_imm, imm_neg_add, BitVec.ofNat_add_ofNat,
      BitVec.toNat_ofNat, Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, Nat.mod_eq_of_lt,
      sext64_id, fw8_same, fw4_same, fw2_same, fw1_same,
      fw1_wm8, fw1_wm4, fw1_wm2, fw1_ins, fw2_wm8, fw2_wm4, fw2_wm2, fw2_ins,
      fw4_wm8, fw4_wm4, fw4_wm2, fw4_ins, fw8_wm8, fw8_wm4, fw8_wm2, fw8_ins, $facts,*] $[$loc]?)))

/-- **The loads of the callee rows** (an `at_eq` extension, tried first):
forwarded and rewritten by `fat_rd`, then closed. -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (fat_rd; first | done | with_reducible rfl | decide))

/-- A post-memory in the row's form: the same stores, the addresses by
`kit_disch`, the data by `at_eq`. -/
theorem wm4_congr {m m' : Mem} {a a' : Nat} {d d' : BitVec (8 * 4)} (hm : m = m')
    (ha : a = a') (hd : d = d') : writeMap4 m a d = writeMap4 m' a' d' := by subst hm ha hd; rfl
theorem wm2_congr {m m' : Mem} {a a' : Nat} {d d' : BitVec (8 * 2)} (hm : m = m')
    (ha : a = a') (hd : d = d') : writeMap2 m a d = writeMap2 m' a' d' := by subst hm ha hd; rfl

open Lean Elab Tactic Meta in
/-- The store at the head of a memory term (`writeMap8`/`4`/`2`, `insert`)
and its congruence lemma. -/
def storeCongr? (e : Expr) : Option Name :=
  if e.isAppOfArity ``writeMap8 3 then some ``At.writeMap8_congr
  else if e.isAppOfArity ``writeMap4 3 then some ``wm4_congr
  else if e.isAppOfArity ``writeMap2 3 then some ``wm2_congr
  else if e.isAppOf ``Std.ExtHashMap.insert then some ``At.insert_congr
  else none

open Lean Elab Tactic Meta in
/-- **`fat_mem`**: a post-memory (the segment's store chain) equal to the
row's memory (an abbreviation): store by store, the addresses by
`kit_disch` and the data by `at_eq`, and the rest syntactically. Never a
`rfl` across a store chain: the stored values hold loads through earlier
stores, and unifying such terms unshared is exponential. -/
partial def fatMem : TacticM Unit := withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, r) := t.eq? | throwError "fat_mem: not an equation"
  -- the row's memory abbreviation unfolded one step (never the stores, which
  -- are themselves reducible)
  let r' ← if (storeCongr? r).isSome then pure r else
    match ← unfoldDefinition? r with
    | some e => pure e.headBeta
    | none => pure r
  match storeCongr? l, storeCongr? r' with
  | some c, some c' =>
    unless c == c' do throwError "fat_mem: different stores"
    if r' != r then
      let g ← getMainGoal
      replaceMainGoal [← g.replaceTargetDefEq (← mkEq l r')]
    evalTactic (← `(tactic| refine $(mkIdent c) ?_ ?_ ?_))
    let gs ← getUnsolvedGoals
    match gs with
    | [gm, ga, gd] =>
      setGoals [gm]; fatMem
      setGoals [ga]; evalTactic (← `(tactic| kit_disch))
      setGoals [gd]; evalTactic (← `(tactic| exact At.un_congr (by at_eq)))
    | _ => throwError "fat_mem: congruence"
  | _, _ => evalTactic (← `(tactic| with_reducible rfl))

elab "fat_mem" : tactic => fatMem

/-- A return target `ra` (aligned) with its low bit cleared. -/
theorem upd_ret0 (r : BitVec 64) (h : r.toNat % 4 = 0) :
    BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1 = r := by
  rw [Vsa.Sim.sext_zero, BitVec.add_zero]; exact Lua.Vm.Sim.Kit.upd_ret r h

/-- A return target: ground, or the aligned `ra` (in a register, or reloaded
from a slot the root facts fix). -/
syntax "fat_ret" : tactic
macro_rules
  | `(tactic| fat_ret) => `(tactic| first
    | with_reducible rfl
    | ground_decide
    | ((try fat_rd)
       first
       | exact upd_ret0 _ (by assumption)
       | exact Lua.Vm.Sim.Kit.upd_ret _ (by assumption)
       | (rw [upd_ret0 _ (by assumption)] <;> assumption)
       | (rw [Lua.Vm.Sim.Kit.upd_ret _ (by assumption)] <;> assumption)))

/-- A segment's side condition: a return target's alignment (`fat_ret`, only
on a goal about `BitVec.update`: a `decide`/`rfl` on an address would unfold
it past the recursion limit, an exception `first` does not catch), an address
(`kit_disch`), or a read the root facts fix. -/
elab "fat_side" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  if (t.find? fun e => e.isConstOf ``Sail.BitVec.update).isSome then
    evalTactic (← `(tactic| fat_ret))
  else
    evalTactic (← `(tactic| first
      | kit_disch
      | (fat_rd; first | done | ground_decide | omega)))

/-- A branch guard the generator decided: the loads by `fat_rd`, then ground. -/
syntax "fat_gnd" : tactic
macro_rules
  | `(tactic| fat_gnd) => `(tactic| first
    | decide
    | (fat_rd; first | done | decide))

/-- A branch guard from the at-lemma's hypothesis about the row's values. -/
macro "fat_guard " h:ident : tactic => `(tactic| first
  | exact $h
  | (refine At.guard_congr (by exact $h) ?_ ?_ <;> at_eq))

/-- The argument syntax of a segment theorem for `fat_seg`: `_` for values,
`(by fat_guard hg_k)` for a guard the at-lemma states, `(by fat_gnd)` for a
decided one, `(by fat_side)` for the rest. -/
def fatSegArgs (n : Name) : TermElabM (Array Term) := do
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
            args := args.push (← `((by fat_guard $(mkIdent (Name.mkSimple nm)))))
          else
            args := args.push (← `((by fat_gnd)))
        else args := args.push (← `((by fat_side)))
      else args := args.push (← `(_))
    return args

/-- **`fat_seg seg`**: the segment `seg` applied at the row `h` (after
`intro c h` and the context's facts). -/
elab "fat_seg " n:ident : tactic => do
  let nm ← realizeGlobalConstNoOverload n
  let args ← withMainContext <| Tactic.runTermElab (fatSegArgs nm)
  let seg ← `($(mkIdent nm) $args*)
  let h := mkIdent `h; let acc := mkIdent `acc
  evalTactic (← `(tactic| have $acc:ident := Vsa.Machine.Steps.refl $(mkIdent `c)))
  evalTactic (← `(tactic|
    obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (by pins_of $h) $seg))

set_option hygiene false in
/-- **`fat_close`**: the post-row (`at_pins`) and post-memory (`fat_mem`),
the pc given by `fat_side` where it is a return target. -/
macro "fat_close" : tactic => `(tactic| (
  -- the post-state normalised once (its values share subterms: one `simp`
  -- with one cache, not one per pin and per store)
  try fat_rd at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin (Vsa.Sim.SegSt.at h (by fat_ret)) ?_).mem_eq ?_⟩
  · at_pins h
  · fat_mem))

set_option hygiene false in
/-- **`fat_call sum`**: a call at-lemma's proof (after `intro c h` and the
context's facts): the summary `sum`, which keeps the memory, at the row, the
return row by `at_pins`. -/
macro "fat_call " sum:term : tactic => `(tactic| (
  have acc := Vsa.Machine.Steps.refl c
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h) $sum
  exact ⟨_, acc, Vsa.Sim.SegSt.repin h (by at_pins h)⟩))

/-! ## Branch guards over `Nat` atoms -/

theorem fult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [zopz0zI_u, BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  simp

theorem fuge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  simp only [zopz0zKzJ_u, BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  simp

theorem fbeq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact e this

theorem fbne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = !decide (a = b) := by
  rw [bne, fbeq ha hb]

/-- A guard between two `Nat`-valued registers, as a fact about the `Nat`s. -/
macro "fat_cmp" : tactic => `(tactic| (
  try simp only [at_row, abiCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fult, fuge, fbeq, fbne, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_false', Bool.not_eq_true]
  try omega))

/-! ## Chaining a callee's at-lemmas -/

/-- The closer of an at-lemma's hypothesis when chaining: a fact in context,
an address bound, or a guard the facts decide. -/
syntax "fat_hyp" : tactic
macro_rules
  | `(tactic| fat_hyp) => `(tactic| first
    | assumption
    | omega
    | (fat_cmp; done)
    | (fat_rd; first | done | decide | assumption))

/-- The arguments of an at-lemma for `fat_run`. -/
def fatRunArgs (n : Name) : TermElabM (Array Term) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut args : Array Term := #[]
    for x in xs do
      let t ← inferType x
      unless (← x.fvarId!.getDecl).binderInfo.isExplicit do continue
      if ← Meta.isProp t then args := args.push (← `((by fat_hyp)))
      else args := args.push (← `(_))
    return args

/-- The (row, memory) names of a `SegSt pc L (ArmPay M o)` type. -/
def segKey (ty : Expr) : MetaM (Name × Name) := do
  let ty ← instantiateMVars ty
  let P := ty.getAppArgs[2]!
  return (At.headName ty.getAppArgs[1]!, At.headName (P.getAppArgs[0]!))

/-- The (row, memory) names an at-lemma (a `Triple`) starts from. -/
def fatLemmaKey (n : Name) : MetaM (Name × Name) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun _ body => do
    if body.isAppOfArity ``Triple 2 then
      let P := body.getAppArgs[0]!
      -- `SegSt pc L Pay` as a predicate (eta-reduced)
      let P := P.eta
      if P.isAppOfArity ``SegSt 3 then
        let pay := P.getAppArgs[2]!
        return (At.headName P.getAppArgs[1]!, At.headName (pay.getAppArgs[0]!))
    return (.anonymous, .anonymous)

/-- **`fat_run ns h acc [stops]`**: from `h : SegSt pc …`, apply the
at-lemmas of `ns` that start at `pc` (the first whose row and memory match
and whose hypotheses `fat_hyp` closes), until a pc that is not a literal (the
callee's own return), or one of `stops`. -/
syntax "fat_run " ident ident ident (" until " "[" num,* "]")? : tactic

elab_rules : tactic
  | `(tactic| fat_run $ns:ident $h:ident $acc:ident $[until [$st,*]]?) => do
  let stops : List Nat := match st with
    | some s => s.getElems.toList.map (·.getNat)
    | none => []
  let mut fuel := 96
  let mut first := true
  while fuel > 0 do
    fuel := fuel - 1
    let (pc, key) ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "fat_run: no {h}"
      return (← segPc ld.type, ← segKey ld.type)
    let some pc := pc | return
    if !first && stops.contains pc then return
    first := false
    let cands ← At.atCands ns.getId pc none
    let mut done := false
    let mut errs : Array MessageData := #[]
    for n in cands do
      unless (← fatLemmaKey n) == key do continue
      let s ← saveState
      try
        let args ← Tactic.runTermElab (fatRunArgs n)
        let lem ← `($(mkIdent n) $args*)
        withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
          obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (Vsa.Sim.SegSt.pins $h) $lem))
        done := true
        break
      catch e =>
        errs := errs.push m!"{n}: {e.toMessageData}"
        s.restore
    unless done do
      if cands.isEmpty || errs.isEmpty then
        throwError "fat_run: no at-lemma at 0x{hex8 pc} for {key}"
      throwError "fat_run: no at-lemma at 0x{hex8 pc} applies:{indentD (MessageData.joinSep errs.toList "\n")}"
  throwError "fat_run: out of fuel"

end Lua.Vm.Sim.AtF
