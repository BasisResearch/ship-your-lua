import Lua.Ast.Semantics

/-!
# An executable interpreter for F1 source, sound for `LuaSem`

`evalE`/`evalL` evaluate expressions; `execS`/`execL`/`execBF`/`execB`/
`forIter` run statements, statement lists, blocks (resolving `goto`s to
their labels) and numeric-`for` iterations with a fuel bound; `luaRun` runs
a chunk. They are *not* the semantics: `LuaSem` is the inductive relation
(`Lua/Ast/Semantics.lean`). They exist so that the kernel can build
`LuaSem` derivations for concrete programs: `luaRun_sound` turns a
successful run into a derivation, and `decide +kernel` evaluates the run.
This mirrors `Lua/Bytecode/Exec.lean` (`run_sound`, `bcSem_of_run`) for
`BcSem`. The interpreter only has to be sound, not complete.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host Builtin printLine forCount)

/-- An integer binary operator (arithmetic, bitwise, order). -/
def evalIntBin (op : BinOp) : Value → Option Value → Option Value
  | .int x, some (.int y) =>
    match op.arith, op.cmp with
    | some f, _ => (f x y).map .int
    | none, some g => some (.bool (g x y))
    | none, none => none
  | _, _ => none

/-- A binary operator on the left value and (if it is needed) the right
one. -/
def evalBin (op : BinOp) (va : Value) (vb : Option Value) : Option Value :=
  match op with
  | .and => if va.isFalse then some va else vb
  | .or => if va.isFalse then vb else some va
  | .eq => vb.map fun w => .bool (decide (va = w))
  | .ne => vb.map fun w => .bool (decide (va ≠ w))
  | op => evalIntBin op va vb

def evalUn : UnOp → Value → Option Value
  | .neg, .int x => some (.int (0 - x))
  | .bnot, .int x => some (.int (~~~x))
  | .not, v => some (.bool v.isFalse)
  | _, _ => none

/-- A name: the innermost local, else the global `_ENV.x`. -/
def evalName (ρ : Env) (x : Name) : Option Value :=
  match ρ.lookup x with
  | some v => some v
  | none => if ρ.lookup "_ENV" = none then initGlobal x else none

/-- Expression evaluation, computed (`none`: no `Eval` derivation found). -/
def evalE (ρ : Env) : Exp → Option Value
  | .nil => some .nil
  | .false => some (.bool false)
  | .true => some (.bool true)
  | .numeral (.int i) => some (.int i)
  | .prefixexp (.var (.name x)) => evalName ρ x
  | .prefixexp (.paren e) => evalE ρ e
  | .binop op a b =>
    match evalE ρ a with
    | some va => evalBin op va (evalE ρ b)
    | none => none
  | .unop op a =>
    match evalE ρ a with
    | some va => evalUn op va
    | none => none
  | _ => none

/-- An `explist`, left to right. -/
def evalL (ρ : Env) : List Exp → Option (List Value)
  | [] => some []
  | e :: es =>
    match evalE ρ e, evalL ρ es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- A nested block's result, with its locals dropped. -/
def scopeRes (ρ : Env) : Option (Env × String × Sig) → Option (Env × String × Sig)
  | some (ρ₁, o₁, sg) => some (scope ρ ρ₁, o₁, sg)
  | none => none

section
variable (H : Host)

mutual
/-- One statement with `fuel`: the final environment, output and
completion. Every nested run gets one unit less. -/
def execS : Nat → Env → String → Stat → Option (Env × String × Sig)
  | 0, _, _, _ => none
  | n + 1, ρ, o, st =>
    match st with
    | .semi => some (ρ, o, .normal)
    | .label _ => some (ρ, o, .normal)
    | .local_ vars es =>
      if vars.all (·.attrib != .close) then
        match evalL ρ es with
        | some vs => some (bindLocals (vars.map (·.name)) vs ρ, o, .normal)
        | none => none
      else none
    | .assign vars es =>
      match evalL ρ es with
      | some vs =>
        match assignLocals ρ vars vs with
        | some ρ₁ => some (ρ₁, o, .normal)
        | none => none
      | none => none
    | .functioncall (.call f (.explist args)) =>
      match evalE ρ (.prefixexp f), evalL ρ args with
      | some (.builtin .print), some vs => some (ρ, o ++ printLine H vs, .normal)
      | _, _ => none
    | .break_ => some (ρ, o, .brk)
    | .goto_ l => some (ρ, o, .goto_ l)
    | .do_ b =>
      scopeRes ρ (execB n ρ o b)
    | .while_ c b =>
      match evalE ρ c with
      | some v =>
        if v.isFalse then some (ρ, o, .normal)
        else
          match execB n ρ o b with
          | some (ρ₁, o₁, sg) =>
            if sg = .normal then execS n (scope ρ ρ₁) o₁ (.while_ c b)
            else some (scope ρ ρ₁, o₁, sg.exitLoop)
          | none => none
      | none => none
    | .repeat_ b c =>
      match execB n ρ o b with
      | some (ρ₁, o₁, sg) =>
        if sg = .normal then
          match evalE ρ₁ c with
          | some v =>
            if v.isFalse then execS n (scope ρ ρ₁) o₁ (.repeat_ b c)
            else some (scope ρ ρ₁, o₁, .normal)
          | none => none
        else some (scope ρ ρ₁, o₁, sg.exitLoop)
      | none => none
    | .if_ c t eifs els =>
      match evalE ρ c with
      | some v =>
        if v.isFalse then
          match eifs, els with
          | (c', t') :: eifs', _ => execS n ρ o (.if_ c' t' eifs' els)
          | [], some b =>
            scopeRes ρ (execB n ρ o b)
          | [], none => some (ρ, o, .normal)
        else
          scopeRes ρ (execB n ρ o t)
      | none => none
    | .fornum x e₁ e₂ e₃ b =>
      match evalE ρ e₁, evalE ρ e₂, evalE ρ (Stat.forStep e₃) with
      | some (.int i), some (.int l), some (.int st) =>
        if st = 0 then none
        else
          match forCount i l st with
          | none => some (ρ, o, .normal)
          | some k => forIter n ρ o x i st k b
      | _, _, _ => none
    | _ => none

/-- A statement list, stopping at the first abrupt completion. -/
def execL : Nat → Env → String → List Stat → Option (Env × String × Sig)
  | 0, _, _, _ => none
  | _ + 1, ρ, o, [] => some (ρ, o, .normal)
  | n + 1, ρ, o, st :: ss =>
    match execS n ρ o st with
    | some (ρ₁, o₁, sg) => if sg = .normal then execL n ρ₁ o₁ ss else some (ρ₁, o₁, sg)
    | none => none

/-- A block from a suffix of its statements, resolving `goto`s to its
labels. -/
def execBF : Nat → Env → List Stat → Env → String → List Stat → Option (Env × String × Sig)
  | 0, _, _, _, _, _ => none
  | n + 1, base, all, ρ, o, ss =>
    match execL n ρ o ss with
    | some (ρ₁, o₁, sg) =>
      match sg.target all with
      | none => some (ρ₁, o₁, sg)
      | some (rest, k) => execBF n base all (jumpEnv base k ρ₁) o₁ rest
    | none => none

def execB : Nat → Env → String → Block → Option (Env × String × Sig)
  | 0, _, _, _ => none
  | n + 1, ρ, o, .mk ss none => execBF n ρ ss ρ o ss
  | _ + 1, _, _, .mk _ (some _) => none

/-- The iterations of a numeric `for` from control value `i` with `k`
further iterations (the bytecode's count). -/
def forIter : Nat → Env → String → Name → BitVec 64 → BitVec 64 → BitVec 64 → Block →
    Option (Env × String × Sig)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, ρ, o, x, i, st, k, b =>
    match execB n ((x, .int i) :: ρ) o b with
    | some (ρ₁, o₁, sg) =>
      if sg ≠ .normal ∨ k = 0 then some (scope ρ ρ₁, o₁, sg.exitLoop)
      else forIter n (scope ρ ρ₁) o₁ x (i + st) st (k - 1) b
    | none => none
end

end

/-- Run a chunk from the empty environment: its output, if it completes
normally within `fuel`. -/
def luaRun (H : Host) (fuel : Nat) (c : Chunk) : Option String :=
  match execB H fuel [] "" c with
  | some (_, out, .normal) => some out
  | _ => none

/-! ## Soundness -/

section Soundness
variable {H : Host}

theorem evalName_sound {ρ : Env} {x : Name} {v : Value} (h : evalName ρ x = some v) :
    Eval ρ (.prefixexp (.var (.name x))) v := by
  unfold evalName at h
  split at h
  · rename_i w hw; cases h; exact .local_ hw
  · rename_i hx
    split at h
    · rename_i he; exact .global hx he h
    · cases h

theorem evalBin_sound {ρ : Env} {op : BinOp} {a b : Exp} {va v : Value} {vb : Option Value}
    (h : evalBin op va vb = some v) (ha : Eval ρ a va) (hb : ∀ w, vb = some w → Eval ρ b w) :
    Eval ρ (.binop op a b) v := by
  have gen : ∀ {op : BinOp}, evalIntBin op va vb = some v → Eval ρ (.binop op a b) v := by
    intro op h
    cases va with
    | int x =>
      cases vb with
      | some w =>
        cases w with
        | int y =>
          have eb := hb _ rfl
          simp only [evalIntBin] at h
          cases hf : op.arith with
          | some f =>
            simp only [hf] at h
            cases hr : f x y with
            | none => simp [hr] at h
            | some r =>
              simp only [hr, Option.map_some, Option.some.injEq] at h
              subst h; exact .arith ha eb hf hr
          | none =>
            cases hg : op.cmp with
            | some g => simp only [hf, hg, Option.some.injEq] at h; subst h; exact .cmp ha eb hg
            | none => simp [hf, hg] at h
        | _ => simp [evalIntBin] at h
      | none => simp [evalIntBin] at h
    | _ => simp [evalIntBin] at h
  cases op with
  | and =>
    simp only [evalBin] at h
    split at h
    · rename_i hf; cases h; exact .andF ha hf
    · rename_i hf; exact .andT ha (Bool.eq_false_iff.mpr hf) (hb _ h)
  | or =>
    simp only [evalBin] at h
    split at h
    · rename_i hf; exact .orF ha hf (hb _ h)
    · rename_i hf; cases h; exact .orT ha (Bool.eq_false_iff.mpr hf)
  | eq =>
    simp only [evalBin] at h
    cases hv : vb with
    | none => simp [hv] at h
    | some w => simp only [hv, Option.map_some, Option.some.injEq] at h; subst h; exact .eq ha (hb _ hv)
  | ne =>
    simp only [evalBin] at h
    cases hv : vb with
    | none => simp [hv] at h
    | some w => simp only [hv, Option.map_some, Option.some.injEq] at h; subst h; exact .ne ha (hb _ hv)
  | _ => simp only [evalBin] at h; exact gen h

theorem evalUn_sound {ρ : Env} {op : UnOp} {a : Exp} {va v : Value} (h : evalUn op va = some v)
    (ha : Eval ρ a va) : Eval ρ (.unop op a) v := by
  cases op <;> cases va <;> simp only [evalUn, Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first | exact .neg ha | exact .bnot ha | exact .not ha

theorem evalE_sound {ρ : Env} : ∀ {e : Exp} {v : Value}, evalE ρ e = some v → Eval ρ e v
  | .nil, v, h => by cases h; exact .nil
  | .false, v, h => by cases h; exact .false
  | .true, v, h => by cases h; exact .true
  | .numeral (.int i), v, h => by cases h; exact .int
  | .prefixexp (.var (.name x)), v, h => evalName_sound h
  | .prefixexp (.paren e), v, h => .paren (evalE_sound h)
  | .binop op a b, v, h => by
    simp only [evalE] at h
    split at h
    · rename_i va ha
      exact evalBin_sound h (evalE_sound ha) fun w hw => evalE_sound hw
    · cases h
  | .unop op a, v, h => by
    simp only [evalE] at h
    split at h
    · rename_i va ha; exact evalUn_sound h (evalE_sound ha)
    · cases h
  | .numeral (.float _), v, h => by simp [evalE] at h
  | .string _, v, h => by simp [evalE] at h
  | .vararg, v, h => by simp [evalE] at h
  | .functiondef _, v, h => by simp [evalE] at h
  | .tableconstructor _, v, h => by simp [evalE] at h
  | .prefixexp (.functioncall _), v, h => by simp [evalE] at h
  | .prefixexp (.var (.index _ _)), v, h => by simp [evalE] at h
  | .prefixexp (.var (.field _ _)), v, h => by simp [evalE] at h

theorem evalL_sound {ρ : Env} : ∀ {es : List Exp} {vs : List Value},
    evalL ρ es = some vs → EvalList ρ es vs
  | [], vs, h => by cases h; exact .nil
  | e :: es, vs, h => by
    unfold evalL at h
    split at h
    · rename_i v vs' he hes; cases h; exact .cons (evalE_sound he) (evalL_sound hes)
    · cases h

/-- Soundness of the statement interpreters at one fuel. -/
structure ExecSound (H : Host) (n : Nat) : Prop where
  stat : ∀ {ρ o st ρ' o' sg}, execS H n ρ o st = some (ρ', o', sg) → ExecS H ρ o st ρ' o' sg
  list : ∀ {ρ o ss ρ' o' sg}, execL H n ρ o ss = some (ρ', o', sg) → ExecL H ρ o ss ρ' o' sg
  blockFrom : ∀ {base all ρ o ss ρ' o' sg}, execBF H n base all ρ o ss = some (ρ', o', sg) →
    ExecBF H base all ρ o ss ρ' o' sg
  block : ∀ {ρ o b ρ' o' sg}, execB H n ρ o b = some (ρ', o', sg) → ExecB H ρ o b ρ' o' sg
  forIter : ∀ {ρ o x i st k b ρ' o' sg}, forIter H n ρ o x i st k b = some (ρ', o', sg) →
    ForIter H ρ o x i st k b ρ' o' sg

/-- A nested block's result, scoped. -/
private theorem scopeRes_some {ρ : Env} {r : Option (Env × String × Sig)} {ρ' o' sg}
    (h : scopeRes ρ r = some (ρ', o', sg)) :
    ∃ ρ₁, r = some (ρ₁, o', sg) ∧ ρ' = scope ρ ρ₁ := by
  cases r with
  | none => simp [scopeRes] at h
  | some t =>
    obtain ⟨ρ₁, o₁, sg₁⟩ := t
    simp only [scopeRes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ρ₁, rfl, rfl⟩

/-- Soundness of `execS`/`execL`/`execBF`/`execB`/`forIter` at every fuel,
together (they are mutually recursive). -/
theorem execSound : ∀ n, ExecSound H n
  | 0 => ⟨fun h => by simp [execS] at h, fun h => by simp [execL] at h,
          fun h => by simp [execBF] at h, fun h => by simp [execB] at h,
          fun h => by simp [forIter] at h⟩
  | n + 1 => by
    obtain ⟨ihS, ihL, ihBF, ihB, ihF⟩ := execSound n
    refine ⟨fun {ρ o st ρ' o' sg} h => ?_, fun {ρ o ss ρ' o' sg} h => ?_,
      fun {base all ρ o ss ρ' o' sg} h => ?_, fun {ρ o b ρ' o' sg} h => ?_,
      fun {ρ o x i st k b ρ' o' sg} h => ?_⟩
    · -- execS
      cases st with
      | semi =>
        simp only [execS, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .semi
      | label l =>
        simp only [execS, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .label
      | local_ vars es =>
        simp only [execS] at h
        split at h
        · rename_i hc
          split at h
          · rename_i vs hv
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact .local_ hc (evalL_sound hv)
          · cases h
        · cases h
      | assign vars es =>
        simp only [execS] at h
        split at h
        · rename_i vs hv
          split at h
          · rename_i ρ₁ ha
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact .assign (evalL_sound hv) ha
          · cases h
        · cases h
      | functioncall c =>
        cases c with
        | call f args =>
          cases args with
          | explist args =>
            simp only [execS] at h
            split at h
            · rename_i vs hf hv
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h; exact .callPrint (evalE_sound hf) (evalL_sound hv)
            · cases h
          | tableconstructor _ => simp [execS] at h
          | string _ => simp [execS] at h
        | method _ _ _ => simp [execS] at h
      | break_ =>
        simp only [execS, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .brk
      | goto_ l =>
        simp only [execS, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .goto_
      | do_ b =>
        simp only [execS] at h
        obtain ⟨ρ₁, hb, rfl⟩ := scopeRes_some h
        exact .do_ (ihB hb)
      | while_ c b =>
        simp only [execS] at h
        split at h
        · rename_i v hv
          split at h
          · rename_i hf
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact .whileF (evalE_sound hv) hf
          · rename_i hf
            have hf' := Bool.eq_false_iff.mpr hf
            split at h
            · rename_i ρ₁ o₁ sg₁ hb
              split at h
              · rename_i hs; subst hs; exact .whileT (evalE_sound hv) hf' (ihB hb) (ihS h)
              · rename_i hs
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h; exact .whileX (evalE_sound hv) hf' (ihB hb) hs
            · cases h
        · cases h
      | repeat_ b c =>
        simp only [execS] at h
        split at h
        · rename_i ρ₁ o₁ sg₁ hb
          split at h
          · rename_i hs; subst hs
            split at h
            · rename_i v hv
              split at h
              · rename_i hf; exact .repeatAgain (ihB hb) (evalE_sound hv) hf (ihS h)
              · rename_i hf
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .repeatDone (ihB hb) (evalE_sound hv) (Bool.eq_false_iff.mpr hf)
            · cases h
          · rename_i hs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact .repeatX (ihB hb) hs
        · cases h
      | if_ c t eifs els =>
        simp only [execS] at h
        split at h
        · rename_i v hv
          split at h
          · rename_i hf
            split at h
            · exact .ifElseif (evalE_sound hv) hf (ihS h)
            · obtain ⟨ρ₁, hb, rfl⟩ := scopeRes_some h
              exact .ifElse (evalE_sound hv) hf (ihB hb)
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h; exact .ifNone (evalE_sound hv) hf
          · rename_i hf
            obtain ⟨ρ₁, hb, rfl⟩ := scopeRes_some h
            exact .ifT (evalE_sound hv) (Bool.eq_false_iff.mpr hf) (ihB hb)
        · cases h
      | fornum x e₁ e₂ e₃ b =>
        simp only [execS] at h
        split at h
        · rename_i i l st h₁ h₂ h₃
          split at h
          · cases h
          · rename_i hst
            split at h
            · rename_i hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact .forSkip (evalE_sound h₁) (evalE_sound h₂) (evalE_sound h₃) hst hc
            · rename_i k hc
              exact .forRun (evalE_sound h₁) (evalE_sound h₂) (evalE_sound h₃) hst hc (ihF h)
        · cases h
      | forin _ _ _ => simp [execS] at h
      | function_ _ _ => simp [execS] at h
      | localfunction _ _ => simp [execS] at h
    · -- execL
      cases ss with
      | nil =>
        simp only [execL, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .nil
      | cons st ss =>
        simp only [execL] at h
        split at h
        · rename_i ρ₁ o₁ sg₁ hs
          split at h
          · rename_i he; subst he; exact .cons (ihS hs) (ihL h)
          · rename_i he
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h; exact .stop (ihS hs) he
        · cases h
    · -- execBF
      simp only [execBF] at h
      split at h
      · rename_i ρ₁ o₁ sg₁ hl
        split at h
        · rename_i ht
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h; exact .done (ihL hl) ht
        · rename_i rest k ht; exact .jump (ihL hl) ht (ihBF h)
      · cases h
    · -- execB
      cases b with
      | mk ss ret =>
        cases ret with
        | none => simp only [execB] at h; exact .mk (ihBF h)
        | some _ => simp [execB] at h
    · -- forIter
      simp only [forIter] at h
      split at h
      · rename_i ρ₁ o₁ sg₁ hb
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .last (ihB hb) hc
        · rename_i hc
          have hk : k ≠ 0 := fun hk => hc (Or.inr hk)
          have hsg : sg₁ = .normal := Classical.byContradiction fun hs => hc (Or.inl hs)
          subst hsg
          exact .next (ihB hb) hk (ihF h)
      · cases h

/-- **Validation route**: a successful run of the interpreter is a
`LuaSem` derivation. -/
theorem luaRun_sound {fuel : Nat} {c : Chunk} {out : String}
    (h : luaRun H fuel c = some out) : LuaSem H c out := by
  unfold luaRun at h
  split at h
  · rename_i ρ' out' he
    cases h
    exact ⟨ρ', (execSound fuel).block he⟩
  · cases h

end Soundness

end Lua.Ast
