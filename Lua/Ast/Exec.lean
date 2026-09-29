import Lua.Ast.Semantics

/-!
# An executable interpreter for F1 source, sound for `LuaSem`

`evalE`/`evalL` evaluate expressions; `exec`/`forIter` run statement lists
and numeric-`for` iterations with a fuel bound; `luaRun` runs a chunk. They
are *not* the semantics: `LuaSem` is the inductive relation
(`Lua/Ast/Semantics.lean`). They exist so that the kernel can build
`LuaSem` derivations for concrete programs: `luaRun_sound` turns a
successful run into a derivation, and `decide +kernel` evaluates the run.
This mirrors `Lua/Bytecode/Exec.lean` (`run_sound`, `bcSem_of_run`) for
`BcSem`. The interpreter only has to be sound, not complete.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host printLine forCount)

/-- Expression evaluation, computed (`none`: no `Eval` derivation found). -/
def evalE (ρ : Env) : Expr → Option Value
  | .nil => some .nil
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .var x => ρ.lookup x
  | .binop op a b =>
    match evalE ρ a, evalE ρ b with
    | some va, some vb =>
      match op with
      | .eq => some (.bool (decide (va = vb)))
      | .ne => some (.bool (decide (va ≠ vb)))
      | op =>
        match va, vb with
        | .int x, .int y =>
          match op.arith, op.cmp with
          | some f, _ => (f x y).map .int
          | none, some f => some (.bool (f x y))
          | none, none => none
        | _, _ => none
    | _, _ => none
  | .neg a =>
    match evalE ρ a with
    | some (.int x) => some (.int (0 - x))
    | _ => none
  | .not a => (evalE ρ a).map fun v => .bool v.isFalse
  | .and a b =>
    match evalE ρ a with
    | some v => if v.isFalse then some v else evalE ρ b
    | none => none
  | .or a b =>
    match evalE ρ a with
    | some v => if v.isFalse then evalE ρ b else some v
    | none => none

/-- Argument lists, left to right. -/
def evalL (ρ : Env) : List Expr → Option (List Value)
  | [] => some []
  | e :: es =>
    match evalE ρ e, evalL ρ es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

mutual
/-- Run a statement list with `fuel`: the final environment, output and
completion. Every nested run (loop body, loop continuation, rest of the
list) gets one unit less. -/
def exec (H : Host) : Nat → Env → String → List Stat → Option (Env × String × Sig)
  | 0, _, _, _ => none
  | _ + 1, ρ, o, [] => some (ρ, o, .normal)
  | n + 1, ρ, o, st :: ss =>
    match st with
    | .local_ x e =>
      match evalE ρ e with
      | some v => exec H n ((x, v) :: ρ) o ss
      | none => none
    | .locals xs es =>
      match evalL ρ es with
      | some vs => exec H n (bindLocals xs vs ρ) o ss
      | none => none
    | .assign x e =>
      match evalE ρ e with
      | some v =>
        match ρ.update x v with
        | some ρ₁ => exec H n ρ₁ o ss
        | none => none
      | none => none
    | .print args =>
      match evalL ρ args with
      | some vs => exec H n ρ (o ++ printLine H vs) ss
      | none => none
    | .break_ => some (ρ, o, .brk)
    | .while_ c b =>
      match evalE ρ c with
      | some v =>
        if v.isFalse then exec H n ρ o ss
        else
          match exec H n ρ o b with
          | some (ρ₁, o₁, .normal) => exec H n (scope ρ ρ₁) o₁ (.while_ c b :: ss)
          | some (ρ₁, o₁, .brk) => exec H n (scope ρ ρ₁) o₁ ss
          | none => none
      | none => none
    | .repeat_ b c =>
      match exec H n ρ o b with
      | some (ρ₁, o₁, .normal) =>
        match evalE ρ₁ c with
        | some v =>
          if v.isFalse then exec H n (scope ρ ρ₁) o₁ (.repeat_ b c :: ss)
          else exec H n (scope ρ ρ₁) o₁ ss
        | none => none
      | some (ρ₁, o₁, .brk) => exec H n (scope ρ ρ₁) o₁ ss
      | none => none
    | .if_ c t e =>
      match evalE ρ c with
      | some v =>
        match exec H n ρ o (if v.isFalse then e else t) with
        | some (ρ₁, o₁, .normal) => exec H n (scope ρ ρ₁) o₁ ss
        | some (ρ₁, o₁, .brk) => some (scope ρ ρ₁, o₁, .brk)
        | none => none
      | none => none
    | .numFor x e₁ e₂ e₃ b =>
      match evalE ρ e₁, evalE ρ e₂, evalE ρ e₃ with
      | some (.int i), some (.int l), some (.int st) =>
        if st = 0 then none
        else
          match forCount i l st with
          | none => exec H n ρ o ss
          | some k =>
            match forIter H n ρ o x i st k b with
            | some (ρ₁, o₁) => exec H n ρ₁ o₁ ss
            | none => none
      | _, _, _ => none

/-- The iterations of a numeric `for` from control value `i` with `k`
further iterations (the bytecode's count). -/
def forIter (H : Host) : Nat → Env → String → String → BitVec 64 → BitVec 64 → BitVec 64 →
    List Stat → Option (Env × String)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, ρ, o, x, i, st, k, b =>
    match exec H n ((x, .int i) :: ρ) o b with
    | some (ρ₁, o₁, sg) =>
      if sg = .brk ∨ k = 0 then some (scope ρ ρ₁, o₁)
      else forIter H n (scope ρ ρ₁) o₁ x (i + st) st (k - 1) b
    | none => none
end

/-- Run a chunk from the empty environment: its output, if it completes
normally within `fuel`. -/
def luaRun (H : Host) (fuel : Nat) (s : Chunk) : Option String :=
  match exec H fuel [] "" s with
  | some (_, out, .normal) => some out
  | _ => none

/-! ## Soundness -/

section Soundness
variable {H : Host}

theorem evalE_sound {ρ : Env} : ∀ {e : Expr} {v : Value}, evalE ρ e = some v → Eval ρ e v
  | .nil, v, h => by cases h; exact .nil
  | .bool b, v, h => by cases h; exact .bool
  | .int i, v, h => by cases h; exact .int
  | .var x, v, h => .var h
  | .binop op a b, v, h => by
    unfold evalE at h
    split at h
    · rename_i va vb ha hb
      have ea := evalE_sound ha
      have eb := evalE_sound hb
      split at h
      · cases h; exact .eq ea eb
      · cases h; exact .ne ea eb
      · split at h
        · rename_i x y
          split at h
          · rename_i f hf
            cases hr : f x y with
            | none => simp [hr] at h
            | some r =>
              simp only [hr, Option.map_some, Option.some.injEq] at h
              subst h; exact .arith ea eb hf hr
          · rename_i f _ hf
            cases h; exact .cmp ea eb hf
          · cases h
        · cases h
    · cases h
  | .neg a, v, h => by
    unfold evalE at h
    split at h
    · rename_i x hx; cases h; exact .neg (evalE_sound hx)
    · cases h
  | .not a, v, h => by
    unfold evalE at h
    cases ha : evalE ρ a with
    | none => simp [ha] at h
    | some w =>
      simp only [ha, Option.map_some, Option.some.injEq] at h
      subst h; exact .not (evalE_sound ha)
  | .and a b, v, h => by
    unfold evalE at h
    split at h
    · rename_i w hw
      split at h
      · rename_i hf; cases h; exact .andF (evalE_sound hw) hf
      · rename_i hf
        exact .andT (evalE_sound hw) (Bool.eq_false_iff.mpr hf) (evalE_sound h)
    · cases h
  | .or a b, v, h => by
    unfold evalE at h
    split at h
    · rename_i w hw
      split at h
      · rename_i hf; exact .orF (evalE_sound hw) hf (evalE_sound h)
      · rename_i hf; cases h; exact .orT (evalE_sound hw) (Bool.eq_false_iff.mpr hf)
    · cases h

theorem evalL_sound {ρ : Env} : ∀ {es : List Expr} {vs : List Value},
    evalL ρ es = some vs → EvalList ρ es vs
  | [], vs, h => by cases h; exact .nil
  | e :: es, vs, h => by
    unfold evalL at h
    split at h
    · rename_i v vs' he hes; cases h; exact .cons (evalE_sound he) (evalL_sound hes)
    · cases h

/-- Soundness of `exec` and `forIter` at every fuel, together (they are
mutually recursive). -/
theorem exec_forIter_sound : ∀ n : Nat,
    (∀ {ρ o ss ρ' o' sg}, exec H n ρ o ss = some (ρ', o', sg) → Exec H ρ o ss ρ' o' sg) ∧
    (∀ {ρ o x i st k b ρ' o'}, forIter H n ρ o x i st k b = some (ρ', o') →
      ForIter H ρ o x i st k b ρ' o')
  | 0 => ⟨fun h => by simp [exec] at h, fun h => by simp [forIter] at h⟩
  | n + 1 => by
    obtain ⟨ihE, ihF⟩ := exec_forIter_sound n
    refine ⟨fun {ρ o ss ρ' o' sg} h => ?_, fun {ρ o x i st k b ρ' o'} h => ?_⟩
    · cases ss with
      | nil => simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl, rfl⟩ := h; exact .nil
      | cons st ss =>
        cases st with
        | local_ x e =>
          simp only [exec] at h
          split at h
          · rename_i v hv; exact .local_ (evalE_sound hv) (ihE h)
          · cases h
        | locals xs es =>
          simp only [exec] at h
          split at h
          · rename_i vs hv; exact .locals (evalL_sound hv) (ihE h)
          · cases h
        | assign x e =>
          simp only [exec] at h
          split at h
          · rename_i v hv
            split at h
            · rename_i ρ₁ hu; exact .assign (evalE_sound hv) hu (ihE h)
            · cases h
          · cases h
        | print args =>
          simp only [exec] at h
          split at h
          · rename_i vs hv; exact .print (evalL_sound hv) (ihE h)
          · cases h
        | break_ =>
          simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h; exact .brk
        | while_ c b =>
          simp only [exec] at h
          split at h
          · rename_i v hv
            split at h
            · rename_i hf; exact .whileF (evalE_sound hv) hf (ihE h)
            · rename_i hf
              have hf' := Bool.eq_false_iff.mpr hf
              split at h
              · rename_i ρ₁ o₁ hb; exact .whileT (evalE_sound hv) hf' (ihE hb) (ihE h)
              · rename_i ρ₁ o₁ hb; exact .whileB (evalE_sound hv) hf' (ihE hb) (ihE h)
              · cases h
          · cases h
        | repeat_ b c =>
          simp only [exec] at h
          split at h
          · rename_i ρ₁ o₁ hb
            split at h
            · rename_i v hv
              split at h
              · rename_i hf; exact .repeatAgain (ihE hb) (evalE_sound hv) hf (ihE h)
              · rename_i hf
                exact .repeatDone (ihE hb) (evalE_sound hv) (Bool.eq_false_iff.mpr hf) (ihE h)
            · cases h
          · rename_i ρ₁ o₁ hb; exact .repeatB (ihE hb) (ihE h)
          · cases h
        | if_ c t e =>
          simp only [exec] at h
          split at h
          · rename_i v hv
            split at h
            · rename_i ρ₁ o₁ hb; exact .ifN (evalE_sound hv) (ihE hb) (ihE h)
            · rename_i ρ₁ o₁ hb
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h; exact .ifB (evalE_sound hv) (ihE hb)
            · cases h
          · cases h
        | numFor x e₁ e₂ e₃ b =>
          simp only [exec] at h
          split at h
          · rename_i i l st h₁ h₂ h₃
            split at h
            · cases h
            · rename_i hst
              split at h
              · rename_i hc
                exact .forSkip (evalE_sound h₁) (evalE_sound h₂) (evalE_sound h₃) hst hc (ihE h)
              · rename_i k hc
                split at h
                · rename_i ρ₁ o₁ hi
                  exact .forRun (evalE_sound h₁) (evalE_sound h₂) (evalE_sound h₃) hst hc
                    (ihF hi) (ihE h)
                · cases h
          · cases h
    · simp only [forIter] at h
      split at h
      · rename_i ρ₁ o₁ sg hb
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .last (ihE hb) hc
        · rename_i hc
          have hk : k ≠ 0 := fun hk => hc (Or.inr hk)
          have hsg : sg = .normal := by cases sg <;> simp_all
          subst hsg
          exact .next (ihE hb) hk (ihF h)
      · cases h

/-- **Validation route**: a successful run of the interpreter is a
`LuaSem` derivation. -/
theorem luaRun_sound {fuel : Nat} {s : Chunk} {out : String}
    (h : luaRun H fuel s = some out) : LuaSem H s out := by
  unfold luaRun at h
  split at h
  · rename_i ρ' out' he
    cases h
    exact ⟨ρ', (exec_forIter_sound fuel).1 he⟩
  · cases h

end Soundness

end Lua.Ast
