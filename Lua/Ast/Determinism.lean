import Lua.Ast.Semantics

/-!
# Determinism of `LuaSem`

Every source program has at most one output: `Eval`, `EvalList`, `ExecS`,
`ExecL`, `ExecBF`, `ExecB` and `ForIter` are functional in their inputs.
The statement relations are proved together by mutual structural recursion
on the first derivation. Translation validation (`Lua/Compile/TV.lean`)
uses this to turn one agreeing output into `∀ out, LuaSem s out ↔ BcSem p
out`.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host)

theorem BinOp.arith_cmp_disjoint {op : BinOp} {f g} (hf : op.arith = some f)
    (hg : op.cmp = some g) : False := by
  cases op <;> simp [BinOp.arith, BinOp.cmp] at hf hg

theorem Eval.det {ρ : Env} {e : Exp} {v₁ v₂ : Value} (h₁ : Eval ρ e v₁) (h₂ : Eval ρ e v₂) :
    v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | nil => cases h₂; rfl
  | false => cases h₂; rfl
  | true => cases h₂; rfl
  | int => cases h₂; rfl
  | local_ h =>
    cases h₂ with
    | local_ h' => rw [h] at h'; exact Option.some.inj h'
    | global h' => rw [h] at h'; cases h'
  | global h _ hg =>
    cases h₂ with
    | local_ h' => rw [h] at h'; cases h'
    | global _ _ hg' => rw [hg] at hg'; exact Option.some.inj hg'
  | paren _ ih => cases h₂ with | paren h' => exact ih h'
  | arith _ _ hf hr iha ihb =>
    cases h₂ with
    | arith ha' hb' hf' hr' =>
      cases iha ha'; cases ihb hb'; rw [hf] at hf'; cases hf'; rw [hr] at hr'; cases hr'; rfl
    | cmp _ _ hg => exact (BinOp.arith_cmp_disjoint hf hg).elim
    | _ => simp [BinOp.arith] at hf
  | eq _ _ iha ihb =>
    cases h₂ with
    | eq ha' hb' => cases iha ha'; cases ihb hb'; rfl
    | arith _ _ hf => simp [BinOp.arith] at hf
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | ne _ _ iha ihb =>
    cases h₂ with
    | ne ha' hb' => cases iha ha'; cases ihb hb'; rfl
    | arith _ _ hf => simp [BinOp.arith] at hf
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | cmp _ _ hg iha ihb =>
    cases h₂ with
    | cmp ha' hb' hg' => cases iha ha'; cases ihb hb'; rw [hg] at hg'; cases hg'; rfl
    | arith _ _ hf => exact (BinOp.arith_cmp_disjoint hf hg).elim
    | _ => simp [BinOp.cmp] at hg
  | andF _ hf ih =>
    cases h₂ with
    | andF ha' => exact ih ha'
    | andT ha' hf' => cases ih ha'; rw [hf] at hf'; cases hf'
    | arith _ _ hf' => simp [BinOp.arith] at hf'
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | andT _ hf _ iha ihb =>
    cases h₂ with
    | andF ha' hf' => cases iha ha'; rw [hf] at hf'; cases hf'
    | andT _ _ hb' => exact ihb hb'
    | arith _ _ hf' => simp [BinOp.arith] at hf'
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | orT _ hf ih =>
    cases h₂ with
    | orT ha' => exact ih ha'
    | orF ha' hf' => cases ih ha'; rw [hf] at hf'; cases hf'
    | arith _ _ hf' => simp [BinOp.arith] at hf'
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | orF _ hf _ iha ihb =>
    cases h₂ with
    | orT ha' hf' => cases iha ha'; rw [hf] at hf'; cases hf'
    | orF _ _ hb' => exact ihb hb'
    | arith _ _ hf' => simp [BinOp.arith] at hf'
    | cmp _ _ hg => simp [BinOp.cmp] at hg
  | neg _ ih => cases h₂ with | neg ha' => cases ih ha'; rfl
  | bnot _ ih => cases h₂ with | bnot ha' => cases ih ha'; rfl
  | not _ ih => cases h₂ with | not ha' => cases ih ha'; rfl

theorem EvalList.det {ρ : Env} {es : List Exp} {vs₁ vs₂ : List Value}
    (h₁ : EvalList ρ es vs₁) (h₂ : EvalList ρ es vs₂) : vs₁ = vs₂ := by
  induction h₁ generalizing vs₂ with
  | nil => cases h₂; rfl
  | cons he _ ih => cases h₂ with | cons he' hes' => rw [Eval.det he he', ih hes']

/-- The final configuration of a statement, list, block or loop. -/
structure Exec.Same (ρ₁ ρ₂ : Env) (o₁ o₂ : String) (sg₁ sg₂ : Sig) : Prop where
  env : ρ₁ = ρ₂
  out : o₁ = o₂
  sig : sg₁ = sg₂

/-- A condition's truth value decides the branch. -/
private theorem isFalse_cases {ρ c v w} (h : Eval ρ c v) (h' : Eval ρ c w)
    (hv : v.isFalse = true) (hw : w.isFalse = false) : False := by
  cases Eval.det h h'; rw [hv] at hw; cases hw

variable {H : Host}

mutual
theorem ExecS.det {ρ o st ρ₁ o₁ sg₁ ρ₂ o₂ sg₂} (h₁ : ExecS H ρ o st ρ₁ o₁ sg₁)
    (h₂ : ExecS H ρ o st ρ₂ o₂ sg₂) : Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .semi => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .label => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .local_ _ he => cases h₂ with | local_ _ he' => cases EvalList.det he he'; exact ⟨rfl, rfl, rfl⟩
  | .assign he ha =>
    cases h₂ with
    | assign he' ha' => cases EvalList.det he he'; rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl, rfl⟩
  | .callPrint _ he => cases h₂ with | callPrint _ he' => cases EvalList.det he he'; exact ⟨rfl, rfl, rfl⟩
  | .brk => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .goto_ => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .do_ hb => cases h₂ with | do_ hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
  | .whileF hc hf =>
    cases h₂ with
    | whileF => exact ⟨rfl, rfl, rfl⟩
    | whileT hc' hf' => exact (isFalse_cases hc hc' hf hf').elim
    | whileX hc' hf' => exact (isFalse_cases hc hc' hf hf').elim
  | .whileT hc hf hb hr =>
    cases h₂ with
    | whileF hc' hf' => exact (isFalse_cases hc' hc hf' hf).elim
    | whileT _ _ hb' hr' => obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact ExecS.det hr hr'
    | whileX _ _ hb' hs => exact (hs (ExecB.det hb hb').sig.symm).elim
  | .whileX hc hf hb hs =>
    cases h₂ with
    | whileF hc' hf' => exact (isFalse_cases hc' hc hf' hf).elim
    | whileT _ _ hb' => exact (hs (ExecB.det hb hb').sig).elim
    | whileX _ _ hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
  | .repeatDone hb hc hf =>
    cases h₂ with
    | repeatDone hb' => obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
    | repeatAgain hb' hc' hf' =>
      obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact (isFalse_cases hc' hc hf' hf).elim
    | repeatX hb' hs => exact (hs (ExecB.det hb hb').sig.symm).elim
  | .repeatAgain hb hc hf hr =>
    cases h₂ with
    | repeatDone hb' hc' hf' =>
      obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact (isFalse_cases hc hc' hf hf').elim
    | repeatAgain hb' _ _ hr' => obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact ExecS.det hr hr'
    | repeatX hb' hs => exact (hs (ExecB.det hb hb').sig.symm).elim
  | .repeatX hb hs =>
    cases h₂ with
    | repeatDone hb' => exact (hs (ExecB.det hb hb').sig).elim
    | repeatAgain hb' => exact (hs (ExecB.det hb hb').sig).elim
    | repeatX hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
  | .ifT hc hf hb =>
    cases h₂ with
    | ifT _ _ hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
    | ifElseif hc' hf' => exact (isFalse_cases hc' hc hf' hf).elim
    | ifElse hc' hf' => exact (isFalse_cases hc' hc hf' hf).elim
    | ifNone hc' hf' => exact (isFalse_cases hc' hc hf' hf).elim
  | .ifElseif hc hf hr =>
    cases h₂ with
    | ifT hc' hf' => exact (isFalse_cases hc hc' hf hf').elim
    | ifElseif _ _ hr' => exact ExecS.det hr hr'
  | .ifElse hc hf hb =>
    cases h₂ with
    | ifT hc' hf' => exact (isFalse_cases hc hc' hf hf').elim
    | ifElse _ _ hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
  | .ifNone hc hf =>
    cases h₂ with
    | ifT hc' hf' => exact (isFalse_cases hc hc' hf hf').elim
    | ifNone => exact ⟨rfl, rfl, rfl⟩
  | .forSkip h1 h2 h3 _ hc =>
    cases h₂ with
    | forSkip => exact ⟨rfl, rfl, rfl⟩
    | forRun h1' h2' h3' _ hc' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
  | .forRun h1 h2 h3 _ hc hi =>
    cases h₂ with
    | forSkip h1' h2' h3' _ hc' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
    | forRun h1' h2' h3' _ hc' hi' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
      exact ForIter.det hi hi'
termination_by structural h₁

theorem ExecL.det {ρ o ss ρ₁ o₁ sg₁ ρ₂ o₂ sg₂} (h₁ : ExecL H ρ o ss ρ₁ o₁ sg₁)
    (h₂ : ExecL H ρ o ss ρ₂ o₂ sg₂) : Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .cons hs hr =>
    cases h₂ with
    | cons hs' hr' => obtain ⟨rfl, rfl, -⟩ := ExecS.det hs hs'; exact ExecL.det hr hr'
    | stop hs' hn => exact (hn (ExecS.det hs hs').sig.symm).elim
  | .stop hs hn =>
    cases h₂ with
    | cons hs' => exact (hn (ExecS.det hs hs').sig).elim
    | stop hs' => exact ExecS.det hs hs'
termination_by structural h₁

theorem ExecBF.det {base all ρ o ss ρ₁ o₁ sg₁ ρ₂ o₂ sg₂}
    (h₁ : ExecBF H base all ρ o ss ρ₁ o₁ sg₁) (h₂ : ExecBF H base all ρ o ss ρ₂ o₂ sg₂) :
    Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .done hl ht =>
    cases h₂ with
    | done hl' => exact ExecL.det hl hl'
    | jump hl' ht' =>
      obtain ⟨-, -, rfl⟩ := ExecL.det hl hl'; rw [ht] at ht'; cases ht'
  | .jump hl ht hr =>
    cases h₂ with
    | done hl' ht' =>
      obtain ⟨-, -, rfl⟩ := ExecL.det hl hl'; rw [ht] at ht'; cases ht'
    | jump hl' ht' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := ExecL.det hl hl'; rw [ht] at ht'; cases ht'
      exact ExecBF.det hr hr'
termination_by structural h₁

theorem ExecB.det {ρ o b ρ₁ o₁ sg₁ ρ₂ o₂ sg₂} (h₁ : ExecB H ρ o b ρ₁ o₁ sg₁)
    (h₂ : ExecB H ρ o b ρ₂ o₂ sg₂) : Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .mk hf => cases h₂ with | mk hf' => exact ExecBF.det hf hf'
termination_by structural h₁

theorem ForIter.det {ρ o x i st n b ρ₁ o₁ sg₁ ρ₂ o₂ sg₂}
    (h₁ : ForIter H ρ o x i st n b ρ₁ o₁ sg₁) (h₂ : ForIter H ρ o x i st n b ρ₂ o₂ sg₂) :
    Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .last hb hc =>
    cases h₂ with
    | last hb' => obtain ⟨rfl, rfl, rfl⟩ := ExecB.det hb hb'; exact ⟨rfl, rfl, rfl⟩
    | next hb' hk' =>
      cases (ExecB.det hb hb').sig
      rcases hc with hc | hc
      · exact (hc rfl).elim
      · exact (hk' hc).elim
  | .next hb hk hi =>
    cases h₂ with
    | last hb' hc' =>
      cases (ExecB.det hb hb').sig
      rcases hc' with hc' | hc'
      · exact (hc' rfl).elim
      · exact (hk hc').elim
    | next hb' _ hi' =>
      obtain ⟨rfl, rfl, -⟩ := ExecB.det hb hb'; exact ForIter.det hi hi'
termination_by structural h₁
end

/-- **`LuaSem` is deterministic.** -/
theorem LuaSem.deterministic {c : Chunk} {o o' : String} (h : LuaSem H c o)
    (h' : LuaSem H c o') : o = o' := by
  obtain ⟨_, he⟩ := h
  obtain ⟨_, he'⟩ := h'
  exact (ExecB.det he he').out

end Lua.Ast
