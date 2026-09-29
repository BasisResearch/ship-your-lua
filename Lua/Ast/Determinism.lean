import Lua.Ast.Semantics

/-!
# Determinism of `LuaSem`

Every F1 source program has at most one output: `Eval`, `EvalList`,
`Exec` and `ForIter` are functional in their inputs. `Exec`/`ForIter` are
proved together by mutual structural recursion on the first derivation.
Translation validation (`Lua/Compile/TV.lean`) uses this to turn one
agreeing output into `∀ out, LuaSem s out ↔ BcSem p out`.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host)

theorem BinOp.arith_cmp_disjoint {op : BinOp} {f g} (hf : op.arith = some f)
    (hg : op.cmp = some g) : False := by
  cases op <;> simp [BinOp.arith, BinOp.cmp] at hf hg

theorem Eval.det {ρ : Env} {e : Expr} {v₁ v₂ : Value} (h₁ : Eval ρ e v₁) (h₂ : Eval ρ e v₂) :
    v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | nil => cases h₂; rfl
  | bool => cases h₂; rfl
  | int => cases h₂; rfl
  | var h => cases h₂ with | var h' => rw [h] at h'; exact Option.some.inj h'
  | arith _ _ hf hr iha ihb =>
    cases h₂ with
    | arith ha' hb' hf' hr' =>
      cases iha ha'; cases ihb hb'; rw [hf] at hf'; cases hf'; rw [hr] at hr'; cases hr'; rfl
    | eq => simp [BinOp.arith] at hf
    | ne => simp [BinOp.arith] at hf
    | cmp _ _ hg => exact (BinOp.arith_cmp_disjoint hf hg).elim
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
    | eq => simp [BinOp.cmp] at hg
    | ne => simp [BinOp.cmp] at hg
  | neg _ ih => cases h₂ with | neg ha' => cases ih ha'; rfl
  | not _ ih => cases h₂ with | not ha' => cases ih ha'; rfl
  | andF _ hf ih =>
    cases h₂ with
    | andF ha' => exact ih ha'
    | andT ha' hf' => cases ih ha'; rw [hf] at hf'; cases hf'
  | andT _ hf _ iha ihb =>
    cases h₂ with
    | andF ha' hf' => cases iha ha'; rw [hf] at hf'; cases hf'
    | andT _ _ hb' => exact ihb hb'
  | orT _ hf ih =>
    cases h₂ with
    | orT ha' => exact ih ha'
    | orF ha' hf' => cases ih ha'; rw [hf] at hf'; cases hf'
  | orF _ hf _ iha ihb =>
    cases h₂ with
    | orT ha' hf' => cases iha ha'; rw [hf] at hf'; cases hf'
    | orF _ _ hb' => exact ihb hb'

theorem EvalList.det {ρ : Env} {es : List Expr} {vs₁ vs₂ : List Value}
    (h₁ : EvalList ρ es vs₁) (h₂ : EvalList ρ es vs₂) : vs₁ = vs₂ := by
  induction h₁ generalizing vs₂ with
  | nil => cases h₂; rfl
  | cons he _ ih => cases h₂ with | cons he' hes' => rw [Eval.det he he', ih hes']

/-- The final configuration of a statement list. -/
structure Exec.Same (ρ₁ ρ₂ : Env) (o₁ o₂ : String) (sg₁ sg₂ : Sig) : Prop where
  env : ρ₁ = ρ₂
  out : o₁ = o₂
  sig : sg₁ = sg₂

variable {H : Host}

mutual
theorem Exec.det {ρ : Env} {o : String} {ss : List Stat} {ρ₁ ρ₂ : Env} {o₁ o₂ : String}
    {sg₁ sg₂ : Sig} (h₁ : Exec H ρ o ss ρ₁ o₁ sg₁) (h₂ : Exec H ρ o ss ρ₂ o₂ sg₂) :
    Exec.Same ρ₁ ρ₂ o₁ o₂ sg₁ sg₂ := by
  match h₁ with
  | .nil => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .local_ he hr => cases h₂ with | local_ he' hr' => cases Eval.det he he'; exact Exec.det hr hr'
  | .locals he hr =>
    cases h₂ with | locals he' hr' => cases EvalList.det he he'; exact Exec.det hr hr'
  | .assign he hu hr =>
    cases h₂ with
    | assign he' hu' hr' =>
      cases Eval.det he he'; rw [hu] at hu'; cases hu'; exact Exec.det hr hr'
  | .print he hr => cases h₂ with | print he' hr' => cases EvalList.det he he'; exact Exec.det hr hr'
  | .brk => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | .whileF he hf hr =>
    cases h₂ with
    | whileF _ _ hr' => exact Exec.det hr hr'
    | whileT he' hf' => cases Eval.det he he'; rw [hf] at hf'; cases hf'
    | whileB he' hf' => cases Eval.det he he'; rw [hf] at hf'; cases hf'
  | .whileT he hf hb hr =>
    cases h₂ with
    | whileF he' hf' => cases Eval.det he he'; rw [hf] at hf'; cases hf'
    | whileT _ _ hb' hr' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
    | whileB _ _ hb' => cases (Exec.det hb hb').sig
  | .whileB he hf hb hr =>
    cases h₂ with
    | whileF he' hf' => cases Eval.det he he'; rw [hf] at hf'; cases hf'
    | whileT _ _ hb' => cases (Exec.det hb hb').sig
    | whileB _ _ hb' hr' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
  | .repeatDone hb he hf hr =>
    cases h₂ with
    | repeatDone hb' _ _ hr' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
    | repeatAgain hb' he' hf' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; cases Eval.det he he'; rw [hf] at hf'; cases hf'
    | repeatB hb' => cases (Exec.det hb hb').sig
  | .repeatAgain hb he hf hr =>
    cases h₂ with
    | repeatDone hb' he' hf' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; cases Eval.det he he'; rw [hf] at hf'; cases hf'
    | repeatAgain hb' _ _ hr' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
    | repeatB hb' => cases (Exec.det hb hb').sig
  | .repeatB hb hr =>
    cases h₂ with
    | repeatDone hb' => cases (Exec.det hb hb').sig
    | repeatAgain hb' => cases (Exec.det hb hb').sig
    | repeatB hb' hr' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
  | .ifN he hb hr =>
    cases h₂ with
    | ifN he' hb' hr' =>
      cases Eval.det he he'; obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact Exec.det hr hr'
    | ifB he' hb' => cases Eval.det he he'; cases (Exec.det hb hb').sig
  | .ifB he hb =>
    cases h₂ with
    | ifN he' hb' => cases Eval.det he he'; cases (Exec.det hb hb').sig
    | ifB he' hb' =>
      cases Eval.det he he'; obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact ⟨rfl, rfl, rfl⟩
  | .forSkip h1 h2 h3 _ hc hr =>
    cases h₂ with
    | forSkip _ _ _ _ _ hr' => exact Exec.det hr hr'
    | forRun h1' h2' h3' _ hc' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
  | .forRun h1 h2 h3 _ hc hi hr =>
    cases h₂ with
    | forSkip h1' h2' h3' _ hc' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
    | forRun h1' h2' h3' _ hc' hi' hr' =>
      cases Eval.det h1 h1'; cases Eval.det h2 h2'; cases Eval.det h3 h3'
      rw [hc] at hc'; cases hc'
      obtain ⟨rfl, rfl⟩ := ForIter.det hi hi'
      exact Exec.det hr hr'
termination_by structural h₁

theorem ForIter.det {ρ : Env} {o x : String} {i st n : BitVec 64} {b : List Stat}
    {ρ₁ ρ₂ : Env} {o₁ o₂ : String}
    (h₁ : ForIter H ρ o x i st n b ρ₁ o₁) (h₂ : ForIter H ρ o x i st n b ρ₂ o₂) :
    ρ₁ = ρ₂ ∧ o₁ = o₂ := by
  match h₁ with
  | .last hb hc =>
    cases h₂ with
    | last hb' => obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact ⟨rfl, rfl⟩
    | next hb' hk' =>
      cases (Exec.det hb hb').sig
      rcases hc with hc | hc
      · cases hc
      · exact (hk' hc).elim
  | .next hb hk hi =>
    cases h₂ with
    | last hb' hc' =>
      cases (Exec.det hb hb').sig
      rcases hc' with hc' | hc'
      · cases hc'
      · exact (hk hc').elim
    | next hb' _ hi' =>
      obtain ⟨rfl, rfl, -⟩ := Exec.det hb hb'; exact ForIter.det hi hi'
termination_by structural h₁
end

/-- **`LuaSem` is deterministic.** -/
theorem LuaSem.deterministic {s : Chunk} {o o' : String} (h : LuaSem H s o)
    (h' : LuaSem H s o') : o = o' := by
  obtain ⟨_, he⟩ := h
  obtain ⟨_, he'⟩ := h'
  exact (Exec.det he he').out

end Lua.Ast
