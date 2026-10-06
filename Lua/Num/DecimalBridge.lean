import Lua.Num.Decimal
import Lua.Bytecode.Semantics
import Lua.Ast.Semantics

/-!
# One `str2int`

`Lua.Num.str2int` (`Lua/Num/Decimal.lean`, the transcription of `l_str2int`)
is the semantics' `str2int`: the bytecode's and the source semantics' copies
are equal to it, so swapping them for it (step S1 of
`abstractions/FLOAT-DESIGN.md`) keeps their behaviour on integers.
-/

namespace Lua.Num

/-- The bytecode semantics' digit scan is `digits` (it is exported from
`Lua.Num`). -/
theorem digits_bytecode : Lua.Bytecode.digits = digits := rfl

/-- The bytecode semantics' `str2int` is `str2int` (it is exported from
`Lua.Num`, FLOAT-DESIGN.md S1). -/
theorem str2int_bytecode : Lua.Bytecode.str2int = str2int := rfl

/-- `digits` as a `takeWhile`: the value, count and rest of the leading
digits. -/
theorem digits_takeWhile (hex : Bool) (s : List UInt8) (a n : Nat) :
    digits hex s a n =
      ((s.takeWhile fun c => (digitVal hex c).isSome).foldl
          (fun a c => a * (if hex then 16 else 10) + (digitVal hex c).getD 0) a,
        n + (s.takeWhile fun c => (digitVal hex c).isSome).length,
        s.drop (s.takeWhile fun c => (digitVal hex c).isSome).length) := by
  induction s generalizing a n with
  | nil => simp [digits]
  | cons c cs ih =>
    cases h : digitVal hex c with
    | none => simp [digits, h]
    | some d =>
      simp only [digits, h, List.takeWhile_cons, Option.isSome_some, ite_true, List.foldl_cons,
        Option.getD_some, List.length_cons, List.drop_succ_cons]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem isSpace_ast : Lua.Ast.isSpace = isSpace := by
  funext c; by_cases h : c = 32 <;> simp [h, Lua.Ast.isSpace, isSpace]

theorem digitVal_ast (hex : Bool) :
    Lua.Ast.digitVal (if hex then 16 else 10) = digitVal hex := by
  funext c; cases hex <;> simp [Lua.Ast.digitVal, digitVal]

theorem dropWhile_nil_iff (p : UInt8 → Bool) (l : List UInt8) :
    l.dropWhile p = [] ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    by_cases h : p c = true <;> simp [h, ih]

/-- `Ast.str2int` after the sign and the base. -/
def astFinal (neg : Bool) (base : Nat) (s : List UInt8) : Option (BitVec 64) :=
  let ds := s.takeWhile fun c => (Lua.Ast.digitVal base c).isSome
  let n := ds.foldl (fun a c => a * base + (Lua.Ast.digitVal base c).getD 0) 0
  if ds = [] ∨ !(s.drop ds.length).all Lua.Ast.isSpace ∨
      (base = 10 ∧ n > 2 ^ 63 - 1 + (if neg then 1 else 0)) then none
  else some (if neg then 0 - BitVec.ofNat 64 n else BitVec.ofNat 64 n)

/-- `str2int` after the sign and the base. -/
def numFinal (neg hex : Bool) (s : List UInt8) : Option (BitVec 64) :=
  let (a, n, rest) := digits hex s 0 0
  if n = 0 ∨ (rest.dropWhile isSpace) ≠ [] ∨ (!hex ∧ 2 ^ 63 - 1 + (if neg then 1 else 0) < a) then
    none
  else some (if neg then 0 - BitVec.ofNat 64 a else BitVec.ofNat 64 a)

theorem final_eq (neg hex : Bool) (s : List UInt8) :
    astFinal neg (if hex then 16 else 10) s = numFinal neg hex s := by
  simp only [astFinal, numFinal, digits_takeWhile, digitVal_ast, isSpace_ast]
  generalize s.takeWhile (fun c => (digitVal hex c).isSome) = ds
  have hall : ((s.drop ds.length).all isSpace = true) ↔ (s.drop ds.length).dropWhile isSpace = [] := by
    simp [dropWhile_nil_iff]
  by_cases h1 : ds = []
  · subst h1; simp
  · by_cases h2 : (s.drop ds.length).all isSpace = true
    · have h2' := hall.1 h2
      cases hex <;> simp [h1, h2, h2', gt_iff_lt]
    · have h2' : ¬ (s.drop ds.length).dropWhile isSpace = [] := fun h => h2 (hall.2 h)
      simp [h1, h2, h2']

/-- `Ast.str2int`'s base prefix. -/
def astPre (s : List UInt8) : Nat × List UInt8 :=
  match s with
  | 48 :: x :: r => if x = 120 ∨ x = 88 then (16, r) else (10, s)
  | r => (10, r)

/-- `str2int`'s base prefix. -/
def numPre (s : List UInt8) : Bool × List UInt8 :=
  match s with
  | 48 :: x :: t => if x == 120 || x == 88 then (true, t) else (false, s)
  | _ => (false, s)

theorem pre_eq (s : List UInt8) :
    astPre s = ((if (numPre s).1 then 16 else 10), (numPre s).2) := by
  unfold astPre numPre
  split
  · rename_i x r
    by_cases hx : x = 120 ∨ x = 88
    · have : (x == 120 || x == 88) = true := by rcases hx with h | h <;> simp [h]
      simp [hx, this]
    · have : (x == 120 || x == 88) = false := by simp at hx; simp [hx.1, hx.2]
      simp [hx, this]
  · rename_i r h
    split
    · simp_all
    · simp

/-- The source semantics' `str2int` is `str2int`. -/
theorem str2int_ast : Lua.Ast.str2int = str2int := by
  funext s
  have ha : Lua.Ast.str2int s =
      (let s := s.dropWhile isSpace
       let (neg, s) := takeSign s
       let (base, s) := astPre s
       astFinal neg base s) := by
    rw [← isSpace_ast]; rfl
  have hn : str2int s =
      (let s := s.dropWhile isSpace
       let (neg, s) := takeSign s
       let (hex, s) := numPre s
       numFinal neg hex s) := rfl
  rw [ha, hn]
  simp only [pre_eq]
  exact final_eq _ _ _

end Lua.Num
