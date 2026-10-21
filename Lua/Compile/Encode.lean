import Lua.Bytecode.Semantics
import Lean.Elab.Tactic.Omega

/-!
# Instruction emission for Layer B

The layouts of `CREATE_ABCk`, `CREATE_ABx` and `CREATE_Ax` in
`lopcodes.h`. Bounded operands make addition equivalent to the C macro's
disjoint bitwise union. These constructors do not silently truncate an
operand: the public checked entry points return `none` on overflow.

This is compiler infrastructure, not a compiler correctness theorem.
-/

namespace Lua.Compile.Encode

open Lua.Bytecode

private theorem opcode_bound (op : OpCode) : op.toNat < 128 := by
  cases op <;> decide

/-- `CREATE_Ax`, with the operands bounded by their encoded widths. -/
def ax (op : OpCode) (x : Fin 33554432) : Word :=
  BitVec.ofNat 32 (op.toNat + 128 * x.val)

/-- `CREATE_ABx`. -/
def abx (op : OpCode) (a : Fin 256) (x : Fin 131072) : Word :=
  ax op ⟨a.val + 256 * x.val, by omega⟩

/-- `CREATE_ABCk`. -/
def abc (op : OpCode) (a b c : Fin 256) (k : Bool) : Word :=
  abx op a ⟨k.toNat + 2 * b.val + 512 * c.val, by cases k <;> simp <;> omega⟩

private theorem ax_value (op : OpCode) (x : Fin 33554432) :
    (ax op x).toNat = op.toNat + 128 * x.val := by
  have := opcode_bound op
  simp only [ax, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem ax_op (op : OpCode) (x : Fin 33554432) : (ax op x).op? = some op := by
  have := opcode_bound op
  simp only [Word.op?, Word.opNum, Word.field, ax_value, Nat.shiftRight_eq_div_pow]
  have h : (op.toNat + 128 * x.val) / 2 ^ 0 % 2 ^ 7 = op.toNat := by omega
  rw [h, OpCode.ofNat?_toNat]

theorem ax_arg (op : OpCode) (x : Fin 33554432) : (ax op x).ax = x.val := by
  have := opcode_bound op
  simp only [Word.ax, Word.field, ax_value, Nat.shiftRight_eq_div_pow]
  omega

theorem abx_a (op : OpCode) (a : Fin 256) (x : Fin 131072) : (abx op a x).a = a.val := by
  have := opcode_bound op
  simp only [Word.a, Word.field, abx, ax_value, Nat.shiftRight_eq_div_pow]
  omega

theorem abx_arg (op : OpCode) (a : Fin 256) (x : Fin 131072) :
    (abx op a x).bx = x.val := by
  have := opcode_bound op
  simp only [Word.bx, Word.field, abx, ax_value, Nat.shiftRight_eq_div_pow]
  omega

/-- All decoded fields of an ABC instruction, packaged for emitter clients. -/
structure ABCFields (w : Word) (op : OpCode) (a b c : Nat) (k : Bool) : Prop where
  opcode : w.op? = some op
  argA : w.a = a
  argB : w.b = b
  argC : w.c = c
  flag : w.k = k

theorem abc_fields (op : OpCode) (a b c : Fin 256) (k : Bool) :
    ABCFields (abc op a b c k) op a.val b.val c.val k := by
  have ho := opcode_bound op
  constructor
  · exact ax_op _ _
  · exact abx_a _ _ _
  · simp only [Word.b, Word.field, abc, abx, ax_value, Nat.shiftRight_eq_div_pow]
    cases k <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · simp only [Word.c, Word.field, abc, abx, ax_value, Nat.shiftRight_eq_div_pow]
    cases k <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · unfold Word.k
    have hk : (abc op a b c k).field 15 1 = k.toNat := by
      simp only [Word.field, abc, abx, ax_value, Nat.shiftRight_eq_div_pow]
      cases k <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    rw [hk]
    cases k <;> rfl

/-- All decoded fields of an Ax instruction. -/
structure AXFields (w : Word) (op : OpCode) (x : Nat) : Prop where
  opcode : w.op? = some op
  arg : w.ax = x

/-- All decoded fields of an ABx instruction. -/
structure ABXFields (w : Word) (op : OpCode) (a x : Nat) : Prop where
  opcode : w.op? = some op
  argA : w.a = a
  arg : w.bx = x

/-- Checked `CREATE_Ax`: rejects operands that would be truncated. -/
def ax? (op : OpCode) (x : Nat) : Option Word :=
  if h : x < 33554432 then some (ax op ⟨x, h⟩) else none

/-- Checked `CREATE_ABx`. -/
def abx? (op : OpCode) (a x : Nat) : Option Word :=
  if h : a < 256 ∧ x < 131072 then some (abx op ⟨a, h.1⟩ ⟨x, h.2⟩) else none

/-- Checked `CREATE_ABCk`; `Bool` enforces the one-bit flag bound. -/
def abc? (op : OpCode) (a b c : Nat) (k : Bool) : Option Word :=
  if h : a < 256 ∧ b < 256 ∧ c < 256 then
    some (abc op ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨c, h.2.2⟩ k)
  else none

theorem ax?_fields {op x w} (h : ax? op x = some w) : AXFields w op x := by
  unfold ax? at h
  split at h
  · cases h
    exact ⟨ax_op _ _, ax_arg _ _⟩
  · contradiction

theorem abx?_fields {op a x w} (h : abx? op a x = some w) : ABXFields w op a x := by
  unfold abx? at h
  split at h
  · cases h
    exact ⟨ax_op _ _, abx_a _ _ _, abx_arg _ _ _⟩
  · contradiction

theorem abc?_fields {op a b c k w} (h : abc? op a b c k = some w) :
    ABCFields w op a b c k := by
  unfold abc? at h
  split at h
  · cases h
    exact abc_fields _ _ _ _ _
  · contradiction

theorem ax?_isSome (op x) : (ax? op x).isSome = true ↔ x < 33554432 := by
  simp [ax?]

theorem abx?_isSome (op a x) :
    (abx? op a x).isSome = true ↔ a < 256 ∧ x < 131072 := by
  simp [abx?]

theorem abc?_isSome (op a b c k) :
    (abc? op a b c k).isSome = true ↔ a < 256 ∧ b < 256 ∧ c < 256 := by
  simp [abc?]

/-- `fixjump`'s inclusive range: the excess-K encoding is asymmetric by one. -/
def JumpFits (off : Int) : Prop :=
  -(Word.offsetSJ : Int) ≤ off ∧ off ≤ 16777216

instance (off : Int) : Decidable (JumpFits off) := inferInstanceAs (Decidable (_ ∧ _))

/-- Checked `codesJ(OP_JMP, off, 0)`. All 25 displacement bits are used;
there is no independent `k` operand for a jump. -/
def sj? (off : Int) : Option Word :=
  if h : JumpFits off then
    some (ax .JMP ⟨(off + Word.offsetSJ).toNat, by
      dsimp [JumpFits, Word.offsetSJ] at h ⊢
      omega⟩)
  else none

/-- The opcode and signed displacement decoded from an emitted jump. -/
structure JumpFields (w : Word) (off : Int) : Prop where
  opcode : w.op? = some .JMP
  arg : w.sj = off

theorem sj?_fields {off w} (h : sj? off = some w) : JumpFields w off := by
  unfold sj? at h
  split at h
  next hf =>
    cases h
    constructor
    · exact ax_op _ _
    · unfold Word.sj
      rw [ax_arg]
      dsimp [JumpFits, Word.offsetSJ] at hf ⊢
      omega
  · contradiction

theorem sj?_isSome (off) : (sj? off).isSome = true ↔ JumpFits off := by
  simp [sj?]

/-- `fixjump`: require an existing JMP and replace its signed displacement.
Natural destinations exclude C's `NO_JUMP = -1` sentinel. Destinations may
be the end of the current code, as when compiling a forward jump. -/
def patchJump? (w : Word) (pc dest : Nat) : Option Word :=
  if w.op? = some .JMP then sj? ((dest : Int) - ((pc : Int) + 1)) else none

theorem patchJump?_isSome (w pc dest) :
    (patchJump? w pc dest).isSome = true ↔
      w.op? = some .JMP ∧ JumpFits ((dest : Int) - ((pc : Int) + 1)) := by
  by_cases ho : w.op? = some .JMP <;> simp [patchJump?, ho, sj?_isSome]

theorem patchJump?_fields {w pc dest w'} (h : patchJump? w pc dest = some w') :
    JumpFields w' ((dest : Int) - ((pc : Int) + 1)) := by
  unfold patchJump? at h
  split at h
  · exact sj?_fields h
  · contradiction

/-- Patching reaches exactly the requested destination in the bytecode
semantics, including backwards jumps and a target at address zero. -/
theorem patchJump?_target {w pc dest w'} (h : patchJump? w pc dest = some w') :
    jumpTo (pc + 1) w'.sj = some dest := by
  have hf := patchJump?_fields h
  rw [hf.arg]
  have ht : (↑(pc + 1) : Int) + ((dest : Int) - ((pc : Int) + 1)) = dest := by omega
  unfold jumpTo
  rw [ht]
  simp

/-- Patch one instruction in a code list, rejecting missing sites, non-JMP
words and displacements outside `fixjump`'s range. -/
def patchJumpAt? (code : List Word) (pc dest : Nat) : Option (List Word) := do
  let w ← code[pc]?
  let w' ← patchJump? w pc dest
  pure (code.set pc w')

theorem patchJumpAt?_isSome (code pc dest) :
    (patchJumpAt? code pc dest).isSome = true ↔
      ∃ w, code[pc]? = some w ∧ w.op? = some .JMP ∧
        JumpFits ((dest : Int) - ((pc : Int) + 1)) := by
  cases hw : code[pc]? <;>
    simp [patchJumpAt?, hw, Option.isSome_bind, patchJump?_isSome]

/-- The patch keeps code length and every other instruction, and the
instruction at the patched site is a JMP with the exact semantic target. -/
structure PatchResult (before after : List Word) (pc dest : Nat) : Prop where
  length : after.length = before.length
  site : ∃ w, after[pc]? = some w ∧ w.op? = some .JMP ∧
    jumpTo (pc + 1) w.sj = some dest
  keep : ∀ i, i ≠ pc → after[i]? = before[i]?

theorem patchJumpAt?_result {code pc dest code'}
    (h : patchJumpAt? code pc dest = some code') : PatchResult code code' pc dest := by
  unfold patchJumpAt? at h
  cases hw : code[pc]? with
  | none => simp [hw] at h
  | some w =>
    cases hp : patchJump? w pc dest with
    | none => simp [hw, hp] at h
    | some w' =>
      simp [hw, hp] at h
      subst code'
      have hi : pc < code.length := List.getElem?_eq_some_iff.mp hw |>.1
      exact ⟨List.length_set, ⟨w', List.getElem?_set_self hi,
        (patchJump?_fields hp).opcode, patchJump?_target hp⟩,
        fun i hn => List.getElem?_set_ne (Ne.symm hn)⟩

end Lua.Compile.Encode
