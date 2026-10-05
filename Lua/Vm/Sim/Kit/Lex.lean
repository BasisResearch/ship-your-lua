import Lua.Vm.Sim.Kit.Str

/-!
# `lexLt` against `l_strcmp`'s chunks (round-4 bake-off, S-SCAN)

`l_strcmp` compares two Lua strings (which may hold `'\0'`) chunk by chunk:
`strcoll` (= `strcmp`) up to the first event (a difference, or `P`'s
`'\0'`), then the chunk lengths (`strlen`), then the next chunk. This file
relates each exit to `lexLt` (`Lua/Bytecode/Semantics.lean`) once, over the
C view of a string (`cb`: its bytes, then `0`).
-/

namespace Lua.Vm.Sim

open Lua.Bytecode

/-- **The C view of a string**: byte `j`, the terminator `0` past the end. -/
def cb (s : List UInt8) (j : Nat) : BitVec 8 :=
  if h : j < s.length then BitVec.ofNat 8 (s[j]'h).toNat else 0#8

/-- The two strings agree below `n`, which is within both. -/
structure Agree (s1 s2 : List UInt8) (n : Nat) : Prop where
  le1 : n ≤ s1.length
  le2 : n ≤ s2.length
  eq : ∀ j (h1 : j < s1.length) (h2 : j < s2.length), j < n → s1[j] = s2[j]

theorem cb_lt {s : List UInt8} {j : Nat} (h : cb s j ≠ 0#8) : j < s.length := by
  unfold cb at h; split at h
  · assumption
  · exact absurd rfl h

theorem cb_toNat_lt (s : List UInt8) (j : Nat) : (cb s j).toNat < 256 := (cb s j).isLt

/-- `lexLt` past a common prefix. -/
theorem lexLt_drop : ∀ (n : Nat) (s1 s2 : List UInt8), Agree s1 s2 n →
    lexLt s1 s2 = lexLt (s1.drop n) (s2.drop n)
  | 0, _, _, _ => rfl
  | n + 1, a :: as, b :: bs, h => by
    have e : a = b := h.eq 0 (by simp) (by simp) (by omega)
    subst e
    have ih := lexLt_drop n as bs ⟨by have := h.le1; simp at this; omega, by have := h.le2; simp at this; omega,
      fun j h1 h2 hj => by have := h.eq (j + 1) (by simp; omega) (by simp; omega) (by omega); simpa using this⟩
    simp [lexLt, ih]
  | n + 1, [], _, h => absurd h.le1 (by simp)
  | n + 1, _ :: _, [], h => absurd h.le2 (by simp)

/-- Agreement extends over one more position with equal C bytes. -/
theorem Agree.step {s1 s2 : List UInt8} {n : Nat} (h : Agree s1 s2 n) (hn1 : n < s1.length)
    (hn2 : n < s2.length) (he : cb s1 n = cb s2 n) : Agree s1 s2 (n + 1) := by
  refine ⟨hn1, hn2, fun j h1 h2 hj => ?_⟩
  rcases Nat.lt_or_ge j n with hj' | hj'
  · exact h.eq j h1 h2 hj'
  · have e : j = n := by omega
    subst e
    unfold cb at he; simp only [hn1, hn2, dite_true] at he
    exact u8_ofNat_inj he

/-- **A chunk scan without events from `i` to `i + k`** keeps the agreement. -/
theorem Agree.scan {s1 s2 : List UInt8} {i k : Nat} (h : Agree s1 s2 i)
    (hok : ∀ j, j < k → cb s1 (i + j) = cb s2 (i + j) ∧ cb s1 (i + j) ≠ 0#8) : Agree s1 s2 (i + k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    have ih := ih fun j hj => hok j (by omega)
    obtain ⟨e, z⟩ := hok k (by omega)
    have l1 := cb_lt z
    have l2 := cb_lt (e ▸ z)
    exact ih.step l1 l2 e

/-- **The first event is a difference**: `lexLt` is the bytes' order. -/
theorem lexLt_of_diff {s1 s2 : List UInt8} {n : Nat} (h : Agree s1 s2 n) (hd : cb s1 n ≠ cb s2 n) :
    lexLt s1 s2 = decide ((cb s1 n).toNat < (cb s2 n).toNat) := by
  rw [lexLt_drop n s1 s2 h]
  have h1 := h.le1; have h2 := h.le2
  unfold cb at hd ⊢
  rcases Nat.lt_or_ge n s1.length with l1 | l1 <;> rcases Nat.lt_or_ge n s2.length with l2 | l2
  · simp only [l1, l2, dite_true] at hd ⊢
    rw [List.drop_eq_getElem_cons l1, List.drop_eq_getElem_cons l2]
    have hne : s1[n] ≠ s2[n] := fun e => hd (by rw [e])
    simp only [lexLt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt s1[n].toNat_lt, Nat.mod_eq_of_lt s2[n].toNat_lt]
    rw [show (s1[n] == s2[n]) = false by simpa using hne]
    simp [UInt8.lt_iff_toNat_lt]
  · have e2 : n = s2.length := by omega
    simp only [l1, show ¬ n < s2.length by omega, dite_true, dite_false] at hd ⊢
    rw [List.drop_eq_getElem_cons l1, List.drop_of_length_le l2]
    simp [lexLt]
  · simp only [l2, show ¬ n < s1.length by omega, dite_true, dite_false] at hd ⊢
    rw [List.drop_of_length_le l1, List.drop_eq_getElem_cons l2]
    have : s2[n].toNat ≠ 0 := fun e => hd (by
      rw [show (0 : Nat) = (0#8 : BitVec 8).toNat from rfl, ← e]; simp)
    simp only [lexLt, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt s2[n].toNat_lt]
    simp; omega
  · simp only [show ¬ n < s1.length by omega, show ¬ n < s2.length by omega, dite_false] at hd
    exact absurd rfl hd

/-- **The first event is a common `'\0'`** at `n`: both strings end there,
or one does, or both continue past an embedded `'\0'`. -/
theorem lexLt_of_zero {s1 s2 : List UInt8} {n : Nat} (h : Agree s1 s2 n) (h1 : cb s1 n = 0#8)
    (h2 : cb s2 n = 0#8) :
    (n = s2.length → lexLt s1 s2 = false) ∧
    (n ≠ s2.length → n = s1.length → lexLt s1 s2 = true) ∧
    (n ≠ s2.length → n ≠ s1.length → Agree s1 s2 (n + 1)) := by
  have l1 := h.le1; have l2 := h.le2
  rw [lexLt_drop n s1 s2 h]
  refine ⟨fun e => ?_, fun e2 e1 => ?_, fun e2 e1 => h.step (by omega) (by omega) (by rw [h1, h2])⟩
  · rw [List.drop_of_length_le (by omega : s2.length ≤ n)]
    rcases (s1.drop n) with _ | ⟨a, as⟩ <;> rfl
  · rw [List.drop_of_length_le (by omega : s1.length ≤ n), List.drop_eq_getElem_cons (by omega : n < s2.length)]
    rfl

end Lua.Vm.Sim
