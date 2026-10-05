import Lua.Bytecode.Semantics

/-!
# `luaV_idiv` in `lvm.c`'s branch order (M1)

`idiv` (`Lua/Bytecode/Semantics.lean`) is floor division over `Int`. The
machine computes it as `lvm.c`'s `luaV_idiv` does: the C quotient `m / n`
(`__divdi3`, `BitVec.sdiv`), decremented when the signs differ
(`(m ^ n) < 0`) and the C remainder `m % n` (`__moddi3`, `BitVec.srem`) is
nonzero. `idivC_eq` is that restatement, one equation; `idiv_m1` the
`n = -1` exit (`0 - m`).
-/

namespace Lua.Vm.Sim.Kit

open Lua.Bytecode

theorem srem_eq_zero_iff (m n : BitVec 64) : m.srem n = 0#64 ↔ n.toInt ∣ m.toInt := by
  rw [Int.dvd_iff_tmod_eq_zero, ← BitVec.toInt_srem]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact BitVec.eq_of_toInt_eq (by rw [h]; rfl)

/-- **`luaV_idiv`, as the machine computes it.** -/
theorem idivC_eq (m n : BitVec 64) (hn : n ≠ 0#64) :
    idiv m n = some (if (m ^^^ n).msb then m.sdiv n - (if m.srem n = 0#64 then 0#64 else 1#64)
      else m.sdiv n) := by
  unfold idiv
  rw [if_neg (show ¬ n = 0 from hn), Option.some.injEq]
  have hb : n.toInt ≠ 0 := fun e => hn (BitVec.eq_of_toInt_eq (by rw [e]; rfl))
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, Int.fdiv_eq_tdiv, BitVec.msb_xor, BitVec.msb_eq_toInt, BitVec.msb_eq_toInt]
  have hsd := BitVec.toInt_sdiv m n
  by_cases hd : n.toInt ∣ m.toInt
  · have h0 : m.srem n = 0#64 := (srem_eq_zero_iff m n).2 hd
    simp only [hd, if_true, h0, Int.sub_zero]
    split
    · rw [BitVec.sub_zero, hsd]
    · rw [hsd]
  · have h0 : ¬ m.srem n = 0#64 := fun e => hd ((srem_eq_zero_iff m n).1 e)
    simp only [hd, if_false, h0]
    by_cases ha : 0 ≤ m.toInt <;> by_cases hb' : 0 ≤ n.toInt <;>
      simp only [ha, hb', if_true, if_false, decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.decide_eq_true, Int.not_lt, Int.sub_zero]
    · simp [show ¬ m.toInt < 0 by omega, show ¬ n.toInt < 0 by omega, hsd]
    · simp only [show ¬ m.toInt < 0 by omega, show n.toInt < 0 by omega, decide_false, decide_true,
        Bool.false_xor, if_true]
      rw [BitVec.toInt_sub, hsd, Int.bmod_sub_bmod]; rfl
    · have hs : n.toInt.sign = 1 := Int.sign_eq_one_of_pos (by omega)
      simp only [show m.toInt < 0 by omega, show ¬ n.toInt < 0 by omega, decide_false, decide_true,
        Bool.true_xor, Bool.not_false, if_true, hs]
      rw [BitVec.toInt_sub, hsd, Int.bmod_sub_bmod]; rfl
    · have hs : n.toInt.sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
      simp [show m.toInt < 0 by omega, show n.toInt < 0 by omega, hs, hsd]

/-- `luaV_idiv`'s `n = -1` exit. -/
theorem idiv_m1 (m : BitVec 64) : idiv m (-1#64) = some (0#64 - m) := by
  unfold idiv
  rw [if_neg (show ¬ (-1#64 : BitVec 64) = 0 by decide), Option.some.injEq]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, show (-1#64 : BitVec 64).toInt = -1 by decide, BitVec.toInt_sub,
    show (0#64 : BitVec 64).toInt = 0 by decide]
  simp [Int.fdiv_eq_ediv]

end Lua.Vm.Sim.Kit
