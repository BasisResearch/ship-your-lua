import Lua.Bytecode.Semantics

/-!
# `luaV_mod` in `lvm.c`'s branch order (M1)

`imod` (`Lua/Bytecode/Semantics.lean`) is floor modulo over `Int`. The
machine computes it as `lvm.c`'s `luaV_mod` does: `n + 1 ≤ 1` (unsigned)
splits off `n = 0` (the error) and `n = -1` (result 0); otherwise the C
remainder `m % n` (`__moddi3`, `BitVec.srem`) corrected by `+ n` when it is
nonzero and its sign differs from `n`'s (`(r ^ n) < 0`). `imodC_eq` is that
restatement, one equation; `imod_neg_one` the `n = -1` exit.
-/

namespace Lua.Vm.Sim.Kit

open Lua.Bytecode

/-- `imod` is `BitVec.smod` (floor modulo) where it is defined. -/
theorem imod_smod (m n : BitVec 64) (hn : n ≠ 0#64) : imod m n = some (m.smod n) := by
  unfold imod
  split
  · exact absurd ‹_› hn
  · rw [← BitVec.toInt_smod, BitVec.ofInt_toInt]

theorem msb_lt (x : BitVec 64) (h : x.toNat < 2^63) : x.msb = false := by
  rw [BitVec.msb_eq_decide]; simp; omega

theorem msb_ge (x : BitVec 64) (h : 2^63 ≤ x.toNat) : x.msb = true := by
  rw [BitVec.msb_eq_decide]; simp; omega

theorem toNat_lt_of_msb (x : BitVec 64) (h : x.msb = false) : x.toNat < 2^63 := by
  rw [BitVec.msb_eq_decide] at h; simp at h; omega

theorem neg_msb (u : BitVec 64) (h0 : u ≠ 0#64) (hl : u.toNat ≤ 2^63) : (-u).msb = true := by
  have : 0 < u.toNat := Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq e)
  apply msb_ge; rw [BitVec.toNat_neg]; omega

/-- A remainder by a negative divisor's magnitude is at most `2^63`. -/
theorem umod_neg_le (x n : BitVec 64) (hs : n.msb = true) :
    (x % -n).toNat < 2^63 := by
  have h1 : 2^63 ≤ n.toNat := by rw [BitVec.msb_eq_decide] at hs; simpa using hs
  have hn0 : 0 < n.toNat := by omega
  have h2 : (-n).toNat = 2^64 - n.toNat := by rw [BitVec.toNat_neg]; omega
  have h3 : 0 < (-n).toNat := by omega
  rw [BitVec.toNat_umod]; have := Nat.mod_lt x.toNat h3; omega

/-- **`luaV_mod`, as the machine computes it.** -/
theorem imodC_eq (m n : BitVec 64) (hn : n ≠ 0#64) :
    imod m n = some (if m.srem n ≠ 0#64 ∧ (n ^^^ m.srem n).msb then m.srem n + n else m.srem n) := by
  rw [imod_smod m n hn, BitVec.smod_eq, BitVec.srem_eq, Option.some.injEq]
  have hn0 : 0 < n.toNat := Nat.pos_of_ne_zero fun e => hn (BitVec.eq_of_toNat_eq e)
  have hnl := n.isLt
  cases hm : m.msb <;> cases hs : n.msb <;> simp only [BitVec.umod_eq, BitVec.msb_xor, hs]
  · -- m ≥ 0, n > 0: no correction
    have : (m % n).msb = false := msb_lt _ (by
      have := toNat_lt_of_msb n hs; rw [BitVec.toNat_umod]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hn0) (by omega))
    simp [this]
  · -- m ≥ 0, n < 0: `u = m % -n`, corrected to `u + n` unless `u = 0`
    have : (m % -n).msb = false := msb_lt _ (by have := umod_neg_le m n hs; omega)
    by_cases hu : m % -n = 0#64 <;> simp [hu, this]
  · -- m < 0, n > 0: `r = -u`, corrected to `n - u` unless `u = 0`
    have hu' : (-m % n).toNat < 2^63 := by
      have := toNat_lt_of_msb n hs; rw [BitVec.toNat_umod]; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hn0) (by omega)
    by_cases hu : -m % n = 0#64
    · simp [hu]
    · have := neg_msb _ hu (by omega)
      have hne : -(-m % n) ≠ 0#64 := fun e => hu (by simpa using e)
      simp only [hu, ite_false, hne, this, ne_eq, not_false_eq_true, Bool.false_xor, and_self,
        ite_true, BitVec.sub_eq_add_neg, BitVec.add_comm n]
  · -- m < 0, n < 0: `r = -u`, never corrected
    by_cases hu : -m % -n = 0#64
    · simp [hu]
    · have := neg_msb _ hu (by have := umod_neg_le (-m) n hs; omega)
      simp [this]

end Lua.Vm.Sim.Kit
