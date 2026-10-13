import Lua.Vm.Fn.FmodEntry

/-!
# `__ieee754_fmod`'s `ilogb` loops (lane float-sf5, (b1))

`e_fmod.c:58-77`: a subnormal operand's `ilogb` by counting shifts
(`for (ix = -1043, i = lx; i > 0; i <<= 1) ix -= 1;`, and from `hx << 11`):
the cycles at `0x8002be34` (`x`, `hx = 0`), `0x8002bee0` (`x`, `hx ≠ 0`),
`0x8002be5c` (`y`, `hy = 0`) and `0x8002c088` (`y`, `hy ≠ 0`). A word
`0 < w < 2^31` is shifted `t = 31 - log₂ w` times before its sign bit is
set, the counter decremented as often. One lemma per cycle (each its own
node functions), by induction on `t`; the other registers pass through.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

theorem log2_dbl {w : Nat} (h : 0 < w) : (2 * w).log2 = w.log2 + 1 := by
  apply (Nat.log2_eq_iff (by omega)).2
  have h1 : 2 ^ w.log2 ≤ w := Nat.log2_self_le (by omega)
  have h2 : w < 2 ^ (w.log2 + 1) := Nat.lt_log2_self
  constructor
  · rw [Nat.pow_succ]; omega
  · rw [Nat.pow_succ, Nat.pow_succ]; rw [Nat.pow_succ] at h2; omega

theorem log2_lt31 {w : Nat} (h0 : 0 < w) (h : w < 2 ^ 31) : w.log2 ≤ 30 := by
  have := (Nat.log2_lt (by omega)).2 h; omega

theorem log2_ge {w : Nat} (h0 : 0 < w) (h : 2 ^ 30 ≤ w) : 30 ≤ w.log2 := Lua.Num.F64.le_log2_of h

set_option hygiene false in
/-- The shift-count induction of an `ilogb` cycle (`N`, `T` its node and
termination functions): one shift per fuel, the counter decremented, until
the word's sign bit is set. -/
macro "fm_ilog " N:ident T:ident : tactic => `(tactic| (
  intro t
  induction t with
  | zero => intro k w c h; omega
  | succ t ih =>
    intro k w c ht htw hw0 hw1 hk hc1 hc2
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hl := log2_lt31 hw0 hw1
    rw [$N:ident, $T:ident]
    fm_nf
    by_cases hb : 2 * (w : Int) < 2 ^ 31
    · have ht1 : 1 ≤ t := by
        have : w.log2 < 30 := by
          rcases Nat.lt_or_ge w.log2 30 with h | h
          · exact h
          · have := Nat.log2_self_le (n := w) (by omega)
            have : 2 ^ 30 ≤ 2 ^ w.log2 := Nat.pow_le_pow_right (by decide) h
            omega
        omega
      fm_nf
      have := ih k (2 * w) (c + -1) ht1 (by rw [log2_dbl hw0]; omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      rw [show ((2 * w : Nat) : Int) = (w : Int) * 2 by push_cast; omega,
        show c + -1 - (t : Int) = c - ((t + 1 : Nat) : Int) by push_cast; omega] at this
      exact this
    · have ht0 : t = 0 := by
        have := log2_ge hw0 (by omega); omega
      subst ht0
      fm_nf
      try simp (disch := omega) only [bmod_high']
      fm_nf
      rw [show c + -1 = c - ((0 + 1 : Nat) : Int) by push_cast; omega]
      exact ⟨rfl, rfl⟩))

/-- `0x8002be34`: `ilogb` of a subnormal `x` with `hx = 0`. -/
theorem ilog_be34 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v15 v16 v17 v28 : BitVec 64) :
    ∀ (t k w : Nat) (c : Int), 1 ≤ t → t = 31 - w.log2 → 0 < w → w < 2 ^ 31 → t ≤ k →
      -2 ^ 31 + 64 + (t : Int) ≤ c → c < 2 ^ 31 →
      N_8002be34 k m s r (BitVec.ofInt 64 (w : Int)) v11 v12 (BitVec.ofInt 64 c) v14 v15 v16 v17 v28 =
        N_8002be40 m s r v11 v12 (BitVec.ofInt 64 (c - t)) v14 v15 v16 v17 v28 ∧
      T_8002be34 k m s r (BitVec.ofInt 64 (w : Int)) v11 v12 (BitVec.ofInt 64 c) v14 v15 v16 v17 v28 =
        T_8002be40 m s r v11 v12 (BitVec.ofInt 64 (c - t)) v14 v15 v16 v17 v28 := by
  fm_ilog N_8002be34 T_8002be34

/-- `0x8002bee0`: `ilogb` of a subnormal `x` with `hx ≠ 0` (from `hx << 11`). -/
theorem ilog_bee0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v15 v16 v17 v28 : BitVec 64) :
    ∀ (t k w : Nat) (c : Int), 1 ≤ t → t = 31 - w.log2 → 0 < w → w < 2 ^ 31 → t ≤ k →
      -2 ^ 31 + 64 + (t : Int) ≤ c → c < 2 ^ 31 →
      N_8002bee0 k m s r (BitVec.ofInt 64 (w : Int)) v11 v12 (BitVec.ofInt 64 c) v14 v15 v16 v17 v28 =
        N_8002beec m s r v11 v12 (BitVec.ofInt 64 (c - t)) v14 v15 v16 v17 v28 ∧
      T_8002bee0 k m s r (BitVec.ofInt 64 (w : Int)) v11 v12 (BitVec.ofInt 64 c) v14 v15 v16 v17 v28 =
        T_8002beec m s r v11 v12 (BitVec.ofInt 64 (c - t)) v14 v15 v16 v17 v28 := by
  fm_ilog N_8002bee0 T_8002bee0

/-- `0x8002be5c`: `ilogb` of a subnormal `y` with `hy = 0`. -/
theorem ilog_be5c (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v13 v14 v15 v16 v17 : BitVec 64) :
    ∀ (t k w : Nat) (c : Int), 1 ≤ t → t = 31 - w.log2 → 0 < w → w < 2 ^ 31 → t ≤ k →
      -2 ^ 31 + 64 + (t : Int) ≤ c → c < 2 ^ 31 →
      N_8002be5c k m s r (BitVec.ofInt 64 c) (BitVec.ofInt 64 (w : Int)) v11 v12 v13 v14 v15 v16 v17 =
        N_8002be68 m s r (BitVec.ofInt 64 (c - t)) v11 v12 v13 v14 v15 v16 v17 ∧
      T_8002be5c k m s r (BitVec.ofInt 64 c) (BitVec.ofInt 64 (w : Int)) v11 v12 v13 v14 v15 v16 v17 =
        T_8002be68 m s r (BitVec.ofInt 64 (c - t)) v11 v12 v13 v14 v15 v16 v17 := by
  fm_ilog N_8002be5c T_8002be5c

/-- `0x8002c088`: `ilogb` of a subnormal `y` with `hy ≠ 0` (from `hy << 11`). -/
theorem ilog_c088 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v13 v14 v15 v16 v17 : BitVec 64) :
    ∀ (t k w : Nat) (c : Int), 1 ≤ t → t = 31 - w.log2 → 0 < w → w < 2 ^ 31 → t ≤ k →
      -2 ^ 31 + 64 + (t : Int) ≤ c → c < 2 ^ 31 →
      N_8002c088 k m s r (BitVec.ofInt 64 c) (BitVec.ofInt 64 (w : Int)) v11 v12 v13 v14 v15 v16 v17 =
        N_8002c094 m s r (BitVec.ofInt 64 (c - t)) v11 v12 v13 v14 v15 v16 v17 ∧
      T_8002c088 k m s r (BitVec.ofInt 64 c) (BitVec.ofInt 64 (w : Int)) v11 v12 v13 v14 v15 v16 v17 =
        T_8002c094 m s r (BitVec.ofInt 64 (c - t)) v11 v12 v13 v14 v15 v16 v17 := by
  fm_ilog N_8002c088 T_8002c088

end Lua.Vm.Fn.Ieee754Fmod
