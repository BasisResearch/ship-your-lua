import Lua.Vm.Fn.FmodPack

/-!
# `__ieee754_fmod`'s normalisation loop (lane float-sf5, (b1))

`e_fmod.c:116-119` (`while (hx < 0x00100000) { hx = hx+hx+(lx>>31); lx <<= 1;
iy -= 1; }`, the cycle at `0x8002c008`): a nonzero remainder `W = hx:lx`
below `2^52` is doubled `z` times, to `[2^52, 2^53)`, and `iy` decremented as
often; then the conversion back (`pack_c020v`). The lemma is by induction on
`z`, the fuel one per doubling; the termination function `T_8002c008` holds
along the same induction.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens

set_option linter.unusedVariables false

/-- **The normalisation loop**: `z ≥ 1` doublings bring `W` to `[2^52, 2^53)`. -/
theorem norm_c008 (s : Nat) (r : BitVec 64) (sx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) :
    ∀ (z k : Nat) (iy hx lx W : Int), 1 ≤ z → z ≤ k → 0 ≤ hx → -2 ^ 31 ≤ lx → lx < 2 ^ 31 →
      W = hx * 2 ^ 32 + lx % 2 ^ 32 → 2 ^ 52 ≤ W * 2 ^ z → W * 2 ^ z < 2 ^ 53 →
      -1074 ≤ iy - z → iy ≤ 1023 →
      N_8002c008 k s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 1048576)
          (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) = packv sx (iy - z) (W * 2 ^ z) ∧
      T_8002c008 k s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 1048576)
          (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) = true := by
  intro z
  induction z with
  | zero => intro k iy hx lx W h; omega
  | succ z ih =>
    intro k iy hx lx W hz hk hx0 hl1 hl2 hW hlo hhi he1 he2
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpz : (0 : Int) < 2 ^ z := Int.pow_pos (by decide)
    have e2 : (W * 2 ^ (z + 1) : Int) = (2 * W) * 2 ^ z := by
      rw [Int.pow_succ]; rw [Int.mul_comm (2 ^ z) 2, ← Int.mul_assoc, Int.mul_comm W 2]
    have hW0 : 0 ≤ W := by
      have : 0 ≤ lx % 2 ^ 32 := Int.emod_nonneg _ (by decide)
      have : 0 ≤ hx * 2 ^ 32 := Int.mul_nonneg hx0 (by decide)
      omega
    rw [e2] at hlo hhi ⊢
    have hWlt : 2 * W < 2 ^ 53 := by
      have : (2 * W) * 1 ≤ (2 * W) * 2 ^ z := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    have hb1 := Int.bmod_emod (x := lx * 2) (m := 2 ^ 32)
    have hb2 := Int.le_bmod (x := lx * 2) (m := 2 ^ 32) (by decide)
    have hb3 := Int.bmod_lt (x := lx * 2) (m := 2 ^ 32) (by decide)
    simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3
    unfold N_8002c008 T_8002c008
    by_cases hz0 : z = 0
    · -- the last doubling: `2W ≥ 2^52`, the exit
      subst hz0
      simp only [Int.pow_zero, Int.mul_one] at hlo hhi ⊢
      fm_nf
      refine ⟨?_, trivial⟩
      rw [pack_c020v s r _ sx _ _ (2 * W) (by omega) (by omega) (by omega) (by omega) h5 (by omega)
        (by omega) (by omega)]
      rw [show iy - 1 = iy + -1 by omega]
    · -- `2W < 2^52`: one more iteration
      have h2 : (2 : Int) ≤ 2 ^ z := by
        have : (2 : Nat) ≤ 2 ^ z := by
          calc (2 : Nat) = 2 ^ 1 := rfl
            _ ≤ 2 ^ z := Nat.pow_le_pow_right (by decide) (by omega)
        exact_mod_cast this
      have hlt : 2 * W < 2 ^ 52 := by
        have : (2 * W) * 2 ≤ (2 * W) * 2 ^ z := Int.mul_le_mul_of_nonneg_left h2 (by omega)
        omega
      fm_nf
      have c1 : 0 ≤ lx % 4294967296 / 2147483648 + hx * 2 := by omega
      have c2 : 2 * W = (lx % 4294967296 / 2147483648 + hx * 2) * 2 ^ 32 + (lx * 2).bmod 4294967296 % 2 ^ 32 := by
        omega
      obtain ⟨hN, hT⟩ := ih k (iy + -1) _ _ (2 * W) (by omega) (by omega) c1 (by omega) (by omega)
        c2 hlo hhi (by omega) (by omega)
      refine ⟨?_, hT⟩
      rw [hN]
      congr 1
      omega

end Lua.Vm.Fn.Ieee754Fmod
