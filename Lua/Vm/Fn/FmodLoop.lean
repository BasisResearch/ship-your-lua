import Lua.Vm.Fn.FmodFin

/-!
# `__ieee754_fmod`'s fix-point loop (lane float-sf5, (b1))

`e_fmod.c:103-110` (`while (n--) { hz = hx-hy; lz = lx-ly; if (lx<ly) hz -= 1;
if (hz<0) { hx = hx+hx+(lx>>31); lx = lx+lx; } else { if ((hz|lz)==0) return
Zero[sx]; hx = hz+hz+(lz>>31); lx = lz+lz; } }`), the cycle at `0x8002bf60`
(six nodes): `j` iterations of `X = hx:lx` against `Y = hy:ly`, the counter
`i` up to `N = i + j`, then the last subtraction (`fin_bfd8`). The result is
the remainder `X · 2^j mod Y` (`Lua.Num.SfRef.fmodLoop_spec`'s invariant
`X < 2Y`); by induction on `j`, at most four nodes (fuel) per iteration.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- The facts of a sign-extended doubling `(2 l).bmod 2^32`. -/
theorem dbl_facts (l : Int) :
    (l * 2).bmod 4294967296 % 4294967296 = l * 2 % 4294967296 ∧
    -2147483648 ≤ (l * 2).bmod 4294967296 ∧ (l * 2).bmod 4294967296 < 2147483648 := by
  have hb1 := Int.bmod_emod (x := l * 2) (m := 2 ^ 32)
  have hb2 := Int.le_bmod (x := l * 2) (m := 2 ^ 32) (by decide)
  have hb3 := Int.bmod_lt (x := l * 2) (m := 2 ^ 32) (by decide)
  simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3
  exact ⟨hb1, by omega, by omega⟩

theorem sub_facts (a b : Int) :
    (a - b).bmod 4294967296 % 4294967296 = (a - b) % 4294967296 ∧
    -2147483648 ≤ (a - b).bmod 4294967296 ∧ (a - b).bmod 4294967296 < 2147483648 := by
  have hb1 := Int.bmod_emod (x := a - b) (m := 2 ^ 32)
  have hb2 := Int.le_bmod (x := a - b) (m := 2 ^ 32) (by decide)
  have hb3 := Int.bmod_lt (x := a - b) (m := 2 ^ 32) (by decide)
  simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3
  exact ⟨hb1, by omega, by omega⟩

/-- One step of the loop on the remainder: `X·2^(j+1) mod Y` from the doubled
`X` (or `X - Y`). -/
theorem step_mod (X Y : Int) (j : Nat) :
    (2 * (X - Y)) * 2 ^ j % Y = X * 2 ^ (j + 1) % Y ∧ (2 * X) * 2 ^ j % Y = X * 2 ^ (j + 1) % Y := by
  have e1 : X * 2 ^ (j + 1) = (2 * (X - Y)) * 2 ^ j + Y * (2 * 2 ^ j) := by
    rw [Int.pow_succ]
    generalize (2 : Int) ^ j = P
    rw [show X * (P * 2) = (X * P) * 2 by rw [Int.mul_assoc],
      show 2 * (X - Y) * P = 2 * (X * P - Y * P) by rw [Int.mul_assoc, Int.sub_mul],
      show Y * (2 * P) = 2 * (Y * P) by rw [Int.mul_left_comm]]
    omega
  have e2 : X * 2 ^ (j + 1) = (2 * X) * 2 ^ j := by
    rw [Int.pow_succ, Int.mul_comm (2 ^ j) 2, ← Int.mul_assoc, Int.mul_comm X 2]
  refine ⟨?_, by rw [e2]⟩
  rw [e1, Int.add_mul_emod_self_left]

/-! ## The loop's nodes, one step each (small contexts: `fm_nf` with `omega`
discharges over the bounds only) -/

section nodes
variable (m : Mem) (s : Nat) (r : BitVec 64) (iy sx hy ly : Int)

theorem st_bf60 (k : Nat) (i N hx lx : Int) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 22) (hy0 : 0 ≤ hy)
    (hy1 : hy < 2 ^ 22) (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31) :
    N_8002bf60 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if lx % 4294967296 < ly % 4294967296 then
        N_8002bf3c k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 (hx - hy)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N)
      else
        N_8002bf68 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 (hx - hy)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N)) ∧
    T_8002bf60 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if lx % 4294967296 < ly % 4294967296 then
        T_8002bf3c k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 (hx - hy)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N)
      else
        T_8002bf68 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 (hx - hy)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N)) := by
  rw [N_8002bf60, T_8002bf60]
  fm_nf
  by_cases hc : lx % 4294967296 < ly % 4294967296
  · fm_nf; trivial
  · fm_nf; trivial

theorem st_bf3c (k : Nat) (i N hz hx lx : Int) (hz0 : -2 ^ 23 ≤ hz) (hz1 : hz < 2 ^ 23)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31) :
    N_8002bf3c (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if hz + -1 < 0 then
        N_8002c058 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
      else
        N_8002bf48 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 (hz + -1))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296))) ∧
    T_8002bf3c (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if hz + -1 < 0 then
        T_8002c058 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
      else
        T_8002bf48 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 (hz + -1))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296))) := by
  rw [N_8002bf3c, T_8002bf3c]
  fm_nf
  by_cases hc : hz + -1 < 0
  · fm_nf; trivial
  · fm_nf; trivial

theorem st_bf68 (k : Nat) (i N hz hx lx : Int) (hz0 : -2 ^ 23 ≤ hz) (hz1 : hz < 2 ^ 23)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31) :
    N_8002bf68 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if hz < 0 then
        N_8002c058 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
      else
        N_8002bf74 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296))
          (BitVec.ofInt 64 hz ||| BitVec.ofInt 64 ((lx - ly).bmod 4294967296))) ∧
    T_8002bf68 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if hz < 0 then
        T_8002c058 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
      else
        T_8002bf74 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296))
          (BitVec.ofInt 64 hz ||| BitVec.ofInt 64 ((lx - ly).bmod 4294967296))) := by
  rw [N_8002bf68, T_8002bf68]
  fm_nf
  by_cases hc : hz < 0
  · fm_nf; trivial
  · fm_nf; trivial

theorem st_bf74 (k : Nat) (i N hz lz : Int) (hz0 : -2 ^ 23 ≤ hz) (hz1 : hz < 2 ^ 23)
    (hl1 : -2 ^ 31 ≤ lz) (hl2 : lz < 2 ^ 31) :
    N_8002bf74 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz)
        (BitVec.ofInt 64 hz ||| BitVec.ofInt 64 lz) =
      (if hz = 0 ∧ lz = 0 then N_8002bf78 m s r (BitVec.ofInt 64 sx)
      else
        N_8002bf48 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz)) ∧
    T_8002bf74 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz)
        (BitVec.ofInt 64 hz ||| BitVec.ofInt 64 lz) =
      (if hz = 0 ∧ lz = 0 then true
      else
        T_8002bf48 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz)) := by
  rw [N_8002bf74, T_8002bf74]
  fm_nf
  by_cases hc : hz = 0 ∧ lz = 0
  · fm_nf; trivial
  · fm_nf; trivial

theorem st_c058 (k : Nat) (i N hx lx : Int) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 22) (hi : 0 ≤ i) (hiN : i < N) (hN : N < 2 ^ 32)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) :
    N_8002c058 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if N = i + 1 then
        N_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 ((lx * 2).bmod 4294967296))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 (lx % 4294967296 / 2147483648 + hx * 2)) (BitVec.ofInt 64 ly)
      else
        N_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 ((lx * 2).bmod 4294967296)) (BitVec.ofInt 64 hy)
          (BitVec.ofInt 64 (lx % 4294967296 / 2147483648 + hx * 2)) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)) ∧
    T_8002c058 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      (if N = i + 1 then
        T_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 ((lx * 2).bmod 4294967296))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 (lx % 4294967296 / 2147483648 + hx * 2)) (BitVec.ofInt 64 ly)
      else
        T_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 ((lx * 2).bmod 4294967296)) (BitVec.ofInt 64 hy)
          (BitVec.ofInt 64 (lx % 4294967296 / 2147483648 + hx * 2)) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)) := by
  rw [N_8002c058, T_8002c058]
  fm_nf
  by_cases hc : N = i + 1
  · fm_nf; trivial
  · have hc' : ¬N % 18446744073709551616 = (i + 1) % 18446744073709551616 := by omega
    simp only [hc', hc, if_false]
    trivial

theorem st_bf48 (k : Nat) (i N hz lz : Int) (hz0 : 0 ≤ hz) (hz1 : hz < 2 ^ 22) (hi : 0 ≤ i) (hiN : i < N) (hN : N < 2 ^ 32)
    (hl1 : -2 ^ 31 ≤ lz) (hl2 : lz < 2 ^ 31) :
    N_8002bf48 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz) =
      (if N = i + 1 then
        N_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 ((lz * 2).bmod 4294967296))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 (lz % 4294967296 / 2147483648 + hz * 2)) (BitVec.ofInt 64 ly)
      else
        N_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 ((lz * 2).bmod 4294967296)) (BitVec.ofInt 64 hy)
          (BitVec.ofInt 64 (lz % 4294967296 / 2147483648 + hz * 2)) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)) ∧
    T_8002bf48 (k + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) (BitVec.ofInt 64 lz) =
      (if N = i + 1 then
        T_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 ((lz * 2).bmod 4294967296))
          (BitVec.ofInt 64 hy) (BitVec.ofInt 64 (lz % 4294967296 / 2147483648 + hz * 2)) (BitVec.ofInt 64 ly)
      else
        T_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 ((lz * 2).bmod 4294967296)) (BitVec.ofInt 64 hy)
          (BitVec.ofInt 64 (lz % 4294967296 / 2147483648 + hz * 2)) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)) := by
  rw [N_8002bf48, T_8002bf48]
  fm_nf
  by_cases hc : N = i + 1
  · fm_nf; trivial
  · have hc' : ¬N % 18446744073709551616 = (i + 1) % 18446744073709551616 := by omega
    simp only [hc', hc, if_false]
    trivial

theorem st_c070 (hx lx : Int) (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31) :
    N_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      N_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) ∧
    T_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      T_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) := by
  unfold N_8002c070 T_8002c070
  simp only [lo_ofInt, sub32, sext64 _ (show 31 - 0 + 1 ≤ 64 by decide), toInt_ofInt32]
  trivial

end nodes

theorem mod2 (a b : Int) (ha : 0 ≤ a) (hab : a < 2 * b) :
    a % b = if b ≤ a then a - b else a := by
  split
  · have e : a % b = ((a - b) + b) % b := by rw [show (a - b) + b = a by omega]
    rw [e, Int.add_emod_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact Int.emod_eq_of_lt ha (by omega)

/-- The result's exponent stays in range (`R · 2^(iy - 52)` is a multiple of
`2^-1074`), as an opaque fact (`omega` never opens it). -/
def LowOk (iy : Int) (R : Nat) : Prop := R ≠ 0 → -1074 ≤ iy - ((52 - R.log2 : Nat) : Int)

/-- The loop's exit (`0x8002c070`): the last subtraction on the words of `X1`. -/
theorem exit_c070 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hy ly hx lx X1 : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 21) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hY1 : 2 ^ 52 ≤ hy * 2 ^ 32 + ly % 2 ^ 32) (hiy : iy ≤ 1023) (hx0 : 0 ≤ hx)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hX1 : X1 = hx * 2 ^ 32 + lx % 2 ^ 32)
    (hX : X1 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32)) (hlow : LowOk iy (X1 % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) :
    N_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = outv sx iy (X1 % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat ∧
    T_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
  obtain ⟨e1, e2⟩ := st_c070 m s r iy sx hy ly hx lx hl1 hl2 hm1 hm2
  rw [e1, e2]
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have h0 : 0 ≤ X1 % (hy * 2 ^ 32 + ly % 2 ^ 32) := Int.emod_nonneg _ (by omega)
  apply fin_bfd8 hro s r iy sx hx lx hy ly _ h5 hx0 hy0 hy1 hl1 hl2 hm1 hm2 hY1 (by omega) _ hiy hlow
  rw [Int.toNat_of_nonneg h0, mod2 _ _ (by omega) hX, hX1]

/-- The loop's claim for `j` remaining iterations: from the head, the
remainder `X · 2^j mod Y` packed. -/
def LoopClaim (m : Mem) (s : Nat) (r : BitVec 64) (iy sx hy ly : Int) (j : Nat) : Prop :=
  ∀ (k : Nat) (i N hx lx : Int), 4 * j ≤ k → N = i + j → 0 ≤ i → N < 2 ^ 32 →
    0 ≤ hx → -2 ^ 31 ≤ lx → lx < 2 ^ 31 →
    hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32) →
    LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ j) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) →
    N_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ j) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bf60 k m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N) = true

section step
variable {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hy ly : Int)
  (h5 : sx = 0 ∨ sx = 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 21) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
  (hY1 : 2 ^ 52 ≤ hy * 2 ^ 32 + ly % 2 ^ 32) (hiy : iy ≤ 1023)

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- One doubling of the words `hx1:lx1 = 2 X'` at the loop's bottom (`c058`,
`bf48`): the exit when the counter is done, else the loop for `j` more. -/
theorem dbl_next (j : Nat) (ih : 1 ≤ j → LoopClaim m s r iy sx hy ly j) (k' : Nat) (i N hx1 lx1 X' : Int)
    (hk' : 4 * j ≤ k') (hN : N = i + (j + 1)) (hi : 0 ≤ i) (hN2 : N < 2 ^ 32)
    (hx0 : 0 ≤ hx1) (hl1 : -2 ^ 31 ≤ lx1) (hl2 : lx1 < 2 ^ 31) (hX0 : 0 ≤ X')
    (hw : hx1 * 2 ^ 32 + lx1 % 2 ^ 32 = 2 * X') (hX : X' < hy * 2 ^ 32 + ly % 2 ^ 32)
    (hlow : LowOk iy (((2 * X') * 2 ^ j) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) :
    (if N = i + 1 then
      N_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx1) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx1) (BitVec.ofInt 64 ly)
    else
      N_8002bf60 k' m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 lx1) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx1) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 N)) = outv sx iy (((2 * X') * 2 ^ j) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat ∧
    (if N = i + 1 then
      T_8002c070 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx1) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx1) (BitVec.ofInt 64 ly)
    else
      T_8002bf60 k' m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (i + 1)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 lx1) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx1) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 N)) = true := by
  by_cases hc : N = i + 1
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [if_pos hc, if_pos hc]
    simp only [Int.pow_zero, Int.mul_one] at hlow ⊢
    exact exit_c070 hro s r iy sx hy ly hx1 lx1 (2 * X') h5 hy0 hy1 hm1 hm2 hY1 hiy hx0 hl1 hl2 hw.symm
      (by omega) hlow
  · rw [if_neg hc, if_neg hc]
    have := ih (by omega) k' (i + 1) N hx1 lx1 hk' (by omega) (by omega) hN2 hx0 hl1 hl2 (by omega) (by rw [hw]; exact hlow)
    rw [hw] at this; exact this

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- **One iteration** of the fix-point loop (`e_fmod.c:104-109`). -/
theorem loop_step (j : Nat) (ih : 1 ≤ j → LoopClaim m s r iy sx hy ly j) : LoopClaim m s r iy sx hy ly (j + 1) := by
  intro k i N hx lx hk hN hi hN2 hx0 hl1 hl2 hX hlow
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 4 := ⟨k - 4, by omega⟩
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hly := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hly2 := Int.emod_lt_of_pos ly (show (0 : Int) < 2 ^ 32 by decide)
  have hx1 : hx < 2 ^ 22 := by omega
  obtain ⟨sm1, sm2⟩ := step_mod (hx * 2 ^ 32 + lx % 2 ^ 32) (hy * 2 ^ 32 + ly % 2 ^ 32) j
  -- through `0x8002c058`: `X` doubled
  have viaC : ∀ k', 4 * j ≤ k' → hx * 2 ^ 32 + lx % 2 ^ 32 < hy * 2 ^ 32 + ly % 2 ^ 32 →
      N_8002c058 (k' + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N) =
        outv sx iy (((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (j + 1)) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat ∧
      T_8002c058 (k' + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 N) = true := by
    intro k' hk' hlt
    obtain ⟨d1, d2, d3⟩ := dbl_facts lx
    obtain ⟨e1, e2⟩ := st_c058 m s r iy sx hy ly k' i N hx lx hx0 hx1 hi (by omega) hN2 hl1 hl2
    rw [e1, e2, ← sm2]
    exact dbl_next hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy j ih k' i N _ _ _ hk' hN hi hN2
      (by omega) d2 d3 (by omega) (by omega) hlt (by rw [sm2]; exact hlow)
  -- through `0x8002bf48`: `X - Y` doubled (`hz:lz` its words)
  have viaB : ∀ k' (hz : Int), 4 * j ≤ k' →
      hy * 2 ^ 32 + ly % 2 ^ 32 ≤ hx * 2 ^ 32 + lx % 2 ^ 32 →
      hz * 2 ^ 32 + (lx - ly).bmod 4294967296 % 2 ^ 32 =
        hx * 2 ^ 32 + lx % 2 ^ 32 - (hy * 2 ^ 32 + ly % 2 ^ 32) →
      N_8002bf48 (k' + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296)) =
        outv sx iy (((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (j + 1)) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat ∧
      T_8002bf48 (k' + 1) m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 i) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 hz) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 N)
          (BitVec.ofInt 64 ((lx - ly).bmod 4294967296)) = true := by
    intro k' hz hk' hge hzw
    obtain ⟨_, s2, s3⟩ := sub_facts lx ly
    obtain ⟨t1, t2, t3⟩ := dbl_facts ((lx - ly).bmod 4294967296)
    have hlz := Int.emod_nonneg ((lx - ly).bmod 4294967296) (show (4294967296 : Int) ≠ 0 by decide)
    have hlz2 := Int.emod_lt_of_pos ((lx - ly).bmod 4294967296) (show (0 : Int) < 4294967296 by decide)
    have hz0 : 0 ≤ hz := by omega
    have hz1 : hz < 2 ^ 22 := by omega
    obtain ⟨e1, e2⟩ := st_bf48 m s r iy sx hy ly k' i N hz _ hz0 hz1 hi (by omega) hN2 s2 s3
    rw [e1, e2, ← sm1]
    exact dbl_next hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy j ih k' i N _ _ _ hk' hN hi hN2
      (by omega) t2 t3 (by omega) (by omega) (by omega) (by rw [sm1]; exact hlow)
  obtain ⟨_, s2, s3⟩ := sub_facts lx ly
  rw [show k + 4 = (k + 3) + 1 from rfl]
  obtain ⟨e1, e2⟩ := st_bf60 m s r iy sx hy ly (k + 3) i N hx lx hx0 hx1 hy0 (by omega) hl1 hl2 hm1 hm2
  rw [e1, e2]
  by_cases hb : lx % 4294967296 < ly % 4294967296
  · -- a borrow: `hz = hx - hy - 1`
    rw [if_pos hb, if_pos hb, show k + 3 = (k + 2) + 1 from rfl]
    obtain ⟨f1, f2⟩ := st_bf3c m s r iy sx hy ly (k + 2) i N (hx - hy) hx lx (by omega) (by omega)
      hl1 hl2 hm1 hm2
    rw [f1, f2]
    by_cases hn : hx - hy + -1 < 0
    · rw [if_pos hn, if_pos hn, show k + 2 = (k + 1) + 1 from rfl]
      exact viaC (k + 1) (by omega) (by omega)
    · rw [if_neg hn, if_neg hn, show k + 2 = (k + 1) + 1 from rfl]
      exact viaB (k + 1) _ (by omega) (by omega) (by omega)
  · rw [if_neg hb, if_neg hb, show k + 3 = (k + 2) + 1 from rfl]
    obtain ⟨f1, f2⟩ := st_bf68 m s r iy sx hy ly (k + 2) i N (hx - hy) hx lx (by omega) (by omega)
      hl1 hl2 hm1 hm2
    rw [f1, f2]
    by_cases hn : hx - hy < 0
    · rw [if_pos hn, if_pos hn, show k + 2 = (k + 1) + 1 from rfl]
      exact viaC (k + 1) (by omega) (by omega)
    · rw [if_neg hn, if_neg hn, show k + 2 = (k + 1) + 1 from rfl]
      obtain ⟨g1, g2⟩ := st_bf74 m s r iy sx hy ly (k + 1) i N (hx - hy) ((lx - ly).bmod 4294967296)
        (by omega) (by omega) s2 s3
      rw [g1, g2]
      by_cases hz : hx - hy = 0 ∧ (lx - ly).bmod 4294967296 = 0
      · -- `X = Y`: `Zero[sx]`
        rw [if_pos hz, if_pos hz, ld_bf78 hro s r sx h5]
        have hXY : hx * 2 ^ 32 + lx % 2 ^ 32 = hy * 2 ^ 32 + ly % 2 ^ 32 := by
          obtain ⟨s1, _, _⟩ := sub_facts lx ly
          omega
        rw [hXY, Int.mul_emod_right]
        exact ⟨by unfold outv; rfl, rfl⟩
      · rw [if_neg hz, if_neg hz]
        exact viaB k _ (by omega) (by omega) (by obtain ⟨s1, _, _⟩ := sub_facts lx ly; omega)

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- **The fix-point loop** (`e_fmod.c:103-110`) from its head `0x8002bf60`:
`j + 1` iterations, then the last subtraction and the conversion back. -/
theorem loop_bf60 : ∀ j, LoopClaim m s r iy sx hy ly (j + 1) := by
  intro j
  induction j with
  | zero => exact loop_step hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy 0 (fun h => absurd h (by omega))
  | succ j ih => exact loop_step hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy (j + 1) (fun _ => ih)

end step

end Lua.Vm.Fn.Ieee754Fmod
