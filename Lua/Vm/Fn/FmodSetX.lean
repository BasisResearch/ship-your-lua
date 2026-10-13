import Lua.Vm.Fn.FmodSetY

/-!
# `__ieee754_fmod`'s set-up of a subnormal `x` (lane float-sf5, (b1))
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- The subnormal `y`'s two set-ups (`0x8002c0b4`, `0x8002be94`), by the
machine's test `iy ≥ -1053`, on `y`'s raw words. -/
theorem y_sub {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (iy sx ix hx lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hl1 : -2 ^ 31 ≤ lx)
    (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hX2 : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 53) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1023)
    (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)
    (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
    (hix : iy ≤ ix) (hix1 : -1053 ≤ ix) (hix2 : ix ≤ 1023)
    (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
      ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat)) :
    (if -1053 ≤ iy then
      N_8002c0b4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
    else
      N_8002be94 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
        ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat) ∧
    (if -1053 ≤ iy then
      T_8002c0b4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
    else
      T_8002be94 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)) = true := by
  by_cases hb : -1053 ≤ iy
  · rw [if_pos hb, if_pos hb]
    exact y_c0b4 hro s r iy sx ix hx lx hy ly h5 hx0 hl1 hl2 hy0 hy1 hm1 hm2 hX2 hb hiy2 hY1 hY2 hix hix2 hlow
  · rw [if_neg hb, if_neg hb]
    -- `n ≥ 32`: `Y < 2^21`, so `hy = 0` and `ly = Y`
    have hp : (2 : Int) ^ 32 ≤ 2 ^ (-1022 - iy).toNat := ipow_mono (by omega)
    have hYs : hy * 2 ^ 32 + ly % 2 ^ 32 < 2 ^ 21 := by
      have hYn : 0 ≤ hy * 2 ^ 32 + ly % 2 ^ 32 := by
        have := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide); omega
      have : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ 32 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat :=
        Int.mul_le_mul_of_nonneg_left hp hYn
      omega
    have hYe : hy * 2 ^ 32 + ly % 2 ^ 32 = ly := by omega
    rw [hYe] at hY1 hY2 hlow ⊢
    exact y_be94 hro s r iy sx ix hx lx ly h5 hx0 hl1 hl2 (by omega) hm2 hX2 hiy1 (by omega) hY1 hY2 (by omega)
      hix2 hlow

open Lean in
set_option hygiene false in
/-- **The chamber generator for `0x8002be78`** (`e_fmod.c:84-87`, a subnormal
`x` shifted to normal by `n = -1022 - ix ≤ 31`, with a subnormal `y`): one
chamber per `n`, the shifts literal; then `y`'s set-up (`y_sub`). -/
macro "fm_xbe78_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"xbe78_{n}")) {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
          (iy sx hx lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 20)
          (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
          (hm2 : ly < 2 ^ 31)
          (hX1 : 2 ^ 52 ≤ (hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ $nl) (hX2 : (hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ $nl < 2 ^ 53)
          (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1023)
          (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)
          (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat < 2 ^ 53) (hix : iy ≤ -$il)
          (hlow : LowOk iy (((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ $nl) * 2 ^ (-$il - iy).toNat) %
            ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat)) :
          N_8002be78 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
              (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
              (BitVec.ofInt 64 (-1053)) =
            outv sx iy (((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ $nl) * 2 ^ (-$il - iy).toNat) %
              ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat) ∧
          T_8002be78 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
              (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
              (BitVec.ofInt 64 (-1053)) = true := by
        have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
        have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
        obtain ⟨b1, b2, b3⟩ := shl_facts lx (2 ^ $nl)
        have hXe : ((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ $nl) =
            (hx * 2 ^ $nl + lx % 4294967296 / 2 ^ (32 - $nl)) * 2 ^ 32 +
              (lx * 2 ^ $nl).bmod 4294967296 % 2 ^ 32 := by
          simp only [Int.reducePow, Nat.reduceSub] at b1 ⊢; omega
        rw [hXe] at hlow hX1 hX2 ⊢
        unfold N_8002be78 T_8002be78
        fm_nf
        simp only [Int.reducePow, Nat.reduceSub] at b1 b2 b3 hlow hX1 hX2 ⊢
        exact y_sub hro s r iy sx _ _ _ hy ly h5 (by omega) b2 b3 hy0 hy1 hm1 hm2 (by omega) hiy1 hiy2 hY1 hY2
          hix (by omega) (by omega) hlow))
  return ⟨mkNullNode cmds⟩

fm_xbe78_chambers 1 32

open Lean in
set_option hygiene false in
/-- The chambers `xbe78_<n>` joined by `n = -1022 - ix` (a balanced split). -/
macro "fm_xbe78_cover" : command => do
  let rec tree (a b : Nat) (fuel : Nat) : MacroM (TSyntax `tactic) := do
    match fuel with
    | 0 => `(tactic| omega)
    | fuel + 1 =>
      if b ≤ a + 1 then
        let il := Syntax.mkNumLit (toString (1022 + a))
        let ch := mkIdent (Name.mkSimple s!"xbe78_{a}")
        `(tactic| (obtain rfl : ix = -$il := by omega
                   rw [show ((-1022 : Int) - -$il).toNat = $(Syntax.mkNumLit (toString a)) by decide] at hX1 hX2 hlow ⊢
                   exact $ch hro s r iy sx hx lx hy ly h5 hx0 hx1 hl1 hl2 hy0 hy1 hm1 hm2 hX1 hX2 hiy1 hiy2 hY1 hY2
                     hix hlow))
      else
        let c := (a + b) / 2
        let cl := Syntax.mkNumLit (toString (1022 + c))
        let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a c fuel):tactic)
        let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree c b fuel):tactic)
        `(tactic| if hS : -$cl < ix then $t1 else $t2)
  let tac ← tree 1 32 64
  `(command|
    /-- **A subnormal `x` shifted by `n = -1022 - ix ≤ 31`** (`e_fmod.c:84-87`,
    `0x8002be78`), a subnormal `y`. -/
    theorem x_be78 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
        (iy ix sx hx lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 20)
        (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
        (hm2 : ly < 2 ^ 31) (hix1 : -1053 ≤ ix) (hix2 : ix ≤ -1023)
        (hX1 : 2 ^ 52 ≤ (hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (-1022 - ix).toNat)
        (hX2 : (hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (-1022 - ix).toNat < 2 ^ 53)
        (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1023)
        (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)
        (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat < 2 ^ 53) (hix : iy ≤ ix)
        (hlow : LowOk iy (((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (-1022 - ix).toNat) * 2 ^ (ix - iy).toNat) %
          ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat)) :
        N_8002be78 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
            (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
            (BitVec.ofInt 64 (-1053)) =
          outv sx iy (((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (-1022 - ix).toNat) * 2 ^ (ix - iy).toNat) %
            ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat) ∧
        T_8002be78 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
            (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
            (BitVec.ofInt 64 (-1053)) = true := by
      $tac:tactic)

fm_xbe78_cover

end Lua.Vm.Fn.Ieee754Fmod
