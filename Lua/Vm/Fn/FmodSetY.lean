import Lua.Vm.Fn.FmodIlogb

/-!
# `__ieee754_fmod`'s set-up of a subnormal `y` (lane float-sf5, (b1))
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- The facts of a word shifted left and sign-extended. -/
theorem shl_facts (l : Int) (P : Int) :
    (l * P).bmod 4294967296 % 4294967296 = l * P % 4294967296 ∧
    -2147483648 ≤ (l * P).bmod 4294967296 ∧ (l * P).bmod 4294967296 < 2147483648 := by
  have hb1 := Int.bmod_emod (x := l * P) (m := 2 ^ 32)
  have hb2 := Int.le_bmod (x := l * P) (m := 2 ^ 32) (by decide)
  have hb3 := Int.bmod_lt (x := l * P) (m := 2 ^ 32) (by decide)
  simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3
  exact ⟨hb1, by omega, by omega⟩

open Lean in
set_option hygiene false in
/-- **The chamber generator for `0x8002c0b4`** (`e_fmod.c:93-96`, a
subnormal `y` shifted to normal by `n = -1022 - iy ≤ 31`): one chamber per
`n`, the shifts literal; then the loop entry `entry_bfd0`. -/
macro "fm_yc0b4_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"yc0b4_{n}")) {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
          (sx ix hx lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hl1 : -2 ^ 31 ≤ lx)
          (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
          (hX2 : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 53)
          (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ $nl)
          (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ $nl < 2 ^ 53)
          (hix : -$il ≤ ix) (hix2 : ix ≤ 1023)
          (hlow : LowOk (-$il) ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - -$il).toNat) %
            ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ $nl)).toNat)) :
          N_8002c0b4 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
              (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
            outv sx (-$il) ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - -$il).toNat) %
              ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ $nl)).toNat) ∧
          T_8002c0b4 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
              (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
        have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
        have hly := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
        have hly2 := Int.emod_lt_of_pos ly (show (0 : Int) < 2 ^ 32 by decide)
        obtain ⟨b1, b2, b3⟩ := shl_facts ly (2 ^ $nl)
        have hYe : ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ $nl) =
            (hy * 2 ^ $nl + ly % 4294967296 / 2 ^ (32 - $nl)) * 2 ^ 32 +
              (ly * 2 ^ $nl).bmod 4294967296 % 2 ^ 32 := by
          simp only [Int.reducePow, Nat.reduceSub] at b1 ⊢; omega
        rw [hYe] at hlow ⊢
        unfold N_8002c0b4 T_8002c0b4
        fm_nf
        simp only [Int.reducePow, Nat.reduceSub] at b1 b2 b3 hlow hY1 hY2 hYe ⊢
        refine entry_bfd0 hro s r _ sx _ _ h5 (by omega) (by omega) b2 b3 (by omega) (by omega) ix hx lx
          (by omega) (by omega) hx0 hl1 hl2 (by omega) (by omega) (by omega) (by omega) hlow))
  return ⟨mkNullNode cmds⟩

fm_yc0b4_chambers 1 32

open Lean in
set_option hygiene false in
/-- The chambers `yc0b4_<n>` joined by `n = -1022 - iy` (a balanced split). -/
macro "fm_yc0b4_cover" : command => do
  let rec tree (a b : Nat) (fuel : Nat) : MacroM (TSyntax `tactic) := do
    match fuel with
    | 0 => `(tactic| omega)
    | fuel + 1 =>
      if b ≤ a + 1 then
        let il := Syntax.mkNumLit (toString (1022 + a))
        let ch := mkIdent (Name.mkSimple s!"yc0b4_{a}")
        `(tactic| (obtain rfl : iy = -$il := by omega
                   rw [show ((-1022 : Int) - -$il).toNat = $(Syntax.mkNumLit (toString a)) by decide] at hY1 hY2 hlow ⊢
                   exact $ch hro s r sx ix hx lx hy ly h5 hx0 hl1 hl2 hy0 hy1 hm1 hm2 hX2 hY1 hY2 hix hix2 hlow))
      else
        let c := (a + b) / 2
        let cl := Syntax.mkNumLit (toString (1022 + c))
        let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a c fuel):tactic)
        let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree c b fuel):tactic)
        `(tactic| if hS : -$cl < iy then $t1 else $t2)
  let tac ← tree 1 32 64
  `(command|
    /-- **A subnormal `y` shifted by `n = -1022 - iy ≤ 31`** (`e_fmod.c:93-96`,
    `0x8002c0b4`), then the loop entry. -/
    theorem y_c0b4 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
        (iy sx ix hx lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hl1 : -2 ^ 31 ≤ lx)
        (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
        (hX2 : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 53) (hiy1 : -1053 ≤ iy) (hiy2 : iy ≤ -1023)
        (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)
        (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
        (hix : iy ≤ ix) (hix2 : ix ≤ 1023)
        (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
          ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat)) :
        N_8002c0b4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
            (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
          outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
            ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat) ∧
        T_8002c0b4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
            (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
      $tac:tactic)

fm_yc0b4_cover


open Lean in
set_option hygiene false in
/-- **The chamber generator for `0x8002be94`** (`e_fmod.c:97-99`, a
subnormal `y` with `n = -1022 - iy ≥ 32`: `hy = ly << (n - 32)`, `ly = 0`):
one chamber per `n`; then the loop entry `entry_bea4`. -/
macro "fm_ybe94_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    let hyw ← if n = 32 then `(ly) else `(ly * 2 ^ ($nl - 32))
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"ybe94_{n}")) {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
          (sx ix hx lx ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hl1 : -2 ^ 31 ≤ lx)
          (hl2 : lx < 2 ^ 31) (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31)
          (hX2 : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 53)
          (hY1 : 2 ^ 52 ≤ ly * 2 ^ $nl) (hY2 : ly * 2 ^ $nl < 2 ^ 53)
          (hix : -$il < ix) (hix2 : ix ≤ 1023)
          (hlow : LowOk (-$il) ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - -$il).toNat) % (ly * 2 ^ $nl)).toNat)) :
          N_8002be94 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
              (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
            outv sx (-$il) ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - -$il).toNat) % (ly * 2 ^ $nl)).toNat) ∧
          T_8002be94 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
              (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
        have hYe : ly * 2 ^ $nl = ($hyw) * 2 ^ 32 + (0 : Int) % 2 ^ 32 := by
          simp only [Int.reducePow, Nat.reduceSub]; omega
        rw [hYe] at hlow ⊢
        rw [hYe] at hY1 hY2
        unfold N_8002be94 T_8002be94
        fm_nf
        simp only [Int.reducePow, Nat.reduceSub] at hlow hY1 hY2 ⊢
        have h := entry_bea4 hro s r (-$il) sx ($hyw) 0 h5 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (ix - -$il) hx lx (by omega) (by omega) hx0 hl1 hl2 rfl (by omega)
          (by simp only [Int.zero_emod, Int.add_zero, Int.reducePow, Nat.reduceSub] at hlow ⊢; exact hlow)
        simp only [Int.zero_emod, Int.add_zero, Int.reducePow, Nat.reduceSub] at h
        exact h))
  return ⟨mkNullNode cmds⟩

fm_ybe94_chambers 32 53

open Lean in
set_option hygiene false in
/-- The chambers `ybe94_<n>` joined by `n = -1022 - iy` (a balanced split). -/
macro "fm_ybe94_cover" : command => do
  let rec tree (a b : Nat) (fuel : Nat) : MacroM (TSyntax `tactic) := do
    match fuel with
    | 0 => `(tactic| omega)
    | fuel + 1 =>
      if b ≤ a + 1 then
        let il := Syntax.mkNumLit (toString (1022 + a))
        let ch := mkIdent (Name.mkSimple s!"ybe94_{a}")
        `(tactic| (obtain rfl : iy = -$il := by omega
                   rw [show ((-1022 : Int) - -$il).toNat = $(Syntax.mkNumLit (toString a)) by decide] at hY1 hY2 hlow ⊢
                   exact $ch hro s r sx ix hx lx ly h5 hx0 hl1 hl2 hm0 hm2 hX2 hY1 hY2 hix hix2 hlow))
      else
        let c := (a + b) / 2
        let cl := Syntax.mkNumLit (toString (1022 + c))
        let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a c fuel):tactic)
        let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree c b fuel):tactic)
        `(tactic| if hS : -$cl < iy then $t1 else $t2)
  let tac ← tree 32 53 64
  `(command|
    /-- **A subnormal `y` with `n = -1022 - iy ≥ 32`** (`e_fmod.c:97-99`,
    `0x8002be94`: its low word alone, shifted into `hy`), then the loop. -/
    theorem y_be94 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
        (iy sx ix hx lx ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hl1 : -2 ^ 31 ≤ lx)
        (hl2 : lx < 2 ^ 31) (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31)
        (hX2 : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 53) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1054)
        (hY1 : 2 ^ 52 ≤ ly * 2 ^ (-1022 - iy).toNat) (hY2 : ly * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
        (hix : iy < ix) (hix2 : ix ≤ 1023)
        (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
          (ly * 2 ^ (-1022 - iy).toNat)).toNat)) :
        N_8002be94 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
            (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
          outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
            (ly * 2 ^ (-1022 - iy).toNat)).toNat) ∧
        T_8002be94 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
            (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
      $tac:tactic)

fm_ybe94_cover

end Lua.Vm.Fn.Ieee754Fmod
