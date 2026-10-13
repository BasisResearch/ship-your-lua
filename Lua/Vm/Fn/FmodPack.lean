import Lua.Vm.Fn.FmodLens
import Lua.Vm.Fn.Ieee754Fmod

/-!
# `__ieee754_fmod`'s conversion back (lane float-sf5, (b1), the pack stage)

`e_fmod.c:126-138`, the nodes from `0x8002c020`: a normalised remainder
`hx:lx` (`2^20 ≤ hx < 2^21`) at exponent `iy` packed normal (`iy ≥ -1022`,
`0x8002c028`: `pack_c028`) or subnormal (`0x8002c118`: shifted right by
`n = -1022 - iy`, three ways by `n`). The machine's shifts by `n` are
variable; the subnormal stage is one chamber per `n ∈ [1, 52]` (the shifts
literal), emitted by the chamber generator `fm_psub_chambers` and joined by
`fm_psub_cover` (never a hand chamber list, rule R18).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens

set_option linter.unusedVariables false

/-- **Normal output** (`e_fmod.c:127-129`): `hx - 2^20`, the exponent field
`iy + 1023` and the sign or-ed into the high word. -/
theorem pack_c028 (s : Nat) (r : BitVec 64) (iy sx hx lx : Int) (h1 : -1022 ≤ iy) (h2 : iy ≤ 1023)
    (h3 : 2 ^ 20 ≤ hx) (h4 : hx < 2 ^ 21) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : -2 ^ 31 ≤ lx) (h7 : lx < 2 ^ 31) :
    N_8002c028 s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) =
      BitVec.ofInt 64 ((sx + (iy + 1023) * 2 ^ 20 + (hx - 2 ^ 20)) * 2 ^ 32 + lx % 2 ^ 32) := by
  unfold N_8002c028
  fm_nf
  fm_close

open Lean in
set_option hygiene false in
/-- **The subnormal-output chamber generator**: for each `n ∈ [lo, hi)`, the
chamber `psub_<n>`: at `iy = -1022 - n` the machine's three-way shift
(`e_fmod.c:131-137`) is `hx:lx >> n` with the sign word on top. -/
macro "fm_psub_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"psub_{n}")) (s : Nat) (r : BitVec 64) (sx hx lx : Int)
          (h3 : 2 ^ 20 ≤ hx) (h4 : hx < 2 ^ 21) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : -2 ^ 31 ≤ lx)
          (h7 : lx < 2 ^ 31) :
          N_8002c118 s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx)
              (BitVec.ofInt 64 lx) =
            BitVec.ofInt 64 (sx * 2 ^ 32 + (hx * 2 ^ 32 + lx % 2 ^ 32) / 2 ^ $nl) := by
        unfold N_8002c118
        fm_nf
        try unfold N_8002c128
        try unfold N_8002c1e0
        fm_nf
        try unfold N_8002c1e8
        try unfold N_8002c21c
        unfold N_8002c140
        fm_nf
        fm_close))
  return ⟨mkNullNode cmds⟩

fm_psub_chambers 1 53

open Lean in
set_option hygiene false in
/-- The chambers `psub_<n>` joined by `n` (a balanced split). -/
macro "fm_psub_cover" : command => do
  let rec tree (a b : Nat) (fuel : Nat) : MacroM (TSyntax `tactic) := do
    match fuel with
    | 0 => `(tactic| omega)
    | fuel + 1 =>
      if b ≤ a + 1 then
        let il := Syntax.mkNumLit (toString (1022 + a))
        let ch := mkIdent (Name.mkSimple s!"psub_{a}")
        `(tactic| (obtain rfl : iy = -$il := by omega
                   rw [show ((-1022 : Int) - -$il).toNat = $(Syntax.mkNumLit (toString a)) by decide]
                   exact $ch s r sx hx lx h3 h4 h5 h6 h7))
      else
        let c := (a + b) / 2
        let cl := Syntax.mkNumLit (toString (1022 + c))
        let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a c fuel):tactic)
        let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree c b fuel):tactic)
        `(tactic| if hS : -$cl < iy then $t1 else $t2)
  let tac ← tree 1 53 64
  `(command|
    /-- **Subnormal output** (`e_fmod.c:130-137`), `-1074 ≤ iy < -1022`. -/
    theorem pack_c118 (s : Nat) (r : BitVec 64) (iy sx hx lx : Int) (h1 : -1074 ≤ iy) (h2 : iy < -1022)
        (h3 : 2 ^ 20 ≤ hx) (h4 : hx < 2 ^ 21) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : -2 ^ 31 ≤ lx)
        (h7 : lx < 2 ^ 31) :
        N_8002c118 s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) =
          BitVec.ofInt 64 (sx * 2 ^ 32 + (hx * 2 ^ 32 + lx % 2 ^ 32) / 2 ^ (-1022 - iy).toNat) := by
      $tac:tactic)

fm_psub_cover

/-- **The conversion back** (`e_fmod.c:126-138`) of a normalised remainder. -/
theorem pack_c020 (s : Nat) (r : BitVec 64) (iy sx hx lx : Int) (h1 : -1074 ≤ iy) (h2 : iy ≤ 1023)
    (h3 : 2 ^ 20 ≤ hx) (h4 : hx < 2 ^ 21) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : -2 ^ 31 ≤ lx) (h7 : lx < 2 ^ 31) :
    N_8002c020 s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) =
      if -1022 ≤ iy then BitVec.ofInt 64 ((sx + (iy + 1023) * 2 ^ 20 + (hx - 2 ^ 20)) * 2 ^ 32 + lx % 2 ^ 32)
      else BitVec.ofInt 64 (sx * 2 ^ 32 + (hx * 2 ^ 32 + lx % 2 ^ 32) / 2 ^ (-1022 - iy).toNat) := by
  unfold N_8002c020
  fm_nf
  split
  · rename_i h; rw [if_neg (by omega)]; exact pack_c118 s r iy sx hx lx h1 h h3 h4 h5 h6 h7
  · rename_i h; rw [if_pos (by omega)]; exact pack_c028 s r iy sx hx lx (by omega) h2 h3 h4 h5 h6 h7

/-- The packed result of a normalised remainder `M = hx:lx` (`2^52 ≤ M < 2^53`)
at exponent `e`, sign word `sx`. -/
def packv (sx e M : Int) : BitVec 64 :=
  if -1022 ≤ e then BitVec.ofInt 64 ((sx + (e + 1023) * 2 ^ 20) * 2 ^ 32 + (M - 2 ^ 52))
  else BitVec.ofInt 64 (sx * 2 ^ 32 + M / 2 ^ (-1022 - e).toNat)

/-- `pack_c020` on the remainder's value. -/
theorem pack_c020v (s : Nat) (r : BitVec 64) (iy sx hx lx M : Int) (h1 : -1074 ≤ iy) (h2 : iy ≤ 1023)
    (h3 : 2 ^ 20 ≤ hx) (h4 : hx < 2 ^ 21) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : -2 ^ 31 ≤ lx) (h7 : lx < 2 ^ 31)
    (hM : M = hx * 2 ^ 32 + lx % 2 ^ 32) :
    N_8002c020 s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx) =
      packv sx iy M := by
  rw [pack_c020 s r iy sx hx lx h1 h2 h3 h4 h5 h6 h7, packv, hM]
  split
  · congr 1; omega
  · rfl

end Lua.Vm.Fn.Ieee754Fmod
