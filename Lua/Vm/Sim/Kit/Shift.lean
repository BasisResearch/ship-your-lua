import Lua.Vm.Sim.Bits
import Lua.Bytecode.Semantics

/-!
# `luaV_shiftl` as the machine computes it

`lvm.c`'s `luaV_shiftl(x, y)` is inlined in `OP_SHL`/`OP_SHR`/`OP_SHLI`/
`OP_SHRI` as two branches on the shift amount and one RV64 shift:
`bltz` (or `bltu` on `C`), then `blt`/`bltu`/`bgeu` against a bound, then
`sll`/`srl` by the amount's low six bits (through `negw` for a negative
amount), or `0`. The kernel's `shiftl`/`shiftr`
(`Lua/Bytecode/Semantics.lean`) is restated here per machine branch, with
the guards as the machine's `Bool`s (`msb` for `bltz`, as `at_vals` reads
`slt_zero`):

* `shiftlC_*`: `shiftl x y` with `y` the amount register (`OP_SHL`, `OP_SHLI`);
* `shiftrC_*`: `shiftr x y`, branching on the machine's amount `0 - y` (`OP_SHR`);
* `shiftrK_*`: `shiftr x sC`, branching on the field `C` (`OP_SHRI`);
* `sc_eq`: the immediate `sC` as `addiw c, -127` (`OP_SHLI`).

Each family is `big` (the result is `0`), `run`, `neg_big`, `neg_run`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Lua.Vm.Sim

/-- `subw`: the low words subtracted, sign-extended (`negw` is `wsub 0`). -/
abbrev wsub (x y : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) ((Sail.BitVec.extractLsb x 31 0) - (Sail.BitVec.extractLsb y 31 0))

theorem extract6_toNat (y : BitVec 64) : (Sail.BitVec.extractLsb y 5 0).toNat = y.toNat % 64 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]

theorem extract32_toNat (y : BitVec 64) : (Sail.BitVec.extractLsb y 31 0).toNat = y.toNat % 2 ^ 32 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]

theorem sll_eq (x y : BitVec 64) :
    shift_bits_left x (Sail.BitVec.extractLsb y 5 0) = x <<< (y.toNat % 64) := by
  simp only [shift_bits_left, BitVec.shiftLeft_eq', extract6_toNat]

theorem srl_eq (x y : BitVec 64) :
    shift_bits_right x (Sail.BitVec.extractLsb y 5 0) = x >>> (y.toNat % 64) := by
  simp only [shift_bits_right, BitVec.ushiftRight_eq', extract6_toNat]

theorem sext_low (v : BitVec 32) : (sign_extend (m := 64) v).toNat % 64 = v.toNat % 64 := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.toNat_signExtend]
  have := BitVec.toNat_setWidth (x := v) (i := 64)
  have : v.toNat < 2 ^ 32 := v.isLt
  split <;> simp_all <;> omega

theorem wsub_low (x y : BitVec 64) : (wsub x y).toNat % 64 = (x.toNat + (2 ^ 64 - y.toNat)) % 64 := by
  simp only [wsub]; rw [sext_low, BitVec.toNat_sub, extract32_toNat, extract32_toNat]
  have := x.isLt; have := y.isLt
  omega

theorem toInt_neg (y : BitVec 64) (h : y.toInt < 0) : y.toInt = (y.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at * <;> omega

theorem toInt_nonneg (y : BitVec 64) (h : ¬ y.toInt < 0) : y.toInt = (y.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at * <;> omega

theorem slt_int (x y : BitVec 64) : zopz0zI_s x y = decide (x.toInt < y.toInt) := by
  unfold zopz0zI_s; simp

theorem msb_int (y : BitVec 64) : y.msb = decide (y.toInt < 0) := by
  rw [BitVec.msb_eq_toInt]

theorem lit63 : (0x3f#64 : BitVec 64).toInt = 63 := by decide
theorem litm63 : (0xffffffffffffffc1#64 : BitVec 64).toInt = -63 := by decide

set_option hygiene false in
/-- The guards as `Int` facts about `y.toInt`. -/
local macro "sh_int" : tactic => `(tactic| (
  rw [msb_int] at h1; rw [slt_int] at h2
  simp only [lit63, litm63, decide_eq_true_eq, decide_eq_false_iff_not, Int.not_lt] at h1 h2
  unfold Lua.Bytecode.shiftl))

section
variable {y : BitVec 64}

theorem shiftlC_big (h1 : y.msb = false) (h2 : zopz0zI_s 0x3f#64 y = true) (x : BitVec 64) :
    Lua.Bytecode.shiftl x y = 0x0#64 := by
  sh_int; rw [if_neg (by omega), if_pos (by omega)]; rfl

theorem shiftlC_run (h1 : y.msb = false) (h2 : zopz0zI_s 0x3f#64 y = false) (x : BitVec 64) :
    Lua.Bytecode.shiftl x y = shift_bits_left x (Sail.BitVec.extractLsb y 5 0) := by
  sh_int; rw [if_neg (by omega), if_neg (by omega), sll_eq]
  have := toInt_nonneg y (by omega)
  congr 1; omega

theorem shiftlC_neg_big (h1 : y.msb = true) (h2 : zopz0zI_s y 0xffffffffffffffc1#64 = true)
    (x : BitVec 64) : Lua.Bytecode.shiftl x y = 0x0#64 := by
  sh_int; rw [if_pos (by omega), if_pos (by omega)]; rfl

theorem shiftlC_neg_run (h1 : y.msb = true) (h2 : zopz0zI_s y 0xffffffffffffffc1#64 = false)
    (x : BitVec 64) :
    Lua.Bytecode.shiftl x y = shift_bits_right x (Sail.BitVec.extractLsb (wsub 0x0#64 y) 5 0) := by
  sh_int; rw [if_pos (by omega), if_neg (by omega), srl_eq]
  have := toInt_neg y (by omega)
  rw [wsub_low]; congr 1; simp; omega

/-! `OP_SHR`: the machine's amount is `0 - y` (`neg a4,a2`). -/

theorem shiftrC_big (h1 : (0x0#64 - y).msb = false) (h2 : zopz0zI_s 0x3f#64 (0x0#64 - y) = true)
    (x : BitVec 64) : Lua.Bytecode.shiftr x y = 0x0#64 := shiftlC_big h1 h2 x

theorem shiftrC_run (h1 : (0x0#64 - y).msb = false) (h2 : zopz0zI_s 0x3f#64 (0x0#64 - y) = false)
    (x : BitVec 64) :
    Lua.Bytecode.shiftr x y = shift_bits_left x (Sail.BitVec.extractLsb (0x0#64 - y) 5 0) :=
  shiftlC_run h1 h2 x

theorem shiftrC_neg_big (h1 : (0x0#64 - y).msb = true)
    (h2 : zopz0zI_s (0x0#64 - y) 0xffffffffffffffc1#64 = true) (x : BitVec 64) :
    Lua.Bytecode.shiftr x y = 0x0#64 := shiftlC_neg_big h1 h2 x

theorem shiftrC_neg_run (h1 : (0x0#64 - y).msb = true)
    (h2 : zopz0zI_s (0x0#64 - y) 0xffffffffffffffc1#64 = false) (x : BitVec 64) :
    Lua.Bytecode.shiftr x y = shift_bits_right x (Sail.BitVec.extractLsb y 5 0) := by
  change Lua.Bytecode.shiftl x (0x0#64 - y) = _
  rw [msb_int] at h1; rw [slt_int] at h2
  simp only [litm63, decide_eq_true_eq, decide_eq_false_iff_not, Int.not_lt] at h1 h2
  unfold Lua.Bytecode.shiftl
  rw [if_pos (by exact h1), if_neg (by omega), srl_eq]
  have e := toInt_neg _ h1
  have hs := BitVec.toNat_sub (0x0#64 : BitVec 64) y
  have := y.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] at hs
  congr 1; rw [e, hs]; omega

end

/-! `OP_SHRI` and `OP_SHLI`: the immediate `sC = C - 127`. -/

theorem c_lt (ins : Lua.Bytecode.Word) : ins.c < 256 := by
  simp only [Lua.Bytecode.Word.c, Lua.Bytecode.Word.field]; omega

theorem sc_neg_aux : ∀ c : Nat, c < 256 → (0#64 - BitVec.ofInt 64 ((c : Int) - 127)).toInt =
    127 - (c : Int) := by decide +kernel

theorem sc_neg (ins : Lua.Bytecode.Word) :
    (0#64 - BitVec.ofInt 64 ins.sc).toInt = 127 - (ins.c : Int) :=
  sc_neg_aux ins.c (c_lt ins)

theorem sc_low_aux : ∀ c : Nat, c < 256 →
    (c ≤ 127 → (wsub 0x7f#64 (BitVec.ofNat 64 c)).toNat % 64 = (127 - c) % 64) ∧
    (127 < c → (wsub 0x0#64 (wsub 0x7f#64 (BitVec.ofNat 64 c))).toNat % 64 = (c - 127) % 64) := by
  decide +kernel

theorem sc_eq_aux : ∀ c : Nat, c < 256 → BitVec.ofInt 64 ((c : Int) - 127) =
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 c + 0xffffffffffffff81#64) 31 0) := by
  decide +kernel

/-- **`sC` as `addiw a6, c, -127`.** -/
theorem sc_eq (ins : Lua.Bytecode.Word) : BitVec.ofInt 64 ins.sc =
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 ins.c + 0xffffffffffffff81#64) 31 0) :=
  sc_eq_aux ins.c (c_lt ins)

theorem ult_ofNat (k c : Nat) (hk : k < 2 ^ 64) (hc : c < 256) :
    zopz0zI_u (BitVec.ofNat 64 k) (BitVec.ofNat 64 c) = decide (k < c) := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]

theorem uge_ofNat (k c : Nat) (hk : k < 2 ^ 64) (hc : c < 256) :
    zopz0zKzJ_u (BitVec.ofNat 64 k) (BitVec.ofNat 64 c) = decide (c ≤ k) := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]

set_option hygiene false in
/-- The `C` guards as `Nat` facts, the amount `0 - sC` as `127 - C`. -/
local macro "shri_int" : tactic => `(tactic| (
  have hc := c_lt ins
  rw [ult_ofNat _ _ (by omega) hc] at h1
  first | rw [uge_ofNat _ _ (by omega) hc] at h2 | rw [ult_ofNat _ _ (by omega) hc] at h2
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt, Nat.not_le] at h1 h2
  have hn := sc_neg ins
  have hl := sc_low_aux ins.c hc
  change Lua.Bytecode.shiftl x (0#64 - BitVec.ofInt 64 ins.sc) = _
  unfold Lua.Bytecode.shiftl))

section
variable {ins : Lua.Bytecode.Word}

theorem shiftrK_big (h1 : zopz0zI_u 0x7f#64 (BitVec.ofNat 64 ins.c) = false)
    (h2 : zopz0zKzJ_u 0x3f#64 (BitVec.ofNat 64 ins.c) = true) (x : BitVec 64) :
    Lua.Bytecode.shiftr x (BitVec.ofInt 64 ins.sc) = 0x0#64 := by
  shri_int; rw [if_neg (by omega), if_pos (by omega)]; rfl

theorem shiftrK_run (h1 : zopz0zI_u 0x7f#64 (BitVec.ofNat 64 ins.c) = false)
    (h2 : zopz0zKzJ_u 0x3f#64 (BitVec.ofNat 64 ins.c) = false) (x : BitVec 64) :
    Lua.Bytecode.shiftr x (BitVec.ofInt 64 ins.sc) =
      shift_bits_left x (Sail.BitVec.extractLsb (wsub 0x7f#64 (BitVec.ofNat 64 ins.c)) 5 0) := by
  shri_int; rw [if_neg (by omega), if_neg (by omega), sll_eq, hl.1 h1]
  have := toInt_nonneg (0#64 - BitVec.ofInt 64 ins.sc) (by omega)
  congr 1; omega

theorem shiftrK_neg_big (h1 : zopz0zI_u 0x7f#64 (BitVec.ofNat 64 ins.c) = true)
    (h2 : zopz0zI_u 0xbe#64 (BitVec.ofNat 64 ins.c) = true) (x : BitVec 64) :
    Lua.Bytecode.shiftr x (BitVec.ofInt 64 ins.sc) = 0x0#64 := by
  shri_int; rw [if_pos (by omega), if_pos (by omega)]; rfl

theorem shiftrK_neg_run (h1 : zopz0zI_u 0x7f#64 (BitVec.ofNat 64 ins.c) = true)
    (h2 : zopz0zI_u 0xbe#64 (BitVec.ofNat 64 ins.c) = false) (x : BitVec 64) :
    Lua.Bytecode.shiftr x (BitVec.ofInt 64 ins.sc) = shift_bits_right x
      (Sail.BitVec.extractLsb (wsub 0x0#64 (wsub 0x7f#64 (BitVec.ofNat 64 ins.c))) 5 0) := by
  shri_int; rw [if_pos (by omega), if_neg (by omega), srl_eq, hl.2 h1]
  have e : (-(0#64 - BitVec.ofInt 64 ins.sc).toInt).toNat = (ins.c - 127) % 64 := by omega
  rw [e]

end

end Lua.Vm.Sim
