import Lua.Vm.Arms.Head
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites

/-!
# Instruction fields as `luaV_execute` computes them (A1)

The arms of `luaV_execute` decode the 32-bit instruction in s4 with RV64
shifts and masks (`srliw`, `zext.b`, `andi`, `slli`, `addw`); the generated
segment theorems (`Lua.Vm.Arms.seg_*`) state their results as Sail
bit-vector terms. These lemmas turn each such term into the `Nat` field of
`Lua.Bytecode.Word` (`GETARG_A`, `GETARG_B`, `GETARG_sBx`, `GETARG_sJ`, the
opcode) once, for every instruction word:

* `extract_sext`: `lw`'s sign extension read back as 32 bits;
* `opcode_mask`: `andi a4,s4,127` of the sign-extended word;
* `field8`: `srliw k` then `zext.b` (the 8-bit fields A, B, C);
* `shl_ofNat`: `slli` of a value below `2^64`;
* `sext_add_shr`: `addw` of a negative bias and `srliw k` (the signed
  fields sBx, sJ, as `n + 2^64 - bias`);
* `imm12`: a non-negative 12-bit immediate.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

/-- `extractLsb 31 0` undoes a 32-to-64-bit sign extension. -/
theorem extract_sext (x : BitVec 32) : Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0 = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : i < 32 := by omega
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend]
  simp [h1, show i < 64 by omega]

theorem sext_toNat_small (x : BitVec 32) (h : x.toNat < 2 ^ 31) :
    (BitVec.signExtend 64 x).toNat = x.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp; omega
  · rw [BitVec.msb_eq_decide]; simp; omega

theorem shr_lt_two_pow_31 (n k : Nat) (hn : n < 2 ^ 32) (hk : 1 ≤ k) : n >>> k < 2 ^ 31 := by
  rw [Nat.shiftRight_eq_div_pow]
  have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have := Nat.div_le_div_left h2 (by decide : 0 < 2 ^ 1) (a := n)
  omega

/-- `andi rd, rs, 127` of a sign-extended word: the opcode field. -/
theorem opcode_mask (x : BitVec 32) :
    sign_extend (m := 64) x &&& sign_extend (m := 64) (0x07f#12)
      = BitVec.ofNat 64 (x.toNat % 2 ^ 7) := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h127 : BitVec.signExtend 64 (0x07f#12) = BitVec.ofNat 64 (2 ^ 7 - 1) := by decide
  rw [BitVec.getLsbD_and, h127, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, BitVec.getLsbD_signExtend]
  by_cases h : i < 7
  · simp [h, hi, show i < 32 by omega, BitVec.testBit_toNat]
  · simp [h]

/-- `srliw rd, rs, k` then `zext.b`: an 8-bit field. -/
theorem field8 (x : BitVec 32) (k : Nat) (hk : 1 ≤ k) (hk2 : k < 32) :
    sign_extend (m := 64) (shift_bits_right x (BitVec.ofNat 5 k)) &&& sign_extend (m := 64) (0x0ff#12)
      = BitVec.ofNat 64 ((x.toNat >>> k) % 2 ^ 8) := by
  simp only [sign_extend, Sail.BitVec.signExtend, shift_bits_right]
  apply BitVec.eq_of_toNat_eq
  have hs : (x >>> (BitVec.ofNat 5 k)).toNat = x.toNat >>> k := by
    simp [Nat.mod_eq_of_lt (show k < 32 by omega)]
  have hlt := shr_lt_two_pow_31 x.toNat k x.isLt hk
  rw [BitVec.toNat_and, sext_toNat_small _ (hs ▸ hlt), hs]
  have h255 : (BitVec.signExtend 64 (0x0ff#12)).toNat = 2 ^ 8 - 1 := by decide
  rw [h255, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

/-- A non-negative 12-bit immediate. -/
theorem imm12 (k : Nat) (hk : k < 2048) :
    sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · simp; omega
  · rw [BitVec.msb_eq_decide]; simp; omega

/-- `addi`/an address `rs + imm` of a value below `2^64`. -/
theorem add_imm (n k : Nat) (hk : k < 2048) :
    BitVec.ofNat 64 n + sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (n + k) := by
  rw [imm12 k hk, BitVec.ofNat_add_ofNat]

/-- `slli rd, rs, k`. -/
theorem shl_ofNat (n k : Nat) (hk : k < 64) :
    shift_bits_left (BitVec.ofNat 64 n) (Sail.BitVec.extractLsb (BitVec.ofNat 6 k) 5 0)
      = BitVec.ofNat 64 (n * 2 ^ k) := by
  simp only [shift_bits_left, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

/-- `addw` of a bias `C = 2^32 - off` and `srliw k`, sign-extended: the
signed field `n - off`, as `n + 2^64 - off`. -/
theorem sext_add_shr (C x : BitVec 32) (k off : Nat) (hk : 1 ≤ k) (hk2 : k < 32)
    (hC : C.toNat + off = 2 ^ 32) (hoff : off ≤ 2 ^ 31) :
    sign_extend (m := 64) (C + shift_bits_right x (BitVec.ofNat 5 k))
      = BitVec.ofNat 64 (x.toNat >>> k + 2 ^ 64 - off) := by
  simp only [sign_extend, Sail.BitVec.signExtend, shift_bits_right]
  apply BitVec.eq_of_toNat_eq
  have hs : (x >>> (BitVec.ofNat 5 k)).toNat = x.toNat >>> k := by
    simp [Nat.mod_eq_of_lt (show k < 32 by omega)]
  have hlt := shr_lt_two_pow_31 x.toNat k x.isLt hk
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.toNat_add, hs, BitVec.msb_eq_decide,
    BitVec.toNat_add, hs, BitVec.toNat_ofNat]
  generalize x.toNat >>> k = n at hlt ⊢
  have hc := C.isLt
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> omega

/-- **A register's slot address**, `base + 16·field`: `srliw k`, `zext.b`,
`slli 4`, `add` of the base (`RA(i)`, `RB(i)`). -/
theorem slot_addr (base k : Nat) (x : BitVec 32) (hk : 1 ≤ k) (hk2 : k < 32) :
    BitVec.ofNat 64 base + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (BitVec.ofNat 5 k))) &&&
      sign_extend (m := 64) (0x0ff#12)) (Sail.BitVec.extractLsb (0x04#6) 5 0)
      = BitVec.ofNat 64 (base + 16 * ((x.toNat >>> k) % 2 ^ 8)) := by
  rw [extract_sext, field8 x k hk hk2, shl_ofNat _ 4 (by decide), BitVec.ofNat_add_ofNat]
  congr 1
  omega

/-- A slot address plus an immediate, read as a `Nat`. -/
theorem slot_toNat (base k j : Nat) (x : BitVec 32) (hk : 1 ≤ k) (hk2 : k < 32) (hj : j < 2048)
    (hb : base + 16 * 256 + j < 2 ^ 64) :
    ((BitVec.ofNat 64 base + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (BitVec.ofNat 5 k))) &&&
      sign_extend (m := 64) (0x0ff#12)) (Sail.BitVec.extractLsb (0x04#6) 5 0))
      + sign_extend (m := 64) (BitVec.ofNat 12 j)).toNat
      = base + 16 * ((x.toNat >>> k) % 2 ^ 8) + j := by
  rw [slot_addr base k x hk hk2, add_imm _ j hj, BitVec.toNat_ofNat]
  have : (x.toNat >>> k) % 2 ^ 8 < 256 := Nat.mod_lt _ (by decide)
  omega

/-- `sd` of a 64-bit register stores it unchanged. -/
theorem sdData_sext (x : BitVec 64) : sdData_val (sign_extend (m := 64) x) = x := by
  simp only [sdData_val, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  omega

/-- `sb` of a zero-extended byte stores the byte. -/
theorem stData_zext (b : BitVec 8) : stData 1 (zero_extend (m := 64) b) = b := by
  simp only [stData, zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  omega

/-- The `Nat` form of a signed field is the bytecode's `Int` one. -/
theorem ofNat_bias (n off : Nat) (h : off ≤ 2 ^ 63) :
    BitVec.ofNat 64 (n + 2 ^ 64 - off) = BitVec.ofInt 64 ((n : Int) - off) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

end Lua.Vm.Sim

namespace Lua.Vm.Sim

/-- `sd` of a 64-bit value stores it unchanged. -/
theorem sdData_id (x : BitVec 64) : sdData_val x = x := by
  have := sdData_sext x
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq] at this
  exact this

/-- **The arms' address arithmetic**: normalise the slot, immediate and
field terms of a generated segment's side condition to `BitVec.ofNat`, read
`toNat`, and close with `omega` over the facts in context. -/
macro "arm_arith" : tactic => `(tactic| (
  simp (config := { decide := true }) only [extract_sext, field8, add_imm, shl_ofNat,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.add_zero]
  omega))

end Lua.Vm.Sim
