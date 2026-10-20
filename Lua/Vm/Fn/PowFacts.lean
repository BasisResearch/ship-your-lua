import Lua.Vm.Fn.PowLens
import Lua.Vm.Fn.PowR

/-!
# `__ieee754_pow`'s leaves (lane float-sf7)

The machine facts the level (b) walk applies at its leaves: the signalling
tests of `e_pow.c:121,128` (`issignaling_inline`), false on quiet operands.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.PowLens

open Lua.Num

/-- `issignaling_inline(x)` on the machine (`e_pow.c:121`, `bgeu`): not
signalling, so `x` is quiet. -/
theorem sig_ge (x : BitVec 64) (hq : PowR.NotSNaN x) :
    zopz0zKzJ_u (shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x34#6) 5 0))
      (shift_bits_left ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12))
        (Sail.BitVec.extractLsb (0x33#6) 5 0)) ^^^ x) (Sail.BitVec.extractLsb (0x01#6) 5 0)) = true := by
  rw [SfLens.sll_lit, SfLens.sll_lit, SfLens.sll_lit]
  unfold zopz0zKzJ_u
  simp only [BitVec.toNatInt, decide_eq_true_eq, ge_iff_le]
  have hx := x.isLt
  have hq' := hq
  unfold PowR.NotSNaN at hq'
  rw [Unorddf2.isNaN_fields] at hq'
  simp only [decide_eq_true_eq] at hq'
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_xor, BitVec.toNat_add, BitVec.toNat_ofNat]
  have e1 : (sign_extend (m := 64) (0x001#12)).toNat = 1 := by decide
  have e2 : (sign_extend (m := 64) (0xfff#12)).toNat = 2 ^ 64 - 1 := by decide
  rw [e1, e2]
  simp only [Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod, Nat.zero_mod, Nat.zero_add,
    Nat.one_mul, Nat.pow_one]
  rw [Nat.xor_comm, show (2251799813685248 : Nat) = 2 ^ 51 by rfl, nat_xor_51]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_le]
  omega

end Lua.Vm.Fn.PowLens
