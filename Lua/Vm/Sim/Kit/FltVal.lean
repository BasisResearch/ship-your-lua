import Lua.Vm.Sim.Kit.AtFloat
import Lua.Vm.Sim.Kit.AtCond

/-!
# Float values on the machine (lane float-m0, M1)

What every float arm reads off the soft-float routines' specifications
(`Lua.Vm.Fn.<R>.S`, `SoftFloatSpec`) once:

* the machine's 0/1 answers of the comparisons (`slti 0` of `__ledf2`,
  `seqz` of `__eqdf2`, `not; srli 63` of `__gedf2`, `blez`/`slti 1` in
  `floatforloop`) as `F64`'s order (`F64.lt`, `F64.le`, `F64.eq`), and so
  `Float.Model`'s (`F64.lt_eq_model`, …);
* a payload's model (`F64.toModel`: the register's value, `ValRepr.flt`),
  and the round trip `toModel_toBits`;
* the immediates the arms convert (`sB`, `sC`, `sBx`) as integers;
* the kernels' float cases (`δ` on a float and an integer immediate).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Num

/-! ## The model of a payload -/

/-- **The round trip**: a model datum's bits read back as the datum. -/
theorem toModel_toBits (y : Float.Model) : F64.toModel y.toBits.toBitVec = y := by
  obtain ⟨b, hv⟩ := y
  have e : Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 b.toBitVec) = b.toBitVec := by
    rw [F64.unpack_eq]
    by_cases hc : F64.cls b.toBitVec = .nan
    · rw [hc]
      have hn := hv.eq_packedNaN
      simp only [F64.cls] at hc
      split at hc
      · split at hc
        · cases hc
        · rename_i h1 h2
          refine (hn ?_ ?_).symm
          · exact (F64.exp_eq_ones _).2 h1
          · exact fun e => h2 ((F64.man_eq_zero _).1 e)
      · split at hc
        · split at hc <;> cases hc
        · cases hc
    · exact F64.pack_cls _ hc
  simp only [F64.toModel, Float.Model.ofBits, Float.Model.pack, Float.Model.mk.injEq]
  rw [e]

/-- `F64.ofInt` read as the model's conversion. -/
theorem toModel_ofInt (i : BitVec 64) : F64.toModel (F64.ofInt i) = Float.Model.ofInt i.toInt := by
  rw [F64.ofInt_eq_model, toModel_toBits]

/-- A computed float as a register's representation (`Value.ofFloat`). -/
theorem _root_.Lua.Vm.Sim.ValRepr.ofFloat_of {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {y : Float.Model}
    (ht : t = BitVec.ofNat 8 vNumFlt) (hx : x = y.toBits.toBitVec) :
    ValRepr mo ι t x (Value.ofFloat y) := by
  subst ht hx
  have := ValRepr.flt (mo := mo) (ι := ι) (x := y.toBits.toBitVec)
  rwa [show Float.Model.ofBits (UInt64.ofBitVec y.toBits.toBitVec) = y from toModel_toBits y] at this

/-- A float register's tag and model. -/
theorem _root_.Lua.Vm.Sim.ValRepr.flt_parts {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {y : Float.Model} {n : Bool}
    (h : ValRepr mo ι t x (.flt y n)) : t = BitVec.ofNat 8 vNumFlt ∧ F64.toModel x = y ∧ x.msb = n := by
  cases h with
  | flt => exact ⟨rfl, rfl, rfl⟩

/-! ## The comparisons' answers -/

theorem zext_bit (b : Bool) : zero_extend (m := 64) (bool_to_bit b) = if b then 1#64 else 0#64 := by
  cases b <;> decide

/-- `slti a0, a0, 0` of `__ledf2` (`luai_numlt`). -/
theorem slt_ledf2 (a b : BitVec 64) :
    zopz0zI_s (Lua.Vm.Fn.Ledf2.S a b) 0#64 = F64.lt a b := by
  unfold Lua.Vm.Fn.Ledf2.S F64.lt
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `slti a5, a0, 1` of `__ledf2` (`luai_numle`). -/
theorem slt1_ledf2 (a b : BitVec 64) :
    zopz0zI_s (Lua.Vm.Fn.Ledf2.S a b) 1#64 = F64.le a b := by
  unfold Lua.Vm.Fn.Ledf2.S F64.le
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `seqz` of `__eqdf2` (`luai_numeq`). -/
theorem seqz_eqdf2 (a b : BitVec 64) :
    zopz0zI_u (Lua.Vm.Fn.Eqdf2.S a b) 1#64 = F64.eq a b := by
  unfold Lua.Vm.Fn.Eqdf2.S
  cases F64.eq a b <;> decide

/-- `not; srli 63` of `__gedf2` (`luai_numge`): `b ≤ a`. -/
theorem ge_gedf2 (a b : BitVec 64) :
    shift_bits_right (Lua.Vm.Fn.Gedf2.S a b ^^^ 0xffffffffffffffff#64)
      (Sail.BitVec.extractLsb (0x3f#64) 5 0) = if F64.le b a then 1#64 else 0#64 := by
  unfold Lua.Vm.Fn.Gedf2.S F64.le
  rw [F64.compare_swap a b]
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `blez` of `__gedf2(step, 0)` (`floatforloop`'s `luai_numlt(0, step)`, negated). -/
theorem blez_gedf2 (a b : BitVec 64) :
    zopz0zKzJ_s (0#64) (Lua.Vm.Fn.Gedf2.S a b) = !F64.lt b a := by
  unfold Lua.Vm.Fn.Gedf2.S F64.lt
  rw [F64.compare_swap a b]
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-! ## Immediates -/

/-- `sB` (`addiw a0, a5, -127` of `zext.b (srliw s4, 16)`), as `__floatsidf` reads it. -/
theorem sb_fsi : ∀ b : Nat, b < 256 →
    ((sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 b + 0xffffffffffffff81#64) 31 0)).setWidth 32).signExtend 64
      = BitVec.ofInt 64 ((b : Int) - 127) := by
  decide +kernel

/-- `sBx` (`lui a5, 0xffff0; addiw a5, a5, 1; addw a0, a5, (srliw s4, 15)`), as
`__floatsidf` reads it. -/
theorem sbx_fsi (bx : Nat) (h : bx < 2 ^ 17) :
    ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (0xffffffffffff0000#64 + 0x1#64) 31 0)) 31 0) +
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 bx) 31 0))).setWidth 32).signExtend 64
      = BitVec.ofInt 64 ((bx : Int) - 65535) := by
  have e1 : Sail.BitVec.extractLsb (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (0xffffffffffff0000#64 + 0x1#64) 31 0)) 31 0 = 0xffff0001#32 := by decide
  have e2 : Sail.BitVec.extractLsb (BitVec.ofNat 64 bx) 31 0 = BitVec.ofNat 32 bx := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb]
  rw [e1, e2]
  have e3 : (sign_extend (m := 64) (0xffff0001#32 + BitVec.ofNat 32 bx)).setWidth 32 =
      0xffff0001#32 + BitVec.ofNat 32 bx := by
    simp only [sign_extend, Sail.BitVec.signExtend]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend, hi]
    intro; omega
  rw [e3]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt,
    Int.bmod_eq_of_le (by omega) (by omega), BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  split <;> omega

/-- `0.0`'s bits. -/
theorem toModel_zero : F64.toModel 0#64 = Lua.Num.zero := by decide +kernel

/-- `luai_numadd` commutes (`F64.add_comm` through the round trip). -/
theorem model_add_comm (a b : Float.Model) : Float.Model.add a b = Float.Model.add b a := by
  have h := F64.add_comm a.toBits.toBitVec b.toBits.toBitVec
  rw [F64.add_eq_model, F64.add_eq_model, toModel_toBits, toModel_toBits] at h
  have := congrArg F64.toModel h
  rwa [toModel_toBits, toModel_toBits] at this

/-- `GETARG_Bx` has 17 bits. -/
theorem Word.bx_lt (w : Word) : w.bx < 2 ^ 17 := by
  simp only [Word.bx, Word.field]; exact Nat.mod_lt _ (by decide)

/-- `GETARG_C` is a byte. -/
theorem Word.c_lt (w : Word) : w.c < 256 := by
  simp only [Word.c, Word.field]; exact Nat.mod_lt _ (by decide)

theorem toInt_imm : ∀ b : Nat, b < 256 → (BitVec.ofInt 64 ((b : Int) - 127)).toInt = (b : Int) - 127 := by
  decide +kernel

/-- `ofI` of an 8-bit immediate is the model's conversion. -/
theorem ofI_imm (b : Nat) (hb : b < 256) :
    ofI (BitVec.ofInt 64 ((b : Int) - 127)) = Float.Model.ofInt ((b : Int) - 127) := by
  simp only [ofI, toInt_imm b hb]

/-- `l_intfitsf` of an 8-bit immediate. -/
theorem intfitsf_imm : ∀ b : Nat, b < 256 → intfitsf (BitVec.ofInt 64 ((b : Int) - 127)) = true := by
  decide +kernel

/-! ## The kernels' float cases -/

/-- `LTnum` of a float and an immediate (`op_orderI`, `luai_numlt`). -/
theorem δ_lt_fi (x : Float.Model) (n : Bool) (b : Nat) (hb : b < 256) :
    δ .lt [.flt x n, .int (BitVec.ofInt 64 ((b : Int) - 127))] =
      some (.bool (Float.Model.lt x (ofI (BitVec.ofInt 64 ((b : Int) - 127))))) := by
  simp [δ, Value.toNum?, ltNum, ltFloatInt, intfitsf_imm b hb]

/-- `LEnum` of an immediate and a float (`GEI`: `i <= x`). -/
theorem δ_le_if (x : Float.Model) (n : Bool) (b : Nat) (hb : b < 256) :
    δ .le [.int (BitVec.ofInt 64 ((b : Int) - 127)), .flt x n] =
      some (.bool (Float.Model.le (ofI (BitVec.ofInt 64 ((b : Int) - 127))) x)) := by
  simp [δ, Value.toNum?, leNum, leIntFloat, intfitsf_imm b hb]

/-- **Open (lane float-m0): `OP_EQI` on a float.** `lvm.c`'s `OP_EQI` tests
`luai_numeq(fltvalue(ra), cast_num(im))` (`__eqdf2` on the ELF); the
kernel's test is `δ .eq`, `luaV_equalobj`'s mixed case (`luaV_tointegerns`
with `F2Ieq` on the float, `eqNum`). For an 8-bit immediate the two agree
(an integral float within `2^53` converts exactly). Supplied by a
`Lua.Num` lemma relating `flttointeger … .eq` to `Float.Model.beq` (open);
the ELF's `EQI` on floats is evidenced by `c/tests/float/` (`==`). -/
def EqiFlt_Statement : Prop := ∀ (x : Float.Model) (n : Bool) (b : Nat), b < 256 →
  δ .eq [.flt x n, .int (BitVec.ofInt 64 ((b : Int) - 127))] =
    some (.bool (Float.Model.beq x (ofI (BitVec.ofInt 64 ((b : Int) - 127)))))

end Lua.Vm.Sim.At
