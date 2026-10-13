import Lua.Vm.Sim.Kit.FltVal
import Lua.Vm.Fn.Floor

/-!
# Float values of the order arms (round-5 bake-off, A-INC)

What `OP_LT`'s float paths read off the soft-float routines beyond
`Kit/FltVal.lean`:

* the comparison idioms `sgtz` of `__gedf2`, `srli 63` of `__ledf2`, the
  branches `bltz`/`bgez` on `__gedf2`/`__ledf2` and `beqz` on `__eqdf2`, each
  the 4-valued compare evaluated (`rcases … <;> decide`);
* `l_intfitsf`'s unsigned window (`bgeu`/`bltu`);
* the `.rodata` constants of `luaV_flttointeger`'s range check
  (`(double)LUA_MININTEGER`, `-(double)LUA_MININTEGER`) and `1.0`;
* `__fixdfdi` against the model's `toInt64` off NaN (`fixdfdi_model`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Num

/-! ## Comparison idioms -/

/-- `sgtz` of `__gedf2(a, b)`: `b < a`. -/
theorem sgtz_gedf2 (a b : BitVec 64) : zopz0zI_s 0#64 (Lua.Vm.Fn.Gedf2.S a b) = F64.lt b a := by
  unfold Lua.Vm.Fn.Gedf2.S F64.lt
  rw [F64.compare_swap a b]
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `bltz` on `__gedf2(a, b)`: not `b ≤ a`. -/
theorem bltz_gedf2 (a b : BitVec 64) : zopz0zI_s (Lua.Vm.Fn.Gedf2.S a b) 0#64 = !F64.le b a := by
  unfold Lua.Vm.Fn.Gedf2.S F64.le
  rw [F64.compare_swap a b]
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `bgez` on `__ledf2(a, b)`: not `a < b`. -/
theorem bgez_ledf2 (a b : BitVec 64) : zopz0zKzJ_s (Lua.Vm.Fn.Ledf2.S a b) 0#64 = !F64.lt a b := by
  unfold Lua.Vm.Fn.Ledf2.S F64.lt
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `srli 63` of `__ledf2(a, b)`: `a < b`. -/
theorem srl63_ledf2 (a b : BitVec 64) :
    shift_bits_right (Lua.Vm.Fn.Ledf2.S a b) (Sail.BitVec.extractLsb (0x3f#64) 5 0) =
      if F64.lt a b then 1#64 else 0#64 := by
  unfold Lua.Vm.Fn.Ledf2.S F64.lt
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

/-- `beqz` on `__eqdf2(a, b)`: `a = b`. -/
theorem beqz_eqdf2 (a b : BitVec 64) : (Lua.Vm.Fn.Eqdf2.S a b == 0x0#64) = F64.eq a b := by
  unfold Lua.Vm.Fn.Eqdf2.S
  cases F64.eq a b <;> decide

/-- `sext.w` of a 0/1 answer. -/
theorem sext_ite (b : Bool) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((if b then 1#64 else 0#64) + 0x0#64) 31 0) =
      if b then 1#64 else 0#64 := by
  cases b <;> decide

/-! ## `l_intfitsf` -/

/-- `bgeu` of `l_intfitsf`'s window: the integer fits. -/
theorem fits_ge (i : BitVec 64) :
    zopz0zKzJ_u 0x40000000000000#64 (i + 0x20000000000000#64) = intfitsf i := by
  unfold zopz0zKzJ_u intfitsf
  simp only [Sail.BitVec.toNatInt, BitVec.add_comm i]
  simp; omega

/-- `bltu` of `l_intfitsf`'s window: the integer does not fit. -/
theorem fits_lt (i : BitVec 64) :
    zopz0zI_u 0x40000000000000#64 (i + 0x20000000000000#64) = !intfitsf i := by
  unfold zopz0zI_u intfitsf
  simp only [Sail.BitVec.toNatInt, BitVec.add_comm i]
  rw [Bool.eq_iff_iff]; simp; omega

/-! ## `.rodata` constants -/

/-- An 8-byte `.rodata` read. -/
theorem rod8 {m : Mem} (h : RodataRead m) (o : Nat) (ho : o + 8 ≤ Image.rodataSize) :
    bytesT8 m (Image.rodataBase + o) =
      (((((((Image.rodataByte (o + 7)).append (Image.rodataByte (o + 6))).append
        (Image.rodataByte (o + 5))).append (Image.rodataByte (o + 4))).append
        (Image.rodataByte (o + 3))).append (Image.rodataByte (o + 2))).append
        (Image.rodataByte (o + 1))).append (Image.rodataByte o) := by
  have hb := fun i (hi : i < 8) => h (o + i) (by omega)
  simp only [bytesT1, ← Nat.add_assoc] at hb
  have h0 := hb 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT8, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega),
    hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]

/-- `(double)LUA_MININTEGER` at `0x8005c478`. -/
theorem rod_min {m : Mem} (h : RodataRead m) : bytesT8 m 2147861624 = 0xc3e0000000000000#64 := by
  have := rod8 h (2147861624 - Image.rodataBase) (by decide)
  rw [show Image.rodataBase + (2147861624 - Image.rodataBase) = 2147861624 by decide] at this
  rw [this]; decide

/-- `-(double)LUA_MININTEGER` at `0x8005c480`. -/
theorem rod_max {m : Mem} (h : RodataRead m) : bytesT8 m 2147861632 = 0x43e0000000000000#64 := by
  have := rod8 h (2147861632 - Image.rodataBase) (by decide)
  rw [show Image.rodataBase + (2147861632 - Image.rodataBase) = 2147861632 by decide] at this
  rw [this]; decide

/-- `1.0` at `0x8005c488`. -/
theorem rod_one {m : Mem} (h : RodataRead m) : bytesT8 m 2147861640 = 0x3ff0000000000000#64 := by
  have := rod8 h (2147861640 - Image.rodataBase) (by decide)
  rw [show Image.rodataBase + (2147861640 - Image.rodataBase) = 2147861640 by decide] at this
  rw [this]; decide

theorem toModel_min : F64.toModel 0xc3e0000000000000#64 = minIntF := by decide +kernel
theorem toModel_max : F64.toModel 0x43e0000000000000#64 = Float.Model.neg minIntF := by decide +kernel
theorem toModel_one : F64.toModel 0x3ff0000000000000#64 = Float.Model.ofNat 1 := by decide +kernel

/-! ## `__fixdfdi` -/

theorem cls_inf_sign {x : F64} {a : Bool} (h : x.cls = .inf a) : a = x.sign := by
  unfold F64.cls at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

theorem cls_fin_sign {x : F64} {a : Bool} {m : Nat} {e : Int} (h : x.cls = .fin a m e) : a = x.sign := by
  unfold F64.cls at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h <;> cases h; rfl
    · cases h; rfl

theorem shr_mantissa (em : Float.Model.UnpackedFloat.ExtendedMantissa) (s : Nat) :
    (em >>> s).mantissa = em.mantissa / 2 ^ s := by
  cases s with
  | zero => show em.mantissa = em.mantissa / 1; simp
  | succ s => rw [F64.shiftRight_succ]

theorem roundToInt_eq (a : Bool) (m : Nat) (e : Int) :
    Float.Model.UnpackedFloat.roundToInt (F64.sgn a) m e =
      F64.sgnApply a (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat) := by
  unfold Float.Model.UnpackedFloat.roundToInt Float.Model.UnpackedFloat.decreaseExponent
    Float.Model.UnpackedFloat.shiftToExponent
  simp only [Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, shr_mantissa]
  cases a <;> by_cases he : 0 ≤ e <;> simp [F64.sgn, F64.sgnApply, Float.Model.UnpackedFloat.Sign.apply, he] <;>
    first
    | (rw [Int.max_eq_left he]; simp)
    | (rw [Int.max_eq_right (by omega), Int.toNat_of_nonpos (by omega)]; simp)

/-- `Int64.ofIntClamp`'s bits: saturated at both ends. -/
theorem ofIntClamp_bv (i : Int) : (Int64.ofIntClamp i).toBitVec =
    if i < -(2 ^ 63) then BitVec.ofNat 64 (2 ^ 63) else if 2 ^ 63 ≤ i then BitVec.ofNat 64 (2 ^ 63 - 1)
    else BitVec.ofInt 64 i := by
  unfold Int64.ofIntClamp
  have h1 : Int64.minValue.toInt = -(2 ^ 63) := by decide
  have h2 : Int64.maxValue.toInt = 2 ^ 63 - 1 := by decide
  split <;> rename_i ha
  · split <;> rename_i hb
    · rw [if_neg (by omega), if_neg (by omega)]; rfl
    · rw [if_neg (by omega), if_pos (by omega)]; rfl
  · rw [if_pos (by omega)]; rfl

/-- **`__fixdfdi` is the model's `toInt64`** off NaN: both truncate toward
zero and saturate by the sign. -/
theorem fixdfdi_cls (x : F64) (h : x.cls ≠ .nan) :
    Lua.Vm.Fn.Fixdfdi.S x = (F64.toModel x).toInt64.toBitVec := by
  have hu : (F64.toModel x).toInt64 = (x.cls.toU).toInt64 := by
    show (F64.toModel x).unpack.toInt64 = _
    rw [F64.toModel_unpack]
  rw [hu]
  unfold Lua.Vm.Fn.Fixdfdi.S F64.truncInt?
  rcases hc : x.cls with _ | a | a | ⟨a, m, e⟩
  · exact absurd hc h
  · have := cls_inf_sign hc; subst this
    cases hs : x.sign <;> simp [F64.Cls.toU, F64.sgn, Float.Model.UnpackedFloat.toInt64,
      Float.Model.UnpackedFloat.toInt, Int64.ofIntClamp] <;> decide
  · simp only [F64.Cls.toU, Float.Model.UnpackedFloat.toInt64, Float.Model.UnpackedFloat.toInt]
    rfl
  · have := cls_fin_sign hc; subst this
    have hv : ∀ v : Nat, (if -(2 ^ 63 : Int) ≤ F64.sgnApply x.sign v ∧ F64.sgnApply x.sign v < 2 ^ 63 then
        BitVec.ofInt 64 (F64.sgnApply x.sign v) else if x.sign then BitVec.ofNat 64 (2 ^ 63)
        else BitVec.ofNat 64 (2 ^ 63 - 1)) = (Int64.ofIntClamp (F64.sgnApply x.sign v)).toBitVec := by
      intro v
      rw [ofIntClamp_bv]
      cases x.sign
      · simp only [F64.sgnApply, Bool.false_eq_true, ite_false]
        by_cases h : (v : Int) < 2 ^ 63
        · rw [if_pos ⟨by omega, h⟩, if_neg (by omega), if_neg (by omega)]
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      · simp only [F64.sgnApply, ite_true]
        by_cases h : (v : Int) ≤ 2 ^ 63
        · rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega), if_neg (by omega)]
        · rw [if_neg (by omega), if_pos (by omega)]
    by_cases hm : 0 < m
    · simp only [F64.Cls.toU, dite_eq_left_iff, hm, dif_pos, Float.Model.UnpackedFloat.toInt64,
        Float.Model.UnpackedFloat.toInt, roundToInt_eq]
      exact hv _
    · obtain rfl : m = 0 := by omega
      simp only [Nat.zero_shiftLeft, Nat.zero_div, ite_self]
      generalize x.sign = b
      cases b <;> rfl

/-- `fixdfdi_cls` from a comparison that held (no NaN compares). -/
theorem fixdfdi_model (x : F64) (h : Float.Model.le minIntF (F64.toModel x) = true) :
    Lua.Vm.Fn.Fixdfdi.S x = (F64.toModel x).toInt64.toBitVec := by
  refine fixdfdi_cls x fun hx => ?_
  rw [← toModel_min, ← F64.le_eq_model] at h
  unfold F64.le F64.compare at h
  rw [hx] at h
  split at h <;> simp_all

end Lua.Vm.Sim.At
