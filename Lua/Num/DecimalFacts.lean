import Lua.Num.Decimal

/-!
# Kernel-checked facts about `Lua/Num/Decimal.lean`

Each is one `decide +kernel`, so the definitions evaluate in the kernel, as
`bcSem_of_run` needs for concrete programs. Every value here was measured on
the ELF on Sail (`c/tests/float/run.sh`).
-/

namespace Lua.Num

/-- The bytes of an ASCII string. -/
def ascii (s : String) : List UInt8 := s.toList.map (·.toNat.toUInt8)

/-! ## The escape programs' numbers (`Lua/Programs/Escape.lean`) -/

/-- `"1.5"` is the float `1.5` (`"1.5"+1`, `-"1.5"`). -/
theorem str2number_1_5 :
    str2number (ascii "1.5") = some (.flt (Float.Model.ofBits 0x3ff8000000000000)) := by
  decide +kernel

/-- `"2"` is the integer `2` (`for i=1,"2"`). -/
theorem str2number_2 : str2number (ascii "2") = some (.int 2) := by decide +kernel

/-- `2.5` prints as `2.5`. -/
theorem tostring_2_5 : tostringbuffBits 0x4004000000000000#64 = ascii "2.5" := by decide +kernel

/-- `-1.5` prints as `-1.5`. -/
theorem tostring_neg_1_5 : tostringbuffBits 0xbff8000000000000#64 = ascii "-1.5" := by
  decide +kernel

/-- `1.0` prints as `1.0` (`tostringbuff`'s `.0`). -/
theorem tostring_1 : tostringbuffBits 0x3ff0000000000000#64 = ascii "1.0" := by decide +kernel

/-- `-0.0` prints as `-0.0`. -/
theorem tostring_neg0 : tostringbuffBits 0x8000000000000000#64 = ascii "-0.0" := by
  decide +kernel

/-! ## `%.14g` boundaries -/

/-- `1e15` switches to `%e` style (`expt > 14`). -/
theorem tostring_1e15 : tostringbuffBits 0x430c6bf526340000#64 = ascii "1e+15" := by
  decide +kernel

/-- `2^53` rounds to 14 digits. -/
theorem tostring_2p53 : tostringbuffBits 0x4340000000000000#64 = ascii "9.007199254741e+15" := by
  decide +kernel

/-- `100000000000000.5` rounds to `1e+14`. -/
theorem tostring_1e14_half :
    tostringbuffBits 0x42d6bcc41e900020#64 = ascii "1e+14" := by
  decide +kernel

/-- `_dtoa_r`'s small-integer path keeps trailing zeros on a 14th-digit tie
(`keepsZeros`): `649981820981505` and `100000000000005`. -/
theorem tostring_keeps_zeros :
    tostringbuffBits 0x4302793d7c668808#64 = ascii "6.4998182098150e+14" ∧
    tostringbuffBits 0x42d6bcc41e900140#64 = ascii "1.0000000000000e+14" := by
  decide +kernel

/-- The smallest subnormal. -/
theorem tostring_min_sub : tostringbuffBits 1#64 = ascii "4.9406564584125e-324" := by
  decide +kernel

/-- A negative NaN prints `-nan` (newlib `signbit`); the ELF's `0/0` is the
positive canonical NaN and prints `nan`. -/
theorem tostring_nan : tostringbuffBits 0x7ff8000000000000#64 = ascii "nan" ∧
    tostringbuffBits 0xfff8000000000000#64 = ascii "-nan" := by
  decide +kernel

/-! ## newlib `gethex`'s deviations from correct rounding (`gethexRound`) -/

/-- `0x40000000000003p0` (`2^54+3`) reads as `2^54`: the sticky bit just
below the round bit is missed. The decimal numeral of the same value is
correctly rounded to `2^54+4`. -/
theorem gethex_sticky :
    str2d (ascii "0x40000000000003p0") = some (Float.Model.ofBits 0x4350000000000000) ∧
    str2d (ascii "18014398509481987.0") = some (Float.Model.ofBits 0x4350000000000001) := by
  decide +kernel

/-- `0x1.00000000000001p-1075`, just above half the smallest subnormal,
reads as `0`, not `2^-1074`. -/
theorem gethex_subnormal :
    str2d (ascii "0x1.00000000000001p-1075") = some zero := by
  decide +kernel

/-- The binary exponent is a 32-bit `Long`: `p4294967296` is `p0`. -/
theorem gethex_wrap :
    str2d (ascii "0x1p4294967296") = some (Float.Model.ofBits 0x3ff0000000000000) := by
  decide +kernel

/-! ## `l_str2d`'s rejections -/

/-- `inf`, `nan` and anything whose first of `.xXnN` is `n`/`N` are not
numerals; an embedded `\0` is not either. -/
theorem str2number_rejects :
    str2number (ascii "inf") = none ∧ str2number (ascii "nan") = none ∧
    str2number (ascii "1e5N") = none ∧ str2number [49, 0] = none := by
  decide +kernel

end Lua.Num
