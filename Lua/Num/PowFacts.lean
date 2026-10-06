import Lua.Num.Pow

/-!
# Kernel-checked facts about `Lua/Num/Pow.lean`

Each is one `decide +kernel`, so `pow` evaluates in the kernel. Every value
here was also measured on the ELF on Sail (`c/tests/float/run_pow.sh`,
vectors in `c/tests/float/pow.vec`).
-/

namespace Lua.Num

local notation "F" b => Float.Model.ofBits b

/-- `2 ^ 0.5` is `sqrt 2` (`e_pow.c:166-168`). -/
theorem pow_2_half : pow (F 0x4000000000000000) (F 0x3FE0000000000000) = F 0x3FF6A09E667F3BCD := by
  decide +kernel

/-- `2 ^ 10 = 1024`, exact (the general path, `e_pow.c:220-318`). -/
theorem pow_2_10 : pow (F 0x4000000000000000) (F 0x4024000000000000) = F 0x4090000000000000 := by
  decide +kernel

/-- `10 ^ -1` is `one/x` (`e_pow.c:163`): the double nearest `0.1`. -/
theorem pow_10_m1 : pow (F 0x4024000000000000) (F 0xBFF0000000000000) = F 0x3FB999999999999A := by
  decide +kernel

/-- `10 ^ -3` (inexact, the general path, `e_pow.c:220-318`): the double
nearest `0.001`. -/
theorem pow_10_m3 : pow (F 0x4024000000000000) (F 0xC008000000000000) = F 0x3F50624DD2F1A9FC := by
  decide +kernel

/-- `0.1 ^ 3` (with `0.1` the double `0x3FB999999999999A`). -/
theorem pow_tenth_3 : pow (F 0x3FB999999999999A) (F 0x4008000000000000) = F 0x3F50624DD2F1A9FD := by
  decide +kernel

/-- `3 ^ 1.5` (inexact). -/
theorem pow_3_1_5 : pow (F 0x4008000000000000) (F 0x3FF8000000000000) = F 0x4014C8DC2E423980 := by
  decide +kernel

/-- `(-8) ^ (1/3)` is NaN (`e_pow.c:191`). -/
theorem pow_m8_third : pow (F 0xC020000000000000) (F 0x3FD5555555555555) = .nan := by
  decide +kernel

/-- `0 ^ -1 = +inf` (`e_pow.c:174-184`). -/
theorem pow_0_m1 : pow (F 0) (F 0xBFF0000000000000) = .inf := by
  decide +kernel

/-- `(-0) ^ -1 = -inf` (`e_pow.c:163`: `one/x`). -/
theorem pow_m0_m1 : pow (F 0x8000000000000000) (F 0xBFF0000000000000) = F 0xFFF0000000000000 := by
  decide +kernel

/-- `(-0) ^ -3 = -inf` (`e_pow.c:182`, odd integer). -/
theorem pow_m0_m3 : pow (F 0x8000000000000000) (F 0xC008000000000000) = F 0xFFF0000000000000 := by
  decide +kernel

/-- `1 ^ nan = 1` (`e_pow.c:128`). -/
theorem pow_1_nan : pow (F 0x3FF0000000000000) .nan = F 0x3FF0000000000000 := by
  decide +kernel

/-- `nan ^ 0 = 1` (`e_pow.c:120-123`). -/
theorem pow_nan_0 : pow .nan (F 0) = F 0x3FF0000000000000 := by
  decide +kernel

/-- `0 ^ 0 = 1` (`w_pow.c:71-76`). -/
theorem pow_0_0 : pow (F 0) (F 0) = F 0x3FF0000000000000 := by
  decide +kernel

/-- `2 ^ 1024` overflows to `+inf` (`e_pow.c:276-280`, `__math_oflow`). -/
theorem pow_2_1024 : pow (F 0x4000000000000000) (F 0x4090000000000000) = .inf := by
  decide +kernel

/-- `2 ^ -1074` is the least subnormal (`scalbn`, `e_pow.c:316`). -/
theorem pow_2_m1074 : pow (F 0x4000000000000000) (F 0xC090C80000000000) = F 1 := by
  decide +kernel

/-- `(-2) ^ -3 = -0.125` (`sign = -one`, `e_pow.c:194-196`). -/
theorem pow_m2_m3 : pow (F 0xC000000000000000) (F 0xC008000000000000) = F 0xBFC0000000000000 := by
  decide +kernel

/-- `(1 + 2^-52) ^ 2^65` overflows (`|y| > 2^64`, `e_pow.c:200-205`). -/
theorem pow_near1_huge : pow (F 0x3FF0000000000001) (F 0x4400000000000000) = .inf := by
  decide +kernel

/-- `x ^ 2` is `x * x` in Lua (`luai_numpow`, `llimits.h:339-342`). -/
theorem numpow_3_2 : numpow (F 0x4008000000000000) (F 0x4000000000000000) = F 0x4022000000000000 := by
  decide +kernel

end Lua.Num
