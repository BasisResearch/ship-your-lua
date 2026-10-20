import Lua.Num.Pow
import Lua.Vm.Fn.PowAttr

/-!
# `e_pow.c`'s transcription in stages (lane float-sf7)

The level-(b) proof of `__ieee754_pow` follows the machine's fork tree with
the model beside it (`Lua/Vm/Fn/PowLens.lean`); where several of the
machine's paths join, the proof cuts: one lemma per join, whose right side is
the model's remaining computation. A join inside one of
`Lua/Num/Pow.lean`'s functions needs that remainder named: each stage below
is the tail of a transcribed function, from the C line the machine joins at,
and `*_stage` states the function as its head followed by the stage (`rfl`).

The stages restate `Lua/Num/Pow.lean`'s text (that module is imported by the
bytecode semantics; a change to it rebuilds the semantics and every arm), so
the transcription stays the one definition and these are checked equal to it.
-/

namespace Lua.Num.Pow

local infixl:65 " +. " => Float.Model.add
local infixl:70 " *. " => Float.Model.mul

/-- `scalbn`'s tail (`s_scalbn.c:95-106`): `x` with high word `hx` and biased
exponent `k` (`x` normal, or a subnormal scaled by `2^54`), scaled by `2^n`. -/
@[pw_stage] def scalbnTail (x : Float.Model) (hx k n : Int32) : Float.Model :=
  let twom54 := K 0x3C90000000000000   -- s_scalbn.c:74
  let huge   := K 0x7E37E43C8800759C   -- s_scalbn.c:75, 1.0e+300
  let tiny   := K 0x01A56E1FC2F8F359   -- s_scalbn.c:76, 1.0e-300
  if k == 0x7ff then x +. x                                         -- :95
  else if n > 50000 then huge *. copysign huge x                    -- :96-97
  else
    let k := k + n                                                  -- :98
    if k > 0x7fe then huge *. copysign huge x                       -- :99
    else if k > 0 then setHigh x ((u hx &&& (0x800fffff : UInt32)) ||| u (k <<< 20))  -- :100-101
    else if k ≤ -54 then tiny *. copysign tiny x                    -- :102-103
    else
      let k := k + 54                                               -- :104
      setHigh x ((u hx &&& (0x800fffff : UInt32)) ||| u (k <<< 20)) *. twom54  -- :105-106

/-- `scalbn` as its normalisation (`s_scalbn.c:87-94`) and `scalbnTail`. -/
theorem scalbn_stage (x0 : Float.Model) (n : Int32) :
    scalbn x0 n =
      let two54  := K 0x4350000000000000
      let tiny   := K 0x01A56E1FC2F8F359
      let hx0 := hiW x0
      let lx := (loW x0).toInt32
      let k0 := (hx0 &&& (0x7ff00000 : UInt32).toInt32) >>> 20
      let pre : Sum Float.Model (Float.Model × Int32 × Int32) :=
        if k0 == 0 then
          if (lx ||| (hx0 &&& 0x7fffffff)) == 0 then .inl x0
          else
            let x := x0 *. two54
            let hx := hiW x
            let k := ((hx &&& (0x7ff00000 : UInt32).toInt32) >>> 20) - 54
            if n < -50000 then .inl (tiny *. x)
            else .inr (x, hx, k)
        else .inr (x0, hx0, k0)
      match pre with
      | .inl r => r
      | .inr (x, hx, k) => scalbnTail x hx k n := rfl

end Lua.Num.Pow
