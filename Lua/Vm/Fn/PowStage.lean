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
local infixl:65 " -. " => Float.Model.sub
local infixl:70 " *. " => Float.Model.mul
local infixl:70 " /. " => Float.Model.div

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

/-- `exp2Poly`'s tail (`e_pow.c:314-318`): `z·2^n`, by `scalbn` when the
exponent leaves the normal range, times `sign`. -/
@[pw_stage] def exp2Fin (z : Float.Model) (n : Int32) (sign : Float.Model) : Float.Model :=
  let j := hiW z + (n <<< 20)                                       -- :314-315
  let z := if (j >>> 20) ≤ 0 then scalbn z n else setHigh z (u j)   -- :316-317
  sign *. z                                                         -- :318

/-- `exp2Tail`'s tail (`e_pow.c:304-318`): `2^(p_l+p_h)` by the polynomial,
scaled by `2^n`, times `sign`. -/
@[pw_stage] def exp2Poly (p_l p_h : Float.Model) (n : Int32) (sign : Float.Model) : Float.Model :=
  let t := setLow (p_l +. p_h) 0                                    -- :304-305
  let u' := t *. lg2_h                                              -- :306
  let v := (p_l -. (t -. p_h)) *. lg2 +. t *. lg2_l                 -- :307
  let z := u' +. v                                                  -- :308
  let w := v -. (z -. u')                                           -- :309
  let t := z *. z                                                   -- :310
  let t1 := z -. t *. (P1 +. t *. (P2 +. t *. (P3 +. t *. (P4 +. t *. P5)))) -- :311
  let r := (z *. t1) /. (t1 -. two) -. (w +. z *. w)                -- :312
  let z := one -. (r -. z)                                          -- :313
  exp2Fin z n sign

/-- `exp2Tail` past its overflow tests (`e_pow.c:292-318`): `n`, the integer
part of `(p_l + p_h)/ln 2` held in `z`'s high word `j`, and `exp2Poly`. -/
@[pw_stage] def exp2N (j : Int32) (p_l p_h sign : Float.Model) : Float.Model :=
  let i := j &&& 0x7fffffff                                         -- :292
  let k := (i >>> 20) - 0x3ff                                       -- :293
  let (n, p_h) : Int32 × Float.Model :=
    if i > 0x3fe00000 then                                          -- :295
      let n := j + ((0x00100000 : Int32) >>> (k + 1))               -- :296
      let k := ((n &&& 0x7fffffff) >>> 20) - 0x3ff                  -- :297
      let t := setHigh zero (u (n &&& ~~~((0x000fffff : Int32) >>> k))) -- :298-299
      let n := ((n &&& 0x000fffff) ||| 0x00100000) >>> (20 - k)     -- :300
      let n := if j < 0 then -n else n                              -- :301
      (n, p_h -. t)                                                 -- :302
    else (0, p_h)
  exp2Poly p_l p_h n sign

/-- `exp2Tail` as its overflow tests and `n` (`e_pow.c:269-302`) and `exp2Poly`. -/
theorem exp2Tail_stage (y t1 t2 sign : Float.Model) :
    exp2Tail y t1 t2 sign =
      let neg := Float.Model.lt sign zero
      let y1 := setLow y 0
      let p_l := (y -. y1) *. t1 +. y *. t2
      let p_h := y1 *. t1
      let z := p_l +. p_h
      let j := hiW z
      let i := loW z
      let early : Option Float.Model :=
        if j ≥ 0x40900000 then
          if (u (j - 0x40900000) ||| i) != 0 then some (mathOflow neg)
          else if Float.Model.lt (z -. p_h) (p_l +. ovt) then some (mathOflow neg)
          else none
        else if (j &&& 0x7fffffff) ≥ 0x4090cc00 then
          if ((u j - 0xc090cc00) ||| i) != 0 then some (mathUflow neg)
          else if Float.Model.le p_l (z -. p_h) then some (mathUflow neg)
          else none
        else none
      match early with
      | some r => r
      | none => exp2N j p_l p_h sign := rfl

/-- `exp2Tail` past `j ≥ 0x40900000` (`e_pow.c:277-281`): the overflow tests, then `exp2N`. -/
@[pw_stage] def exp2Hi (p_l p_h sign : Float.Model) : Float.Model :=
  let neg := Float.Model.lt sign zero
  let z := p_l +. p_h
  let j := hiW z
  let i := loW z
  if (u (j - 0x40900000) ||| i) != 0 then mathOflow neg
  else if Float.Model.lt (z -. p_h) (p_l +. ovt) then mathOflow neg
  else exp2N j p_l p_h sign

/-- `exp2Tail` below `j ≥ 0x40900000` (`e_pow.c:282-287`): the underflow tests, then `exp2N`. -/
@[pw_stage] def exp2Lo (p_l p_h sign : Float.Model) : Float.Model :=
  let neg := Float.Model.lt sign zero
  let z := p_l +. p_h
  let j := hiW z
  let i := loW z
  if (j &&& 0x7fffffff) ≥ 0x4090cc00 then
    if ((u j - 0xc090cc00) ||| i) != 0 then mathUflow neg
    else if Float.Model.le p_l (z -. p_h) then mathUflow neg
    else exp2N j p_l p_h sign
  else exp2N j p_l p_h sign

/-- `exp2Tail` as `p_l`, `p_h` (`e_pow.c:269-274`) and the test `j ≥ 0x40900000`. -/
theorem exp2Tail_split (y t1 t2 sign : Float.Model) :
    exp2Tail y t1 t2 sign =
      let y1 := setLow y 0
      let p_l := (y -. y1) *. t1 +. y *. t2
      let p_h := y1 *. t1
      if hiW (p_l +. p_h) ≥ 0x40900000 then exp2Hi p_l p_h sign else exp2Lo p_l p_h sign := by
  rw [exp2Tail_stage]
  simp only [exp2Hi, exp2Lo]
  generalize (y -. setLow y 0) *. t1 +. y *. t2 = p_l
  generalize setLow y 0 *. t1 = p_h
  generalize hiW (p_l +. p_h) = j
  generalize loW (p_l +. p_h) = i
  generalize (u (j - 1083179008) ||| i != 0) = a
  generalize ((u j - 3230714880) ||| i != 0) = e
  generalize Float.Model.lt (p_l +. p_h -. p_h) (p_l +. ovt) = b
  generalize Float.Model.le p_l (p_l +. p_h -. p_h) = f
  by_cases h1 : j ≥ 1083179008 <;> by_cases h2 : (j &&& 2147483647) ≥ 1083231232 <;>
    cases a <;> cases b <;> cases e <;> cases f <;> simp [h1, h2]

end Lua.Num.Pow
