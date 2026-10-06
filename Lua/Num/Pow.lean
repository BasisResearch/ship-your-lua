/-!
# `pow`: the ELF's libm `pow`, transcribed over `Float.Model`

Lua's `^` on floats is `luai_numpow(L,a,b) = (b == 2) ? (a)*(a) : pow(a,b)`
(`vendor/lua-5.4.7/src/llimits.h:339-342`). The ELF (`c/Makefile`: xPack
riscv-none-elf-gcc 15.2.0, newlib 4.5.0.20241231, `-march=rv64i -mabi=lp64`,
soft-float) links newlib's fdlibm `pow`:

| ELF symbol | address | source (newlib tag `newlib-4.5.0`) |
|---|---|---|
| `pow` | `0x8002b9fc` (70 insns) | `newlib/libm/math/w_pow.c:59-101` |
| `__ieee754_pow` | `0x8002c2a8` (893 insns) | `newlib/libm/math/e_pow.c:103-319` |
| `scalbn` | `0x8002d09c` | `newlib/libm/common/s_scalbn.c:79-107` |
| `__math_oflow`, `__math_uflow` | `0x8002d2d0`, `0x8002d2b8` | `newlib/libm/common/math_err.c:47-73` |
| `__ieee754_sqrt` | `0x8002d448` | `newlib/libm/math/e_sqrt.c` |
| `fabs` | `0x8002d78c` | `newlib/libm/math/s_fabs.c:53-63` |

Sources: `https://sourceware.org/git/?p=newlib-cygwin.git;a=blob_plain;f=newlib/libm/<dir>/<file>;hb=refs/tags/newlib-4.5.0`.
Line numbers below cite those files.

## The model of each C operation

* double `+ − × ÷` are libgcc's soft-fp `__adddf3`/`__subdf3`/`__muldf3`/
  `__divdf3`: IEEE binary64, round-to-nearest-even, and every NaN result is
  the canonical `0x7ff8000000000000` (`abstractions/ledger/float-s0a.md`,
  measured on Sail). They are `Float.Model.add/sub/mul/div`, whose NaN is
  that same canonical NaN. Unary `-` on a double is a sign flip; it is applied
  only to non-NaN values here (`e_pow.c:160,182`), so `Float.Model.neg` is
  exact.
* `__ieee754_sqrt` is fdlibm's bit-by-bit square root, correctly rounded in
  round-to-nearest (its own header comment; soft-fp has no other rounding
  mode here). It is called only for `x ≥ +0`, not NaN (`e_pow.c:166-168`), so
  it is `Float.Model.sqrt`.
* `(double)n` for `int n` (`e_pow.c:263`) is `__floatsidf`: exact, `Float.Model.ofInt`.
* `EXTRACT_WORDS`/`GET_HIGH_WORD`/`SET_LOW_WORD`/`SET_HIGH_WORD`/`INSERT_WORDS`
  (`newlib/libm/common/fdlibm.h:298-352`) are bit operations on `toBits`;
  the word types follow C (`__int32_t` = `Int32`, `__uint32_t` = `UInt32`,
  RV64 `addw`/`sllw`/`sraw` wrap like Lean's fixed-width arithmetic).
* **NaN payloads.** `Float.Model.ofBits` canonicalises NaN bit patterns, and
  `Float.Model` has only the one (quiet, positive) NaN. No step of
  `e_pow.c` reads a NaN payload of a value this model can hold: NaN inputs
  are dispatched at lines 120-130, where the only payload test is
  `issignaling_inline` (`newlib/libm/common/math_config.h:181-187`), false for
  the canonical quiet NaN; every later word operation acts on non-NaN values
  (finite, or `±∞` in `fabs`/`scalbn`), and its result is a non-NaN pattern or
  feeds a soft-fp operation that canonicalises. A signalling-NaN *input*
  (`pow(sNaN, 0)` and `pow(1, sNaN)` are NaN on the ELF, `e_pow.c:121,128`)
  is outside `Float.Model`.
* The wrapper (`w_pow.c`): newlib 4.5 is built without `_IEEE_LIBM`, so
  `_LIB_VERSION` is the constant `_POSIX_`
  (`newlib/libm/common/math_config.h:43-53`) and the ELF's `pow` is the
  `_POSIX_` path: it only sets `errno`, and its value is
  `__ieee754_pow(x,y)` except `pow(±0,±0) = 1.0` (`w_pow.c:71-76`; the ELF loads
  the constant `0x3ff0000000000000` from `0x8005c488`). `errno` is not part of
  the value and is dropped.
-/

namespace Lua.Num
namespace Pow

/-! ## Word access (`fdlibm.h:298-352`) -/

/-- `GET_HIGH_WORD` as `__int32_t`. -/
def hiW (d : Float.Model) : Int32 := (d.toBits >>> 32).toUInt32.toInt32

/-- `GET_LOW_WORD` as `__uint32_t`. -/
def loW (d : Float.Model) : UInt32 := d.toBits.toUInt32

/-- `INSERT_WORDS(d, hi, lo)`. -/
def insertWords (hi : UInt32) (lo : UInt32) : Float.Model :=
  .ofBits ((hi.toUInt64 <<< 32) ||| lo.toUInt64)

/-- `SET_LOW_WORD(d, v)`. -/
def setLow (d : Float.Model) (v : UInt32) : Float.Model := insertWords (hiW d).toUInt32 v

/-- `SET_HIGH_WORD(d, v)`. -/
def setHigh (d : Float.Model) (v : UInt32) : Float.Model := insertWords v (loW d)

/-- `__int32_t` to `__uint32_t` (C's implicit conversion: the same bits). -/
abbrev u (i : Int32) : UInt32 := i.toUInt32

/-! ## Arithmetic -/

local infixl:65 " +. " => Float.Model.add
local infixl:65 " -. " => Float.Model.sub
local infixl:70 " *. " => Float.Model.mul
local infixl:70 " /. " => Float.Model.div

/-- A double constant from its bit pattern. -/
abbrev K (b : UInt64) : Float.Model := .ofBits b

/-- `fabs` (`s_fabs.c:59-62`): clear the sign bit of the high word. -/
def fabs (x : Float.Model) : Float.Model := setHigh x (u (hiW x) &&& 0x7fffffff)

/-- `copysign` (`newlib/libm/common/s_copysign.c`): `x`'s magnitude, `y`'s sign. -/
def copysign (x y : Float.Model) : Float.Model :=
  setHigh x ((u (hiW x) &&& 0x7fffffff) ||| (u (hiW y) &&& 0x80000000))

/-- `scalbn(x, n)` (`s_scalbn.c:79-107`). -/
def scalbn (x0 : Float.Model) (n : Int32) : Float.Model :=
  let two54  := K 0x4350000000000000   -- s_scalbn.c:73
  let twom54 := K 0x3C90000000000000   -- s_scalbn.c:74
  let huge   := K 0x7E37E43C8800759C   -- s_scalbn.c:75, 1.0e+300
  let tiny   := K 0x01A56E1FC2F8F359   -- s_scalbn.c:76, 1.0e-300
  let hx0 := hiW x0
  let lx := (loW x0).toInt32
  let k0 := (hx0 &&& (0x7ff00000 : UInt32).toInt32) >>> 20             -- :87
  -- :88-94, 0 or subnormal x
  let pre : Sum Float.Model (Float.Model × Int32 × Int32) :=
    if k0 == 0 then
      if (lx ||| (hx0 &&& 0x7fffffff)) == 0 then .inl x0               -- :89
      else
        let x := x0 *. two54                                          -- :90
        let hx := hiW x                                               -- :91
        let k := ((hx &&& (0x7ff00000 : UInt32).toInt32) >>> 20) - 54 -- :92
        if n < -50000 then .inl (tiny *. x)                           -- :93
        else .inr (x, hx, k)
    else .inr (x0, hx0, k0)
  match pre with
  | .inl r => r
  | .inr (x, hx, k) =>
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

/-- `xflow(sign, y)` (`math_err.c:47-51`): `(sign ? -y : y) * y`. -/
def xflow (sign : Bool) (y : Float.Model) : Float.Model :=
  (if sign then Float.Model.neg y else y) *. y

/-- `__math_uflow` (`math_err.c:54-57`): `xflow(sign, 0x1p-767)`, a signed zero. -/
def mathUflow (sign : Bool) : Float.Model := xflow sign (K 0x1000000000000000)

/-- `__math_oflow` (`math_err.c:70-73`): `xflow(sign, 0x1p769)`, a signed infinity. -/
def mathOflow (sign : Bool) : Float.Model := xflow sign (K 0x7000000000000000)

/-- `issignaling_inline` (`math_config.h:181-187`, `IEEE_754_2008_SNAN` = 1). -/
def issignaling (x : Float.Model) : Bool :=
  2 * (x.toBits ^^^ 0x0008000000000000) > 2 * 0x7ff8000000000000

/-! ## Constants (`e_pow.c:72-100`), from the hex comments -/

def one     := K 0x3FF0000000000000
def zero    := K 0x0000000000000000
def two     := K 0x4000000000000000
def two53   := K 0x4340000000000000
def L1      := K 0x3FE3333333333303
def L2      := K 0x3FDB6DB6DB6FABFF
def L3      := K 0x3FD55555518F264D
def L4      := K 0x3FD17460A91D4101
def L5      := K 0x3FCD864A93C9DB65
def L6      := K 0x3FCA7E284A454EEF
def P1      := K 0x3FC555555555553E
def P2      := K 0xBF66C16C16BEBD93
def P3      := K 0x3F11566AAF25DE2C
def P4      := K 0xBEBBBD41C5D26BF1
def P5      := K 0x3E66376972BEA4D0
def lg2     := K 0x3FE62E42FEFA39EF
def lg2_h   := K 0x3FE62E4300000000
def lg2_l   := K 0xBE205C610CA86C39
/-- `ovt = 8.0085662595372944372e-0017` (`e_pow.c:94`, no hex comment): the
nearest double, `0x3C971547652B82FE`. -/
def ovt     := K 0x3C971547652B82FE
def cp      := K 0x3FEEC709DC3A03FD
def cp_h    := K 0x3FEEC709E0000000
def cp_l    := K 0xBE3E2FE0145B01F5
def ivln2   := K 0x3FF71547652B82FE
def ivln2_h := K 0x3FF7154760000000
def ivln2_l := K 0x3E54AE0BF85DDF44
/-- `bp[k]` (`e_pow.c:72`). -/
def bp (k : Int32) : Float.Model := if k == 0 then one else K 0x3FF8000000000000
/-- `dp_h[k]` (`e_pow.c:73`). -/
def dp_h (k : Int32) : Float.Model := if k == 0 then zero else K 0x3FE2B80340000000
/-- `dp_l[k]` (`e_pow.c:74`). -/
def dp_l (k : Int32) : Float.Model := if k == 0 then zero else K 0x3E4CFDEB43CFD006
/-- The literals `0.5`, `0.3333333333333333333333`, `0.25` (`e_pow.c:213`) and
`3.0` (`e_pow.c:250,252`). -/
def half := K 0x3FE0000000000000
def third := K 0x3FD5555555555555
def quarter := K 0x3FD0000000000000
def three := K 0x4008000000000000

/-! ## `__ieee754_pow` (`e_pow.c:103-319`) -/

/-- `yisint` (`e_pow.c:137-150`): 0 not an integer, 1 odd, 2 even; computed
only for `hx < 0`. -/
def yisint (hx iy : Int32) (ly : UInt32) : Int32 :=
  if hx < 0 then
    if iy ≥ 0x43400000 then 2                                         -- :139
    else if iy ≥ 0x3ff00000 then
      let k := (iy >>> 20) - 0x3ff                                    -- :141
      if k > 20 then
        let j := (ly >>> (52 - k).toUInt32).toInt32                   -- :143
        if (u j <<< (52 - k).toUInt32) == ly then 2 - (j &&& 1) else 0 -- :144
      else if ly == 0 then
        let j := iy >>> (20 - k)                                      -- :146
        if (j <<< (20 - k)) == iy then 2 - (j &&& 1) else 0           -- :147
      else 0
    else 0
  else 0

/-- `log2(|x|)` as `t1 + t2` for the regular case (`e_pow.c:198-267`):
`|y| > 2^31` near one (`:212-218`) or the general case (`:220-266`).
`.inl r` is an early return (`:199-209`). -/
def log2Split (x : Float.Model) (ix hy iy : Int32) (sign : Float.Model) :
    Sum Float.Model (Float.Model × Float.Model) :=
  let neg := Float.Model.lt sign zero                                 -- `sign<0`
  let ax := fabs x                                                    -- :172
  if iy > 0x42000000 then                                             -- :199
    if iy > 0x43f00000 then                                           -- :200
      if ix ≤ 0x3fefffff then .inl (if hy < 0 then mathOflow false else mathUflow false) -- :201-202
      else .inl (if hy > 0 then mathOflow false else mathUflow false)  -- :203-204
    else if ix < 0x3fefffff then .inl (if hy < 0 then mathOflow neg else mathUflow neg) -- :208
    else if ix > 0x3ff00000 then .inl (if hy > 0 then mathOflow neg else mathUflow neg) -- :209
    else
      let t := ax -. one                                              -- :212
      let w := (t *. t) *. (half -. t *. (third -. t *. quarter))      -- :213
      let u' := ivln2_h *. t                                          -- :214
      let v := t *. ivln2_l -. w *. ivln2                             -- :215
      let t1 := setLow (u' +. v) 0                                    -- :216-217
      let t2 := v -. (t1 -. u')                                       -- :218
      .inr (t1, t2)
  else
    -- :223-224, subnormal x
    let (ax, n, ix) : Float.Model × Int32 × Int32 :=
      if ix < 0x00100000 then
        let ax := ax *. two53
        (ax, -53, hiW ax)
      else (ax, 0, ix)
    let n := n + ((ix >>> 20) - 0x3ff)                                -- :225
    let j := ix &&& 0x000fffff                                        -- :226
    let ix := j ||| 0x3ff00000                                        -- :228
    let (k, n, ix) : Int32 × Int32 × Int32 :=
      if j ≤ 0x3988E then (0, n, ix)                                  -- :229
      else if j < 0xBB67A then (1, n, ix)                             -- :230
      else (0, n + 1, ix - 0x00100000)                                -- :231
    let ax := setHigh ax (u ix)                                       -- :232
    let u' := ax -. bp k                                              -- :235
    let v := one /. (ax +. bp k)                                      -- :236
    let s := u' *. v                                                  -- :237
    let s_h := setLow s 0                                             -- :238-239
    let t_h := setHigh zero (u (((ix >>> 1) ||| (0x20000000 : Int32)) + (0x00080000 : Int32) + (k <<< (18 : Int32)))) -- :241-242
    let t_l := ax -. (t_h -. bp k)                                    -- :243
    let s_l := v *. ((u' -. s_h *. t_h) -. s_h *. t_l)                -- :244
    let s2 := s *. s                                                  -- :246
    let r := s2 *. s2 *. (L1 +. s2 *. (L2 +. s2 *. (L3 +. s2 *. (L4 +. s2 *. (L5 +. s2 *. L6))))) -- :247
    let r := r +. s_l *. (s_h +. s)                                   -- :248
    let s2 := s_h *. s_h                                              -- :249
    let t_h := setLow (three +. s2 +. r) 0                            -- :250-251
    let t_l := r -. ((t_h -. three) -. s2)                            -- :252
    let u' := s_h *. t_h                                              -- :254
    let v := s_l *. t_h +. t_l *. s                                   -- :255
    let p_h := setLow (u' +. v) 0                                     -- :257-258
    let p_l := v -. (p_h -. u')                                       -- :259
    let z_h := cp_h *. p_h                                            -- :260
    let z_l := cp_l *. p_h +. p_l *. cp +. dp_l k                     -- :261
    let t := Float.Model.ofInt n.toInt                                -- :263
    let t1 := setLow (((z_h +. z_l) +. dp_h k) +. t) 0                -- :264-265
    let t2 := z_l -. (((t1 -. t) -. dp_h k) -. z_h)                   -- :266
    .inr (t1, t2)

/-- `2^(p_h+p_l)` times `sign` (`e_pow.c:269-318`), from `y` and
`log2|x| = t1 + t2`. -/
def exp2Tail (y t1 t2 sign : Float.Model) : Float.Model :=
  let neg := Float.Model.lt sign zero
  let y1 := setLow y 0                                                -- :270-271
  let p_l := (y -. y1) *. t1 +. y *. t2                               -- :272
  let p_h := y1 *. t1                                                 -- :273
  let z := p_l +. p_h                                                 -- :274
  let j := hiW z                                                      -- :275
  let i := loW z
  let early : Option Float.Model :=
    if j ≥ 0x40900000 then                                            -- :276
      if (u (j - 0x40900000) ||| i) != 0 then some (mathOflow neg)    -- :277-278
      else if Float.Model.lt (z -. p_h) (p_l +. ovt) then some (mathOflow neg) -- :280
      else none
    else if (j &&& 0x7fffffff) ≥ 0x4090cc00 then                      -- :282
      if ((u j - 0xc090cc00) ||| i) != 0 then some (mathUflow neg)    -- :283-284
      else if Float.Model.le p_l (z -. p_h) then some (mathUflow neg) -- :286
      else none
    else none
  match early with
  | some r => r
  | none =>
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
    let t := setLow (p_l +. p_h) 0                                    -- :304-305
    let u' := t *. lg2_h                                              -- :306
    let v := (p_l -. (t -. p_h)) *. lg2 +. t *. lg2_l                 -- :307
    let z := u' +. v                                                  -- :308
    let w := v -. (z -. u')                                           -- :309
    let t := z *. z                                                   -- :310
    let t1 := z -. t *. (P1 +. t *. (P2 +. t *. (P3 +. t *. (P4 +. t *. P5)))) -- :311
    let r := (z *. t1) /. (t1 -. two) -. (w +. z *. w)                -- :312
    let z := one -. (r -. z)                                          -- :313
    let j := hiW z + (n <<< 20)                                       -- :314-315
    let z := if (j >>> 20) ≤ 0 then scalbn z n else setHigh z (u j)   -- :316-317
    sign *. z                                                         -- :318

/-- `__ieee754_pow(x, y)` (`e_pow.c:103-319`). -/
def ieee754Pow (x y : Float.Model) : Float.Model :=
  let hx := hiW x; let lx := loW x                                    -- :115
  let hy := hiW y; let ly := loW y                                    -- :116
  let ix := hx &&& 0x7fffffff; let iy := hy &&& 0x7fffffff            -- :117
  -- :120-123, y == ±0
  if (u iy ||| ly) == 0 then
    if issignaling x then x +. y else one
  -- :126-130, x or y NaN
  else if ix > 0x7ff00000 || (ix == 0x7ff00000 && lx != 0) ||
          iy > 0x7ff00000 || (iy == 0x7ff00000 && ly != 0) then
    if (u (hx - 0x3ff00000) ||| lx) == 0 && !issignaling y then one else x +. y
  else
  let yi := yisint hx iy ly                                           -- :137-150
  -- :153-170, special y
  let specY : Option Float.Model :=
    if ly == 0 then
      if iy == 0x7ff00000 then                                        -- :154
        if (u (ix - 0x3ff00000) ||| lx) == 0 then some one            -- :155-156
        else if ix ≥ 0x3ff00000 then some (if hy ≥ 0 then y else zero) -- :157-158
        else some (if hy < 0 then Float.Model.neg y else zero)        -- :159-160
      else if iy == 0x3ff00000 then                                   -- :162
        some (if hy < 0 then one /. x else x)                         -- :163
      else if hy == 0x40000000 then some (x *. x)                     -- :165
      else if hy == 0x3fe00000 && hx ≥ 0 then some (Float.Model.sqrt x) -- :166-168
      else none
    else none
  match specY with
  | some r => r
  | none =>
  let ax := fabs x                                                    -- :172
  -- :174-186, x is ±0, ±inf, ±1
  if lx == 0 && (ix == 0x7ff00000 || ix == 0 || ix == 0x3ff00000) then
    let z := ax
    let z := if hy < 0 then one /. z else z
    if hx < 0 then
      if ((ix - 0x3ff00000) ||| yi) == 0 then (z -. z) /. (z -. z)
      else if yi == 1 then Float.Model.neg z
      else z
    else z
  else
  let n : Int32 := ((u hx >>> 31) - 1).toInt32                        -- :190
  if (n ||| yi) == 0 then (x -. x) /. (x -. x)                        -- :191
  else
  let sign := if (n ||| (yi - 1)) == 0 then Float.Model.neg one else one -- :193-196
  match log2Split x ix hy iy sign with
  | .inl r => r
  | .inr (t1, t2) => exp2Tail y t1 t2 sign

end Pow

/-- The ELF's `pow(x, y)` (`w_pow.c:59-101`, `_LIB_VERSION == _POSIX_`): the
value of `__ieee754_pow`, with `pow(±0, ±0) = 1.0` (`w_pow.c:71-76`); the
`errno` updates are not part of the value. -/
def pow (x y : Float.Model) : Float.Model :=
  let z := Pow.ieee754Pow x y
  if Float.Model.isNaN y then z                                       -- w_pow.c:70
  else if Float.Model.beq x (.ofNat 0) then                           -- w_pow.c:71
    if Float.Model.beq y (.ofNat 0) then Pow.one else z               -- w_pow.c:72-81
  else z                                                              -- w_pow.c:83-99

/-- `luai_numpow` (`llimits.h:339-342`): `b == 2 ? a*a : pow(a,b)`. -/
def numpow (a b : Float.Model) : Float.Model :=
  if Float.Model.beq b (Pow.two) then Float.Model.mul a a else pow a b

end Lua.Num
