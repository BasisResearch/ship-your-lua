/-!
# Lua's decimal side of floats: `str2int`, `str2d`, `%.14g`, `tostringbuff`

The numerals and float printing of the Lua 5.4.7 ELF, over core's IEEE
binary64 model `Float.Model` (`Init/Data/Float/Model/`, Lean v4.34). Each
definition transcribes named C source:

* `vendor/lua-5.4.7/src/lobject.c`: `l_str2int` (276-305), `l_str2dloc`
  (228-235), `l_str2d` (251-270), `luaO_str2num` (308-320), `tostringbuff`
  (355-368);
* `luaconf.h`: `lua_str2number` = `strtod` (484), `lua_strx2number` =
  `lua_str2number` (610), `LUA_NUMBER_FMT` `"%.14g"` (480);
* newlib 4.5.0 (the ELF's libc, `c/Makefile`):
  `newlib/libc/stdlib/strtod.c` `_strtod_l` (243-1273) and `ULtod` (206-239),
  `newlib/libc/stdlib/gdtoa-gethex.c` `gethex` (144-359),
  `newlib/libc/stdio/vfprintf.c` (`%g`: 979-1000, 1063-1070, 1455-1510;
  `cvt` 1552-1640; `exponent` 1646-1675), `newlib/libc/stdlib/dtoa.c`
  `_dtoa_r` mode 2 (round half even on the last digit: 827-841).

What the model gives and what is written here:

* decimal rounding (`strtod`'s correctly rounded result) is the model's
  `Float.Model.ofScientific m e` (RNE of `m·10^e`);
* hex floats (`gethex`) are NOT correctly rounded on the ELF, so they are a
  transcription of `gethex`'s own rounding (three deviations, measured on
  Sail, see `gethexRound`);
* `%.14g` is the exact 14-significant-digit RNE of the unpacked value; the
  sign of a NaN is not in the model, so `fmt14g` takes it explicitly
  (`nanNeg`), as newlib prints it (`signbit`, vfprintf.c:990-991).

Validation: `c/tests/float/` (differential tests against the ELF on Sail,
`run.sh`; `scripts/test_decimal.lean` is the Lean side).
-/

namespace Lua.Num

open Float.Model (UnpackedFloat)

/-! ## Characters -/

/-- `lisspace` (`lctype.c` table, `LUA_USE_CTYPE 0`) and the spaces newlib
`_strtod_l` skips (strtod.c:286-292): `'\t' '\n' '\v' '\f' '\r' ' '`. -/
def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- A digit's value: `lisdigit`, and if `hex` also `lisxdigit` with
`luaO_hexavalue` (lobject.c:131-136); newlib's `__hexdig` table
(gdtoa-gethex.c:40-58) has the same digits. -/
def digitVal (hex : Bool) (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c.toNat - 48)
  else if hex ∧ 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if hex ∧ 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55)
  else none

/-- The leading digits of `s`: their value (accumulated from `a`), their
count (from `n`), and the rest. -/
def digits (hex : Bool) : List UInt8 → Nat → Nat → Nat × Nat × List UInt8
  | [], a, n => (a, n, [])
  | c :: cs, a, n =>
    match digitVal hex c with
    | some d => digits hex cs (a * (if hex then 16 else 10) + d) (n + 1)
    | none => (a, n, c :: cs)

/-- A leading `-`/`+` (`isneg`, lobject.c:141-145; strtod.c:278-285). -/
def takeSign : List UInt8 → Bool × List UInt8
  | 45 :: t => (true, t)
  | 43 :: t => (false, t)
  | t => (false, t)

/-! ## Integers: `l_str2int` -/

/-- `l_str2int` (lobject.c:276-305) on a whole Lua string, with
`luaO_str2num`'s length check (`l_strton`, lvm.c; `lua_stringtonumber`):
spaces, a sign, `0x` hex digits (wrapping mod 2^64) or decimal digits
(rejected on overflow: `MAXBY10`/`MAXLASTD`, then `l_str2d` makes it a
float), spaces, and nothing else. An embedded `\0` ends the C string early,
so the length check rejects it (here: `0` is not a space).

This is THE `str2int`: `Lua.Bytecode.str2int` and `Lua.Ast.str2int` are
equal to it (`Lua/Num/DecimalBridge.lean`). -/
def str2int (s : List UInt8) : Option (BitVec 64) :=
  let s := s.dropWhile isSpace
  let (neg, s) := takeSign s
  let (hex, s) := match s with
    | 48 :: x :: t => if x == 120 || x == 88 then (true, t) else (false, s)
    | _ => (false, s)
  let (a, n, rest) := digits hex s 0 0
  if n = 0 ∨ (rest.dropWhile isSpace) ≠ [] ∨ (!hex ∧ 2 ^ 63 - 1 + (if neg then 1 else 0) < a) then
    none
  else some (if neg then 0 - BitVec.ofNat 64 a else BitVec.ofNat 64 a)

/-! ## Floats from the model -/

/-- `x` with its sign flipped when `neg` (strtod.c:1272,
`return sign ? -dval(rv) : dval(rv)`). -/
def withSign (neg : Bool) (x : Float.Model) : Float.Model :=
  if neg then x.neg else x

/-- `0.0`. -/
def zero : Float.Model := Float.Model.pack (.zero .positive)

/-- `+inf`. -/
def inf : Float.Model := Float.Model.pack (.infinity .positive)

/-- The float `b·2^e`, for `(b, e)` in `binary64` canonical form
(`b < 2^53`; `b ≥ 2^52` or `e = -1074`); `0` if `b = 0`. This is `ULtod`
(strtod.c:206-239) of `gethex`'s bits and exponent. -/
def ofCanon (b : Nat) (e : Int) : Float.Model :=
  if h : b = 0 then zero else Float.Model.pack (.finite .positive b e (Nat.pos_of_ne_zero h))

/-! ## Hex floats: newlib `gethex` -/

/-- gdtoa's `Long` is `__int32_t` (mprec.h:85): its arithmetic wraps to 32
bits (measured on Sail: `0x1p4294967296` reads as `1.0`). -/
def wrap32 (x : Int) : Int := (x + 2 ^ 31) % 2 ^ 32 - 2 ^ 31

/-- `any_on(b, k)` (mprec.c:1019-1044): some bit below bit `k` is set. -/
def anyOn (b k : Nat) : Bool := b % 2 ^ k != 0

/-- Bit `k` of `b`. -/
def bitAt (b k : Nat) : Bool := b / 2 ^ k % 2 == 1

/-- `gethex`'s result (`STRTOG_*`, gdtoa.h), with the bits it returns. -/
inductive HexRes
  /-- `STRTOG_NoNumber`: no hex digit at all. -/
  | noNumber
  /-- `STRTOG_Zero`: a zero mantissa, or an underflow to zero. -/
  | zero
  /-- `STRTOG_Infinite`: an overflow. -/
  | inf
  /-- `STRTOG_Normal`/`STRTOG_Denormal`: the value `b·2^e`, canonical. -/
  | fin (b : Nat) (e : Int)
  deriving Repr, DecidableEq

/-- `fpi` of `_strtod_l` (strtod.c:299): `emin = 1-1023-53+1`. -/
def hexEmin : Int := -1074
/-- `fpi` of `_strtod_l` (strtod.c:299): `emax = 2046-1023-53+1`. -/
def hexEmax : Int := 971

/-- `gethex`'s rounding of the mantissa `b > 0` with exponent `e` to 53 bits,
round-to-nearest (gdtoa-gethex.c:244-358). It is a transcription, and it
deviates from correct rounding in three ways, each measured on the ELF
(`c/tests/float/parse.lua`):

* the sticky bit of the first shift tests `any_on(b, k-1)`, missing bit
  `k-1` just below the round bit, and nothing when `k ≤ 1`
  (gdtoa-gethex.c:259-261): `0x40000000000003p0` reads as `2^54`, not
  `2^54+4`;
* at the subnormal boundary (`n = nbits`, gdtoa-gethex.c:286) the bits lost
  by the first shift are ignored: `0x1.00000000000001p-1075` reads as `0`,
  not `2^-1074`;
* the exponent is a 32-bit `Long` (`wrap32`). -/
def gethexRound (b : Nat) (e : Int) : HexRes :=
  let nbits := 53
  let n := Nat.log2 b + 1   -- `n = 32*n - hi0bits(L)`: the bit length
  -- gdtoa-gethex.c:253-270: shift to `nbits` bits
  let (b, e, lost) : Nat × Int × Nat :=
    if n > nbits then
      let n := n - nbits
      let lost :=
        if anyOn b n then
          let k := n - 1
          if bitAt b k then (if k > 1 && anyOn b (k - 1) then 3 else 2) else 1
        else 0
      (b / 2 ^ n, wrap32 (e + n), lost)
    else if n < nbits then
      (b * 2 ^ (nbits - n), wrap32 (e - (nbits - n : Nat)), 0)
    else (b, e, 0)
  -- `up` for FPI_Round_near (gdtoa-gethex.c:324-327)
  let up (lost b : Nat) : Bool := lost &&& 2 != 0 && (lost &&& 1 != 0 || b % 2 == 1)
  if e > hexEmax then .inf                                      -- 271-276
  else if e < hexEmin then                                      -- 280-313
    let n := (hexEmin - e).toNat
    if n ≥ nbits then
      if n == nbits && (n < 2 || anyOn b (n - 1)) then .fin 1 hexEmin else .zero
    else
      let k := n - 1
      let lost := if lost != 0 then 1 else if k > 0 then (if anyOn b k then 1 else 0) else 0
      let lost := if bitAt b k then lost ||| 2 else lost
      let b := b / 2 ^ n
      .fin (if up lost b then b + 1 else b) hexEmin            -- 318-353
  else if up lost b then
    if b + 1 ≥ 2 ^ nbits then                                   -- 343-349
      if wrap32 (e + 1) > hexEmax then .inf else .fin ((b + 1) / 2) (e + 1)
    else .fin (b + 1) e
  else .fin b e

/-- Hex digits from the front: their values and the rest. -/
def hexRun : List UInt8 → List Nat × List UInt8
  | [] => ([], [])
  | c :: cs =>
    match digitVal true c with
    | some d => let (ds, r) := hexRun cs; (d :: ds, r)
    | none => ([], c :: cs)

/-- The mantissa scan of `gethex` (gdtoa-gethex.c:164-199), from the text
after `0x`. -/
structure HexScan where
  /-- The significant hex digits, `s0` to `s1` without the point. -/
  ds : List Nat
  /-- `s - decpt`: the hex digits after the point (0 on the `goto pcheck`
  exits, which leave `e = 0`). -/
  nf : Nat
  /-- No nonzero digit. -/
  zret : Bool
  /-- Some digit (a skipped zero counts). -/
  havedig : Bool
  /-- The text at `pcheck`. -/
  rest : List UInt8

/-- `gethex`'s scan (gdtoa-gethex.c:164-199). -/
def hexScan (t : List UInt8) : HexScan :=
  let lz := t.takeWhile (· == 48)
  let s := t.drop lz.length
  let havedig := lz.length != 0
  match s with
  | [] => ⟨[], 0, true, havedig, []⟩
  | c :: s' =>
    if (digitVal true c).isSome then
      let (ip, r) := hexRun s
      match r with
      | 46 :: r' => let (fp, r'') := hexRun r'; ⟨ip ++ fp, fp.length, false, havedig, r''⟩
      | _ => ⟨ip, 0, false, havedig, r⟩
    else if c == 46 then
      match s' with
      | [] => ⟨[], 0, true, havedig, []⟩
      | c2 :: _ =>
        if (digitVal true c2).isSome then
          let z := s'.takeWhile (· == 48)
          let s2 := s'.drop z.length
          let (fp, r) := hexRun s2
          ⟨fp, z.length + fp.length, fp.isEmpty, true, r⟩
        else ⟨[], 0, true, havedig, s'⟩
    else ⟨[], 0, true, havedig, s⟩

/-- Decimal exponent digits into a `Long`, wrapping (gdtoa-gethex.c:216-218). -/
def expDigits32 : List UInt8 → Int → Int × List UInt8
  | [], a => (a, [])
  | c :: cs, a =>
    match digitVal false c with
    | some d => expDigits32 cs (wrap32 (10 * a + d))
    | none => (a, c :: cs)

/-- `pcheck` (gdtoa-gethex.c:202-221): an optional `p`/`P`, a sign and
decimal digits added to `e`; without digits the text stays at `p`. -/
def hexPExp (e : Int) (s : List UInt8) : Int × List UInt8 :=
  match s with
  | c :: t =>
    if c == 112 || c == 80 then
      let (neg, t') := takeSign t
      match t' with
      | d :: _ =>
        if (digitVal false d).isSome then
          let (e1, r) := expDigits32 t' 0
          (wrap32 (e + (if neg then wrap32 (-e1) else e1)), r)
        else (e, s)
      | [] => (e, s)
    else (e, s)
  | [] => (e, s)

/-- `gethex` (gdtoa-gethex.c:144-359) on the text after `0x`: the result
and the text after it (`*sp`). -/
def gethex (t : List UInt8) : HexRes × List UInt8 :=
  let sc := hexScan t
  let (e, rest) := hexPExp (wrap32 (-(wrap32 (sc.nf * 4)))) sc.rest
  if sc.zret then ((if sc.havedig then .zero else .noNumber), rest)
  else (gethexRound (sc.ds.foldl (fun a d => a * 16 + d) 0) e, rest)

/-! ## Decimal floats: newlib `_strtod_l` -/

/-- The decimal subject sequence of `_strtod_l` (strtod.c:340-470) after the
sign: the significand `m` (all digits, the point dropped), the exponent of
`m·10^e`, and the text after it; `none` is `ret0` (no digit). The written
exponent saturates at `19999` (strtod.c:412-416). -/
def decScan (s : List UInt8) : Option (Nat × Int × List UInt8) :=
  let (ip, ni, r) := digits false s 0 0
  let (fp, nf, r) := match r with
    | 46 :: t => digits false t 0 0
    | _ => (0, 0, r)
  let m := ip * 10 ^ nf + fp
  let seen := ni + nf != 0
  match r with
  | c :: t =>
    if c == 101 || c == 69 then
      if !seen then none
      else
        let (eneg, t') := takeSign t
        match t' with
        | d :: _ =>
          if (digitVal false d).isSome then
            let (l, _, r') := digits false t' 0 0
            let l : Int := min l 19999
            some (m, (if eneg then -l else l) - nf, r')
          else some (m, -(nf : Int), r)
        | [] => some (m, -(nf : Int), r)
    else if seen then some (m, -(nf : Int), r) else none
  | [] => if seen then some (m, -(nf : Int), []) else none

/-- newlib `_strtod_l` (strtod.c:243-1273): the value and the text after the
subject sequence (`*se`), or `none` for no conversion (`*se = s00`).

It omits `INFNAN_CHECK` (strtod.c:431-470): Lua calls `strtod` only on
strings without `n`/`N` (`l_str2d`), and without them `inf`/`nan` never
match. The decimal value is the model's correctly rounded
`Float.Model.ofScientific`, which `_strtod_l`'s bignum path computes
(validated on the ELF: `c/tests/float/parse.lua`). -/
def strtod (s : List UInt8) : Option (Float.Model × List UInt8) :=
  let s := s.dropWhile isSpace
  let (neg, s) := takeSign s
  match s with
  | 48 :: x :: t =>
    if x == 120 || x == 88 then
      -- strtod.c:297-337
      match gethex t with
      | (.noNumber, _) => some (zero, x :: t)       -- `s = s00` (the `x`), `sign = 0`
      | (.zero, r) => some (withSign neg zero, r)
      | (.inf, r) => some (withSign neg inf, r)
      | (.fin b e, r) => some (withSign neg (ofCanon b e), r)
    else decimal neg s
  | _ => decimal neg s
where
  /-- strtod.c:340-470 and the correctly rounded value. -/
  decimal (neg : Bool) (s : List UInt8) : Option (Float.Model × List UInt8) :=
    (decScan s).map fun (m, e, r) =>
      (withSign neg (if m = 0 then zero else Float.Model.ofScientific m e), r)

/-- `l_str2d` (lobject.c:251-270) with `l_str2dloc` (228-235) on a whole Lua
string: reject when the first of `.xXnN` is `n`/`N` (`inf`, `nan`); else
`strtod` (`lua_strx2number` is `lua_str2number`, luaconf.h:610), then
trailing spaces and the end. The locale retry gives the same answer (the
decimal point is `.`, `c/src/baremetal.h:21`). A `\0` byte is never
accepted, which is `l_strton`'s length check. -/
def str2d (s : List UInt8) : Option Float.Model :=
  let special (c : UInt8) : Bool := c == 46 || c == 120 || c == 88 || c == 110 || c == 78
  match (s.takeWhile (· != 0)).find? special with
  | some 110 | some 78 => none
  | _ =>
    match strtod s with
    | none => none
    | some (x, r) => if r.dropWhile isSpace = [] then some x else none

/-- A Lua numeral's value (`TValue` numbers). -/
inductive Numeral
  | int (i : BitVec 64)
  | flt (x : Float.Model)
  deriving DecidableEq

/-- `luaO_str2num` (lobject.c:308-320) with `l_strton`'s length check: an
integer if `l_str2int` accepts, else a float if `l_str2d` does. -/
def str2number (s : List UInt8) : Option Numeral :=
  match str2int s with
  | some i => some (.int i)
  | none => (str2d s).map .flt

/-! ## `%.14g` and `tostringbuff` -/

/-- `10^k ≤ m·2^e`, exactly. -/
def pow10Le (m : Nat) (e k : Int) : Bool :=
  10 ^ k.toNat * 2 ^ (-e).toNat ≤ m * 2 ^ e.toNat * 10 ^ (-k).toNat

/-- The decimal exponent of `m·2^e > 0`: the `k` with
`10^k ≤ m·2^e < 10^(k+1)` (`_dtoa_r`'s `k`). The estimate
`⌊t·78913/2^18⌋` of `⌊t·log₁₀2⌋` (`t = log₂ m + e`) is within
`[k-2, k+1]` for `|t| ≤ 1100`, and three exact comparisons fix it. -/
def decExp (m : Nat) (e : Int) : Int :=
  let t : Int := (Nat.log2 m : Int) + e
  let k0 := t * 78913 / 262144
  let k1 := if pow10Le m e k0 then k0 else k0 - 1
  let k2 := if pow10Le m e (k1 + 1) then k1 + 1 else k1
  if pow10Le m e (k2 + 1) then k2 + 1 else k2

/-- `_dtoa_r` mode 2 with 14 digits (vfprintf.c:1624-1627): the digits `d`
(`10^13 ≤ d < 10^14`, trailing zeros kept) and the decimal exponent `k` of
the correctly rounded `d·10^(k-13)` of `m·2^e > 0`, ties to even on the last
digit (dtoa.c:827-841). -/
def dec14 (m : Nat) (e : Int) : Nat × Int :=
  let k := decExp m e
  let s : Int := 13 - k
  let num := m * 2 ^ e.toNat * 10 ^ s.toNat
  let den := 2 ^ (-e).toNat * 10 ^ (-s).toNat
  let d := num / den
  let r := num % den
  let d := if 2 * r > den || (2 * r == den && d % 2 == 1) then d + 1 else d
  if d == 10 ^ 14 then (10 ^ 13, k + 1) else (d, k)

/-- Decimal digits, most significant first. -/
def natDigits (n : Nat) : List UInt8 :=
  (Nat.toDigits 10 n).map fun c => c.toNat.toUInt8

/-- `exponent` (vfprintf.c:1646-1675): `e`, the sign, at least two digits. -/
def expBytes (x : Int) : List UInt8 :=
  let d := natDigits x.natAbs
  101 :: (if x < 0 then 45 else 43) :: (if d.length < 2 then 48 :: d else d)

/-- `_dtoa_r` keeps the trailing zeros of its 14 digits: its floating
"quick" path (dtoa.c:434-545) and its bignum path (827-855) trim them, but
the small-integer path (550-593, an integer value `k ≤ Int_max = 14`) does
not, and it runs only when the quick path fails. For an integer below
`10^15` that is an exact tie at the 14th digit (the quick path's fraction is
within `eps` of `0.5` only then); without a bump (the 14th digit even) the
digits are `v / 10` as written (measured: `649981820981505` prints
`6.4998182098150e+14`; host glibc prints `6.499818209815e+14`). -/
def keepsZeros (m : Nat) (e : Int) : Bool :=
  let v := m * 2 ^ e.toNat / 2 ^ (-e).toNat
  m * 2 ^ e.toNat % 2 ^ (-e).toNat == 0 && 10 ^ 14 ≤ v && v < 10 ^ 15 && v % 10 == 5 && v / 10 % 2 == 0

/-- `%.14g` of the finite nonzero `(-1)^neg·m·2^e` (vfprintf.c:1063-1070,
1455-1510): `%e` style when `expt ≤ -4 ∨ expt > 14` (`expt = k+1`), else
`%f` style, both on `_dtoa_r`'s digits: without trailing zeros (`%g`, no
`#`), except as `keepsZeros` says. -/
def fmtFinite (neg : Bool) (m : Nat) (e : Int) : List UInt8 :=
  let (d, k) := dec14 m e
  let sig := if keepsZeros m e then natDigits d
    else ((natDigits d).reverse.dropWhile (· == 48)).reverse
  let ndig := sig.length
  let expt := k + 1
  let body :=
    if expt ≤ -4 || expt > 14 then
      match sig with
      | c :: rest => c :: ((if rest.isEmpty then [] else 46 :: rest) ++ expBytes k)
      | [] => []
    else if expt ≤ 0 then
      [48, 46] ++ List.replicate (-expt).toNat 48 ++ sig
    else if ndig ≤ expt.toNat then
      sig ++ List.replicate (expt.toNat - ndig) 48
    else sig.take expt.toNat ++ 46 :: sig.drop expt.toNat
  (if neg then [45] else []) ++ body

/-- `snprintf(buf, 44, "%.14g", x)` on the ELF (`lua_number2str`,
luaconf.h:420; newlib vfprintf.c): `inf`/`-inf` (979-988), `nan`/`-nan` by
the sign bit (990-998; the model has no NaN sign, so it is `nanNeg`), `0`/
`-0` (`cvt` takes the sign bit, 1561), else `fmtFinite`. -/
def fmt14g (nanNeg : Bool) (x : Float.Model) : List UInt8 :=
  match x.unpack with
  | .notANumber => if nanNeg then [45, 110, 97, 110] else [110, 97, 110]
  | .infinity s => (if s = .negative then [45] else []) ++ [105, 110, 102]
  | .zero s => (if s = .negative then [45] else []) ++ [48]
  | .finite s m e _ => fmtFinite (s = .negative) m e

/-- `%.14g` of a raw double: its sign bit is the NaN sign. -/
def fmt14gBits (b : BitVec 64) : List UInt8 :=
  fmt14g b.msb (Float.Model.ofBits (UInt64.ofBitVec b))

/-- `tostringbuff` (lobject.c:355-368) of a float: `%.14g`, then `.0` when
the result "looks like an int" (every byte in `-0123456789`). -/
def tostringbuff (nanNeg : Bool) (x : Float.Model) : List UInt8 :=
  let b := fmt14g nanNeg x
  if b.all (fun c => c == 45 || (48 ≤ c && c ≤ 57)) then b ++ [46, 48] else b

/-- `tostringbuff` of a raw double. -/
def tostringbuffBits (b : BitVec 64) : List UInt8 :=
  tostringbuff b.msb (Float.Model.ofBits (UInt64.ofBitVec b))

end Lua.Num
