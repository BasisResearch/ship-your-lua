# Lane float-s0b: the decimal side of floats (FLOAT-DESIGN.md step S0b)

Base: main `75aa247`, re-scoped by §1 as revised in `7c625a0`. δ's float
spec is core's `Float.Model` (Lean v4.34). Lines are non-blank,
non-comment lines. CPU and peak memory are one `lake env lean <file>` each
(`/usr/bin/time -v`).

## Result

| target | status | where |
|---|---|---|
| `l_str2int` (THE `str2int`) | **defined** | `Lua.Num.str2int` (`Lua/Num/Decimal.lean`) |
| the semantics' copies equal it | **proved** | `str2int_bytecode`, `str2int_ast` (`Lua/Num/DecimalBridge.lean`) |
| `l_str2d` over newlib `_strtod_l`; `luaO_str2num` | **defined** | `strtod`, `str2d`, `str2number`; decimal rounding is `Float.Model.ofScientific` |
| hex floats (`lua_strx2number` = `strtod` → newlib `gethex`) | **defined** | `gethex`, `gethexRound`: a transcription, because the ELF does not round correctly (below) |
| `%.14g` and `tostringbuff` | **defined** | `dec14`, `fmtFinite`, `keepsZeros`, `fmt14g (nanNeg) x`, `tostringbuff`, `…Bits` |
| kernel evaluation | **proved** facts | `Lua/Num/DecimalFacts.lean`: 15 `decide +kernel` theorems (whole file under 1 s) |
| the machine side (`G14From`, `Str2dFrom`) | open | M0 |

Axioms: `str2int_bytecode` `[propext, Quot.sound]`; `str2int_ast`,
`str2number_1_5`, `tostring_nan`, `gethex_sticky`
`[propext, Classical.choice, Quot.sound]` (check.sh stage 6). No `sorry`,
`native_decide` or `bv_decide`; Lean's `Float` is not used.
`scripts/check.sh`: all stages OK.

## Numbers

| file | lines | CPU (user) | peak |
|---|---|---|---|
| `Lua/Num/Decimal.lean` | 250 | 0.9 s | 0.83 GB |
| `Lua/Num/DecimalBridge.lean` | 106 | 1.0 s | 0.83 GB |
| `Lua/Num/DecimalFacts.lean` | 45 | 0.8 s | 0.83 GB |
| `scripts/test_decimal.lean` (the Lean side of the tests) | 24 | 1.0 s | — |
| `c/tests/float/{gen.py,run.sh}` | 175 + 38 | — | — |

## Differential tests (`c/tests/float/run.sh`)

The vectors come from `gen.py` (seeded). They are compared line by line
with the ELF on the Sail emulator; the host `lua` is shown for information.

| suite | vectors | Lean = ELF | host `lua` ≠ ELF | Sail wall |
|---|---|---|---|---|
| `fmt` (`tostring` of doubles given by their bits) | 1,629 | **all** | 8 (`keepsZeros`) | 737 s |
| `parse` (`tonumber` of strings) | 574 | **all** | 7 (`gethex`, the 19999 saturation) | 2,567 s + 1,501 s + 27 s |

The vectors cover:
* ±0 and ±inf, and NaN with both signs and with payloads;
* subnormals, and the normal/subnormal boundary;
* powers of 2 and 10 across the whole range, with their neighbours;
* the 14-digit boundaries `9.99999999999995·10^k`, with their neighbours;
* exact ties at the 15th digit, both fractional and integer;
* `1e15`, `1e16`, `2^53`, and random bit patterns.

The parse strings cover:
* integer edge cases: overflow to float, hex wrap, signs, spaces, and an embedded `\0`;
* decimal numerals: 1-40 digits, exponents −345 to 315, round trips, and exact binary midpoints (subnormal, normal, overflow) with neighbours ±10^-60;
* `strtod`'s exponent saturation at 19999 (a 20,000-character numeral; its mirror with 20,006 significant digits ran over 90 min on Sail in `_strtod_l`'s bignum path, so it is not a vector);
* hex floats: random, and boundary cases;
* the `n`/`N` rejections.

## Findings (all measured on the ELF)

1. **NaN.** `0/0` is the positive canonical NaN `0x7ff8000000000000`,
   printed `nan`. `-(0/0)` is printed `-nan`, because newlib tests `signbit`
   (vfprintf.c:990-991). A NaN with a payload prints `nan`. Host x86 prints
   `0/0` as `-nan`.
2. **`%.14g` keeps zeros on integer ties.** `_dtoa_r`'s small-integer path
   (dtoa.c:550-593) does not trim trailing zeros. It runs only when the
   floating quick path fails, and for an integer below 10^15 that happens
   only on an exact 14th-digit tie. Examples: `649981820981505` prints
   `6.4998182098150e+14` and `100000000000005` prints `1.0000000000000e+14`,
   where glibc prints `6.499818209815e+14` and `1e+14`. This is
   `keepsZeros`.
3. **newlib `gethex` does not round correctly.** gdtoa-gethex.c is
   transcribed as `gethexRound`. Each case is a `decide` theorem:
   * `gethex_sticky`: the sticky test is `any_on(b, k-1)`, which misses the
     bit just below the round bit. So `0x40000000000003p0` reads as `2^54`,
     where the decimal numeral of the same value gives `2^54+4`.
   * `gethex_subnormal`: at `n = nbits` the bits lost by the first shift are
     ignored. So `0x1.00000000000001p-1075` reads as `0`, not `2^-1074`.
   * `gethex_wrap`: the binary exponent is a 32-bit `Long`. So
     `0x1p4294967296` reads as `1.0`, and `0x1p-2147483648` reads as `inf`.
4. **Decimal `strtod` agrees with `Float.Model.ofScientific`** on every
   vector, ties included. The vectors are 1-40-digit numerals, exact binary
   midpoints to 767 digits, and subnormals. The written exponent saturates
   at 19999 (strtod.c:412-416), which is transcribed: `"0."+20005 zeros+"1e20010"` is `1e-07` on the ELF and in Lean, `10000.0` on glibc. Nothing disagreed.
5. `l_str2d`'s `n`/`N` rule makes `strtod`'s INFNAN branch unreachable, so
   `strtod` here omits it.

## Notes for S1

* Swap `Lua.Bytecode.str2int`/`Lua.Ast.str2int` for `Lua.Num.str2int`. The
  bridge theorems are the rewrite.
* `str2number` is `luaO_str2num` with the length check.
* `tostringbuff nanNeg x` takes the NaN sign that `Value.flt` carries.
* Everything is `decide +kernel`-evaluable.
