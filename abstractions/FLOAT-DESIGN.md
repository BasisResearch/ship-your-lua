# Floats in `δ`: design

Status: design only. Nothing here is built.

**Why.** `vm_refinement_Statement luaLayout` is false as stated. Lua 5.4.7
coerces strings to numbers (`LUA_NOCVTS2N` is unset), and that coercion can
produce floats at points where `BcSem` is stuck. The three counterexamples
are `"1.5"+1`, `for i=1,"2"` and `-"1.5"` (`Lua/Programs/Escape.lean`,
`abstractions/ledger/f1-lane-5.md` on branch `f1-lane-5`). The decision is to
add floats to the value semantics, rather than restrict `Supported`.

Tags used below:
* **[CHECK]** marks a claim recalled from memory that must be verified
  before anything depends on it.
* **[measured]** marks a number taken from this repository's objdump or host
  `lua` on 2026-10-06. The scripts are reproducible: one
  `riscv-none-elf-objdump -d`, then a per-function CFG pass that counts
  nontrivial SCCs as loops and entry-to-exit paths in loop-free functions.

---

## 0. What the ELF links and calls [measured]

The ELF is `-march=rv64i -mabi=lp64` (`c/Makefile`; ELF flags `0x0`). It has
no F/D extension, so every `double` operation is a call into libgcc soft-fp
or newlib libm. `lmathlib` is not linked into the ELF, so `math.*` does not
exist on the target. `function_match.tsv` records each libgcc routine as
`identical_mod_reloc` to its `libgcc.a` object, so these routines are the
stock libgcc code.

### Soft-float and libm routines reachable from `luaV_execute` and its numeric helpers

| routine | entry | insns | loops | entry→exit paths | callees |
|---|---|---|---|---|---|
| `__adddf3` | `0x8002d7a8` | 418 | 0 | 497 | `__clzdi2` |
| `__subdf3` | `0x8002e9d0` | 440 | 0 | 509 | `__clzdi2` |
| `__muldf3` | `0x8002e504` | 307 | 0 | 5,335 | `__clzdi2`, `__muldi3` |
| `__divdf3` | `0x8002de30` | 328 | 0 | ≥ 12,035 (2 jump tables, so the count is a lower bound) | `__clzdi2`, `__udivdi3`, `__umoddi3`, `__muldi3` |
| `__floatdidf` (int64→double) | `0x8002f200` | 86 | 0 | 11 | `__clzdi2` |
| `__floatsidf` (int32→double) | `0x8002f0f8` | 36 | 0 | 2 | `__clzdi2` |
| `__fixdfdi` (double→int64, trunc) | `0x8002f188` | 30 | 0 | 6 | — |
| `__eqdf2` (= `__nedf2`) | `0x8002e350` | 28 | 0 | 19 | — |
| `__gedf2` (= `__gtdf2`) | `0x8002e3c0` | 40 | 0 | 67 | — |
| `__ledf2` (= `__ltdf2`) | `0x8002e460` | 41 | 0 | 67 | — |
| `__clzdi2` | `0x8002f7ec` | 22 | 1 (5 insns) | — | — |
| `floor` (fdlibm `s_floor`) | `0x8002bb14` | 114 | 0 | 16 | `__adddf3`, `__gedf2` (the `huge+x>0` inexact trick) |
| `fmod` (wrapper) | `0x8002b964` | 38 | 0 | 3 | `__ieee754_fmod`, `__divdf3`, `__eqdf2`, `__unorddf2` |
| `__ieee754_fmod` | `0x8002bdb4` | 317 | 6 | — | `__divdf3`, `__muldf3` |
| `pow` (wrapper) | `0x8002b9fc` | 70 | 0 | — | `__ieee754_pow`, … |
| `__ieee754_pow` | `0x8002c2a8` | 893 | 0 | — | `+ − × ÷`, `__floatsidf`, `scalbn` (106), `fabs`; tail-calls `__ieee754_sqrt` (209 insns, 4 loops) |

`luaV_execute` calls these routines directly: `__adddf3`, `__subdf3`,
`__muldf3`, `__divdf3`, `__floatdidf`, `__floatsidf`, `__eqdf2`, `__gedf2`,
`__ledf2`, `__fixdfdi`, `floor`, `fmod`, `pow`, `luaV_tointeger` and
`luaV_tonumber_`. It never calls `__negdf2`: float `UNM` flips the sign bit
inline.

### Lua's numeric helpers (all loop-free)

| helper | insns | role |
|---|---|---|
| `luaV_flttointeger` | 57 | `floor` + range guard + `__fixdfdi` (F2I modes) |
| `luaV_tointegerns` / `luaV_tointeger` | 59 / 90 | the second also does string→number (`luaO_str2num`) |
| `luaV_tonumber_` | 48 | int→float (`__floatdidf`) or string→number |
| `luaV_modf` | 39 | `luai_nummod` (`fmod` + sign fix) |
| `luaV_lessthan` / `luaV_lessequal` | 143 / 145 | `LTnum`/`LEnum` (mixed int/float), `l_strcmp`, `luaT_callorderTM` |
| `luaV_equalobj` | 212 | mixed int/float equality by `luaV_tointegerns(F2Ieq)` |
| `luaO_rawarith` / `numarith` / `intarith` | 156 / 75 / 46 | `lua_arith`'s path (the string metamethods) |

### Printing a float

The chain is `luaB_print` → `luaL_tolstring` (153) → `lua_pushfstring("%f")`
→ `luaO_pushvfstring` (282) → `tostringbuff` (33; `snprintf` + `strspn`,
adds `.0`) → `snprintf` (53) → `_svfprintf_r` (3,212; jump-table dispatch)
→ `_dtoa_r` (1,407; 12 loops).

`_dtoa_r` uses newlib's bignum kit: `_Balloc` 43, `_Bfree` 9, `__multadd`
90 (1 loop), `__i2b` 52, `__multiply` 185 (3), `__pow5mult` 91 (1),
`__lshift` 100 (4), `__mcmp` 22 (1), `__mdiff` 147 (4), `__d2b` 82,
`__hi0bits` 34, `__lo0bits` 71, `quorem` 155 (4). Allocation goes through
`_calloc_r` and the reent `_freelist`, and `__assert_func` handles OOM.

`CONCAT` of a float takes the same path from `luaO_tostring` (37) →
`tostringbuff`. There is one `snprintf` call node in the whole numeric
printing path.

### Parsing a numeral string

The chain is `luaO_str2num` (191, 4 loops) → `l_str2int`, or failing that
`l_str2d` (inlined; `strpbrk(".xXnN")`) → `l_str2dloc` (41) → `strtod` (6)
→ `_strtod_l` (1,601; 9 loops; 2 jump tables).

`_strtod_l` calls `__gethex` (547, 9 loops) for hex floats and a bignum
slow path: `__s2b` 89, `__b2d` 78, `__ratio` 47, `__ulp` 36, `sulp` 25,
`__mdiff`, `__lshift`, `__pow5mult`, `__i2b`, `__d2b`.

`l_str2d` returns `NULL` for any string that contains `n` or `N`, so
`strtod`'s `inf`/`nan` branches (`__match`, `__hexnan`) are **unreachable
from Lua**. Every summary below can assume the input string has no `n`/`N`.

The string-arithmetic route on the machine is a full Lua→C call:
`MMBIN*` → `luaT_trybinTM` → `luaT_callTMres` → `luaD_call` of the C
closure `arith_add` (lstrlib) → `tonum` → `lua_stringtonumber` →
`luaO_str2num`, then `lua_arith` → `luaO_arith` → `luaO_rawarith`.

### Host `lua` 5.4.7 (x86-64) probes [measured]

| expr | host | note |
|---|---|---|
| `0/0`, `-(0/0)` | `-nan`, `nan` | x86 default NaN has the sign bit set. The ELF's soft-fp NaN is positive (§5 R1), so **the host is not an oracle for NaN sign** |
| `1%0.0` | `-nan` | the ELF gives `fmod(1,0)` = `0/0` = canonical NaN |
| `1e15`, `2^53`, `100.0`, `-0.0` | `1e+15`, `9.007199254741e+15`, `100.0`, `-0.0` | `.0` only when `%.14g` gives `[-0-9]*` |
| `"0x1p4"+0`, `"1e400"+0` | `16.0`, `inf` | hex floats via `strtod`; overflow is accepted |
| `3.0\|0`, `1//0.0`, `3 % -2.0`, `-7 % 3.0` | `3`, `inf`, `-1.0`, `2.0` | |
| `for i="1",2` | `1.0`, `2.0` | a string `init` takes the **float** loop |
| `1 == 1.0`, `2^63 == math.mininteger` | `true`, `false` | |
| `luac -l`: `2^0.5` | `LOADK 1.4142135623731` | **`^` is constant-folded on the host with glibc `pow`** (§5 R5) |

---

## 1. An IEEE binary64 model that is provable

### Candidates

| candidate | finding | verdict |
|---|---|---|
| Vendored `riscv-lean` (Sail RV64D → Lean) | `Lean_RV64D/LeanRV64D/RiscvExtras.lean`: `riscv_f64Add`, `riscv_f64Mul`, `riscv_f64Div`, `riscv_f64Lt`, `riscv_i64ToF64`, `riscv_f64ToI64`, … are all **`axiom`**. The executable model defines them as `panic "TODO"`. Sail RISC-V calls Berkeley SoftFloat in C through `extern`, so there is no float spec in Lean. The ELF never runs an F/D instruction, so these would never be used anyway. | no (Law 2: no axioms) |
| Lean core `Float` | Opaque `extern` operations with no lemmas. Usable only as an `#eval` test oracle through `Float.ofBits`/`toBits` on the host's IEEE hardware. | oracle only |
| Mathlib | Not a dependency (`lake-manifest.json`: iris, batteries, Qq, ELFSage, Sail, Cli). `Mathlib/Data/FP/Basic.lean` (`FP.Float`, `FP.RMode.NE`) is self-described as incomplete and is not a binary64 bit model [CHECK]. Adding Mathlib to a Lean v4.34 project is a heavy, version-pinned dependency. | no |
| Lean 4 IEEE libraries (Flocq-style) | No complete Lean 4 port of Flocq that I know of. There are partial Mathlib-based rounding formalisations (I recall a "Flean" project) [CHECK]. The Sail stdlib may now ship Sail-native float operations (`lib/float/*.sail`) that the Lean backend could translate [CHECK]; that would be a bit-level executable spec, useful as a second oracle, not a proof-friendly one. | not now; revisit as oracles |
| **Write a minimal spec**: round-to-nearest-even of exact dyadic values over `BitVec 64`, with `Nat`/`Int` arithmetic only | Batteries is already a dependency, but we do not need `Rat` at all. Every IEEE result is `round(exact)`, where the exact value is a dyadic `±n·2^e` (add, sub, mul), or a dyadic plus a sticky bit (div: `n₁·2^k / n₂` with remainder ≠ 0). Decimal↔binary is the same with `10^k`. All of it is `Nat.mul/div/mod/pow/shift`, which the kernel evaluates with GMP, so `decide +kernel` works on concrete programs (`bcSem_of_run`). | **recommended** |

### Recommendation: `Lua/Num/F64.lean`, an exact-rounding spec

One module, ELF-independent, imported by both `Lua.Bytecode.Semantics` and
`Lua.Ast.Semantics`.

```lean
namespace Lua.Num
/-- A binary64 datum is its bits. -/
abbrev F64 := BitVec 64

/-- What the bits denote. -/
inductive F64.Cls | nan | inf (neg : Bool) | fin (neg : Bool) (m : Nat) (e : Int)  -- (-1)^neg·m·2^e, m < 2^53

def F64.cls : F64 → F64.Cls
/-- RNE of (-1)^neg·(n + ε)·2^e, where `sticky` says ε ∈ (0,1). It handles
subnormals (emin = -1074) and overflow to ±inf. The sign of an exact zero is
a parameter (IEEE §6.3). -/
def F64.round (neg : Bool) (n : Nat) (e : Int) (sticky : Bool) : F64
def F64.add/sub/mul/div : F64 → F64 → F64     -- exact, then `round`; NaN in or invalid ⇒ `F64.qnan`
def F64.neg (x : F64) : F64 := x ^^^ (1 <<< 63) -- sign flip (Lua's inline `-x`)
def F64.lt/le/eq : F64 → F64 → Bool            -- IEEE ordered; NaN ⇒ false; -0 = +0
def F64.ofInt (i : BitVec 64) : F64            -- __floatdidf: RNE of i.toInt
def F64.truncInt? (x : F64) : Option (BitVec 64) -- __fixdfdi on the range Lua guards
def F64.floor (x : F64) : F64                  -- exact (roundToIntegral toward −∞)
def F64.fmod (x y : F64) : F64                 -- exact: x − trunc(x/y)·y computed exactly
def F64.qnan : F64 := 0x7ff8000000000000#64     -- the ELF's canonical NaN [CHECK: §5 R1]
```

`Lua/Num/Decimal.lean` holds the decimal side:

* `F64.ofDecimal (neg) (d : Nat) (e : Int)` and `F64.ofHex (neg) (m : Nat)
  (e : Int)`: RNE of `d·10^e` and `m·2^e`. When `|e|` exceeds a bound
  (`e + digits d > 310` → ±inf; `< −343` → ±0), the result saturates
  without computing `10^|e|`, so that `decide +kernel` never builds
  `10^999999999`.
* `str2d : List UInt8 → Option F64`: the grammar `strtod` accepts (spaces,
  sign, decimal or `0x` hex mantissa, optional `e`/`p` exponent), with the
  `strpbrk(".xXnN")` mode rule of `l_str2d`, trailing spaces, and nothing
  else.
* `dec14 : F64 → (Bool × Nat × Int)`: the correctly rounded 14-significant-
  digit decimal (RNE on exact ties) of a finite nonzero value. `fmtG14`
  turns it into C99 `%.14g`: exponent `X`; `%e` style if `X < −4 ∨ X ≥ 14`,
  else `%f`; trailing zeros and a bare `.` stripped; exponent sign always
  printed, at least 2 digits. `inf`/`-inf`/`nan`, with NaN sign [CHECK
  newlib].
* `tostringbuff : F64 → List UInt8`: `fmtG14`, then `.0` appended when every
  byte is in `-0123456789`.

**Characterisation lemmas.** These are written once and used by both the
machine proofs and the metatheory:
* `round_nearest`: `round` returns a representable value within half an
  ulp, with ties to even;
* `round_mono`;
* `ofInt_exact` for `|i| ≤ 2^53`;
* `floor_spec`, `fmod_exact`;
* `lt_iff_exact`: on finite values, `lt` is the order on exact values.

They need only `Nat`/`Int` and `omega`, never Mathlib.

**Validation of the spec (evidence, not proof).** `scripts/test_f64.lean`
(`#eval`, outside the proof build) compares
`F64.add/sub/mul/div/ofInt/lt/le/eq/floor` against Lean's host `Float` via
`Float.ofBits` on about 10⁶ random and edge vectors: classes, subnormal
boundaries, ties, `±0`, overflow. NaN results are compared by class only.
`fmtG14` and `str2d` are compared against host `lua` on the corpus
generator's vectors, and against the ELF on the Sail emulator (§3, the
validation harness), which is the only oracle for NaN sign.

**Effort (estimate).**
* `F64.lean` + `Decimal.lean`: about 900–1,300 lines; 2 lanes of about 3–5
  agent-days, which can run in parallel (binary ops / decimal).
* Characterisation lemmas: 1–2 lanes of about 5 days. Only the machine-proof
  route (§3 level 2) needs them, so they are not on the semantics' critical
  path.

---

## 2. What `δ` gains

### Values and the shared number layer

```lean
inductive Value | nil | bool (b : Bool) | int (i : BitVec 64) | flt (x : F64) | str … | builtin …
```

`Const.toValue?`'s `.float b ↦ some (.flt b)`, so `kval` and `LOADK` accept
float constants.

`Lua/Num/Arith.lean` holds one transcription per C function. Both semantics
call it, so `LuaSem` and `BcSem` cannot drift. Today they have duplicate
`str2int`s: `Bytecode.str2int` and `Ast.str2int`.

| Lean | C (Lua 5.4.7) | rule |
|---|---|---|
| `Num := int i \| flt x` | `TValue` numbers | |
| `str2num : List UInt8 → Option Num` | `luaO_str2num` + `l_strton` (`== len+1`) | `str2int` first (decimal overflow ⇒ not an int); else `str2d`; an embedded `\0` rejects |
| `tonumber : Value → Option F64` | `luaV_tonumber_` (`tonumber` macro) | int ⇒ `ofInt`; str ⇒ `str2num` then to float; flt ⇒ itself |
| `tonumberns` | `tonumberns` macro | numbers only, no strings (the `op_arithf` fast path) |
| `flttointeger (m : F2I) : F64 → Option (BitVec 64)` | `luaV_flttointeger` | `f := floor x`; `x ≠ f` ⇒ `eq`: none, `ceil`: `f+1`; then `lua_numbertointeger`: `−2^63 ≤ f < 2^63` ⇒ trunc |
| `tointegerns m`, `tointeger m` | `luaV_tointegerns`, `luaV_tointeger` | the second adds string→`str2num` |
| `intfitsf i` | `l_intfitsf` (`NBM = 53`) | `2^53 + i (unsigned) ≤ 2^54` |
| `ltNum`, `leNum` | `LTnum`/`LEnum`, `LTintfloat`, `LEintfloat`, `LTfloatint`, `LEfloatint` | mixed int/float: compare as floats if `intfitsf`, else through `flttointeger` ceil/floor; out of range ⇒ the sign of `f` |
| `eqNum` | `luaV_equalobj` / `luaV_rawequalobj` | same variant: `int ==` / `F64.eq`; mixed: `tointegerns F2Ieq` on both and `==` (so `2^63 ≠ mininteger`, `NaN ≠ NaN`, `-0 == 0`) |
| `nummod x y` | `luai_nummod` | `m := fmod x y; if (m>0 ? y<0 : (m<0 ∧ y>0)) then m+y else m` |
| `numidiv x y` | `luai_numidiv` | `floor (x / y)` |
| `numpow x y` | `luai_numpow` | `y == 2 ⇒ x·x`, else `H.pow x y` (see the pow decision below) |
| `numarith o x y` | `numarith` | `+ − × / ^ // %` and `unm` as above |
| `rawArith o : Num → Num → Option Num` | `luaO_rawarith` | bitwise: `tointegerns F2Ieq` both, else fail; `/`, `^`: `tonumberns` both ⇒ float; others: int×int ⇒ `intarith` (an error on `n//0`, `n%0`), else floats |
| `showNum` | `tostringbuff` | int: `%d`; flt: `Decimal.tostringbuff` |

**The pow decision.** C does not fix `pow`'s accuracy, and the ELF's
`__ieee754_pow` (fdlibm) is not correctly rounded. Make it a `Host` field,
`Host.pow : F64 → F64 → F64`, beside `showBuiltin`. `luaLayout`'s instance is
`fdlibmPow`, a Lean transcription of `e_pow.c` over `F64`'s operations: it
is loop-free, uses only `+ − × ÷`, `scalbn` and `sqrt`, and is computable,
so concrete programs still `decide`. Everything else in `δ` is concrete.
Keep `Host` minimal.

### `δ` and the kernels, opcode by opcode

All changes are `opKernel` entries and `δ` arms (R16/R17: no `Step`
constructors, no per-rule proof arms). One combinator changes shape.

* **`opArith`** gets a three-way outcome. Today it says "two ints ⇒ result,
  otherwise fall through to `MMBIN`". `luaV_execute`'s fast path is
  `op_arith`/`op_arithK`/`op_arithI` (int×int ⇒ `intop`; both `tonumberns`
  ⇒ float op), `op_arithf` (`DIV`, `POW`: floats only) and `op_bitwise`
  (`tointegerns F2Ieq` both). So:

  ```lean
  inductive Fast | val (v : Value) | mm | err      -- err: n%0 / n//0 (luaG_runerror)
  def fastArith : FastOp → List Value → Fast       -- one arm per lvm.c macro
  -- body: .val v ⇒ edge 0 (store, skip MMBIN); .mm ⇒ edge 1; .err ⇒ none
  ```

* **`BinOp`** gains `div` and `pow`. `BinOp.ofTM` gains `10 ↦ pow` and
  `11 ↦ div`. `strMeta` becomes `add sub mul mod pow div idiv` (`lstrlib.c`
  `stringmetamethods`; `__unm` separately). The bitwise ops stay out, so
  `"3"&1` is still an error.
* **`δ (.tm o)`** (the `MMBIN*` string metamethods) is `arith` in
  `lstrlib.c`: when `o.strMeta` and one operand is a string, apply `tonum`
  to each (a number stays, a string goes through `str2num`, anything else
  errors through `trymt`), then `rawArith`. A `rawArith` failure is an error.
  Non-string `MMBIN` operands (a non-integral float in a bitwise op) are
  `luaG_tointerror`/`opinterror`: `none`.
* **New kernels:**
  * `LOADF`: `move` of `.flt (ofInt sBx)` (`__floatsidf`; exact);
  * `DIV`, `DIVK`, `POW`, `POWK`: `arithRR`/`arithRK` with `div`/`pow`;
  * `MMBIN*` with `TM_DIV`/`TM_POW`.
* **Float paths of existing kernels:**
  * `ADD SUB MUL MOD IDIV` and `…K`, `ADDI`: `luai_num*`, `luaV_modf`,
    `floor`;
  * `BAND BOR BXOR SHL SHR`, `…K`, `SHLI SHRI`: integral floats coerce
    (`3.0|0 = 3`);
  * `BANDK` still demands an integer `K[C]`.
* **`UNM`:** int ⇒ wrap; flt ⇒ `F64.neg`; str ⇒ `__unm` ⇒ `tonum` ⇒
  `rawArith unm` (int or float).
* **`BNOT`:** `tointegerns F2Ieq`, else `none` (`luaG_tointerror`).
* **`EQ`/`EQK`:** `eqNum` for number pairs; structural equality otherwise.
  `δ .eq` no longer uses `decide (x = y)` on `Value`: `.flt` bits are not
  Lua equality.
* **`EQI`:** int `==`; flt ⇒ `F64.eq x (ofInt im)`; else false.
* **`LT`/`LE`:** `ltNum`/`leNum` on numbers; strings unchanged; mixed
  string/number is `none` (`luaG_ordererror`).
* **`LTI LEI GTI GEI`:** `op_orderI`: int; flt ⇒ `F64.lt/le` against
  `ofInt im` (with the `isf` flag deciding the operand order); else `none`.
* **`FORPREP`** (`forprep`, `forlimit`): three edges.
  * Integer loop (`init`, `step` ints): the limit goes through
    `tointeger (step<0 ? ceil : floor)`, which covers strings (`"2"`).
    Otherwise `tonumber` the limit and clip it to `maxinteger`/
    `mininteger`, or skip the loop by the sign. A non-numeral is `none`
    (`luaG_forerror`).
  * Float loop (`tonumber` all three, strings included): a zero step is
    `none`; the skip test is `0<step ? limit<init : init<limit`; otherwise
    defs `[A, A+1, A+2, A+3]` all `.flt`.
  * Skip.
* **`FORLOOP`:** dispatch on `R[A+2]`'s variant, as `lvm.c` does
  (`ttisinteger(s2v(ra+2))`).
  * Int: unchanged.
  * Flt: `floatforloop`, repeated addition `idx := idx + step`, then
    `0<step ? idx ≤ limit : limit ≤ idx` ⇒ defs `[A, A+3]`.
* **`CONCAT`**, **`print`:** `Value.toStr?`/`Value.show (.flt x)` =
  `tostringbuff x`.

### `Supported` gains one static check: loop-internal registers

`lvm.c` reads `R[A+1]` with `ivalue`/`fltvalue` without a tag test (the
lane-5 "`FORLOOP` on a non-integer internal register" escape). `Supported`
must therefore know that, at every `FORLOOP`, `R[A..A+2]` were last written
by the matching `FORPREP`/`FORLOOP`.

Check: no instruction strictly inside the loop's pc range has a def or kill
port in `[A, A+3)`, and no edge enters the range except `FORPREP`'s. `luac`
satisfies this, because the `(for state)` locals are never assigned and
`goto` cannot enter a block. It is decidable and one `decide` per program.
With it, `FORLOOP`'s two kernels cover every reachable state.

### Escapes, after floats

* `Fault.Escape` (the lane-5 superset) is replaced by the exact predicate
  `Fault.Continues` ("`lvm.c` continues here").
* `body_fault`, re-proved over the new table, gives
  `fails_not_continues : φ.Fails vs → ¬ φ.Continues vs`.
* From that, `noEscape_of_supported : Supported p → NoEscape H p`.

The three `Escape.lean` programs become positive `BcSem` facts:
`"2.5\n"`, `"1\n2\n"`, `"-1.5\n"` by `bcSem_of_run` + `decide +kernel`.
This is the acceptance test of S2 below.

---

## 3. What the machine side needs

### Call-node summaries keyed by entry pc

These use the same shape as `divdi3_sum` (`Lua/Vm/Sim/Kit/Divdi3.lean`):

```lean
theorem adddf3_sum (x y r) (f : HFrame) … :
  Triple (SegSt 0x8002d7a8#64 (⟨x10, x⟩ :: ⟨x11, y⟩ :: ⟨x1, r⟩ :: f.pins) (ArmPay mem o))
         (SegSt r (⟨x10, F64.add x y⟩ :: f.pins) (ArmPay mem o))
```

The comparison routines return an `Int`-coded `a0`, so their summaries say
"`a0` is negative/zero/positive iff …", with the NaN conventions:
`__ledf2` gives `+1` on unordered and `__gedf2` gives `−1` [CHECK the exact
values in libgcc `soft-fp/{le,ge}df2.c`].

### Two levels per routine

1. **Machine ⇒ lifted function.** `scripts/syi/gen_fn.py --fn __adddf3
   --fold` emits the block arms and the `FnSummary` DAG fold. The routines
   are loop-free, so the fold is linear in blocks, not in the 497–12,035
   paths. Its result is `a0 = E(x, y)`, a generated Lean function over
   `BitVec 64` (the decompiled routine). `__muldi3`, `__udivdi3`,
   `__umoddi3` and `__clzdi2` enter as call nodes; the first three have
   summaries already, and `__clzdi2` needs one (a 5-instruction loop:
   `loopFromBody`). This level is mechanical.
2. **Lifted function ⇒ spec:** `E x y = F64.add x y`. This is pure Lean,
   ELF-independent, and reusable in ship-your-interpreter (the WHILE ELF has
   the same libgcc). It is the real cost.

   Without `bv_decide`/`native_decide` (Law 2), proofs go through `toNat` +
   `omega` + the characterisation lemmas. Variable shifts are nonlinear for
   `omega`, so a library of soft-fp stage lemmas is needed. The stages are
   unpack (`_FP_UNPACK_SEMIRAW_D`), align with sticky, normalize (`clz`),
   round (`_FP_ROUND`, `_FP_ROUND_NEAREST`) and pack. Each is stated over
   `(neg, m, e)` triples and matched to the lifted blocks by the generator's
   block boundaries.

**Until level 2 lands, each routine's summary is a named, typed premise**
(Law 2), e.g. `SoftFloatSpec`, a structure with one field per routine
(`add : ∀ x y, AddDf3Sum x y`, …). Its doc comment says the premise is
supplied by level 2, and evidenced meanwhile by the validation harness
below.

| routine | level 1 | level 2 (estimate) |
|---|---|---|
| `__floatsidf`, `__fixdfdi`, `__eqdf2` | small | days each |
| `__floatdidf`, `__ledf2`, `__gedf2` | small | days each |
| `floor` | small (calls `__adddf3`/`__gedf2` only for the inexact flag; the result is from bit masks) | about 1 week |
| `__adddf3`, `__subdf3` | medium | 2–4 weeks for the pair, sharing stages |
| `__muldf3` | medium (`__muldi3` ×4 for the 128-bit product) | 2–3 weeks |
| `__divdf3` | medium (jump tables; `__udivdi3`/`__umoddi3`) | 3–5 weeks |
| `fmod`/`__ieee754_fmod` | 6 loops, `loopFromBody` | 3+ weeks |
| `pow`/`__ieee754_pow` (+ `sqrt`, `scalbn`) | 893 + 209 + 106 insns | level 2 is `fdlibmPow`'s own definition: a transcription, so it is level 1 plus `sqrt`'s loops. 2–3 weeks |

### `_dtoa_r` and `_strtod_r`: the cheapest faithful summaries

The bignum code is heap-allocating: `_Balloc` → `_calloc_r`, the reent
freelist, and `__assert_func` on OOM. Gay's algorithms are research-scale
to verify. The cheapest faithful choice is **one obligation per call node,
at the narrowest C interface Lua uses**, not at `_dtoa_r`:

* **`G14From snprintfPc`**: `snprintf(buf, 44, "%.14g", x)`, called from
  `tostringbuff`, writes `fmtG14 x` plus a NUL into `buf[0..44)` and returns
  its length in `a0`. Its frame:
  * memory outside `buf`, the `_impure_ptr` mp fields (`_result`,
    `_freelist`) and heap chunks owned by the allocator is unchanged;
  * the allocator invariant (`Lua/Vm/DlHeap.lean`) is preserved;
  * an OOM disjunct (`__assert_func` → `abort`) is a non-zero exit.

  There is one call node (`tostringbuff.part.0.isra.0`) and one fixed format
  pointer (from `Layout.lean`).
* **`Str2dFrom strtodPc`**: `strtod(s, &end)` on a NUL-terminated string
  with no `n`/`N`, called from `l_str2dloc`, returns `str2d`'s float in `a0`
  and `end` at the end of the longest accepted prefix. It has the same
  frame/heap clauses.

Both are named premises, in the style of `ThrowFrom`. Partial discharge
comes cheapest first:

1. `strtod`'s exact fast path: ≤ 15 significant digits, `|e| ≤ 22`, so the
   result is `digits ×/÷ tens[e]`, one exact soft op; no bignums.
2. `_dtoa_r`'s two fast paths. The small-integer path is `be ≥ 0 ∧ k ≤
   Int_max`. The `try_quick` path applies because `ilim = 14 ≤ Quick_max =
   14` [CHECK]. Both run only `__d2b` (one `Balloc`) plus soft-fp ops. They
   cover most printed values and bail out to the bignum path when inexact.
3. The bignum slow paths, last or never. If never, the premise stays named
   in PHASES.md.

**Validation harness (evidence for every premise).** `c/tests/float/`
proposes Lua programs that print, parse and compute about 10⁵ floats each:
edge classes, ties such as `100000000000000.5` → `1e+14`, subnormals,
`2^±1074`, and hex strings. They run on the Sail emulator (about 47k
steps/s, so about 1 hour per 10⁸ steps). The output is diffed against the
Lean spec run by `#eval`. The libgcc routines are `identical_mod_reloc` to
`libgcc.a`, so a C harness ELF calling `__adddf3` etc. directly on 10⁶
vectors (about 100 steps per call, so about 30 min) gives evidence for
`SoftFloatSpec` at the Lua ELF's code.

### Arms, cheapest first

The census's `luaV_execute_arms.tsv` lists each arm's float callees. Each
arm's float path runs the at-lemma route with the summaries above as call
nodes. `VmRel`/`TValueRepr` gain `float` (tag `vNumFlt = 19`, already in
`Layout.lean`; `ConstRepr` already has floats).

| tier | arms (float paths) | new callees |
|---|---|---|
| T0 | `MOVE`, `TEST`/`TESTSET`, `NOT`, `LOADK` of a float constant (tag-agnostic copies: only `Repr` changes); `UNM` float (inline sign flip) | none |
| T1 | `LOADF`; `EQI`; `LTI LEI GTI GEI` | `__floatsidf`, `__eqdf2`, `__ledf2`, `__gedf2` |
| T2 | `ADD SUB ADDK SUBK ADDI`; `FORLOOP` float | `__adddf3`, `__subdf3`, `__floatdidf`, `__gedf2`/`__ledf2` |
| T3 | `MUL MULK`; `DIV DIVK`; bitwise float coercion (13 arms through `flttointeger`); `EQ EQK` (`luaV_equalobj`); `LT LE` mixed (`LTnum`) | `__muldf3`, `__divdf3`, `floor`, `__fixdfdi` |
| T4 | `MOD MODK`, `IDIV IDIVK` float; `POW POWK`; `FORPREP` (205 insns, 25 branches; `luaV_tointeger`, `luaV_tonumber_` → `strtod`) | `fmod`, `pow`, `Str2dFrom` |
| T5 | `MMBIN MMBINI MMBINK` string coercion; `UNM` on strings; `print`/`CONCAT` of floats | the Lua→C call (`luaT_callTMres` → `luaD_call` → `arith_*`, `lua_arith`); `G14From`; string creation (`luaS_newlstr`) shared with `CONCAT` and `ThrowFrom` |

T5 needs C-closure calls through `luaD_call`. That infrastructure is F3/F4
scale and also blocks `ThrowFrom` and the `ErrorSimRest` sites, so it is
scheduled with them.

---

## 4. Phasing

Each step merges on its own and keeps `scripts/check.sh` green.

| step | content | depends on | parallel with |
|---|---|---|---|
| **S0a** | `Lua/Num/F64.lean`: `cls`, `round`, the binary ops, comparisons, `ofInt`, `truncInt?`, `floor`, `fmod`, `neg`, `qnan`; `#eval` test vs host `Float` | — | S0b, M0 |
| **S0b** | `Lua/Num/Decimal.lean`: `str2d`, `ofDecimal`, `ofHex`, `dec14`, `fmtG14`, `tostringbuff`; test vs host `lua` (NaN sign excepted) | — | S0a, M0 |
| **S0c** | `fdlibmPow` (transcription of `e_pow.c`, `e_sqrt.c`, `s_scalbn.c` over `F64`) | S0a | S1 |
| **S1** | `Lua/Num/Arith.lean` (the table in §2). `Value.flt`, `Fast`, `opArith` 3-way, `BinOp.div/pow`, `Host.pow`; the kernels of §2; `Fragment.lean` ledger moves `LOADF DIV DIVK POW POWK` into F1; the `Supported` loop-register check | S0a, S0b | M0 |
| **S1b** | metatheory re-run: `kstep_iff`, `footprint`, `certain_answers`, `FragmentSound`, `opKernel_wf`, `body_fault`, the new combinators' `Wf`/failure lemmas, gate `bc-rule-fanout` | S1 | S3 |
| **S2** | `Fault.Continues`, `fails_not_continues`, `noEscape_of_supported`; `Escape.lean` becomes three positive `BcSem` facts; float corpus programs through `gen_proto.py` + `bcSem_of_run` | S1b | S3, M1 |
| **S3** | Layer B: `LuaSem`'s `binOp`/`unOp`/numeric `for` delegate to `Lua.Num` (one rulebook arm each, R16); `AstSupported` admits float numerals; `CompileTV` corpus re-run with float programs; check of folded `^` constants (§5 R5) | S1 | S1b, S2, M* |
| **M0** | `Repr`/`VmRel` float case; the `SoftFloatSpec`, `G14From`, `Str2dFrom` premise structures; level 1 for the T1 routines (`__floatsidf`, `__eqdf2`, `__ledf2`, `__gedf2`) and `__clzdi2` | — (spec names from S0a) | S0, S1 |
| **M1 — pilot** | the held-out pilot below | M0, S1 | S2, S3 |
| **M2** | T0, T1 arms, then T2 | M1 adopts | level-2 lanes |
| **M3** | T3, then T4 arms | M2 | level-2 lanes |
| **L2-\*** | level-2 proofs, one lane per routine family: small conversions/compares, add/sub, mul, div, floor/fmod, pow | S0a lemmas | everything after S0a |
| **M4** | T5 (with the F3/F4 C-call work and `ThrowFrom`) | the C-call infrastructure | — |
| **S5** | remove `NoEscape`: `vm_refinement_Statement luaLayout` from `vm_refinement_ne_of_*` + `noEscape_of_supported`, under the named premises `SoftFloatSpec`, `G14From`, `Str2dFrom` (and the remaining lane-5 ones) | S2, M2–M4 | — |

### Held-out pilot (M1): abstraction-discovery check on the soft-float summaries

The question is whether a float arm costs about the same as an int arm
once a summary exists, i.e. whether the call node is one line. A new gate
cluster `a1-float-arm` (ledger `abstractions/ledger/a1-float-arm.tsv`)
measures hand lines per float-path arm.

* **Training:** `LOADF`, `LTI` (float path), `EQI` (float path), on the
  premises `__floatsidf`, `__ledf2`, `__eqdf2`.
* **Held out:** `GEI` (float), `ADDI` (float, via the `__adddf3` premise),
  `FORLOOP` (float, three calls in one arm: `__adddf3`, `__gedf2`/
  `__ledf2`).
* **Pass:** held-out mean ≤ 1.5× the int-arm mean in `a1-kit-arm`, and no
  new per-arm lemma kind. **Fail:** run `/abstraction-discovery` with the
  census restricted to float call nodes before M2.

A second pilot runs on level 2: build the stage library on `__floatdidf` +
`__ledf2`, hold out `__fixdfdi` + `__gedf2`, and measure lines per routine.
It decides whether `__adddf3` level 2 is attempted or stays a premise for
now.

---

## 5. Risks

| # | risk | mitigation |
|---|---|---|
| R1 | **NaN bits and rounding mode.** Expected: RISC-V libgcc soft-fp without `__riscv_flen` uses a fixed round-to-nearest mode and a canonical NaN `0x7ff8000000000000` (sign 0, `_FP_KEEPNANFRACP 0`) [CHECK `libgcc/config/riscv/sfp-machine.h`]. A wrong `F64.qnan` makes every NaN-producing program's print wrong. | read the header; run `print(0/0, -(0/0), 1%0.0)` on the ELF (Sail); the host prints `-nan nan -nan` and is not an oracle |
| R2 | newlib `%g` of NaN: whether `_svfprintf_r` prints a sign for a negative NaN (`-(0/0)`) [CHECK] | same ELF probe; `fmtG14` follows the ELF |
| R3 | `_dtoa_r` mode 2: RNE on exact ties, and `try_quick` applying at `ndigits = 14` (`Quick_max = 14`) [CHECK newlib `mprec`/`dtoa.c` 4.5.0] | test vector `100000000000000.5` → `1e+14` |
| R4 | newlib `_strtod_l` correctly rounded for every input (long mantissas, subnormals, hex with more than 53 bits) [CHECK; I recall historical newlib `strtod` rounding bugs] | harness: random 17–40-digit decimals vs `str2d`; any mismatch is a finding, and the spec follows the ELF only after review |
| R5 | **Host `luac` folds `^` with glibc `pow`** (`2^0.5` → `LOADK 1.4142135623731`), while the ELF computes runtime `^` with fdlibm. Folding also covers `+ − × / // %`, which is IEEE-identical on x86-64 SSE2 (fold refuses NaN and 0 results). So `CompileTV` with `Host.pow = fdlibmPow` can be false on programs with folded `^` | per program in the corpus: `decide` that `fdlibmPow a b` equals the folded constant; a mismatch is a recorded Layer-B obstruction. Alternatively compile chunks with a target-libm `luac` |
| R6 | Proving libgcc soft-fp without `bv_decide`/`native_decide`. This is the largest effort and could stall on variable shifts and `clz` normalisation | the stage-lemma library (L2 pilot); named premises keep Layer A moving; the work is ELF-independent and shared with ship-your-interpreter |
| R7 | Kernel evaluation cost: `decide +kernel` on `F64` with large exponents (`2^2098`, `10^343`). GMP acceleration is expected for `Nat.add/sub/mul/div/mod/pow/shiftLeft/shiftRight` [CHECK `Nat.log2` and `Nat.pow` acceleration in v4.34] | saturation bounds in `ofDecimal`; avoid well-founded recursion in `round` (use `Nat.log2`, or structural fuel = 2100) |
| R8 | Heap effects of `dtoa`/`strtod` (freelist, first-use `calloc`, `_result` kept between calls, OOM `assert`) | the frame/allocator-invariant clauses in `G14From`/`Str2dFrom`; reuse `SWP` + `gen_alloc_steps.py` |
| R9 | `FORLOOP` reads internal registers without tag tests | the `Supported` loop-register check (§2) |
| R10 | `Value`'s `DecidableEq` is structural, and Lua `==` is not (`1 == 1.0`, `NaN`, `-0`). Anything that used `decide (x = y)` as Lua equality is wrong once `.flt` exists: `δ .eq` today; table keys in F2 (`luaH_get` normalises integral floats to ints; a NaN key is an error) | `eqNum`; flag in PHASES' F2 row |
| R11 | `pow` as a `Host` field weakens the semantics' self-containedness | only `pow`; document that it is implementation-defined in C (no accuracy requirement) [CHECK C11 F.10.4.4 / 7.12.7.4] |
| R12 | C11 7.21.6.1 asks for correctly rounded `%g` and `strtod` only as recommended practice (`DECIMAL_DIG`) [CHECK]. The spec is right only if newlib is | R3/R4 tests |
| R13 | `pow`'s level 1 (`__ieee754_pow` 893 insns + `sqrt` loops) and `fmod`'s 6 loops are the largest non-bignum machine runs | tier T4, after the pilot; `loopFromBody` |
| R14 | Escape programs: `Escape.lean`'s obstruction theorems become false-premise-free positive facts, and PHASES' "StuckSim false" row changes | S2 replaces them; PHASES obligations table updated in the same merge |

## Acceptance

* **After S2:** `vm_refinement_ne_Statement` keeps `NoEscape` only as a
  derived lemma. The three escape programs have proved `BcSem` outputs equal
  to the Sail runs' outputs.
* **After S5:** `vm_refinement_Statement luaLayout` is proved under the
  named premises listed in PHASES.md (`SoftFloatSpec` fields not yet
  discharged at level 2, `G14From`, `Str2dFrom`, and lane 5's `ThrowFrom` /
  `ErrorSimRest`), each with its validation-harness evidence recorded in
  `VALIDATION.md`.
