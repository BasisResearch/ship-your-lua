# Floats in `δ`: design

Status: S0a, S0b (lanes float-s0a/s0b), S0c, S1, S1b, S2 and the operator
and `for` part of S3 (lane float-s1, `abstractions/ledger/float-s1.md`) are
built; M0 onwards (the machine side, `FloatArms`) is open.

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

This section was revised on 2026-10-06 after Kiran's note (`~/syi-briefs/FLOAT-MODEL-NOTE.md`). Lean v4.34 core ships a transparent IEEE binary64 model, so δ's spec is Lean's own model, not a hand-written rounding spec.

### What core provides

Checked in the pinned toolchain, `Init/Data/Float/Model/`:

- **`Float.Model`.** A subtype of `UInt64`, with `unpack`/`pack` to `UnpackedFloat` (`Format.binary64`) and RNE rounding in `Unpacked/Round.lean`. It has:
  - arithmetic: `add`, `sub`, `mul`, `div`, `sqrt`, `neg`, `abs`;
  - comparison: `compare : Option Ordering`, `lt`, `le`, `beq`;
  - construction: `ofBits`, `ofInt`/`ofNat`/`ofInt64`/…, and `ofScientific m e` (the RNE of `m·10^e`);
  - conversion: `toInt64` (truncate, with NaN ↦ 0, clamped);
  - classes: `isNaN`, `isInf`, `isFinite`.
- **Native `Float` is equivalent to it** via `Float.toModel`/`Float.ofModel` (`Init/Data/Float/Float.lean`). So host `Float` is now a fast `#eval` oracle connected to the spec *by a theorem*, not an unconnected opaque.
- **NaN is canonicalised.** `pack .notANumber = packedNaN` is positive, exponent all ones, quiet bit only: `0x7ff8000000000000`. Sign and payload are not modelled.
- **No lemma library,** by design. The docstring recommends a separate development proved equal to the model, then transferring lemmas.
- **Not modelled:** `floor`, `fmod`, `pow` (still `extern` opaques on `Float`), Lua's F2I modes, `%.14g`, and hex-float parsing.

The other candidates stay rejected:
- the vendored Sail model's float functions are `axiom`s (Law 2);
- Mathlib is not a dependency;
- a hand-written spec would be a second, untrusted copy of what core already defines.

### Decision

1. **δ's spec is `Float.Model`.** `Value.flt` holds a `Float.Model` together with its *sign bit for NaN* (see 4).
   - `+ − × ÷`, `sqrt`, comparisons, `ofInt`, truncation and decimal rounding (`ofScientific`) are the model's operations, unchanged.
   - `Lua/Num/Arith.lean` defines Lua's numeric functions on top of it, each a transcription of the cited C. These are the parts core lacks:
     - `floor`/`ceil`: exact, defined via `unpack`;
     - `fmod`: exact, as C's `fmod`;
     - Lua's `luai_nummod`/`luai_numidiv`/`luaV_flttointns` (F2I floor/ceil/exact);
     - `pow`: newlib's algorithm, transcribed; the only `Host`-like field.
2. **`Lua/Num/F64.lean` becomes the proof library, not the spec.**
   - It keeps the exact-dyadic development over `BitVec 64` and `Nat`/`Int`, with `round`, `cls` and the characterisation lemmas (`round_nearest`, `round_mono`, `ofInt_exact`, `lt_iff_exact`, `floor_spec`, `fmod_exact`).
   - New obligation: **`F64.add_eq_model`** and its siblings, `F64.op x y = (Float.Model.op (ofBits x) (ofBits y)).toBits` on non-NaN inputs, and class-equal on NaN. This is proved once per operation, then lemmas transfer to the model.
   - The machine proofs (§3, level 2) target F64, then the bridge.
3. **Host `Float` is the fast oracle.** `#eval` tests compare `Float` (via `toModel`/`ofModel`) with `F64` on about 10⁶ vectors. Agreement is evidence for the bridge theorems before they are proved, and it is now *about the same definitions*.
4. **NaN is class-only, with the sign stated explicitly in δ.**
   - Comparisons and arithmetic treat NaN by class, as the model does.
   - Lua observes a NaN's sign only when it is printed (newlib prints `-nan`/`nan` [CHECK on Sail]) and through `math` functions outside F1. So `Value.flt` carries `(m : Float.Model, nanNeg : Bool)`, and δ states:
     - **arithmetic producing NaN** gives the canonical positive NaN. libgcc's RISC-V soft-fp returns a canonical NaN with no payload propagation [CHECK in the ELF: `0/0` on Sail], which matches the model's `packedNaN`;
     - **`neg`/UNM is a raw sign flip** (Lua's `luai_numunm` is `-(a)`; check whether the ELF uses `xor` of bit 63 or `__negdf2`), so `-(0/0)` has `nanNeg = true`;
     - **printing** uses `nanNeg` for `-nan`/`nan`.

   This is the one place δ goes beyond the model, and it is stated as such.
5. **Decimal side** (`Lua/Num/Decimal.lean`, unchanged in scope):
   - `str2d` uses `Float.Model.ofScientific` for the decimal rounding, so `strtod`'s correct rounding is the model's;
   - hex floats (`lua_strx2number`) need a separate exact rounding of `m·2^e`;
   - `%.14g` (`dec14`, `fmtG14`) and `tostringbuff` are defined over the model's unpacked value.

**Effort (revised estimate).**
- The spec side shrinks: no rounding spec to write or validate. What is left is `Arith.lean` (floor, fmod, F2I, pow) and `Decimal.lean`, about 600–900 lines.
- `F64.lean` becomes a proof library plus the bridge theorems, about 900–1,300 lines. It is needed by the machine proofs, not by δ, so it is off the semantics' critical path.

**Impact on the lanes in flight.**
- S0a (`F64.lean`) is re-scoped to "proof library + bridge to `Float.Model`".
- S0b (`Decimal.lean`) uses `ofScientific` for decimal rounding.

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

**The pow decision (as built, lane float-s1).** `pow` is NOT a `Host`
field: a field would make `δ`, and with it `opKernel`/`kernelAt` and every
kernel use, depend on `Host`, while there is one implementation to describe,
the ELF's. `Lua.Num.pow` (`Lua/Num/Pow.lean`) transcribes newlib 4.5.0's
fdlibm `pow` (`w_pow.c` over `e_pow.c`, `s_scalbn.c`) over `Float.Model`, as
`strtod`/`%.14g` already follow newlib; it is computable, so concrete
programs still `decide`, and 1,570 Sail vectors match it bit for bit. A
signalling NaN, which the model cannot hold and on which `pow` differs, is
not a value (`isSNaN`: such a constant has no `LOADK` kernel). The original
proposal follows.

C does not fix `pow`'s accuracy, and the ELF's
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
| R1 | **NaN bits and rounding mode.** Expected: RISC-V libgcc soft-fp without `__riscv_flen` uses a fixed round-to-nearest mode and a canonical NaN `0x7ff8000000000000` (sign 0, `_FP_KEEPNANFRACP 0`) [CHECK `libgcc/config/riscv/sfp-machine.h`]. It must equal `Float.Model`'s `packedNaN` (positive) for δ's "arithmetic NaN is canonical" rule; a mismatch makes every NaN-producing program's print wrong. | read the header; run `print(0/0, -(0/0), 1%0.0)` on the ELF (Sail); the host prints `-nan nan -nan` and is not an oracle |
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
