# F1 lane FMT: the formatting machinery (`snprintf`, `%lld`, `%.14g`, `fprintf`)

Base main `db50e86`. Lines are non-blank, non-comment lines (`/- … -/` blocks
and `--` lines dropped). CPU and peak memory are `lake env lean <file>` of
the module alone (user s / peak RSS). Heartbeats: no option raised anywhere;
every declaration elaborates at the default 200k.

## Result

| target | status | where |
|---|---|---|
| `IntegerToStr_Statement` (`snprintf(buf, 44, "%lld", i)`) | **proved**: `integerToStr_proved` (axioms `[propext, Classical.choice, Quot.sound]`, check.sh stage 6) | `Lua/Vm/Sim/Kit/IntFmtLoop.lean` |
| its statement | **restated**: the buffer may lie above `sp` (`tostringbuff`'s caller's frame; the old `buf + 44 + 4096 ≤ sp` excluded the only caller), the static words read are premises (`IntFmtIn`, `FmtStatic`) | `Lua/Vm/Sim/Kit/CallSpec.lean` |
| `_svfprintf_r` on `%lld` | **generated**: `gen_lua_at.py --fn snprintf/lld`, 278 at-lemmas in 8 parts; helper segments and code pins for `snprintf`, `_svfprintf_r`, `_localeconv_r`, `__locale_mb_cur_max`, `__ascii_mbtowc`, `__ssprint_r`, `__ssputs_r` | `Lua/Vm/AtF/SnprintfLld/*`, `Lua/Vm/Arms/Segs/H*` |
| the digit loop | **proved** by `seg_loop` over the quotient (`snp_loop`); the digits are `decBytes` (`Nat.toDigits 10`), `intBytes_eq` (`LUA_MININTEGER` included) | `Lua/Vm/Sim/Kit/{IntFmtLoop,DecDigits}.lean` |
| `G14From` (`%.14g`, `_dtoa_r`) | **blocked on `MallocR_Statement` (A0)**, PHASES row S0b | — |
| `RunerrorHead_Statement`'s formatting | `%d` is now `integerToStr_proved`; the rest is **blocked on `MallocR_Statement` (A0)** | PHASES row `ErrorSimRest` |
| `Unwind_Statement`'s `fprintf(stderr)` | **blocked on `FreeR_Statement`/`_realloc_r` (A0)** for the unwind around it; not started | PHASES row `ErrorSimRest` |

## Generator extensions (`scripts/gen_lua_at.py`, `gen_lua_arms.py`)

* a narrow reload of the low half of a literal word, with the carried hypothesis;
* `kill` on calls; a `subw` of the same atom; `small32` for `sext.w`/`addiw`/`addw`/`subw`
  of small counts, with signed and unsigned interval decisions (`ub`);
* pure calls may `drop` registers (`umoddi3_sum` drops `ra`); `root_rcellsw`;
* `junk` registers: dead registers a path never reads are pinned (`fmt_pin`);
* `parts`: a spec split into `<Mod>/Defs.lean`, `<Mod>/P<k>.lean` and an index
  (one module of 278 lemmas ran out of memory);
* `gen_lua_arms.py`: `strlen` keeps `s6`/`s10` (`PASS_THROUGH`, `strlen_sumU`);
  `INDIRECT[0x80042f5c]` (`mbtowc` through the locale);
  `PASS_THROUGH_FOR` for `__udivdi3` under `_svfprintf_r`.

## Numbers

| | lines |
|---|---|
| hand: `Kit/IntFmt.lean` (the run per root path, `fat_run`) | 411 |
| hand: `Kit/IntFmtSum.lean` (entry to the conversion, one-digit paths, frame facts, agreements) | 672 |
| hand: `Kit/IntFmtLoop.lean` (the loop, multi-digit paths, the theorem) | 634 |
| hand: `Kit/DecDigits.lean`, `Kit/FmtLib.lean` | 43 + 114 |
| hand: `Kit/Strlen.lean`, `Kit/CallSpec.lean`, `Kit/AtFn.lean` changes | ~110 |
| generator changes (`gen_lua_at.py` +269/−, `gen_lua_arms.py` +40, `gen_lua_code.py` +6) | ~315 |
| generated: `Lua/Vm/AtF/SnprintfLld*` | 6,768 |
| generated: segments and code pins (`Lua/Vm/Arms/Segs/H*`, `Lua/Vm/Code*`) | ~95,000 inserted |

CPU / peak (one module): each `SnprintfLld/P<k>` 60–140 s, ~3.5 GB;
`IntFmt` ~100 s; `IntFmtSum` ~120 s, `IntFmtLoop` ~5 s once its imports
are built (all under 16 GB caps). The whole chain after `FmtLib` changed
(`lake build Lua.Vm.Sim.Kit.IntFmtLoop`, 4 threads): 1,672 s CPU, 6 min wall,
peak 4.0 GB.

## Obstacles met

1. `omega` reaches the maximum recursion depth with several literal
   subtractions of one atom in context (`sp - 864 + 328 ≤ c`, `c ≤ sp - 516`,
   `sp - 536 + 1 ≤ c`: three suffice, `c/build/fmt/om.lean`). Worked around by
   small arithmetic lemmas with only their hypotheses (`okl_c`, `sub864`,
   `mmspan_*`, `snLoopW_off`) and by clearing such facts once used.
2. `exact`/unification of `x - 516` against a different literal subtraction
   unfolds `Nat.sub` by recursion (`SnV.head` takes the cursor, not `sp`).
3. A structure instance's fields on a continuation line below the first field
   do not parse (`sepByIndent`): the loop's next atoms are `SnV.next`/`SnV.exit`.
4. `FmtLib.fmt_scmp` named `not_lt`/`not_le` (Mathlib names): the rule always
   failed silently inside `fat_hyp`'s `first`; fixed, the duplicate in
   `IntFmt.lean` removed.
5. `G14From`: every finite non-zero value reaches `__d2b` → `_Balloc` →
   `_calloc_r` → `_malloc_r` (objdump call graph: `_dtoa_r` 1,407
   instructions calling `_Balloc`, `__d2b`, the bignum routines and eight
   soft-float routines), so even `_dtoa_r`'s fast paths need `MallocR_Statement`.
6. `RunerrorHead_Statement`: `luaS_newlstr` → `luaC_newobj` → `_malloc_r` and
   `luaC_step`; `Unwind_Statement`: `luaD_shrinkstack` (`_realloc_r`),
   `luaE_shrinkCI` (`_free_r`), `fprintf` → `_vfprintf_r` (3,395
   instructions, `__sinit`, `__swsetup_r`, `__sbprintf`).

The run lemmas of `Kit/IntFmt.lean` (one `fat_run` per root path) were typed
by a scratch script over the at-lemma file; if a second format is done, that
script belongs in `gen_lua_at.py` (emit the root paths' run lemmas).
