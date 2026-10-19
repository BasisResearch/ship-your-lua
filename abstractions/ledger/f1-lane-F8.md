# Lane F1-F8: FORPREP's coerced classes, and `luaO_str2num`'s integer path

The base is main `da2dd3e`. The routes are the callee route (`gen_lua_at.py`
`FNS`, `fat_walk`) for `luaV_tointeger`'s and `luaV_tonumber_`'s number
paths, the arm route with join cuts for the `FORPREP` classes, and `kit_run`
over generated helper segments with `seg_loop` for `luaO_str2num`.

The numbers are taken as in lanes F2–F7:

- **Hand lines** are non-blank, non-comment lines, without `import`, `open`,
  `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports
  built (`LEAN_NUM_THREADS=4`). **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k,
  100k or 150k under which the file builds (`> 150k`: builds only at the
  default 200k). The limit is never raised.

## Result

| target | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| `luaV_tointeger` on a float (modes 1, 2) | **proved** | `toint_flt_sum` (`Kit/TointF.lean`) | 208 (with the next row) | `AtF/TointF1` 645, `AtF/TointF2` 962 | 17.7 s (AtF: 70.9 s, 125.7 s) | 2.84 GB (AtF: 3.05, 3.31 GB) | ≤ 150k (AtF: ≤ 100k) |
| `luaV_tonumber_` on an integer | **proved** | `tonum_int_sum` (`Kit/TointF.lean`) | — | `AtF/TonumI` 191 | 10.0 s (AtF) | 2.25 GB | ≤ 50k |
| the coercions as at-route call nodes | **proved** | `tif_ok_at`, `tif_no_at`, `toni_at` (`Kit/AtCoerce.lean`) | 137 | — | 1.7 s | 2.59 GB | ≤ 50k |
| FORPREP, integer loop, float limit | **proved** | `fp_ti` (`Kit/FpCoerce.lean`), `forprep_ti_arm` cases (`Kit/AtFltForprepTI.lean`) | 82 | `At/ForprepTI` 1242 | 56.8 s (at-file 322.0 s) | 2.98 GB (at-file 5.44 GB) | ≤ 100k (at-file > 150k, ≤ 200k) |
| FORPREP, float loops with integer values | **proved** | `fp_cIIF`, `fp_cIFF`, `fp_cFII`, `fp_cFIF`, `fp_cFFI` (`Kit/AtFltForprepC.lean`) | 37 | `At/ForprepC*` 813–879 each (4212) | 28.8 s (CIIF at-file 142.9 s) | 2.81 GB (3.91 GB) | ≤ 100k (≤ 150k) |
| `FpCoerce_Statement` | **proved from `FpStr_Statement`** | `fpCoerce_of` (`Kit/FpCoerce.lean`) | 60 | — | 4.3 s | 2.67 GB | ≤ 50k |
| `str2int` by positions | **proved** | `str2int_S2I` (`Lua/Num/DecimalIdx.lean`) | 189 | — | 1.7 s | 0.82 GB | ≤ 50k |
| `luaO_str2num` on an integer numeral | **proved** | `str2num_int` (+ `s2_dec`, `s2_hex`, `s2_trail`, `s2_lead`) (`Kit/Str2int.lean`) | 570 | `Segs/HluaO_str2num` 5230, `Sites` 4913 | 99.4 s (Segs 46.7 s) | 2.64 GB (2.59 GB) | ≤ 150k (≤ 100k) |
| FORPREP with a string control value | **open**, `FpStr_Statement` | — | — | — | — | — | — |

`FloatArms.FORPREP` is `FpStr_Statement`. The axioms of every new theorem are
`[propext, Classical.choice, Quot.sound]`; they are in check.sh stage 6.
The gate passes (`a1-float-arm` 45 cases, first 2.9, last 1.7).

## What is left, and why

* **`luaV_tonumber_`'s string path** (`0x8001abac`: `luaO_str2num` on the
  `TString`'s contents, the size test, then `__floatdidf` for an integer)
  on an integer numeral is reachable now: `str2num_int` is its callee. It is
  not yet an at-route call node for the `FORPREP` classes with a string.
* **Every non-integer numeral** (and every non-numeral) runs `l_str2d`:
  `strpbrk`, `l_str2dloc` → newlib `_strtod_l`. There is no summary of it:
  the locale lookup, the fast path's `__floatunsidf`/`__muldf3` with the
  `tens` table, the bignum path's `_Balloc` → `_calloc_r` heap allocations,
  `gethex`, and `errno` on overflow. A `StrtodBig_Statement` premise was not
  added: its fast path is not proved either, so nothing would be discharged
  under it.

## How

1. **Variant call lemmas.** A call with two outcomes (`luaV_tointeger`'s
   float mode: in range or not) is two call lemmas, each with its guard
   (`hg_ti`); the run forks on the guard like a branch.
2. **Number classes.** `fpCoerce_of` splits the three control values by
   constructor (`fp_dispatch`); a stuck kernel refutes the class, a string
   goes to `FpStr_Statement`.
3. **A string callee.** The string is `StrAt` (bytes `sb s k` through the
   terminator); the `luai_ctype_` table is `ctypeOf`, read only through
   `decide` lemmas and then `irreducible`; each loop is `seg_loop` over an
   index form of the model (`S2I`, `dacc`); each branch is its own
   declaration (the heartbeat budget is per declaration).
