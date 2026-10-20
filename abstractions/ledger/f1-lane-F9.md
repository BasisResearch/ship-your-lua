# Lane F1-F9: FORPREP with a string control value (`FpStr_Statement`)

The base is main `7bab868`. The routes are the callee route (`gen_lua_at.py`
`FNS`, `fat_run`) for `luaV_tonumber_`'s and `luaV_tointeger`'s string paths
with `luaO_str2num` spliced by hand from lane F1-F8's `str2num_int`, and the
arm route (A-JOIN, `at_walk`/`at_go`) for the `FORPREP` classes with a string.

The numbers are taken as in lanes F2–F8:

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
| `luaV_tonumber_`, `luaV_tointeger` on a string integer numeral | **proved** | `tons_sum`, `tois_sum` (+ `tons_short`/`long`, `tois_short`/`long`) (`Kit/TonumStr.lean`) | 279 | `AtF/TonumSS` 580, `TonumSL` 445, `TointSS` 590, `TointSL` 365 | 61.7 s (AtF: 44.0, 25.3, 46.5, 25.5 s) | 3.18 GB (AtF: 2.23–2.36 GB) | ≤ 150k (AtF: ≤ 50k) |
| the string coercions as at-route call nodes | **proved** | `tsCtx_at`, `tons_at`, `tois_at` (`Kit/AtCoerceS.lean`) | 100 | — | 2.0 s | 2.48 GB | ≤ 50k |
| FORPREP, 18 float-loop classes with a string integer numeral | **proved** | `fp_s{IIS,IFS,ISF,ISS,FIS,FFS,FSI,FSF,FSS,SII,SIF,SIS,SFI,SFF,SFS,SSI,SSF,SSS}` (`Kit/AtFltForprepS.lean`) | 132 (with the next row) | `At/ForprepC*` 812–936 each (15,753) | 165.0 s (at-files: CSSS 186.4 s, CIIS 141.2 s, CSFF 135.7 s) | 3.41 GB (at-files 3.6–3.8 GB) | ≤ 100k (at-files: CSFF ≤ 150k; CSSS, CIIS > 150k, ≤ 200k) |
| FORPREP, integer loop with a string limit (`ISI`) | **proved** | `fp_sISI`, `si_*` (`Kit/AtFltForprepS.lean`) | — | `At/ForprepSI` 637 | (above; at-file 168.7 s) | (at-file 4.09 GB) | (at-file > 150k, ≤ 200k) |
| a string that is no numeral | **proved** (the kernel stuck) | `fpCoerce_of_flt` (`Kit/FpCoerce.lean`) | 139 (+79 on lane F1-F8's 60) | — | 7.5 s | 2.78 GB | ≤ 100k |
| `FpStr_Statement` | **proved from `FpStrFlt_Statement`** | `fpStr_of` (`Kit/FpCoerce.lean`) | — | — | — | — | — |
| FORPREP with a float numeral string | **open**, `FpStrFlt_Statement` | — | — | — | — | — | — |

`FloatArms.FORPREP` is `FpStrFlt_Statement`: `FORPREP` where every string
control value is a numeral (`str2number`) and one of them is no integer
numeral (`l_str2int` rejects it), i.e. a decimal or hex float numeral. The
axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`;
they are in check.sh stage 6.

## What is proved

1. **`luaV_tonumber_`/`luaV_tointeger` on a string integer numeral**
   (`tons_sum`, `tois_sum`, `Kit/TonumStr.lean`). The string paths of both
   helpers were stops in `gen_lua_arms.py` `HELPERS`; they are segments now.
   The generator walks each from the entry to the `luaO_str2num` call (a
   `calls` node whose return is `len + 1`) and from the return (a second root
   whose frame words are root facts: the result's tag `3`, its integer) to
   the helper's return; a short and a long string are two modules each
   (`Tonum{SS,SL}`, `Toint{SS,SL}`: the tag literal and the `tsslen` read).
   The hand side splices `str2num_int` at the call (the string through the
   frame stores by `StrView.wm8`, as `luaO_str2num` reads it by
   `StrView.kstr`), states the root's facts (the frame words through
   `s2Mem`'s two stores, the size test from the view's `shrlen`/`lnglen`:
   `ts_len`), and closes at the window `[sp - 80, sp)` (`tonsW`, `toisW`: the
   generated memories of the run). One tactic per helper over both modules
   (`tons_go NS`, `tois_go NS`).
2. **The call nodes at a row** (`tons_at`, `tois_at`, `Kit/AtCoerceS.lean`).
   The string register's object is live in the call's memory and apart from
   the callee frames (`tsCtx_at`: `Core.unseal` under `WinFrame`, because
   FORPREP's float path spills to `luaV_execute`'s C frame before the call,
   so `ScrFrame` does not hold; `Ranges.own_apart`). The integer is
   `strIntOf (rsOf X j)`, the register's string read through the context.
3. **The arm classes** (`Kit/AtFltForprepS.lean`). A string class is a
   seeded tag fact `nes (3, 19)` (`gen_lua_at.py` `STR_SEED`: neither the
   integer nor the float tag); `decide` reads it. The 18 float-loop classes
   with a string (`fp_s{IIS,…,SSS}`, one generated module each,
   `At/ForprepC*.lean`) run as the three-float loop is (`fps_arm`); the
   integer loop with a string limit (`ISI`, `At/ForprepSI.lean`) has the
   integer loop's five paths (`si_*`, `fp_sISI`). A string operand's view
   (`str_reg_s`) puts its tag facts in `hta`, its integer in `hxm` (read by
   the leaves' `simp`), and its numeral in `hsn` (the kernel's
   `str2number`).
4. **The dispatch** (`fpCoerce_of_flt`, `Kit/FpCoerce.lean`). Each string is
   split on `str2int`; if all are integer numerals, the class's theorem;
   else each string is split on `str2number`: a non-numeral leaves the kernel
   stuck (`tonumber`/`forLimit` fail), and the rest is `FpStrFlt_Statement`.
   `fpStr_of : FpStrFlt_Statement → FpStr_Statement` keeps lane F1-F8's form.

## What is left, and why (step 2 of the lane: `l_str2d` and `strtod`)

`FpStrFlt_Statement` is exactly the float numeral strings. Their machine run
is `luaO_str2num`'s float path, none of which is summarised:

* **`l_str2int`'s failing exits** to `0x80011b5c` (lane F1-F8 proved only the
  accepting path).
* **`l_str2d`** (`0x80011b5c`–`0x80011c94`, 81 instructions, a 272-byte
  frame): `strpbrk(s, ".xXnN")` (a nested scan), `l_str2dloc` (41
  instructions: `strtod`, then the trailing-space loop over `luai_ctype_`);
  the locale retry (`strchr`, `strlen`, `memcpy`, `l_str2dloc` again) runs
  only on a failed first conversion, so it is not on a numeral's path.
* **`strtod` → `_strtod_l`** (`0x800309b4`, 1601 instructions). `strtod`
  passes `__global_locale` (`addi a3, gp, 288`: no locale lookup call) and
  reads `_impure_ptr` (a `.data` word). `_strtod_l` calls `__muldf3` 13 times,
  `_Bfree` 11, `__ledf2` 5, `__lshift` 4, `__floatunsidf` 4, `__adddf3` 4,
  `strncmp` 2 (the decimal point), `__divdf3` 2, and `_Balloc`, `__s2b`,
  `__d2b`, `__mdiff`, `__pow5mult`, `__multiply`, `__ratio`, `__ulp`,
  `__gethex`, `__errno`. Two obstacles:
  - **The decimal fast path** (at most 15 digits, `|e| ≤ 22`: `tens[e]`
    times or over the digits' double) needs a level-(a) walk of
    `_strtod_l`'s digit loops (four `seg_loop`s: leading zeros, digits,
    fraction, exponent) with the soft-float call nodes, and a level-(b)
    proof that the one correctly rounded `__muldf3`/`__divdf3` of two exact
    doubles is `Float.Model.ofScientific m e`. Neither exists; a callee-level
    premise for it alone would be true, but nothing would be discharged under
    it, so none is stated.
  - **The bignum path** (more digits, or a product that is not exact) and
    **`__gethex`** allocate: `_Balloc` pops `_REENT->_freelist[k]` or calls
    `_calloc_r` → `_malloc_r`, and `_Bfree` pushes back. The arm relation's
    `Complement` carries neither the freelists nor the heap's new chunks
    (lane F1-18's finding for `_dtoa_r`; lane F1-19 works on that region
    fact), so the arm cannot be closed after such a call, and a callee-level
    premise that the run keeps the heap would be false. Overflow also stores
    `errno` (F7's `Complement.errno` covers that store).

So the open premise stays at the arm level, with the scope above. The next
step is the fast path (`StrtodFast`: a `gen_lua_at.py` `FNS` spec of
`_strtod_l` with its loops as roots and the soft-float call nodes, then the
exactness lemma), and the slow paths after F1-19's `_REENT` freelist
invariant lands.

## Setup

| file | lines | what |
|---|---|---|
| `scripts/gen_lua_arms.py` | python | `luaV_tonumber_`'s and `luaV_tointeger`'s string paths no longer stops (their segments regenerate; `tonum_int_sum`, `toint_flt_sum`, `toint_sum` build unchanged) |
| `scripts/gen_lua_at.py` | python | `FNS`: `tons`, `tois` (two roots around a `calls` node, `str_cells`); arms: `STR_SEED` (`nes`), `FP_CLASSES` with `S`, `OP_FORPREP_SI`, the `tons`/`tois` call nodes and locations, `IMPORTS` |
| `Kit/TonumStr.lean` | 279 | `tsCx`, `TsCtx`, `StrView.kstr`, `tonsW`, `toisW`, `ts_view`, `ts_len`, `ts_setup`, `ts_tag`, `tons_go`, `tois_go`, `tons_sum`, `tois_sum` |
| `Kit/AtCoerceS.lean` | 100 | `rsOf`, `strIntOf`, `ValRepr.str_tag`, `ValRepr.str_ne`, `tsCtx_at`, `tons_at`, `tois_at`, `at_tons`, `at_tois` |
| `Kit/AtFltForprepS.lean` | 132 | `StrIReg`, `FCl`, `ClsReg`, `FpClsS`, `str_reg_s`, `cls_reg_s`, `fps_views`, `fps_arm`, `SiQ`, `si_*`, the 19 class theorems |
| `Kit/FpCoerce.lean` | +79 | `FpStrFlt`, `FpStrFlt_Statement`, `fp_num3`, `fp_dispatch` (string splits), `fpCoerce_of_flt`, `fpStr_of` |

## Gate

`python3 abstractions/gate.py` is ok after each step: `a1-float-arm` 69
cases (first 2.5, last 2.8; 3 open named premises in its files); `a1-kit-arm`
69 cases (first 1.9, last 4.1).

## Builds

- **Module builds**, one at a time under a 16 GB cap (`LEAN_NUM_THREADS=4`):
  the four `AtF/Tonum*`/`Toint*` modules, `Kit/TonumStr`, `Kit/AtCoerceS`, the
  19 `At/ForprepC*`/`ForprepSI` modules (38–186 s each), `Kit/AtFltForprepS`,
  `Kit/FpCoerce`, `Sim/Fold`. A parallel `lake build` of the kit with the 19
  at-modules stale exceeds 16 GB (the kernel OOM killer stopped it twice), so
  they are built in sequence.
- **Full check.** `scripts/check.sh` (every stage: generators' drift, the
  discipline, the gate, `lake build Lua Vsa VsaIris`, the OS-spec traces,
  stage 6's axioms) passes under a 30 GB cap: 568 s.
- **Obstacles met.**
  - FORPREP's float path stores to `luaV_execute`'s C frame (`sp + 16`)
    before its conversions, so the call's memory is not `ScrFrame`-exact:
    the string's view comes from `Core.unseal` under `WinFrame`
    (`tsCtx_at`).
  - The generated slot address is the row's form (`base + 16 * a + 32`), not
    `X.w.slot j`: the call node takes the address as `n` with `n = X.w.slot j`.
  - One declaration for both string kinds exceeded 150k heartbeats
    (`TonumStr` `> 150k`): one declaration per kind (`tons_short`/`long`),
    now `≤ 150k`.
