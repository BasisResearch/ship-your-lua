# Lane F1-24: `luaL_tolstring` on `print`; `PrintFn_Statement` retired

Base: main `11439f0` (lane F1-23). Route: CLAUDE.md's callee-context row (`gen_lua_at.py --fn`, `FNS`) for
`snprintf/p`, `lua_pushfstring/sp` and `luaL_tolstring/fn`, and the `CALL print` row (per-argument
`TolArg`). Lines are non-blank, non-comment lines. CPU and peak memory are one `lake env lean <file>` each
(user time, maximum resident set) under `systemd-run --user --scope -p MemoryMax=16G`, `LEAN_NUM_THREADS=4`.
Heartbeats are per declaration, bracketed by rerunning the file with `-DmaxHeartbeats` 50000 and 100000. No
heartbeat or recursion limit was raised.

## Result

| target | status | where |
|---|---|---|
| `snprintf(buf, 32, "%p", print)` | **proved**: `snprintfP_sum` (`_svfprintf_r`'s `'p'` conversion over the `SnprintfP` roots, the hex digit loop by `seg_loop`) | `Kit/PtrFmt.lean`, `AtF/SnprintfP{,/Runs}.lean` |
| `lua_pushfstring(L, "%s: %p", "function", print)` | **proved**: `pushfP_sum` (stages `pfp_cut`, `pfp_toK`, `pfp_toJ`, `pfp_toP`, `pfp_snp`, `pfp_toJ2`, `pfp_nl`, `pfp_ret`) | `Kit/PushfP.lean`, `AtF/PushfP.lean` |
| `luaL_tolstring` on `print` | **proved**: `tolfn_sum` (over `TolVIn`, `tf_pre`, `toltop_sum`) | `Kit/TolFn.lean`, `AtF/TolFn.lean` |
| `TolFn_Statement := TolArg IsFn` | **proved**: `tolFn_proved` | `Kit/TolFnProof.lean` |
| `PrintFn_Statement` | **retired as a premise**: `printRel_of` routes functions per argument (`TolFn_Statement`); `CallOpen = {printFlt}`; the statement as written follows from `PrintFlt_Statement` (`printFn_of_flt`) | `Kit/PrintRel.lean`, `Kit/CallOpen.lean`, `Kit/TolFnProof.lean` |

Statement change (strengthening only): `PrKeep` keeps `G(L)->mt[nil … function]` (56 bytes, was 32), so
`PrintIn.mt_fn` survives the loop's earlier arguments; every write the loop makes in `g` is below
`g + 480` or at the string cache (`g + 552`), so no proof changed beyond the two `kM`/`kMt` ranges.

## Factoring first (law 3): one glue from a run to `TolPost`

`tolint_sum → TolPost` was ~1,000 lines specific to integers (`tolI_in`, `tolI_tab`, `prIntHit`, `TiNew`,
`prIntNew`). It is now generic in the class, `ArgStr v b` (`print` shows `b`, 1–20 bytes, one allocation's
cost, no literal is `b`, no literal's object holds it): `tolV_in` (over `TolVIn`, tag/payload/metatable word
parameters; `TolIIn` an abbreviation), `tolV_tab`, `prStrHit`, `prStrNew` (`TiNew … v b …`), and one lemma
`tolPost_of_run`.

| per-class glue | before | after |
|---|---|---|
| integers | 996 (inputs … `tolInt_proved`) + 60 (digit/literal lemmas) | 18 (`tolInt_proved`) + 7 (`argStr_int`) + the 60 |
| `print` | (would copy ~1,000) | 18 (`tolFn_proved`) + 25 (`fn_inv`, `lits_ne_fnU8`, `lits_nomatch_fn`, `argStr_fn`) |
| shared, once | — | 987 (generic section) + 38 (`ArgStr` and its count lemmas) |

Setup cost of the factoring: `TolIntProof.lean` +45 net lines (1,126 → 1,171), counted with this lane.

Also factored on the way (each used by both `"%I"` and `"%s: %p"`): `pf_tail` (the push, the epilogue,
`luaC_checkGC`: one tactic per format module), `pf_newlstr` (the `luaS_newlstr` call node out of `pf_nl`),
`PfSlots`-based `pfT_hit`/`pfT_new`, `SnSave` over the buffer size.

## Numbers

| file | hand lines (net) | CPU (s) | peak (MB) | heartbeats |
|---|---|---|---|---|
| `Kit/PtrFmt.lean` (new) | 389 | 225.0 | 4,578 | 4 decls over 100k (`snSaveAP_C`, `snSaveBP_C`, `facC`, `ptrP_bytes`), all under 200k |
| `Kit/PushfP.lean` (new) | 452 | 41.5 | 3,961 | < 50k |
| `Kit/PushfI.lean` | +35 | 47.0 | 3,826 | 50k–100k (`pf_snp`, unchanged) |
| `Kit/TolFn.lean` (new) | 141 | 11.7 | 3,941 | < 50k |
| `Kit/TolFnProof.lean` (new) | 56 | 1.8 | 3,947 | < 50k |
| `Kit/TolIntProof.lean` | +45 | 27.8 | 4,350 | 50k–100k (`TiNew.keeps`, as before) |
| `Kit/AtAlign.lean` (new; `andm8`, `xor_al` moved from `Memcpy.lean`, −32 there) | 107 | 2.0 | 1,919 | < 50k |
| `Kit/AtSubw.lean` (new) | 23 | 1.4 | 1,886 | < 50k |
| `Kit/IntFmtSum.lean`, `TolInt.lean`, `PrintRel.lean`, `CallOpen.lean`, index files | +8, +3, −1, 0, +10 | — | — | — |
| `scripts/gen_lua_at.py` (`snprintf/p`, `lua_pushfstring/sp`, `luaL_tolstring/fn`, `xres`, `res8`) | +150 | — | — | — |
| `scripts/gen_lua_arms.py` (`helper_edit`, `lua_typename`, `lua_topointer`), `gen_lua_code.py` | +26, +2 | — | — | — |
| **hand total** | **+1,414** | | | |

| generated file | lines (net) | CPU (s) | peak (MB) |
|---|---|---|---|
| `AtF/SnprintfP.lean`, `/Runs.lean` | 2,783 + 326 | 537.9 + 2.0 | 5,895 |
| `AtF/PushfP.lean` | 2,942 | 419.2 | 4,758 |
| `AtF/TolFn.lean` | 1,386 | 398.7 | 4,347 |
| segments/sites (`HluaL_tolstring`, `HluaO_pushvfstring`, `Hsvfprintf_r`, new `Hlua_typename`, `Hlua_topointer`), code pins | +10,888 | — | — |
| **generated total** | **+18,650** | | |

`python3 abstractions/gate.py` passes (`a1-kit-arm`: 69 cases, first 1.9, last 4.1).

## Obstacles

1. **Segment liveness ripple**: new `luaL_tolstring`/`luaO_pushvfstring` paths made `x14` live in shared
   segments; fixed in the specs (`PushfI` `junk`, `tol_lit`'s stop, `snprintf/lld` rows renumbered), never in
   generated output.
2. **`memcpy`'s alignment test** undecided on the walk (`(src ^ dst) & 7`): a residue decision for literals
   and atoms (`xres`, `xor_al`/`xor_mis`); `FmtLib`'s `at_eq` hooks drive `PushfP` past the recursion limit, so
   it imports `AtAlign` instead.
3. **Recursion limits**: `omega` on truncated subtractions inside disjunctions (regions stated additively),
   kernel deep recursion from `simp [BitVec.toNat_ofNat]` on `sp - k + (2^64-1)` (rewrite with `rw`).
4. **Silent OOM** at 16G gives a truncated log that looks clean; every build's exit code is checked.
5. `PrKeep` lacked `G(L)->mt[LUA_TFUNCTION]` (above).
6. Discipline R7 (>8 `∃` in a file): the stage lemmas of `PushfP` are `Triple`s.

## Axioms

`scripts/check.sh` stage 6 adds `snprintfP_sum`, `pf_newlstr`, `pfp_snp`, `pfp_nl`, `pfp_ret`, `pushfP_sum`,
`tf_pre`, `tolfn_sum`, `argStr_int`, `argStr_fn`, `tolPost_of_run`, `tolFn_proved`, `printFn_of_flt`,
`show_ascii` and renames `tolI_in`/`tolI_tab`/`prIntHit`/`prIntNew` to `tolV_in`/`tolV_tab`/`prStrHit`/
`prStrNew`: `[propext, Classical.choice, Quot.sound]`.
