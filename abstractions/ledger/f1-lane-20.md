# Lane F1-20: `luaL_tolstring` on an integer to the machine level; `TolInt_Statement` found false as stated

Base: main `ab205a6` (lane F1-19). Route: CLAUDE.md's A1 rows: callee-context at-lemmas (`gen_lua_at.py --fn`,
`fat_run`), `seg_loop` for `memcpy`'s and `internshrstr`'s loops, `kit_run` for helper segments without
at-lemmas, call nodes spliced by their summaries. Lines are non-blank, non-comment lines. CPU and peak memory
are one `lake env lean <file>` each (user time, maximum resident set). Heartbeats are per declaration,
bracketed by rerunning the file with `-DmaxHeartbeats` 50000 and 100000. No heartbeat or recursion limit was
raised; every declaration elaborates at the default 200000.

## Result

| target | status | where |
|---|---|---|
| `tolInt : TolInt_Statement` | **not discharged; false as stated** (below). The machine route is proved: `tolint_sum` (`luaL_tolstring(L, i, &l)` on an integer `v`: the digits interned, found or created, `PfStr`, pushed, `PfPost`, their tag and length at the return, `PfTs`, `l` their count) from `MallocR_Statement` and `IntegerToStr_Statement` (both proved) | `Kit/TolInt.lean` |
| `printFn : PrintFn_Statement` | **not attempted**: false as stated for the same reason; `"%s: %p"` needs `gen_lua_at.py` specs (`lua_pushfstring/sp`, `snprintf/p`) | — |
| `CallOpen` | unchanged (`tolInt`, `printFlt`, `printFn`); PHASES records the three as not true as stated | `PHASES.md` |

### Why `TolInt_Statement` is false

`TolArg` quantifies the dirty set `D` with a lower bound only (`PrintIn.dirty`), and `PrSt'`'s literals
(`LitsFoot.apart`) must keep their frozen footprint off `D`. After `internshrstr` links a new string `p` at its
bucket's head, every footprint on which the literals' facts are frozen holds `p + gcTtOff`:
`frozen_lits_head_tt` (`Kit/LitsInsert.lean`, machine-checked: a memory differing only at `p`'s tag byte
starts that bucket's chain at a node of the wrong tag, so no table reading satisfies `LitsIn`). Take `D` the
complement of the entry's footprint: `PrintIn` and `PrSt` hold, `p` is fresh (not in `Kept`, so not in the
entry's footprint), so no `PrSt' (i + 1)` exists after a created string, which every integer not interned
yet creates. The same argument applies to `PrintFlt_Statement` and `PrintFn_Statement`.

Fix (next lane): an upper bound on `D` in `PrintIn` (fresh blocks, the bucket array, `g`'s table header
`[g + 48, g + 64)` and current white off `D`), met by `call_printIn`'s `CallD w nci`; then the glue from
`tolint_sum` to `TolPost` (`NlTab` from `PrSt.safe` and `LitsIn.off` by `kwalk_of`, the heap by
`StdoutIn.congrA`, `PrSt' (i + 1)` by `frozen_insert`, `LitsIn.insert`, `StrtSafe.insert`).

## The proofs (per part)

| part | hand lines | generated lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|---|
| `StrtOff` (`LitsIn.off`: the table's words apart from what the literals' facts read, no string but a literal dead, the bucket array 8-aligned) | `EntryData.lean` 45, `Boot/Check.lean` 80 (`strtOffCheck_sound`) | boot witnesses (regenerated) | — | — | — |
| `memcpy_sum` (`Kit/Memcpy.lean`) | 233 | `AtF/Memcpy` 654 | 9.1 | 2,093 | 50k–100k (5 over 50k) |
| `ia_walk_sum` (`Kit/InternAny.lean`: hash loop, bucket, chain walk with `memcmp`, `kwalk_of`) | 485 | `AtF/InternAny` 992 | 16.3 | 2,494 | 50k–100k (8 over 50k) |
| `ia_new`, `ia_new_mem`, `lalloc_sumN` (`Kit/InternNew.lean`: the creation path) | 428 | (in `AtF/InternAny`) | 25.9 | 3,632 | 100k–200k (2 over 100k: `ia_new`, `ia_new_mem`) |
| `newlstr_any_sum`, `IaNewIn.congr`, `IaNewPost.ofM0` (`Kit/Newlstr.lean`) | 118 | — | 1.2 | 3,126 | < 50k |
| `LitsIn.insert`, `StrtSafe.insert`, `frozen_insert`, `frozen_lits_head_tt` (`Kit/LitsInsert.lean`) | 829 | — | 3.9 | 2,346 | < 50k |
| `pushfI_sum` (`Kit/PushfI.lean`: `pf_cut`, `pf_snp`, `pf_nl_reach`, `pf_nl`, `pf_ret`, `PfSlots`, `pfTs_of`) | 891 | `AtF/PushfI` 1,909 | 23.8 | 3,908 | 50k–100k (2 over 50k) |
| `tolint_sum` (`Kit/TolInt.lean`: `ti_pre`, `PfStr.trans`, `NlTab.congr`) | 286 | `AtF/TolInt` 1,215 | 9.0 | 3,728 | 50k–100k (2 over 50k) |
| `Kit/Sext32.lean`, `Kit/AtNarrow.lean` (32-bit count hooks) | 110 | — | < 2 | — | < 50k |
| helper segments and code pins (`HELPERS`: `lua_isinteger`, `lua_tointegerx`, `lua_pushfstring`, `luaO_pushvfstring`, `addstr2buff`, `addnum2buff`, `strchr`, `memcpy`, `luaC_newobj`) | — | `Arms/{Segs,Sites}` 28,296, `Code` 13,242 | — | — | — |

`python3 abstractions/gate.py` passes (`a1-kit-arm`: 69 cases, first 1.9, last 4.1).

## Abstractions added (generator and kit)

* `gen_lua_at.py`: `cuts` (a long path cut into a fresh root: the path's log becomes the root memory, the
  stack words carried as facts), `prune_nat` (an outcome the path's own `Nat` facts refute dropped: the same
  bound tested by `lua_type` and `lua_tointegerx`), root contexts after a call (`calls[..]["root"]`), narrow
  reloads of counts and a narrow load inside a wider literal store.
* `Kit/AtNarrow.lean`: `at_eq` hooks for 32-bit counts (`sw`/`lw`, `addiw`, a word inside a stored zero
  doubleword, `fw4_in8_zero`), guarded so no rewrite is tried against another `sign_extend`.
* `FmtLib`'s `fat_hyp` rule fires only on signed tests (`fmt_scmp_goal`); on a stack word's fact it ran past the
  recursion limit, an exception no `first` catches.
* `PfSlots` (a caller's frame words, one transport per callee), `PfStr` (found or created, over a frame region
  `F`, rebased by `PfStr.trans`), `IaNewPost` over a frame region (`.trans`, `.mono`), `node_off_X` (a found
  node's header bytes apart from an object of `X` by its mark and `u.hnext`).

## Obstacles

1. **`omega` on nested truncated subtractions of large constants** (`sp - 48 - 8192 ≤ a ⊢ sp - 8240 ≤ a`)
   runs past the recursion limit, in core Lean too; the frame regions are stated additively (`PfFr`, `TolFr`).
2. **`fat_hyp`'s fallbacks** (`fat_rd`'s one `simp` over a long store chain; the `fmt_scmp` rule) raise
   recursion errors `first` does not catch. Facts are stated in the context's form so `assumption` closes them;
   a guard whose other outcome would reach the fallbacks is case-split and its at-lemma applied by name.
3. **A count inside an atom list** (`(intBytes i).length` in `pfX`'s `Nat` atoms) made `simp` evaluate it; the
   count is an opaque `n` with `hn : (intBytes i).length = n`.
4. **The heartbeat budget is per declaration**: `ia_new`'s memory facts moved to `ia_new_mem`.
5. `TolInt_Statement` false as stated (above).
6. Other lanes' files touched: `Kit/FmtLib.lean` (`fmt_sext32_ofNat`, `extract_ofNat`, `fmt_pin` moved to
   `Kit/Sext32.lean`, re-exported; the `fat_hyp` rule guarded), `EntryData.lean`/`Boot/Check.lean`/`Sim/Entry.lean`
   (`StrtOff`), `gen_lua_boot_witness.py`, `gen_lua_arms.py`, `gen_lua_code.py`, `gen_lua_at.py` — additive.

## Axioms

`scripts/check.sh` stage 6 lists `memcpy_sum`, `ia_walk_sum`, `ia_new`, `ia_new_mem`, `newlstr_any_sum`,
`IaNewPost.trans`, `PfStr.trans`, `pushfI_sum`, `tolint_sum`, `LitsIn.insert`, `StrtSafe.insert`,
`frozen_insert`, `frozen_lits_head_tt`, `node_off_X`, `intBytes_len`, `pfTs_of`, `strtOffCheck_sound`:
`[propext, Classical.choice, Quot.sound]`.
