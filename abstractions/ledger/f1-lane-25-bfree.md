# F1-25 bignum primitive: newlib `_Bfree`

Base: `11fdb6d`, worker branch `codex-os`, assigned worktree `sol-2`.
The F1-25 ledger, `Kit/BigHeap.lean`, and `abstractions/DEAD-ENDS.md` were
consulted in the main workspace because this worktree predates them.

## Result

`Kit/Bfree.lean` proves `bfree_sum` at `0x8003d700` (nine instructions).
The input and post are named-field structures, `BfreeIn`/`BfreePushIn` and
`BfreePost`.

- NULL: the generated branch and return; no memory/pointer premise, memory
  unchanged.
- Non-NULL: read the signed class at `b + 8`, the freelist pointer at
  `reent + reentFreelistOff` (104), and the old head at `fl + 8*k`; write
  the old head at `b`, then `b` at the slot. `bfreeMem` exposes this exact
  memory, in instruction order. `bfreeMem_push` proves both links.
- Return: PC is the caller's aligned `ra`; `ra`, `sp`, `gp`, `s0`–`s11`
  and the console are preserved. `BfreePost.keep` is equality of optional
  bytes outside the two eight-byte writes, preserving presence as well as
  values. There is no allocator call and no claim that an allocating
  operation leaves the heap unchanged.
- `BigChain.congr` (beside its model in `EntryData.lean`),
  `bfree_rdLE_keep`, and `bfree_chain` prove the chain
  update for an apart owned block (`BfreeOwned`), preserving the class and
  capacity of every old node.

## Abstractions and generation

The first action was `scripts/abs_inventory.sh`. This reuses the
callee-context route: `gen_lua_at.py --fn _Bfree/null,_Bfree`, `FCx`,
`fat_seg`/`fat_close`, generated `runs`, and `fcx_ok`/`pins_of` for the
summary. The signed class load and scaled address are separate generated
segments so existing `AtNarrow` and `fat_shl` close them. No per-site proof,
pin normalizer, generated-file edit, or increased Lean budget is used.

`gen_lua_code.py` has a standalone pin list, and `gen_lua_arms.py` has
`STANDALONE_HELPERS` and a targeted `--helper` regeneration/check option.
Regeneration writes only changed content, preserving existing file timestamps.
The new pins, sites, segments, and AtF files are standalone imports.
`Lua/Vm/Code.lean`, `Lua/Vm/Arms.lean`, and `arms.tsv` are unchanged, as are
all pre-existing generated files and other generators.

Other reused names: `rdLE_congr`, `AllocHeap.rd64_eq`,
`read64_writeMap8`, `sdData_toNat`, `getElem?_writeMap8_out`,
`fw8_wm8`, `bytesT8_writeMap8`, and `sdData_id`.

## Exact premises and remaining work

`bfree_sum` has no whole-function premise. Its input requires `sp ≤ 2^32`
and aligned return PC. On the non-NULL branch it additionally requires:

- eight-aligned `reent`, `b`, and `fl`, in RAM above `tohost`;
  `reent + 112`, `b + 16`, and `fl + 520` bounded by `2^32`;
- `k ≤ 64`, and the block header apart from the 65-pointer array;
- the three actual loaded values (class, freelist pointer, old head).

`bfree_chain` additionally requires the block's present class/capacity
words and that every old chain block is apart from both the owned block
and the array (`BfreeOwned`), plus the old `BigChain`.

The full `ReentMp`/`BigRun` update is not claimed. In particular,
`ReentMpAt.p5v` uses `bigVal`, whose reads follow `_wds`, whereas the
current `BigChain` only bounds `_k` and pins `_maxwds`. A cache-node bound
`_wds ≤ 2^_k` would put those digit reads within the owned block; it is
not a field of the current invariant. Transporting the cache values and
the complete list-array ownership remains to be proved. That lift must
also put the returned block in `B` and apart from every current
`bigBlocks` entry, including `_result` and `_p5s`; `bfree_chain` only
needs separation from its target chain and the array. The main
workspace's pending `Kit/BigHeap.lean` is left intact.

`FloatToStr_Statement` remains open: this is its first bignum primitive.
`_Balloc`, the other `mprec.c` routines, `_dtoa_r`, the `%.14g` formatter,
and the value/length correctness proof remain.

## Validation

All Lean invocations use the main repo's `scripts/lean-capped.sh`, which
checks the worktree lock, at least 25 GB available RAM, inherited 12 GB
scope, and CPU affinity. Builds use this worktree's private `.lake/build`.
No shared dependency cache or unrelated untracked file is changed.

- `lake build Lua.Vm.Sim.Kit.Bfree`: passes, including both generated runs.
- `gen_lua_code.py --check` and `gen_lua_at.py --fn _Bfree/null,_Bfree --check`:
  pass.
- `check_discipline.py` and `abstractions/gate.py`: pass.
- Axiom reports for the pin, both runs, the memory lemmas, `bfree_sum`,
  `BigChain.congr`, and `bfree_chain`: all exactly
  `[propext, Classical.choice, Quot.sound]`. `check.sh` now builds the
  standalone summary and audits those declarations in stage 6.
- `bash scripts/check.sh --static-only`: passes all generator drift checks,
  ELF/hash checks, forbidden-token scan, discipline, abstraction gate, and
  copied-layer checks (`WHILE` roots in the closure: none).
- Python generator syntax, `bash -n scripts/check.sh`, and
  `git diff --check`: pass.
- The handoff patch applies to copies of base `11fdb6d` outside Git and
  reproduces the hashes of all 17 changed files.

The manager performs the full repository build and landing through
`scripts/check.sh`.
