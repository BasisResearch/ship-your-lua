# Round-3 bake-off base: `VmRel` made sound for MOD/IDIV/EQ

The bake-off starts from this commit. It proves no new arm. The six target
statements now have fixed forms, and `VmRel` no longer makes them false.

## Route: Scratch, folded into `Win`

We chose the *Scratch* route over *Re-witness*.

- **Re-witness** would close each arm with `w' := {w with mo := …}`. Every
  field of `Complement` would then have to be re-proved against the new
  `mo`. That includes `ProtoRepr`, `HeapAt`, `StrtAt`, `ErrorJmpAt`,
  `kconst`, and each register's `ValRepr` (strings read their bytes from
  `mo`). A `Complement.rebase` lemma would need a footprint for each of
  these predicates, and no such footprint exists today.
- **Scratch** leaves `w.mo` fixed as the entry memory. It adds one fixed set
  and costs only address arithmetic.

`Scratch w` (`Lua/Vm/Sim/Rel.lean`) is the union of three regions:
- `ci->u.l.savedpc`, the 8 bytes at `ci + 32`: case (a);
- `L->top`, the 8 bytes at `L + 16`: case (b);
- the callee frames `[spEntry - cStackBudget, sp)`: case (c).

The budget comes from the existing bound `cstack_room : symHeapEnd +
cStackBudget ≤ spEntry`, so this region lies above every heap object.

`Scratch` is a disjunct of `Win`, not a separate exemption in `Core.frame`.
As a result, `Core.frame`, `Core.fetch`, `Core.kconst`, `Core.frame_of`,
`Core.write`, `Core.update`, `Core.forloop`, `dispatch` and all 25 generated
arms stay textually unchanged. `Ranges.code_out` and `Ranges.k_out` keep
their form but now also say that the code and constant arrays miss the
scratch words. `Ranges.ci_out` becomes `ci_out` minus the `savedpc` word, and
its two users (`Core.trap`, `trap_of_frame`) each gain one `omega` argument.
`Ranges` gains `L_lo`, which `Win.above` needs.

**`L->top`.** No fetch head reads it. The `lvm.c` `vmfetch` assert says so,
and `CALL print` with C = 1 leaves it at `ra`. The pin `LuaStateAt.top` is
removed. It becomes `RuntimeReadyAt.top`, an entry-only fact that
`OP_VARARGPREP` → `luaT_adjustvarargs` reads at pc 0. Nothing read the old
field (grep), so no proof changed.

## ValRepr tightening

`ValRepr` now takes an intern map `ι : List UInt8 → Nat`, carried in
`RelPtrs.ι`.

- `nil` is exactly `BitVec.ofNat 8 vNil`. Registers are nil only through
  `setnilvalue`: `luaV_finishget` turns an absent or empty key into
  `LUA_VNIL`.
- `str`: the tag is `strTag s`, which is `vShrStr` iff `len ≤ 40`
  (`Lua/Vm/Repr.lean`). `TStringRepr mo x s` holds, and
  `len ≤ 40 → x = ι s`. `TValueRepr.str` is tightened to the same tag,
  because the entry hypothesis must supply it.
- `TStringRepr.inj`: a pointer holds one content. With `ι`, short-string
  pointer equality is therefore content equality in both directions.
- `Close.lean`'s tag lemmas are re-proved over `strTag_cases`.
  `isFalse_of_ne` and the nil lemmas are simpler, because nil's tag is now a
  literal.

## New obligations

All of these go into the existing boot-witness obligation
(`luaRuntimeReady`, PHASES A0.6). `gen_lua_boot_witness.py --check`
evaluates each one natively at both traced entries (`while`, `f1_ops`), and
all of them hold. PHASES.md records them.

| field | content |
|---|---|
| `RuntimeReadyAt.top` | `L->top = func + 1` (moved from `LuaStateAt`, not new) |
| `RuntimeReadyAt.interned` (`KInterned`) | two `vShrStr` constants with equal bytes are one pointer (`loadStringN` → `luaS_newlstr` interns them) |
| `VmRegionsAt.{L_sep_ci, code_sep_L, code_sep_ci, k_sep_L, k_sep_ci}` | `L`, `ci`, the code array and the constant array are pairwise disjoint `l_alloc` blocks |
| `TValueRepr.str` (via `VmEntryData.proto`'s `ConstRepr`) | a constant string's `TValue` tag is `strTag s` (the generator's `k str tag` check is now exact) |

`vmRel_entry` builds `ι` from `KInterned` (`exists_intern`,
`ProtoRepr.kArr`). The `Ranges` proof moved into its own lemma,
`Ranges.of_regions`. Without that move, the added separation facts pushed
the monolithic `vmRel_entry` over the default heartbeat budget. The limit
was not raised.

## Target statements (`Lua/Vm/Sim/Rel.lean`)

`SimArm o` is `sim_ADD`'s statement for opcode `o`. A scratch file checked
`example : SimArm .ADD := … sim_ADD …` and the same for `.EQI`.

- `sim_MOD_Statement := SimArm .MOD` (arm `0x8001dc58`).
- `sim_MODK_Statement`, `sim_IDIV_Statement`, `sim_IDIVK_Statement`.
- `sim_EQ_Statement := SimArm .EQ` (arm `0x8001c690`).
- `sim_EQK_Statement`.

The docstrings argue plausibility instruction by instruction:
- the `savestate` stores hit `Scratch`;
- `__moddi3` and `luaV_equalobj` write only below `sp`;
- `ttypetag`, then the payload, pointer or `memcmp`, decides `δ .eq` under
  the tightened `ValRepr`;
- `n % 0` is the error `imod` leaves without a `Step`.

Still out of scope, as noted in ROUND-3 §3:
- `LuaStateAt.next = 0` breaks at the first CALL;
- the soft-int region specs.

## Numbers

- **Hand lines** (`git diff --numstat`, added/removed, docstrings included):
  - `Lua/Vm/Sim/Rel.lean` +172/−21. Most of this is the six statements'
    docstrings, `Scratch`, and `TStringRepr.inj` (20 lines).
  - `Lua/Vm/Sim/Entry.lean` +103/−45: `exists_intern`, `kArr` with `ι`, and
    `Ranges.of_regions`, which replaces the 16 inline `?_` goals.
  - `Lua/Vm/Sim/Close.lean` +26/−24.
  - `Lua/Vm/Runtime.lean` +32/−3.
  - `Lua/Vm/Repr.lean` +8/−2.
  - `scripts/gen_lua_boot_witness.py` +18/−1.
  - `scripts/check.sh` +5/−1 (4 new axiom reports).
  - Lean total: +341/−95.
- **Regenerated lines: 0.** `gen_lua_arms.py --check` and
  `gen_lua_arm.py --check` show no drift. No generated arm names `Win`,
  `ci_out` or a `ValRepr` constructor whose shape changed.
- **Build CPU** (`lake env lean`, user seconds, one core):

  | module | user s |
  |---|---|
  | `Repr` | 0.50 |
  | `Runtime` | 0.94 |
  | `Rel` | 1.40 |
  | `Close` | 6.79 |
  | `Entry` | 14.96 |

  The full downstream rebuild, `lake build Lua` (682 jobs, 25 arms and the
  Boot data modules), took 1384 s user CPU and 70 s wall; peak RSS was
  3.1 GB.
- **Gate:** `scripts/check.sh` passes every stage except 3c (the
  `a1-arm-sim` gate, red as expected). Stage 6 reports 131 axiom lines, all
  ⊆ {propext, Classical.choice, Quot.sound}.
