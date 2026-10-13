# Lane float-sf3: libm `floor` and `__muldf3` on the `SfRef` route

The base is main `c658715`; the branch was rebased onto it from `f4f03b5`.

Two routines are proved at both levels:

- **libm `floor`** discharges the named premise `FloorSpec`, as
  `Lua.Vm.Sim.floorSpec_proved`.
- **`__muldf3`** is proved as `Lua.Vm.Fn.Muldf3.spec_proved : F m s r a b = F64.mul a b`.
  It is in `gen_lua_at.py`'s `FPROVED`.

`__divdf3` stays open. The obstructions are listed below.

## What is proved

| routine | level (a): the summary | (b2): reference = specification | (b1): lifted `F` = reference | result |
|---|---|---|---|---|
| libm `floor` (`s_floor.c`) | `FloorFn.sum`: 31 nodes, with `__adddf3`/`__gedf2` as call nodes | `SfRef.floor_cls`, then `SfRef.floor_model` (= `Lua.Num.floor`) | `FloorFn.F_eq_ref`: 104 per-exponent chambers and 6 range chambers | `floorSpec_proved : FloorSpec` |
| `__muldf3` (`_FP_MUL`) | `Muldf3.sum`: 76 nodes, with `__muldi3`/`__clzdi2` as call nodes | `SfRef.mul_eq` (= `F64.mul`) | `Muldf3.F_eq_ref`: 5 stage lemmas and 25 class-pair chambers | `Muldf3.spec_proved` |

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` stage 6 lists them:

- `FloorFn.sum`, `FloorFn.F_eq_ref`, `SfRef.floor_cls`, `SfRef.floor_model`,
  `floorSpec_proved`;
- `muldi3_sumK`, `Muldf3.sum`, `SfRef.mul_eq`, `Muldf3.F_eq_ref`,
  `Muldf3.spec_proved`.

There are no `sorry`, `axiom`, `native_decide` or `bv_decide`, and no raised
limits. `scripts/check.sh` passes all stages, with the full build under 30G
and `LEAN_NUM_THREADS=4`.

## Abstractions built

- **Call nodes to proved summaries.** `scripts/gen_lua_fn.py` (`Callee`,
  `CALLEES`) and `Kit/FnCall.lean` provide these.
  - A framed callee's `s` is put in front of the pins with `SegSt.pin_sp`,
    and its patch is absorbed by `memPatch_patch_in`.
  - Kept caller-saved registers come from `Callee.keeps`.
  - A dead kept register is pinned with `pin_gpr`.
- **Frame-slot forwarding (`FORWARD`).**
  - A spill slot that is stored on every path becomes a node parameter
    `vs<off>` with the fact `hs<off>`.
  - Lifted functions after a call read no memory.
  - The syntactic closers `fn_rod_patch`/`fn_ra_patch` avoid unifying slot
    addresses.
- **gcc `-fipa-ra`.** `__muldf3` keeps a4–a7, t1, t3 and t4 across
  `__muldi3`.
  - `gen_lua_arms.py` `PASS_THROUGH` makes `__muldi3`'s segments carry these
    registers only where a caller needs them, so no other caller's segments
    change.
  - The summary carrying them is `muldi3_sumK` (`TFrame`).
  - `muldi3_sum`, with an unchanged statement, is its instance.
- **One-operand chamber generator.** `fl_chambers lo hi` and `fl_cover lo hi`
  live in `Lua/Vm/Fn/SfRefFloor.lean`.
  - They emit one chamber per exponent and sign, the range chambers, a
    balanced cover, and `F_eq_ref`.
  - Rule R18 rejects hand-written chambers.
- **Class-pair chamber generator.** `smc_chambers` in
  `Lua/Vm/Fn/SfRefMul.lean` emits 25 chambers, `G_eq` and `F_eq_ref`.
  - The closers are `smc_spec` (a special operand) and `smc_fin` (through the
    product stage).
  - Rule R18 covers this file too.
- **Mul lens.**
  - Exponent words `ew` are opaque, so `BitVec.ofInt` is never unfolded by
    unification.
  - `umul_ppmm` is handled by `nf_mul_lt`, `nf_lo64` and `umul_eq`.
  - `_FP_FRAC_SRS_2` is handled by `nf_umul_srs`.
  - The canonical pack is covered by `g_e8ec`, `g_e660` and `g_e7a4`, which
    equal `SfRef.packCanon`.
- **(b2) for mul** is `packCanon_eq` and `mulNorm_eq`. They need only the
  existing round laws: `roundPack_eq`, `round_rto` (W1, at most three times)
  and `round_scale`.

## Numbers

- **Lines** count non-blank, non-comment lines.
- **CPU** is user seconds of one `lake env lean <file>` with its imports
  built. Lean's default thread count was used, so CPU is greater than wall
  time.
- **Peak** is maximum resident memory.

| file | lines | CPU (user s) | wall | peak |
|---|---|---|---|---|
| `Lua/Num/SfRefFloor.lean` (b2) | 178 | 1.2 | 0:01 | 0.81 GB |
| `Lua/Vm/Fn/SfRefFloor.lean` (lens, tactics, generator) | 635 | 7.2 | 0:05 | 2.45 GB |
| `Lua/Vm/Fn/SfRefFloor{A,B,C,D}.lean` (104 chambers) | 4 × 9 | 4686 | 4 × ~1:00 | 3.31 GB |
| `Lua/Vm/Fn/SfRefFloorSpec.lean` (cover, model, premise) | 53 | 31 | 0:09 | 2.54 GB |
| `Lua/Num/SfRefMul.lean` (b2) | 158 | 1.2 | 0:01 | 0.81 GB |
| `Lua/Vm/Fn/SfRefMul.lean` (lens, stages, 25 chambers) | 530 | 716 | 0:52 | 3.41 GB |
| `Lua/Vm/Sim/Kit/FnCall.lean`, `Kit/Muldi3.lean` (changed) | 73 + 92 | — | — | — |
| generated `FloorFn`, `Muldf3/{L0,L1}` (level (a)) | 3277 (generated) | 76 / 76 / 116 | — | 2.5 GB |
| **hand-written total** | **1833** | | | |

The `gen_lua_fn.py` diff is +267 lines.

## Tests (differential, against the ELF's lifted function)

| test file | operands | result |
|---|---|---|
| `Lua/Vm/Fn/FloorTest.lean` | 3,058 | machine `FloorFn.F` = `SfRef.floor` = `Lua.Num.floor` = host C `floor`, all `[]` |
| `Lua/Vm/Fn/MulTest.lean` | 7,600 pairs | machine `Muldf3.F` = `SfRef.mul` = `F64.mul` = host `*`, all `[]` |

- **FloorTest** includes a negative control: with `.rodata` absent, the
  machine and the reference differ.
- **MulTest** draws its operands from edges, from boundaries near the
  subnormal and overflow ranges, and from random values.

## Obstructions: `__divdf3`

Level (a) is refused by the generator. To reproduce, register `__divdf3` in
memory; the scratch probe registers it in `HELPERS`/`ROUTINES` and runs
`gen_lua_fn.Fn("__divdf3")`.

1. **The first refusal** is `seg_8002e13c_8002e158: jump out of the helper to
   0x8002f734`. Neither callee has a call-node summary of the right shape:
   - `__udivdi3`'s summary `udivdi3_sum` needs `d ≠ 0`. The generic node
     lemma cannot discharge that, because the divisor `s0 = (Y<<8)>>32` is
     bounded only by the unpack path. Nodes therefore need path facts as
     hypotheses.
   - `__umoddi3` has no summary at all. It is `mv t0,ra; jal __udivdi3;
     mv a0,a1; jr t0`.
2. **With stub callees**, the refusal becomes `seg_8002e178_8002e194: x5 live
   at 0x8002e194 but not carried`. `__umoddi3` clobbers t0 for its return
   address, and call nodes do not model that.
3. **Two class-switch jump tables.** `jr a4` at `0x8002ded4` uses the table at
   `0x80054040` (16 entries). `jr a5` at `0x8002df30` uses the table at
   `0x80054080` (15 entries). `gen_lua_fn.py` treats a segment ending in `jr`
   as a return. It needs a table node that cases on the index and reads the
   `.rodata` entries.
4. **Callee-saved s0–s3 are saved and reassigned mid-body**, at
   `0x8002e118`–`0x8002e24c` (Knuth D's normalised divisor halves and the
   quotient). The generator's `FRAME` model pins s-registers to the caller's
   values.

Level (b) has not been started. It needs `udiv_qrnnd` (the two-step long
division with corrections), the remainder sticky bit and the `__divdf3` W1.
