# Lane F1-21: POW and POWK on the join route

The base is main `4472fc3`. The route is CLAUDE.md's float-arm row (round 5's
A-JOIN) with lanes F1-F6/F1-F7's shape macros and call nodes.

The numbers are taken as in lanes F2–F7:

- **Hand lines** are non-blank, non-comment lines, without `import`, `open`,
  `namespace` and `end`. **Generated** is `wc -l`.
- **CPU** is the user time of one `lake env lean <file>` with its imports
  built (`LEAN_NUM_THREADS=4`). **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k,
  100k or 150k under which the file builds. The limit is never raised; the
  default is 200k.

## Result

| target | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| libm `pow` as an arm call node | **proved** (level (b) given the premise) | `PowQ.spec`, `PowQ.sum`, `wrap_bits`, `notSNaN_toBits`, `powModel_of` (`Lua/Vm/Fn/PowQ.lean`); `at_sIp` (`Kit/AtPow.lean`) | 66 + 4 | — | 1.3 s + 0.9 s | 2.77 GB | ≤ 50k |
| POW | **proved on quiet operands** | `At.sim_POW : Ieee754PowSpec_Statement → SimArmOnM .POW PowQuiet` (`Kit/AtFltPow.lean`) | 1 | `At/Pow` 1649, `Segs/XPOW` 2070, `Sites/SXPOW` 2095 | 12.6 s (at-file 224.3 s) | 3.33 GB (at-file 4.76 GB) | ≤ 100k (at-file ≤ 50k) |
| POWK | **proved on quiet operands** | `At.sim_POWK : Ieee754PowSpec_Statement → SimArmOnM .POWK PowKQuiet` (`Kit/AtFltPowk.lean`) | 1 | `At/Powk` 1658, `Segs/XPOWK` 2190, `Sites/SXPOWK` 2167 | 12.1 s (at-file 255.3 s) | 3.29 GB (at-file 4.79 GB) | ≤ 100k (at-file ≤ 50k) |

`FloatArms` gains `pow_spec : PowR.Ieee754PowSpec_Statement`; `POW` and `POWK`
are narrowed to `SimArmOnM o (¬ PowQuiet)` / `(¬ PowKQuiet)`: the states with a
signalling-NaN float operand. **These two fields are false as stated** (the
obstruction below). `armTable` joins them by `SimArmOnM.split`.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`
(`notSNaN_toBits`: `[propext, Quot.sound]`). They are in check.sh stage 6.

## Setup

| file | hand lines | what |
|---|---|---|
| `scripts/gen_lua_arms.py` | +22 python | POW, POWK in `EXTRA_ARMS`; `STANDALONE`: their segment modules stay out of the index `Lua/Vm/Arms.lean` (imported by their at-files), so no other at-file rebuilds; `pow` in `FLOAT_CALLS`, `FLOAT_CALL_KEEP` (`s6`, `s10` live into the call, as `fmod`). No existing segment changes. |
| `scripts/gen_lua_at.py` | +44 python | `OP_POW`, `OP_POWK` in `FLOAT_ARMS`; `PowQ` in `FCALL_ARM`, `FRAME_G` (all thirteen registers), `FRAME_FN`, `FARGS`, `FSP`, `FOUTER` (`errno`); `FRAME_F` (a call node whose value reads the frame too); `FSPEC_HYP` (a conditional `f<k>_eq`: the premise binder, the operands' guard, its proof) |
| `Lua/Vm/Fn/PowR.lean` | +12 | `Ieee754PowSpec_Statement` restated in bits (the canonical datum); its old model form is `Ieee754PowModel`, `PowR.model`'s premise |
| `Kit/AtJoinPow.lean` | 121 | `SimArmOnM` (a path family over the machine's memory), `SimArmOnM.split`, `sim_arm_onEM`, `armBodyE_cls3`; `QuietAt`, `QuietOps`, `PowQuiet`, `PowKQuiet`; `rod_two`, `toModel_two` (`at_atom_simp`); `pow_q1`/`pow_disch` (the guard's discharger), the stored-float rule; `at_jpow1`, `at_jpowK1`; `pow_arm`, `powk_arm` (one declaration per class of `R[B]`) |

## How

1. **The call node.** `luai_numpow` is `__eqdf2(b, 2.0)` (the `.rodata` word
   `0x8005c468`, a cell the leaf reads by `rod_two`), then `__muldf3(a, a)` or
   `pow(a, b)`. `pow`'s level (a) `Pow.sum` is the summary (`PowQ.sum`); its
   value `Pow.F m s r g x y` reads the caller's frame, so `f<k>` takes the
   row's frame (`FRAME_F`). Its frame and `errno` are `fmod`'s pattern.
2. **A conditional level (b).** `PowQ.spec : Ieee754PowSpec_Statement → FnSp s
   320 → RodataRead m → Q x y → F m s r g x y = (Lua.Num.pow ⟦x⟧ ⟦y⟧).toBits`,
   from `n_wrap` and `wrap_bits` (a value that is `z` or `1.0`, both
   canonical, with the right model). The generated `f<k>_eq` takes the
   premise and the guard (`FSPEC_HYP`); at the store, `pow_disch` discharges
   them: the premise by `assumption`, the guard by `notSNaN_ofInt` (an integer
   operand through `__floatdidf`) or by the arm's `hQo : QuietOps …` and the
   operand's tag fact.
3. **The premise in bits.** The model form (lane float-sf6's statement) does
   not fix a NaN result's sign bit, which `ValRepr.flt` stores (`Value.ofFloat`
   has the canonical NaN's, `false`). The restated premise says the result is
   the canonical datum. Evidence: `Lua/Vm/Fn/PowTest.lean` now checks the bits
   exactly on its 16,900 pairs, for `__ieee754_pow` and for `pow`: `[]`, `[]`.
4. **The arms.** `at_jarithA`'s views; the kernel's `numpow` left in `hk`
   (`at_jmod`'s pattern), so the leaf splits `beq b two` and refutes the side
   the `__eqdf2` fork contradicts. One declaration per class of `R[B]`: the
   whole arm in one declaration exceeds 200k heartbeats (a single pow leaf's
   close took over 800k before the guard's discharger was fixed; afterwards
   each class is ≤ 100k).

## Obstruction: `NotSNaN` is not dischargeable from the relation

- **The relation's clause.** `ValRepr.flt` (`Lua/Vm/Sim/Rel.lean`, `inductive
  ValRepr`) is `ValRepr mo ι vNumFlt x (.flt (Float.Model.ofBits x) x.msb)` for
  **every** `x : BitVec 64`, a signalling NaN included. `Core.stack` relates
  registers and `Core.kconst` relates constants by it.
- **Where the arm is false.** On the ELF, `pow(sNaN, ±0)` and `pow(1, sNaN)`
  are the NaN `0x7ff8000000000000`; the kernel's `Lua.Num.numpow` gives `1.0`
  (`Float.Model` canonicalises the payload, so the model's operand is the
  quiet NaN, and `pow(NaN, 0) = 1`). `PowTest.lean`'s check over
  `(0x7ff0000000000001, ±0)`, `(0xfff4000000000000, 0)`,
  `(1.0, 0x7ff0000000000001)` prints `true`: `Pow.F = qnan` and the model `1.0`.
  So `SimArm .POW` is false on a related state with `R[B]` such a payload and
  `R[C] = 0`, and `FloatArms.POW` was unsatisfiable before this lane too.
- **A program.** No `luac`-compiled source produces one (constant folding never
  yields a NaN, `l_str2d` rejects `nan`, soft-fp NaNs are canonical). A binary
  chunk does: `main.c` loads the embedded chunk with `luaL_loadbufferx(…, "b")`,
  and `lundump.c`'s `loadNumber` copies a float constant's 8 bytes. A chunk
  for `local a = 0.5; local b = 0; return a ^ b` (`LOADK`, `LOADI`, `POW`) with
  the constant's bytes patched to `01 00 00 00 00 00 f0 7f` is `Supported`, the
  relation admits its `K[0]`, and the machine stores a NaN where the kernel
  stores `1.0`.
- **What would close it.** The relation keeps float payloads quiet
  (`ValRepr.flt` with `NotSNaN x`; every stored float is a canonical datum,
  quiet by `PowQ.notSNaN_toBits`, `UNM`'s sign flip keeps quietness, constants
  checked by the boot witness). That changes the relation every arm reads; it
  was not done here (no weakening, and outside this lane).

## Open

- `PowR.Ieee754PowSpec_Statement` (`pow_spec`): `__ieee754_pow`'s level (b).
- `FloatArms.POW`, `FloatArms.POWK`: the signalling-NaN states (false as
  stated; above).

## Builds

- **Module builds.** `Lua.Vm.Fn.PowR`, `Lua.Vm.Fn.PowQ`, `Lua.Vm.Arms.Segs.XPOW(K)`,
  `Lua.Vm.At.Pow`, `Lua.Vm.At.Powk`, `Lua.Vm.Sim.Kit.AtPow`,
  `Lua.Vm.Sim.Kit.AtJoinPow`, `Lua.Vm.Sim.Kit.AtFltPow`,
  `Lua.Vm.Sim.Kit.AtFltPowk`, `Lua.Vm.Sim.Kit`, `Lua.Vm.Sim.Fold` build with exit 0.
- **Gate.** `python3 abstractions/gate.py` is ok: `a1-float-arm` 71 cases
  (first 2.5, last 1.9).
- **Obstacles met.**
  - A first version put the new segment modules in the index
    `Lua/Vm/Arms.lean`, which made every at-file stale; `STANDALONE` keeps the
    index byte-identical.
  - The guard's discharger first went through the anonymous constructor on a
    `def` and through `simp only` without `hX` for `__floatdidf`'s `f<k>_eq`;
    each failed discharge fell back to `simp_all` and timed out. `Q.mk`,
    `QuietOps.l/r` and `simp (disch := assumption)` fixed it.
