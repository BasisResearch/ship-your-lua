# Lane float-m0: soft-float summaries (M0) and the float-arm pilot (M1)

Base: main `726f75f`. Lines are non-blank, non-comment lines. CPU is the user
time of `lake env lean <file>` (imports built), peak RSS from `/usr/bin/time`;
heartbeats are per declaration with `Elab.async false`, in `maxHeartbeats`
units (limit 200000).

## Result

**The pilot FAILS its cost test** (held-out `FORLOOP`), and the gate cluster
`a1-float-arm` fails (`scripts/check.sh` stage 3c): an abstraction-discovery
round is due. Work stopped there; the proved arms are not yet joined into
`FloatArms`/`armTable`.

| target | status | where |
|---|---|---|
| M0 (a): summaries of `__floatsidf`, `__floatdidf`, `__fixdfdi`, `__eqdf2`, `__ledf2`, `__gedf2`, `__adddf3`, `__subdf3` keyed by entry pc (lifted `F`, frame `Fm`, `sum`) | **proved, generated** | `scripts/gen_lua_fn.py` (484) → `Lua/Vm/Fn/*` (10,359 generated lines; `Adddf3` 134 nodes ~250 s, `Subdf3` 143 nodes ~180 s) |
| `__clzdi2` (a callee of the above) | **proved by hand** (`scan_loop` over 7 byte positions, table lane lemma by 256-case `decide`) | `Lua/Vm/Sim/Kit/Clzdi2.lean` (196) |
| helper segments of the routines | generated | `gen_lua_arms.py` `FLOAT_HELPERS` (+58) |
| M0 (b): `F = S` (`S` the `F64` operation, equal to `Float.Model` by S0a) | **open, none closed**: one named premise `SoftFloatSpec` (8 fields) | `Lua/Vm/Fn/Spec.lean` (64); evidence `Lua/Vm/Fn/SpecTest.lean` |
| call nodes on the at-route (`FCALLS`, per-site `f<k>`/`k<k>`, `@[at_fspec] f<k>_eq`) | generated | `gen_lua_at.py` (+154), `Kit/{At,AtCond,AtFloat,AtFAttr,Fn}.lean` |
| float kit: `FltTest`/`sim_fcond`, `at_fcond`, `at_farith`, float `at_hyp`/`at_new_ext` rules, value bridges | setup | `Kit/AtFlt.lean` (86), `Kit/FltVal.lean` (126) |
| `EQI` on a float: `δ .eq` = `Float.Model.beq` for an 8-bit immediate | **open** `EqiFlt_Statement` | `Kit/FltVal.lean` |

## M1 pilot (cluster `a1-float-arm`)

| arm | role | cases | hand lines | per case | CPU (file) | heartbeats | peak |
|---|---|---|---|---|---|---|---|
| LOADF | train | 1 | 8 | 8.0 | 1.0 s | 4,036 | 2.2 GB |
| LTI (float) | train | 3 | 8 | 2.7 | 1.8 s | 10,710 / 6,133 / 29 | 2.2 GB |
| EQI (float) | train | 3 | 8 | 2.7 | 2.1 s | 12,915 / 8,435 / 30 | 2.2 GB |
| GEI (float) | held out | 3 | 8 | 2.7 | 1.9 s | 10,753 / 6,140 / 29 | 2.2 GB |
| ADDI (float) | held out | 1 | 3 | 3.0 | 1.6 s | 10,325 | 2.2 GB |
| FORLOOP (float) | held out | 1 | 29 | 29.0 | 4.4 s | 56,746 | 2.3 GB |

Int arms on the same route (`a1-kit-arm`): 2.1 (first quarter) – 2.9 (last
quarter) lines per case. Held out: GEI 1.0×, ADDI 1.0–1.4× (after a new kit
hand-off, `at_farith`, 20 lines), **FORLOOP 10–14×**; held-out mean 8.0
lines/case = 2.8–3.8×, above the 1.5× bound. Gate: `a1-float-arm` 12 cases,
first quarter 2.7, last quarter 13.3: FAIL.

Where FORLOOP's 29 lines go (the candidate abstraction): the kernel's
three-register float read (`kit_reg` ×3, the non-float cases refuted by
`cases v0 <;> cases v1`), the `jumpTo` back-jump (`hbx`, the target), the
three payload models and tags bundled for the closers (`hta`, `hxm`), the
step's sign and the bound's answer as the closers' `e`, and `luai_numadd`'s
operand order (`model_add_comm`: lvm.c computes `idx + step`, the ELF
`__adddf3(step, idx)`). The comparison and conditional-jump arms share none
of this; a kernel-shape hand-off for `forloopK`'s float body (or a generic
"read `n` float registers of a kernel" step) would be the bake-off's subject.

Kit changes forced by held-out arms: `at_dec_closed` (a guard of the other
exit left open over payloads must not `decide`), and `at_run` rejecting a
candidate whose closer hits the recursion limit (`tryCatchRuntimeEx`; a
fallback `at_hyp` rule unfolded a soft-float summary).

## Tests

* `Lua/Vm/Fn/SpecTest.lean` (`lake env lean`, 1.3 s): each routine's `F`
  against its `S` by evaluation on 2,900 operand pairs (30×30 edges: zeros,
  subnormal/normal boundaries, ±1, ties, 2^53, ±2^63, max finite, ∞, NaNs
  with payload and sign; 2,000 pseudo-random) and 330 + 600 single operands:
  **0 disagreements** for `__eqdf2`, `__ledf2`, `__gedf2`, `__fixdfdi`,
  `__floatsidf`, `__floatdidf`, `__adddf3`, `__subdf3`.
* It caught a false premise: `__floatsidf` tests all of `a0` for zero, so a
  zero low word under a nonzero upper word gives `0.5`, not `0.0`. The field
  `SoftFloatSpec.floatsidf` now assumes a canonical (sign-extended) argument,
  which every call site supplies (`at_sext`, `sext32_canon`: the argument is
  an `addw`).
* The arms' kernels are `forloopK`/`opArith`/`docondjump` of lane float-s1,
  validated end to end against the ELF on Sail there (`run_sem.sh`).

## Builds

`lake build Lua Vsa VsaIris`: OK, 224 s wall, 1,723 s CPU, 3.8 GB peak.
Axioms of the 9 summaries and 6 float arms: {propext, Classical.choice,
Quot.sound} (added to check.sh stage 6). `scripts/check.sh --static-only`:
stages 1–3b OK (`gen_lua_fn.py --check` added to stage 1), 3c FAIL
(`a1-float-arm`, the intended stop signal).
