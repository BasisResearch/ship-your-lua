# Lane F1-22: float payloads quiet in the relation (closing `FloatArms.POW`/`POWK`)

The base is main `cf252a1`. Lane F1-21 found `FloatArms.POW`/`POWK` false as
stated: `ValRepr.flt` admitted every payload, signalling NaNs included, and
on one the ELF's `pow` and the kernel's `numpow` differ.

The numbers are taken as in lanes F2–F1-21:

- **Hand lines** are changed lines that are not blank, not `--`/`/-` comment
  openers, and not `import`/`open`/`namespace`/`end` (doc-comment
  continuation lines are counted).
- **CPU** is the user time of one `lake env lean <file>` with its imports
  built (`LEAN_NUM_THREADS=4`). **Peak** is that run's maximum RSS.

## Result

| target | status | theorem (file) |
|---|---|---|
| quiet payloads in the relation | **proved** | `ValRepr.flt : isSNaN x = false → …` (`Lua/Vm/Sim/Rel.lean`); `isSNaN_fields`, `isSNaN_eq_false_iff`, `isSNaN_congr`, `isSNaN_xor_sign`, `isSNaN_toBits` (`Lua/Vm/Sim/Quiet.lean`); `ValRepr.quiet`, `ValRepr.quiet_of_tag` (`Close.lean`) |
| POW, POWK on every state | **proved** given `pow_spec` | `powQuiet_of`, `powKQuiet_of`, `QuietAt.of_reg`, `QuietAt.of_k`, `SimArmOnM.of_all` (`Kit/AtJoinPow.lean`); `armTable`'s `POW`/`POWK` cases (`Fold.lean`) |

`FloatArms` loses `POW` and `POWK`. Its fields are now `soft` (empty),
`pow_spec : PowR.Ieee754PowSpec_Statement` and
`FORPREP : At.FpStrFlt_Statement`. `SimArmOnM.split` is deleted. It was the
join of a false field. `SimArmOnM` stays: it is the type of `At.sim_POW` and
`At.sim_POWK`.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
They are in check.sh stage 6.

## The construction sites (one lemma per kind)

| kind | where | how quietness is supplied |
|---|---|---|
| a stored model datum (every soft-float result, conversion, `pow`, `fmod`, `floor`, …) | `ValRepr.ofFloat_of` (`Kit/FltVal.lean`), used by every `at_new_ext` store rule | `isSNaN_toBits` inside the lemma; no rule changed |
| a sign flip (`OP_UNM`) | `ValRepr.flt_neg` (`Kit/FltNeg.lean`), its `at_new_ext` rule (`Kit/AtJoinOps.lean`) | `isSNaN_xor_sign`; the operand's quietness by `at_quiet` |
| a copied entry payload (`setfltvalue` of a register's own float: FORPREP, FORLOOP) | `ValRepr.flt_lit` (`Kit/AtJoin.lean`), its `at_new_ext` rule | `at_quiet` (`Kit/FltVal.lean`): the read register's `ValRepr` in context (`ValRepr.quiet`, or `quiet_of_tag` under a tag fact), the payload matched by reducible defeq only |
| a constant | `ConstRepr.valRepr` (`Entry.lean`) | `Const.toValue?` already has no value for an sNaN (`isSNaN`), so the `split`'s hypothesis is the fact |
| a transfer to new memory | `ValRepr.transfer` (`Kit/CallClose.lean`) | the premise is carried |
| MOVE, LOADK, … (old kit arms) | copy a `ValRepr` | unchanged |

**Files touched: 13** (12 Lean files, of which 1 is new, plus `scripts/check.sh`). The docs are
PHASES.md and CLAUDE.md. No generated file and no generator changed. No arm
file and no at-module changed: every arm builds through the hooks above.

| file | hand lines (+/−) | CPU | peak |
|---|---|---|---|
| `Lua/Vm/Sim/Quiet.lean` (new) | +78 | 0.9 s | 0.81 GB |
| `Lua/Vm/Sim/Rel.lean` | +6 / −2 | 1.9 s | 1.85 GB |
| `Lua/Vm/Sim/Close.lean` | +11 | 5.9 s | 1.93 GB |
| `Lua/Vm/Sim/Entry.lean` | +3 / −2 | 20.0 s | 2.88 GB |
| `Lua/Vm/Sim/Kit/FltVal.lean` (`at_quiet`) | +31 / −1 | 1.6 s | 2.59 GB |
| `Lua/Vm/Sim/Kit/FltNeg.lean` | +3 / −2 | 1.0 s | 2.54 GB |
| `Lua/Vm/Sim/Kit/AtJoin.lean` | +7 / −4 | 3.9 s | 2.61 GB |
| `Lua/Vm/Sim/Kit/AtJoinOps.lean` | +1 / −1 | 1.4 s | 2.54 GB |
| `Lua/Vm/Sim/Kit/AtJoinPow.lean` | +48 / −8 | 1.9 s | 3.18 GB |
| `Lua/Vm/Sim/Kit/CallClose.lean` | +1 / −1 | 2.6 s | 2.31 GB |
| `Lua/Vm/Fn/PowQ.lean` (`notSNaN_toBits` from `isSNaN_toBits`) | +2 / −19 | 1.2 s | 2.78 GB |
| `Lua/Vm/Sim/Fold.lean` | +5 / −12 | 5.4 s | 5.18 GB |

For comparison, the heaviest arm that exercises `at_quiet`,
`Kit/AtFltForprepC.lean`, takes 22.4 s and peaks at 2.93 GB. Its source did not change.

## The statement change

`vm_refinement_Statement luaLayout` has the same hypotheses as before.

`ValRepr.flt` gains a premise. `ValRepr` is internal to the relation
`VmRel`. That relation is existential in the fold and is established by
`entrySim`, so the theorem's statement does not mention it.

**Constants.** No boot check and no new entry-contract field are needed.
`Const.toValue?` (`Lua/Bytecode/Semantics.lean`) already maps a float constant
with a signalling-NaN payload to `none`. So `kval p i = some v` (the hypothesis of
`Complement.kconst` and `Core.kconst`) already excludes an sNaN, and a step
through `LOADK`/`K[C]` on one is stuck in the bytecode semantics. Lane F1-21's
note that `Core.kconst` relates an sNaN constant was wrong: the
`ConstRepr.valRepr` split's second branch carries `¬ isSNaN b = true`.

**Coverage.** None of the repository's example programs (`Lua/Programs/*`,
from `c/tests/*.luac`) has a float constant. `luac` cannot produce a signalling NaN
from source: no literal denotes a NaN, and `lcode.c`'s `constfolding` refuses
NaN results. Only a crafted binary chunk can carry one (`lundump.c`
`loadNumber` copies raw bytes). The programs that were covered are covered
unchanged.

## Obstacle met (fixed, not open)

The first form of the `flt_lit` rule passed an explicit `(by at_quiet)` argument:
`exact ValRepr.flt_lit (by at_quiet)`. The elaborator then unified the value
`F64.toModel ?x` with a computed float, such as `ofI z` against
`Floatdidf.S z`, before it assigned `?x` from the payload. That hit `maximum
recursion depth` in `AtFltForprep`/`AtFltForprepC`. The old rule had no
argument, so it unified the payload first. The fix is
`refine ValRepr.flt_lit ?_; at_quiet`. `at_quiet` matches payloads by
reducible defeq only.

## Open

`FloatArms.pow_spec` (`__ieee754_pow` at level (b)) and `FloatArms.FORPREP`
(`FpStrFlt_Statement`) are unchanged.
