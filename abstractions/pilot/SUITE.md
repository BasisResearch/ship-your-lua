# Held-out pilot suite, round 1

Fixed before the fan-out. Nobody has proved any held-out case. Every candidate
and the incumbent are measured on the same cases with the same semantics.

## H: held-out cases (K = 4 per metatheory cluster, plus 3 A1 arms)

The cases extend F1 with **Lua strings** (an F4 slice). This is the next
fragment's real work, and it hits both metatheory clusters. The semantics is
fixed here so that every contender implements the same thing.

Values gain `str (s : List UInt8)` (already a constructor of `Value`). For
Lua 5.4.7 in the "C" locale (bare metal, no `setlocale`):

| # | case | source (`LuaSem`) | bytecode (`Step`) |
|---|---|---|---|
| H1 | string literals | `Exp.string s` evaluates to `.str s` | `LOADK` of a `Const.str` constant (allowed by `Supported`) |
| H2 | concatenation `a .. b` | strings or integers (integers converted with `tostring`, i.e. `%d`); anything else is an error (no rule) | `CONCAT A B`: `R[A] := R[A] .. … .. R[A+B-1]`, right to left as `luaV_concat`. **Write set is the whole range `R[A..A+B-1]`**: `luaV_concat` works in place (`tostring` rewrites number operands into strings in their slots, `lvm.c:649-650`; partial results stay in the range, `lvm.c:679-682`), so the slots above `A` are garbage afterwards (checked in round 1) |
| H3 | length `#a` | of a string: its byte length as `.int` | `LEN A B` on a string |
| H4 | string order `<`, `<=` (and `>`, `>=` by swapping) | `l_strcmp` = byte-lexicographic in the C locale | `LT`/`LE` with two strings |

String equality needs no new rule: raw equality on `Value` already covers it.

For each H case, a contender must deliver, for its cluster:

- **ast-construct-fanout (source):** the rule(s) in `LuaSem`, the executable
  interpreter case, interpreter soundness for the case, determinism for the
  case, and `AstSupported` admitting the construct.
- **bc-rule-fanout (bytecode):** the `Step` rule(s), the executable stepper
  case, stepper soundness and completeness for the case, the footprint /
  definite-initialisation simulation for the case, and `Supported`'s tables.
- **Validation:** `c/tests/f4_strlite.lua` (to be written by the bake-off
  harness, the same file for everyone). It must be `AstSupported` and
  `Supported` in the extended fragment, and its `LuaSem`/`BcSem` outputs must
  equal the ELF's on Sail (kernel-checked).

**A1 arms (forecast cluster; measured only if A0.6 lands in time):** the
machine simulation of the `ADD`, `EQI` and `FORLOOP` arms of `luaV_execute`
against their `Step` rules.

## R: existing proofs to refactor (compression)

- R1: `Lua/FragmentSound.lean`'s `Step.sim` (27 rule arms) plus
  `Lua/Bytecode/Exec.lean`'s `step?_sound`/`step?_complete`: `bc-rule-fanout`.
- R2: `Lua/Ast/Determinism.lean` (`Eval.det`, `ExecS.det`, …) plus
  `Lua/Ast/Exec.lean`'s `execSound`: `ast-construct-fanout`.

## Metrics (per contender, per cluster)

- **held-out cost:** proof lines, generated lines reported separately, agent
  wall time, and failed build attempts, for H1–H4;
- **compression:** R1/R2 after refactoring on the new abstraction, against the
  originals (596 + 261 lines; 216 + 294 lines);
- **setup cost:** lines of the abstraction itself (definitions + its rules'
  proofs);
- **acceptance:** `scripts/check.sh` green (axioms standard, no sorry, no
  raised limits).

A contender wins a cluster iff the held-out cost falls AND the refactor
shrinks against the incumbent. The incumbent is the current style: per-rule
cases written by hand.

## Finding during round 1 (R2-3): a strings fragment without floats is not closed

Checked with the host `lua` built from the vendored source:

| expression | result |
|---|---|
| `"10"+1` | `11` |
| `-"2"` | `-2` |
| `"10"//3`, `"7"%2` | `3`, `1` |
| `"1.5"+1` | **`2.5`** |
| `"3"&1` | error (no bitwise coercion) |
| `"x"+1` | error |

In Lua 5.4, arithmetic coerces numeric strings through the string library's
metamethods, and the ELF opens `string`. Strings can also be *built* at run
time (`"1"..".5"`), so no static check can keep a float result out of a
program once strings are in registers. `vm_refinement`'s iff would be false
for such programs if the semantics were stuck on them.

Consequences:

- **For this bake-off.** H1–H4 are unchanged: their metatheory cost is
  well-defined and is what is measured. Every contender must also add
  **H5**: arithmetic on a string operand that coerces to an integer (by
  `luaO_str2num` + `luaV_tointegerns`) gives the integer result, and
  anything else is left stuck. The float-producing case is recorded as out of
  scope for the pilot.
- **For the plan (PHASES).** F4 (strings) cannot precede Float. Strings and
  floats must land together, or the string metatable's arithmetic must be
  modelled with floats present.

## H5 precisely, and the shared validation program

**H5 on the bytecode side** follows `lvm.c`'s path for an arithmetic opcode
whose operands are not both integers:

- **The arithmetic instruction** (`ADD`/`ADDI`/`ADDK`/…/`UNM`) takes its
  fall-through: `pc + 1`, the `MMBIN`/`MMBINI`/`MMBINK` after it.
- **The `MMBIN*` instruction** (`luaT_trybinTM`) finds `__add`/… in the
  string metatable when an operand is a string. `lstrlib.c`'s `arith_*`
  converts both operands with `tonumber` and applies the operation.
  - If the conversion gives integers, it stores the integer result into
    `R[A]` of the *preceding* arithmetic instruction (`GETARG_A(pc[-2])`) and
    continues at `pc + 1`.
  - Otherwise (a non-numeric string, a float-valued string, or no string
    operand at all) there is no rule.
- **`UNM`** uses `__unm` in the same way, with `MMBIN`.

**On the source side**, H5 is the arithmetic rule extended: an operand that
is a string coercing to an integer is replaced by that integer.

**Shared validation program.** `c/tests/f4_strlite.lua`, with its stripped
chunk `c/tests/f4_strlite.luac`, uses literals, `..` with integer coercion,
`#`, `<`/`<=`/`==`, and arithmetic on integer-valued strings
(`ADDI`→`MMBINI`, `MUL`→`MMBIN`, `MODK`/`IDIVK`→`MMBINK`, `UNM`).
`c/tests/f4_strlite.expected` was recorded from the ELF on Sail, and the
host `lua` agrees. Every contender must prove `LuaSem` (source contenders)
or `BcSem` (bytecode contenders) with exactly this output.
