import Lua.Bytecode.Exec
import Lua.Vm.Host
import Lua.Programs.While
import Lua.Programs.PrintPrint
import Lua.Programs.F1Ops
import Lua.Programs.F1bBits

/-!
# Validating `BcSem` against the binary's I/O

`c/tests/while.luac` is the chunk embedded in `c/lua-riscv-htif.elf`; on
the Sail model the ELF prints `55\n2500\n36\n` and exits 0 (VALIDATION.md).
`while_bcSem` is the kernel-checked derivation that F1's `BcSem` gives the
same output. The derivation is found by `run` and certified by
`bcSem_of_run` (`run_sound`); the semantics itself is the inductive `Step`.
`decide +kernel` evaluates `run` in the kernel only (no `native_decide`, no
extra axioms).
-/

namespace Lua.Programs

open Lua.Bytecode Lua.Vm

theorem while_bcSem : BcSem binaryHost whileProto "55\n2500\n36\n" :=
  bcSem_of_run (n := 4000) (by decide +kernel)

/-- `c/tests/print_print.lua` (`print(print, 1, nil, true)`): on the Sail
model the ELF prints `function: 0x800219b0\t1\tnil\ttrue\n`. -/
theorem printPrint_bcSem :
    BcSem binaryHost printPrintProto "function: 0x800219b0\t1\tnil\ttrue\n" :=
  bcSem_of_run (n := 100) (by decide +kernel)

/-- `c/tests/f1_ops.lua`: every F1 rule family (numeric `for`, floor
`//`/`%` and their `-1` cases, wraparound, `and`/`or` via `TESTSET`, `not`,
equality, immediate and register comparisons). The expected string is the
ELF's output on the Sail model (`c/tests/f1_ops.expected`). -/
theorem f1Ops_bcSem : BcSem binaryHost f1OpsProto
    "385\n10\n7\n4\n1\n-3\t-2\t-4\t1\t-7\t-7\n-9223372036854775808\t-2\t-9223372036854775808\n-9223372036854775808\t0\n5\t6\ttrue\tfalse\ttrue\ttrue\tfalse\n8\ttrue\tfalse\ttrue\tfalse\n7\t2187\ttrue\tfalse\n" :=
  bcSem_of_run (n := 4000) (by decide +kernel)

/-- `c/tests/f1b_bits.lua`: F1b, integer bitwise in every operand form
(`BAND`/`BOR`/`BXOR`/`SHL`/`SHR`, `BANDK`/`BORK`/`BXORK`, `SHRI`/`SHLI`,
`BNOT`), with `luaV_shiftl`'s edge cases. The expected string is the ELF's
output on the Sail model (`c/tests/f1b_bits.expected`). -/
theorem f1b_bcSem : BcSem binaryHost f1bProto
    "2640\t24570\t21930\t-23131\t-1\n90\t23386\t42405\t9223372036854775807\n9223372036854775807\t1\t-9223372036854775808\t1445\t370080\n0\t0\t0\t2891\t185040\t0\t0\n96\t0\t0\t224\t0\t2\t9223372036854775804\n72624976668147841\t129\t72624976668147712\n833130\ttrue\ttrue\n" :=
  bcSem_of_run (n := 4000) (by decide +kernel)

end Lua.Programs
