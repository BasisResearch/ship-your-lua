import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Sim.Kit.Memmove
import Lua.Vm.Sim.Kit.DecDigits
import Lua.Vm.Sim.Kit.HeapKeep
import Lua.Vm.AtF.SnprintfLld

/-!
# `lua_integer2str`: `snprintf(buf, 44, "%lld", i)` (lane F1-FMT)

`IntegerToStr_Statement` over the at-lemmas of `Lua/Vm/AtF/SnprintfLld`
(`gen_lua_at.py --fn snprintf/lld`): `_svfprintf_r` specialised to the
format's bytes. Its roots: the entry, the return from `strlen(".")`
(`strlen_sumS`), the `'d'` conversion `0x80043824`, the digit loop's head
`0x80043b38` (`seg_loop` over the quotient), the loop's exit `0x80043b88`,
and the returns from `memmove` (`memmove_sum`) inside `__ssputs_r`. Every
root's context is `SnG.X`: the run's fixed atoms and a root's own (`SnV`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- The fixed data of a run: `snprintf`'s `sp`, the buffer, the format, `i`,
`ra`, the caller's frame, the variadic spill `a4`-`a7`, the console. -/
structure SnG where
  sp : Nat
  buf : Nat
  fmt : Nat
  i : BitVec 64
  r : BitVec 64
  f : AbiFrame
  a4 : BitVec 64
  a5 : BitVec 64
  a6 : BitVec 64
  a7 : BitVec 64
  o : Array String

/-- A root's own atoms: the digit cursor `c`, the count `k`, the first digit
`c5`; the quotient `q` and the dead registers' words. -/
structure SnV where
  c : Nat := 0
  k : Nat := 0
  c5 : Nat := 0
  q : BitVec 64 := 0
  b19 : BitVec 64 := 0
  b20 : BitVec 64 := 0
  b21 : BitVec 64 := 0
  b22 : BitVec 64 := 0
  b23 : BitVec 64 := 0
  b24 : BitVec 64 := 0

/-- **A root's context** (the generator's atom layout, `SNP_*`). -/
abbrev SnG.X (G : SnG) (V : SnV) (m : Mem) : FCx :=
  FCx.mk' [G.sp, G.buf, G.fmt, V.c, V.k, V.c5]
    [G.r, G.f.s0, G.f.s1, G.f.s2, G.f.s3, G.f.s4, G.f.s5, G.f.s6, G.f.s7, G.f.s8, G.f.s9, G.f.s10,
     G.f.s11, G.i, G.a4, G.a5, G.a6, G.a7, V.q, V.b19, V.b20, V.b21, V.b22, V.b23, V.b24] m G.o

/-! ## The runs of the roots

One lemma per root path, generated (`gen_lua_at.py` `runs`, lane F1-18:
`Lua/Vm/AtF/SnprintfLld/Runs.lean`): the path's at-lemmas applied in order,
the root memory's facts and the path's guards (on `i`, the quotient, the sign
byte) as hypotheses. -/

export Lua.Vm.AtF.SnprintfLld.Runs (run_E run_F run_Dn1 run_Dnm run_Dp1 run_Dpm run_Qp1 run_Qn1 run_Qn2
  run_Lc run_Lx run_Pn run_Pp run_Rp run_Rn1 run_Rn2)

end Lua.Vm.Sim.Kit
