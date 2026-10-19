import Lua.Vm.Sim.Kit.Add
import Lua.Vm.Sim.Kit.Mul
import Lua.Vm.Sim.Kit.Mod
import Lua.Vm.Sim.Kit.Eq
import Lua.Vm.Sim.Kit.Lt
import Lua.Vm.Sim.Kit.Le
import Lua.Vm.Sim.Kit.Eqk
import Lua.Vm.Sim.Kit.Loadnil
import Lua.Vm.Sim.Kit.Tointeger
import Lua.Vm.Sim.Kit.Mulk
import Lua.Vm.Sim.Kit.Modk
import Lua.Vm.Sim.Kit.AtModk
import Lua.Vm.Sim.Kit.AtIdiv
import Lua.Vm.Sim.Kit.AtForprep
import Lua.Vm.Sim.Kit.AtIdivk
import Lua.Vm.Sim.Kit.AtUnm
import Lua.Vm.Sim.Kit.AtShl
import Lua.Vm.Sim.Kit.AtShr
import Lua.Vm.Sim.Kit.AtShli
import Lua.Vm.Sim.Kit.AtShri
import Lua.Vm.Sim.Kit.AtBandk
import Lua.Vm.Sim.Kit.AtBork
import Lua.Vm.Sim.Kit.AtBxork
import Lua.Vm.Sim.Kit.EqLong
import Lua.Vm.Sim.Kit.Adjvar
import Lua.Vm.Sim.Kit.Varargprep
import Lua.Vm.Sim.Kit.AtStr
import Lua.Vm.Sim.Kit.RetFinal
import Lua.Vm.Sim.Kit.AtErr
import Lua.Vm.Sim.Kit.Write
import Lua.Vm.Sim.Kit.Swrite
import Lua.Vm.Sim.Kit.Sflush
import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.AtGettabup
import Lua.Vm.Sim.Kit.Fflush
import Lua.Vm.Sim.Kit.Memmove
import Lua.Vm.Sim.Kit.Memchr
import Lua.Vm.Sim.Kit.Fwrite
import Lua.Vm.Sim.Kit.Sfvwrite
import Lua.Vm.AtF.Sinit
import Lua.Vm.Sim.Kit.AtFltLoadf
import Lua.Vm.Sim.Kit.AtFltLti
import Lua.Vm.Sim.Kit.AtFltEqi
import Lua.Vm.Sim.Kit.AtFltGei
import Lua.Vm.Sim.Kit.AtFltAddi
import Lua.Vm.Sim.Kit.AtFltForloop
import Lua.Vm.Sim.Kit.Sinit
import Lua.Vm.Sim.Kit.Malloc
import Lua.Vm.Sim.Kit.AllocHeap
import Lua.Vm.Sim.Kit.AllocProof
import Lua.Vm.Sim.Kit.HeapKeep
import Lua.Vm.Sim.Kit.Setup
import Lua.Vm.Sim.Kit.Smakebuf
import Lua.Vm.Sim.Kit.Swsetup
import Lua.Vm.Sim.Kit.SfvFirst
import Lua.Vm.Sim.Kit.StdoutSetup
import Lua.Vm.Sim.Kit.HeapFill
import Lua.Vm.Sim.Kit.StdoutEmpty
import Lua.Vm.Sim.Kit.PrintIO
import Lua.Vm.Sim.Kit.LuaApi
import Lua.Vm.Sim.Kit.PrintSum
import Lua.Vm.Sim.Kit.AtFltSub
import Lua.Vm.Sim.Kit.AtFltForprep
import Lua.Vm.Sim.Kit.AtFltLt
import Lua.Vm.Sim.Kit.Precall
import Lua.Vm.Sim.Kit.CallArm
import Lua.Vm.Sim.Kit.CallPrint
import Lua.Vm.Sim.Kit.ExitUp
import Lua.Vm.Sim.Kit.PoscallN
import Lua.Vm.Sim.Kit.PrintS
import Lua.Vm.Sim.Kit.Tolstring
import Lua.Vm.Sim.Kit.PrintRel
import Lua.Vm.Sim.Kit.AtFltLei
import Lua.Vm.Sim.Kit.AtFltGti
import Lua.Vm.Sim.Kit.AtFltAdd
import Lua.Vm.Sim.Kit.AtFltAddk
import Lua.Vm.Sim.Kit.AtFltSubk
import Lua.Vm.Sim.Kit.AtFltUnm
import Lua.Vm.Sim.Kit.AtFltLe
import Lua.Vm.Sim.Kit.AtFltF2I
import Lua.Vm.Sim.Kit.AtFltBnot
import Lua.Vm.Sim.Kit.AtFltBand
import Lua.Vm.Sim.Kit.AtFltBor
import Lua.Vm.Sim.Kit.AtFltBxor
import Lua.Vm.Sim.Kit.AtFltBandk
import Lua.Vm.Sim.Kit.AtFltBork
import Lua.Vm.Sim.Kit.AtFltBxork
import Lua.Vm.Sim.Kit.AtFltShl
import Lua.Vm.Sim.Kit.AtFltShr
import Lua.Vm.Sim.Kit.AtFltShli
import Lua.Vm.Sim.Kit.AtFltShri
import Lua.Vm.Sim.Kit.AtFltMul
import Lua.Vm.Sim.Kit.AtFltMulk
import Lua.Vm.Sim.Kit.FltEqi
import Lua.Vm.Sim.Kit.AtFnFlt
import Lua.Vm.Sim.Kit.EqualobjF
import Lua.Vm.Sim.Kit.AtEqF
import Lua.Vm.Sim.Kit.AtFltEq
import Lua.Vm.Sim.Kit.AtFltDiv
import Lua.Vm.Sim.Kit.AtFltDivk
import Lua.Vm.Sim.Kit.AtFltIdiv
import Lua.Vm.Sim.Kit.AtFltIdivk
import Lua.Vm.Sim.Kit.AtFltMod
import Lua.Vm.Sim.Kit.AtFltModk
import Lua.Vm.Sim.Kit.PushLitProof
import Lua.Vm.Sim.Kit.Getmetafield
import Lua.Vm.Sim.Kit.TolStr
import Lua.Vm.Sim.Kit.TolStrProof
import Lua.Vm.Sim.Kit.IntFmtLoop
import Lua.Vm.Sim.Kit.FpCoerce
import Lua.Vm.Sim.Kit.Str2int

/-!
# The direct kit (round-3 bake-off, contender KIT)

The library (`Kit/Run.lean`: the segment runner `kit_run`; `Kit/Close.lean`:
the arm skeleton, M1 forward evaluation, M3 close, the arm tactics), the
call-node summaries of the libgcc helpers at the Lua ELF's addresses
(`Kit/Muldi3.lean`, `Kit/Udivdi3.lean`, `Kit/Moddi3.lean`), `luaV_mod`
restated (`Kit/ModEq.lean`), and the arms `sim_ADD` (refactor), `sim_MUL`,
`sim_MOD` (held out), `luaV_equalobj`'s summary (`Kit/Equalobj.lean`) and `OP_EQ` but
two long strings (`Kit/Eq.lean`: `eq_short`, `sim_EQ_of_long`).

Round 4 (S-SCAN): the loop and scan rules (`Kit/Scan.lean`: `seg_loop`,
`scan_loop`, `relay`, comprehension log entries `compMem`), live string
views (`Kit/Str.lean`: `Core.unseal`, `Core.str_at`), word lanes
(`Kit/Word.lean`), the string callees (`Kit/Memcmp.lean`, `Kit/Lngstr.lean`,
`Kit/Strcmp.lean`, `Kit/Strlen.lean`, `Kit/Lstrcmp.lean`,
`Kit/LstrcmpPro.lean`, with `Kit/Lex.lean` relating chunks to `lexLt`), and
the closed arm `sim_EQ` (`Kit/EqLong.lean`).

Lane F1-2: `docondjump` and the `l_strcmp` call node on the location-list route
(`Kit/AtCond.lean`), and the string paths of `OP_LE`, `OP_LT` there
(`Kit/AtStr.lean`: `At.sim_LE`, `At.sim_LT`; the kit's `LtStr` is retired).

Lane F1-FMT: `snprintf(buf, 44, "%lld", i)` on the callee-context route
(`Kit/IntFmt.lean` over `AtF/SnprintfLld`, `Kit/IntFmtSum.lean`,
`Kit/IntFmtLoop.lean`: the digit loop by `seg_loop`), `integerToStr_proved :
IntegerToStr_Statement`.
-/
