import Lua.Vm.Sim.Kit.TolIntProof
import Lua.Vm.Sim.Kit.TolFn

/-!
# `TolFn_Statement` (lane F1-24)

`luaL_tolstring` on a function argument in `luaB_print`'s loop (`TolArg
IsFn`): the run `tolfn_sum` (`Kit/TolFn.lean`) on F1's one function `print`,
its entry facts by `tolV_in` (`LUA_VLCF`, `0x80022f18`,
`G(L)->mt[LUA_TFUNCTION]` NULL: `PrintIn.mt_fn`, which `PrKeep` keeps), the
glue to `TolPost` by `tolPost_of_run` over the class facts `argStr_fn`
(`"function: 0x80022f18"`: `print` shows it, twenty bytes, no literal's length).
With it `luaB_print` routes a function per argument (`printRel_of`), and
`CallOpen` is `printFlt` alone.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- `print`'s tag and payload. -/
theorem _root_.Lua.Vm.Sim.ValRepr.fn_inv {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    (h : ValRepr mo ι t x (.builtin .print)) : t = 0x16#8 ∧ x = 0x80022f18#64 := by
  cases h with
  | print hx => exact ⟨rfl, hx⟩

/-- **No literal is `"function: 0x80022f18"`.** -/
theorem lits_ne_fnU8 (ls : LitPtrs) : ∀ l ∈ ls.table, l.bytes ≠ fnU8 := by
  intro l hl he
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> dsimp only at he <;> revert he <;> decide

/-- **No literal's object holds it**: their lengths (`3`, `4`, `5`, `10`)
are not twenty. -/
theorem lits_nomatch_fn {M : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (hL : LitsIn M g sl ls rt) :
    ∀ p ∈ ls.strs, bytesT1 M (p + 11) = BitVec.ofNat 8 fnU8.length →
      (∀ i, i < fnU8.length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 (fnU8.getD i 0).toNat) → False := by
  intro p hp h11 _
  simp only [LitPtrs.strs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [(hL.nil.repr.total hL.nil.short).1] at h11; revert h11; decide
  · rw [(hL.tru.repr.total hL.tru.short).1] at h11; revert h11; decide
  · rw [(hL.fls.repr.total hL.fls.short).1] at h11; revert h11; decide
  · rw [(hL.tos.repr.total hL.tos.short).1] at h11; revert h11; decide

/-- **`print`'s class facts.** -/
theorem argStr_fn : ArgStr (.builtin .print) fnU8 where
  arg := argBytes_fn
  len_lo := by decide
  len_hi := by decide
  cost := rfl
  lits := lits_ne_fnU8
  no_lit := fun hL => lits_nomatch_fn hL

/-- **`luaL_tolstring` on a function argument in `luaB_print`'s loop**
(`TolFn_Statement`, lane F1-24): the run `tolfn_sum` from `TolFIn`
(`tolV_in`), `TolPost` by the glue `tolPost_of_run`. -/
theorem tolFn_proved : TolFn_Statement := by
  intro sp0 L nci func n tbc sl g ls args ι D G B FL ph0 H0 M0 i v hIn hn hv hC hi1 hin ph H m o r f hS hP hr
  cases v with
  | builtin bf =>
    cases bf
    have hx : TolFIn m (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g r :=
      tolV_in hIn hn hS hv argStr_fn (fun h => h.fn_inv) (by decide)
        (by rw [show g + 528 = g + gMtOff + 8 * luaTfunction by rfl]; exact hIn.mt_fn) hi1 hin hr
    exact tolPost_of_run hIn hn hS hP hv argStr_fn hi1 fun K X W cw size hash head d nuse hT c h => by
      obtain ⟨c', s', ts, M3, M, H', hstr, hpost, -, hret⟩ := tolfn_sum AllocProof.mallocR_proved
        (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g r f m o hx ls.seed
        K X W cw size hash head d nuse H hT c h
      exact ⟨c', s', ts, M3, M, H', hstr, hpost, hret⟩
  | nil => exact absurd hC id
  | bool _ => exact absurd hC id
  | int _ => exact absurd hC id
  | flt _ _ => exact absurd hC id
  | str _ => exact absurd hC id

/-- **`luaB_print` on the C frame** from `CALL`'s open part (lane F1-15;
F1-17; F1-18; F1-23; F1-24): `lua_pushstring` of the literals proved
(`pushLit_proved`), `luaL_tolstring` on strings, integers and `print` proved
(`tolStr_proved`, `tolInt_proved`, `tolFn_proved`), `_malloc_r` proved (lane
F1-A0-M, `AllocProof.mallocR_proved`); floats by `CallOpen`'s field
(`printFlt`). (Moved from `Kit/TolIntProof.lean`.) -/
theorem CallOpen.print (O : CallOpen) : PrintRel_Statement :=
  printRel_of AllocProof.mallocR_proved pushLit_proved tolStr_proved tolInt_proved tolFn_proved O.printFlt

/-- (lane F1-24) **`PrintFn_Statement` from the float class**: a list with a
function is a `luaB_print` list (`printRel_of`, functions per argument by
`tolFn_proved`). -/
theorem printFn_of_flt (hFl : PrintFlt_Statement) : PrintFn_Statement :=
  fun sp L nci func n tbc sl g ls args ι D G ph H f M o _ hIn hn hbud =>
    CallOpen.print ⟨hFl⟩ sp L nci func n tbc sl g ls args ι D G ph H f M o trivial hIn hn hbud

end Lua.Vm.Sim.Kit
