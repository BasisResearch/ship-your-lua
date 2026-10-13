import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.RetMem
import Lua.Vm.Sim.Kit.Exit
import Lua.Vm.LayoutErr
import Lua.Vm.Arms.Segs.HluaG_errormsg
import Lua.Vm.Arms.Segs.HluaD_throw
import Lua.Vm.Arms.Segs.Hlongjmp
import Lua.Vm.Arms.Segs.HluaD_rawrunprotected

/-!
# The throw: `luaG_errormsg` → `luaD_throw` → `longjmp` → back in `luaD_pcall` (lane F1-16)

Every Lua error of F1 ends in `luaG_errormsg(L)` (`luaG_runerror`, …,
`lua_error`). With no message handler (`L->errfunc = 0`: `main`'s
`lua_pcall(L, 0, 0, 0)`) it calls `luaD_throw(L, LUA_ERRRUN)`, which finds
`L->errorJmp` (the `lua_longjmp` of `luaD_rawrunprotected`, `ljAddr`), stores
the status in it and calls `longjmp(lj->b, 1)`; newlib's `longjmp` reloads
`ra`, `s0 … s11` and `sp` from the `jmp_buf` and returns `1` into
`luaD_rawrunprotected` after its `setjmp`, which restores `L->nCcalls` and
`L->errorJmp` (`lj.previous`) and returns the status `2` to `luaD_pcall`
(`0x8000b4c0`).

`throw_land` is that run, over the generated segments (`kit_run`), from any
memory with the words it reads (`ThrowMem`); `ThrowPost` is what it leaves.
The words are the boot's (`RuntimeData`): the `jmp_buf` and
`luaD_rawrunprotected`'s frame lie in the caller frames above the entry `sp`
(`CStackAt.callers`), `L->errfunc` and `L->errorJmp` are `LuaStatic`'s.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.Ret Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- `luaD_rawrunprotected`'s `lua_longjmp` (`L->errorJmp`): `previous` at
`0x87fffe60`, the `jmp_buf` from `0x87fffe68` (`ra`, `s0 … s11`, `sp`), the
status at `0x87ffff38`; its frame's `L` at `0x87fffe40`, `oldnCcalls` at
`0x87fffe48`, `ra` at `0x87ffff48`. -/
theorem lj_layout : RuntimeData.ljAddr = 0x87fffe60 ∧ RuntimeData.rawrunSp = 0x87fffe40 ∧
    RuntimeData.setjmpRet = 0x80009c24 := ⟨rfl, rfl, rfl⟩

/-- **The words the throw reads**, in a memory `M`, for the `lua_State` `L`. -/
structure ThrowMem (L : Nat) (M : Mem) : Prop where
  /-- `L->errfunc = 0`: no message handler (`luaG_errormsg`'s `bnez`) -/
  errfunc : bytesT8 M (L + stateErrfuncOff) = 0#64
  /-- `L->errorJmp` (`luaD_throw`'s `beqz`) -/
  errjmp : bytesT8 M (L + stateErrorJmpOff) = BitVec.ofNat 64 RuntimeData.ljAddr
  /-- the `jmp_buf`'s `ra`: `setjmp`'s return in `luaD_rawrunprotected` -/
  jb_ra : bytesT8 M 0x87fffe68 = BitVec.ofNat 64 RuntimeData.setjmpRet
  /-- the `jmp_buf`'s `sp`: `luaD_rawrunprotected`'s frame -/
  jb_sp : bytesT8 M 0x87fffed0 = BitVec.ofNat 64 RuntimeData.rawrunSp
  /-- `luaD_rawrunprotected`'s `L` (`0(sp)`) -/
  rawrun_L : bytesT8 M 0x87fffe40 = BitVec.ofNat 64 L
  /-- `lj.previous` (`32(sp)`): the outermost handler -/
  previous : bytesT8 M 0x87fffe60 = 0#64
  /-- `luaD_rawrunprotected`'s saved `ra` (`264(sp)`): into `luaD_pcall` -/
  rawrun_ra : bytesT8 M 0x87ffff48 = 0x8000b4c0#64

/-- The registers back in `luaD_pcall` after the throw: `sp` its frame, `gp`,
the status `a0 = 2`, `s0 … s11` the `jmp_buf`'s (`M`'s words). -/
abbrev throwRow (M : Mem) : List Pin :=
  [⟨Register.x2, 0x87ffff50#64⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x10, 2#64⟩,
   ⟨Register.x8, bytesT8 M 0x87fffe70⟩, ⟨Register.x9, bytesT8 M 0x87fffe78⟩,
   ⟨Register.x18, bytesT8 M 0x87fffe80⟩, ⟨Register.x19, bytesT8 M 0x87fffe88⟩,
   ⟨Register.x20, bytesT8 M 0x87fffe90⟩, ⟨Register.x21, bytesT8 M 0x87fffe98⟩,
   ⟨Register.x22, bytesT8 M 0x87fffea0⟩, ⟨Register.x23, bytesT8 M 0x87fffea8⟩,
   ⟨Register.x24, bytesT8 M 0x87fffeb0⟩, ⟨Register.x25, bytesT8 M 0x87fffeb8⟩,
   ⟨Register.x26, bytesT8 M 0x87fffec0⟩, ⟨Register.x27, bytesT8 M 0x87fffec8⟩]

/-- **What the throw writes**: the two return addresses below `sp`, the
status `lj.status`, `L->nCcalls`, `L->errorJmp`. -/
def ThrowW (L sp : Nat) (a : Nat) : Prop :=
  (sp - 64 ≤ a ∧ a < sp) ∨ (0x87ffff38 ≤ a ∧ a < 0x87ffff38 + 4) ∨
    (L + stateNCcallsOff ≤ a ∧ a < L + stateNCcallsOff + 4) ∨
    (L + stateErrorJmpOff ≤ a ∧ a < L + stateErrorJmpOff + 8)

/-- **What the throw leaves**: the memory off `ThrowW`, the status `2`,
`L->nCcalls` restored from `luaD_rawrunprotected`'s frame, `L->errorJmp =
NULL`. -/
structure ThrowPost (L sp : Nat) (M M' : Mem) : Prop where
  keep : ∀ a, ¬ ThrowW L sp a → bytesT1 M' a = bytesT1 M a
  status : bytesT4 M' 0x87ffff38 = 2#32
  nCcalls : bytesT4 M' (L + stateNCcallsOff) = swData (bytesT8 M 0x87fffe48)
  errjmp : bytesT8 M' (L + stateErrorJmpOff) = 0#64

theorem t1_wm4_out {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x < a ∨ a + 4 ≤ x) :
    bytesT1 (writeMap4 m a d) x = bytesT1 m x := by
  simp only [bytesT1, getElem?_writeMap4_out m a d x h]

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_negX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    Nat.reduceAdd, bytesT8_wm8_out', bytesT8_wm4_out', bytesT4_wm8_out'', bytesT4_wm4_out',
    bytesT4_wm4_same, sext64_id, t_errfunc, t_errjmp, t_jb_ra, t_jb_sp, t_rawrun_L,
    t_previous, t_rawrun_ra, symGlobalPointer, stateErrfuncOff, stateErrorJmpOff,
    stateNCcallsOff, RuntimeData.ljAddr, RuntimeData.setjmpRet, RuntimeData.rawrunSp] at $h:ident)

set_option hygiene false in
local macro_rules | `(tactic| kit_side_pre) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_negX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    Nat.reduceAdd, bytesT8_wm8_out', bytesT8_wm4_out', bytesT4_wm8_out'', bytesT4_wm4_out',
    bytesT4_wm4_same, sext64_id, t_errfunc, t_errjmp, t_jb_ra, t_jb_sp, t_rawrun_L,
    t_previous, t_rawrun_ra, symGlobalPointer])

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (rw [rtgt _ (by decide)]; decide))

/-- **The throw lands back in `luaD_pcall` with the status `2`**: from
`luaG_errormsg(L)` (any `ra`, `sp` with 64 bytes of room below it and above
`L`'s words, the caller's `s0 … s11`), through `luaD_throw` and `longjmp`,
into `luaD_rawrunprotected`'s return (`0x8000b4c0`, `throwRow`), having
written only `ThrowW` (`ThrowPost`). -/
theorem throw_land (L sp : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hT : ThrowMem L M) (hL : tohostAddr + 16 ≤ L) (hLal : L % 8 = 0) (hLs : L + 200 + 64 ≤ sp)
    (hsp : sp ≤ RuntimeData.spEntry) (hal : sp % 16 = 0) :
    Triple (SegSt (BitVec.ofNat 64 symLuaGErrormsg) (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] sp r f)
        (ArmPay M o))
      (fun c => ∃ M', SegSt 0x8000b4c0#64 (throwRow M) (ArmPay M' o) c ∧ ThrowPost L sp M M') := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  simp only [RuntimeData.spEntry] at hsp
  simp only [callPre, List.cons_append, List.nil_append, symLuaGErrormsg] at h
  have t_errfunc := hT.errfunc; have t_errjmp := hT.errjmp; have t_jb_ra := hT.jb_ra
  have t_jb_sp := hT.jb_sp; have t_rawrun_L := hT.rawrun_L; have t_previous := hT.previous
  have t_rawrun_ra := hT.rawrun_ra
  simp only [stateErrfuncOff, stateErrorJmpOff, RuntimeData.ljAddr, RuntimeData.setjmpRet,
    RuntimeData.rawrunSp] at t_errfunc t_errjmp t_jb_ra t_jb_sp
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  refine ⟨_, acc, _, h.repin (by pins_of h), ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [ThrowW, stateNCcallsOff, stateErrorJmpOff, not_or, not_and, Nat.not_lt] at ha
    simp (disch := omega) only [bytesT1_writeMap8_out, t1_wm4_out]
  · simp (disch := omega) only [bytesT4_wm8_out'', bytesT4_wm4_out', bytesT4_wm4_same]
    decide
  · simp only [stateNCcallsOff]
    simp (disch := omega) only [bytesT4_wm8_out'', bytesT4_wm4_same]
  · simp only [stateErrorJmpOff]
    simp (disch := omega) only [bytesT8_wm8_hitX]

end Lua.Vm.Sim.Kit
