import Lua.Vm.Sim.Kit.AtCoerce
import Lua.Vm.Sim.Kit.TonumStr
import Lua.Vm.Sim.Kit.AtCond

/-!
# FORPREP's string coercions as call nodes at a row (lane F1-F9)

The call at-lemmas of `OP_FORPREP_C*` with a string class (`S`) and of
`OP_FORPREP_SI` (`scripts/gen_lua_at.py`), on a string register `R[A+k]`
holding `xs` that `luaO_str2num` reads as an integer (`str2int xs`):

* `luaV_tonumber_(R[A+k], q)` (`tons_sum`): `a0 = 1`, `*q` the converted
  integer (`__floatdidf`), the callee frames `[sp - 80, sp)` a `clob` with
  content `tonsW`;
* `luaV_tointeger(R[A+1], q, mode)` (`tois_sum`): `a0 = 1`, `*q` the integer,
  the callee frame `[sp - 80, sp)` a `clob` with content `toisW`.

The string is live in the call's memory (`Core.str_at`: the run's stores lie
in `Scratch`, `ScrFrame`) and apart from the callee frames
(`Ranges.own_apart`). The integer is `strIntOf (rsOf X j)`, the register's
string read by the context.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-- Register `j`'s string at the context (`[]` when it is none). -/
def rsOf (X : At.Cx) (j : Nat) : List UInt8 :=
  match X.s.regs j with
  | some (.str s) => s
  | _ => []

/-- The integer `l_str2int` reads (`0` when none). -/
def strIntOf (s : List UInt8) : BitVec 64 := (str2int s).getD 0

theorem rsOf_eq {X : At.Cx} {j : Nat} {xs : List UInt8} (h : X.s.regs j = some (.str xs)) :
    rsOf X j = xs := by simp [rsOf, h]

theorem strIntOf_eq {s : List UInt8} {v : BitVec 64} (h : str2int s = some v) : strIntOf s = v := by
  simp [strIntOf, h]

/-- A string register's tag. -/
theorem _root_.Lua.Vm.Sim.ValRepr.str_tag {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    {s : List UInt8} (h : ValRepr mo ι t x (.str s)) : t = BitVec.ofNat 8 (strTag s) := by
  cases h; rfl

/-- A string register's tag is neither the integer's nor the float's. -/
theorem _root_.Lua.Vm.Sim.ValRepr.str_ne {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    {s : List UInt8} (h : ValRepr mo ι t x (.str s)) :
    t ≠ BitVec.ofNat 8 vNumInt ∧ t ≠ BitVec.ofNat 8 19 := by
  rw [h.str_tag]; rcases strTag_cases s with e | e <;> rw [e] <;> decide

/-- **A string register at a call**: its object live and apart from the
callee frames below `sp` (`TsCtx`), in a memory exact outside `Scratch`
whose slot reads are the entry's. -/
theorem tsCtx_at {X : At.Cx} (hX : X.Ok) {M : Mem} (hm : At.WinFrame X M) {j : Nat}
    (hj : j < X.p.maxstacksize) {xs : List UInt8} (hsx : X.s.regs j = some (.str xs))
    (ht : slotTag M (X.w.slot j) = slotTag X.c.σ.mem (X.w.slot j))
    (hp : slotVal M (X.w.slot j) = slotVal X.c.σ.mem (X.w.slot j)) :
    TsCtx M (X.w.slot j) (slotVal X.c.σ.mem (X.w.slot j)).toNat X.w.sp xs := by
  have hc := hX.core
  have hr := hc.ranges
  have hv := hc.stack j _ hj hsx
  have ho := hv.owned hc.comp
  -- the object lies outside the window, so the run's stores (in `Scratch`,
  -- the slots, `luaV_execute`'s C frame) miss it
  have hview := hc.unseal ho hv.tsr fun a ha => hm a (fun h => ha (.inr (.inr h)))
    (fun h => ha (.inl h)) (fun h => ha (.inr (.inl ⟨by simp only [CFrame] at h; omega, by
      simp only [CFrame, execFrame] at h ⊢; omega⟩)))
  have hap := hr.own_apart ho
  have hsp := hr.sp_eq
  simp only [RuntimeData.spEntry, cStackBudget, execFrame] at hsp hap
  exact ⟨by rw [hp, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [ht, hv.str_tag], hview,
    hap.mono (by omega) (by omega)⟩

/-- **`luaV_tonumber_` on a string integer numeral**, at a call. -/
theorem tons_at {X : At.Cx} (hX : X.Ok) {M : Mem} (hm : At.WinFrame X M) {j : Nat}
    (hj : j < X.p.maxstacksize) {xs : List UInt8} (hsx : X.s.regs j = some (.str xs))
    (hxi : (str2int xs).isSome = true) {q sp : Nat} {r : BitVec 64} {f : HFrame} {o : Array String}
    {n : Nat} (hn : n = X.w.slot j)
    (hx : TifCtx M n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (hspw : sp = X.w.sp)
    (ht : slotTag M n = slotTag X.c.σ.mem n) (hp : slotVal M n = slotVal X.c.σ.mem n) :
    Triple (SegSt 0x8001ab58#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 q⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay M o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
        (ArmPay (writeMap8 (memPatch M (tonsW r n q sp M (strIntOf (rsOf X j))) (sp - 80) 80) q
          (sdData_val (Lua.Vm.Fn.Floatdidf.S (strIntOf (rsOf X j))))) o)) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hxi
  rw [rsOf_eq hsx, strIntOf_eq hv]
  subst hspw hn
  exact tons_sum _ q _ _ xs r f M o hx hsp hgp (tsCtx_at hX hm hj hsx ht hp) hv

/-- **`luaV_tointeger` on a string integer numeral**, at a call. -/
theorem tois_at {X : At.Cx} (hX : X.Ok) {M : Mem} (hm : At.WinFrame X M) {j : Nat}
    (hj : j < X.p.maxstacksize) {xs : List UInt8} (hsx : X.s.regs j = some (.str xs))
    (hxi : (str2int xs).isSome = true) {q sp : Nat} {r md : BitVec 64} {f : HFrame} {o : Array String}
    {n : Nat} (hn : n = X.w.slot j)
    (hx : TifCtx M n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (hspw : sp = X.w.sp)
    (ht : slotTag M n = slotTag X.c.σ.mem n) (hp : slotVal M n = slotVal X.c.σ.mem n) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 q⟩ :: ⟨Register.x12, md⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay M o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
        (ArmPay (writeMap8 (memPatch M (toisW r f.s1 md n q sp M (strIntOf (rsOf X j))) (sp - 80) 80) q
          (sdData_val (strIntOf (rsOf X j)))) o)) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hxi
  rw [rsOf_eq hsx, strIntOf_eq hv]
  subst hspw hn
  exact tois_sum _ q _ _ xs r md f M o hx hsp hgp (tsCtx_at hX hm hj hsx ht hp) hv

end Lua.Vm.Sim.Kit

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout

/-- A register bound in the at-lemma's normal form of the fields. -/
macro "ts_bound" : tactic => `(tactic| (
  try simp only [Word.a, Word.field, Nat.shiftRight_eq_div_pow] at *
  omega))

set_option hygiene false in
/-- The string register's fact `hsx` in the at-lemma's normal form of the
fields. -/
macro "ts_hsx" : tactic => `(tactic| first
  | exact hsx
  | simpa only [Word.a, Word.field, Nat.shiftRight_eq_div_pow, Nat.add_zero] using hsx)

/-- The slot's address in the row's form. -/
macro "ts_slot" : tactic => `(tactic| (
  try simp only [RelPtrs.slot, stackValueSize]
  ts_bound))

/-- **`at_tons f k`**: `luaV_tonumber_`'s string call lemma's proof (after
`at_open` and the dead registers' pins): `tons_at` at the row, the slot's
reads through the path's stores (`at_eq`). -/
syntax "at_tons " ident num : tactic

set_option hygiene false in
macro_rules
  | `(tactic| at_tons $fl:ident $k:num) => do
    let j ← `(X.ins.$fl + $k)
    `(tactic| (
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
      (Lua.Vm.Sim.Kit.tons_at (j := $j) hX (by at_win) (by ts_bound) (by ts_hsx) hxi (sp := X.w.sp)
        (f := hframe?) (by ts_slot) (by tif_ctx) (by rfl) (by rfl) rfl (by at_eq) (by at_eq))
    refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
    · at_pins h
    · at_mem))

/-- **`at_tois f k md`**: `luaV_tointeger`'s string call lemma's proof. -/
syntax "at_tois " ident num num : tactic

set_option hygiene false in
macro_rules
  | `(tactic| at_tois $fl:ident $k:num $md:num) => do
    let j ← `(X.ins.$fl + $k)
    `(tactic| (
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h)
      (Lua.Vm.Sim.Kit.tois_at (j := $j) (md := BitVec.ofNat 64 $md) hX (by at_win) (by ts_bound)
        (by ts_hsx) hxi (sp := X.w.sp) (f := hframe?) (by ts_slot) (by tif_ctx) (by rfl) (by rfl) rfl
        (by at_eq) (by at_eq))
    refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
    · at_pins h
    · at_mem))

end Lua.Vm.Sim.At
