import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.Getshortstr

/-!
# `_ENV` on the location-list route (lane F1-7)

`OP_GETTABUP _ENV "print"` reads through pointers: the closure at `8(sp)`
(`Core.clptr`), `cl->upvals[0]`, `uv->v`, `_ENV`'s tag and table, then calls
`luaH_getshortstr` and reads the found node's tag and value. The relation's
complement holds those objects (`Complement.env`, `EnvMem` over `HeapRead`
regions), so the machine's reads there are the complement's (`Core.frame`).

* the atoms `cl`, `uv`, `tv`, `tab`, `pn` of `At.lean` name the pointers as
  total reads of the complement (`Env.*`);
* `env_*_at`: a machine load at a pointer's address is the pointer;
* `at_env hE hb0`: the at-lemma's numeric facts (the objects' ranges, the
  found node in the node array, `B = 0` in the address form);
* the hooks `at_eq_ext` and `at_side_ext` rewrite the pointer loads of a
  segment's pins and side conditions by `env_*_at` (inner loads first);
* the call node `gss_at`: `luaH_getshortstr`'s summary (`getshortstr_sum`) at
  the row, the memory the complement's off the window (`at_logwin`);
* the arm's closers: the guards on `_ENV`'s tag and the found node's tag
  (`env_tag_m`, `env_ptag_m`), and `print`'s representation (`at_new_ext`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.Kit

section
variable {p : Proto} {c : Vsa.Machine.Config} {s : State} {w : RelPtrs}

/-- A byte of a `HeapRead` range is the complement's. -/
theorem HeapRead.ld1 (hc : Core p c s w) {lo n : Nat} (hR : HeapRead p w lo n) {x : Nat}
    (h1 : lo ≤ x) (h2 : x < lo + n) : bytesT1 c.σ.mem x = bytesT1 w.mo x :=
  hc.frame x (hR.out x h1 h2)

/-- A doubleword of a `HeapRead` range is the complement's. -/
theorem HeapRead.ld8 (hc : Core p c s w) {lo n : Nat} (hR : HeapRead p w lo n) {x : Nat}
    (h1 : lo ≤ x) (h2 : x + 8 ≤ lo + n) : bytesT8 c.σ.mem x = bytesT8 w.mo x :=
  bytesT8_congrT fun _ _ => hc.frame _ (hR.out _ (by omega) (by omega))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable {ts : Nat}

/-- `ld 8(sp)`: the closure (`Core.clptr`). -/
theorem env_cl_at (hc : Core p c s w) {x : Nat} (hx : x = w.sp + 8) :
    bytesT8 c.σ.mem x = BitVec.ofNat 64 w.rt.cl := hx ▸ hc.clptr

/-- `ld 32(cl)`: `cl->upvals[0]`. -/
theorem env_uv_at (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) {x : Nat}
    (hx : x = w.rt.cl + 32) : bytesT8 c.σ.mem x = BitVec.ofNat 64 (Env.uv w.mo w.rt.cl) := by
  subst hx
  rw [HeapRead.ld8 (x := w.rt.cl + 32) hc hE.cl_at (by simp only [lclosureUpvalsOff]; omega)
    (by simp only [lclosureUpvalsOff]; omega)]
  exact (ofNat_toNat64 _).symm

/-- `ld 16(uv)`: `uv->v`. -/
theorem env_tv_at (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) {x : Nat}
    (hx : x = Env.uv w.mo w.rt.cl + 16) : bytesT8 c.σ.mem x = BitVec.ofNat 64 (Env.tv w.mo w.rt.cl) := by
  subst hx
  rw [HeapRead.ld8 (x := Env.uv w.mo w.rt.cl + 16) hc hE.uv_at (by simp only [upvalVOff]; omega)
    (by simp only [upvalVOff]; omega)]
  exact (ofNat_toNat64 _).symm

/-- `ld 0(tv)`: `_ENV`'s table. -/
theorem env_tab_at (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) {x : Nat}
    (hx : x = Env.tv w.mo w.rt.cl) : bytesT8 c.σ.mem x = BitVec.ofNat 64 (Env.tab w.mo w.rt.cl) := by
  subst hx
  rw [HeapRead.ld8 hc hE.tv_at (Nat.le_refl _) (by omega)]
  exact (ofNat_toNat64 _).symm

/-- `_ENV`'s tag, `LUA_VTABLE`. -/
theorem env_tag_m (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) :
    bytesT1 c.σ.mem (Env.tv w.mo w.rt.cl + 8) = BitVec.ofNat 8 vTable := by
  rw [HeapRead.ld1 hc hE.tv_at (by omega) (by omega)]; exact hE.tag

/-- The found node's tag, `LUA_VLCF`. -/
theorem env_ptag_m (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) :
    bytesT1 c.σ.mem (Env.pnode w.mo w.rt.cl ts + 8) = BitVec.ofNat 8 vLcf := by
  have := hE.pnode_mem; simp only [nodeSize] at this
  rw [HeapRead.ld1 hc hE.nodes_at (by omega) (by omega)]; exact hE.ptag

/-- The found node's value, `luaB_print`. -/
theorem env_pval_m (hc : Core p c s w) (hE : EnvMem w.mo w.rt.cl ts (HeapRead p w)) :
    bytesT8 c.σ.mem (Env.pnode w.mo w.rt.cl ts) = BitVec.ofNat 64 symLuaBPrint := by
  have := hE.pnode_mem; simp only [nodeSize] at this
  rw [HeapRead.ld8 hc hE.nodes_at (by omega) (by omega)]; exact hE.pval

end

/-- A string value's ownership and intern pointer (`ValRepr.str`'s premises). -/
theorem _root_.Lua.Vm.Sim.ValRepr.str_parts {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {s : List UInt8}
    (h : ValRepr mo ι t x (.str s)) : ι.own x.toNat s ∧ (s.length ≤ maxShortLen → x.toNat = ι.ptr s) := by
  cases h with
  | str _ hp ho => exact ⟨ho, hp⟩

/-- **The call node `luaH_getshortstr`** at the arm's row: on `_ENV`'s table
and the key `K[C] = "print"` (its intern pointer), it returns the node
`EnvMem` finds, the memory unchanged. The memory at the call is the entry
memory off the window (`hM`), so `EnvMem` holds of it (`EnvMem.congr`). -/
theorem gss_at {X : Cx} (hX : X.Ok)
    (hE : EnvMem X.w.mo X.w.rt.cl (X.w.ι.ptr printKey) (HeapRead X.p X.w))
    (hkc : kval X.p X.ins.c = some (.str printKey)) {m : Mem}
    (hM : ∀ a, ¬ Win X.p X.w a → m[a]? = X.c.σ.mem[a]?) (r : BitVec 64)
    (hr : r.toNat % 4 = 0) (fr : HFrame) :
    Triple (SegSt 0x8001808c#64 (⟨Register.x10, BitVec.ofNat 64 (Env.tab X.w.mo X.w.rt.cl)⟩ ::
        ⟨Register.x11, Loc.den X .kval⟩ :: ⟨Register.x1, r⟩ :: fr.pins)
        (ArmPay m X.c.σ.sailOutput))
      (SegSt r (⟨Register.x10, BitVec.ofNat 64 (Env.pnode X.w.mo X.w.rt.cl (X.w.ι.ptr printKey))⟩ ::
        fr.pins) (ArmPay m X.c.σ.sailOutput)) := by
  have hc := hX.core
  have hag : ∀ lo n, HeapRead X.p X.w lo n → ∀ a, lo ≤ a → a < lo + n →
      bytesT1 m a = bytesT1 X.w.mo a := fun lo n hR a h1 h2 => by
    simp only [bytesT1, hM a (hR.out a h1 h2)]
    exact hc.frame a (hR.out a h1 h2)
  have hEm := hE.congr hag
  have hA := hE.agree hag
  obtain ⟨-, hptr⟩ := (hc.kconst hkc).str_parts
  have hkey : Loc.den X .kval = BitVec.ofNat 64 (X.w.ι.ptr printKey) := by
    rw [← hptr (by decide)]; exact (ofNat_toNat64 _).symm
  rw [← hA.tab, ← hA.pnode, hkey]
  have h1 := hEm.tab_at; have h2 := hEm.key_at; have h3 := hEm.nodes_at
  have hroom : RuntimeData.spEntry - cStackBudget ≤ 2 ^ 32 := by decide
  exact getshortstr_sum _ _ _ r fr _ _
    { ra := hr
      tab_lo := h1.above
      tab_hi := by have := h1.below; omega
      key_lo := h2.above
      key_hi := by have := h2.below; omega
      node_lo := h3.above
      node_hi := by have := h3.below; omega
      lsz_lt := hEm.lsz_lt
      found := hEm.found } rfl

set_option hygiene false in
/-- **`at_env hE hb0`**: an `_ENV` at-lemma's numeric facts: the objects'
ranges (`HeapRead`), the found node in the node array, `B = 0` as the
address arithmetic reads it. -/
macro "at_env " hE:ident hb:ident : tactic => `(tactic| (
  have hb0' := $hb
  simp only [Word.b, Word.field, Nat.shiftRight_eq_div_pow] at hb0'
  have hEcl1 := ($hE).cl_at.above; have hEcl2 := ($hE).cl_at.below
  have hEuv1 := ($hE).uv_at.above; have hEuv2 := ($hE).uv_at.below
  have hEtv1 := ($hE).tv_at.above; have hEtv2 := ($hE).tv_at.below
  have hEtab1 := ($hE).tab_at.above; have hEtab2 := ($hE).tab_at.below
  have hEnd1 := ($hE).nodes_at.above; have hEnd2 := ($hE).nodes_at.below
  have hEpn := ($hE).pnode_mem
  obtain ⟨hEpn1, hEpn2⟩ := hEpn
  simp only [lclosureUpvalsOff, upvalVOff, Env.size, nodeSize, RuntimeData.spEntry, cStackBudget]
    at hEcl1 hEcl2 hEuv1 hEuv2 hEtv1 hEtv2 hEtab1 hEtab2 hEnd1 hEnd2 hEpn1 hEpn2))

set_option hygiene false in
/-- The path's stores miss everything outside the window (they are in the C
frame): the call's memory is the entry memory there. -/
macro "at_logwin" : tactic => `(tactic| (
  intro a ha
  try at_unfold
  simp only [Win, Slots, Scratch, RelPtrs.slot, ciSavedpcOff, stateTopOff, RuntimeData.spEntry,
    cStackBudget, execFrame, stackValueSize, not_or, not_and, Nat.not_lt] at ha
  simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]))

set_option hygiene false in
/-- The pointer loads of a pin, rewritten inner first (`env_*_at`). -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (
    simp (disch := kit_disch) only [sext64_id, env_cl_at hc, env_uv_at hc hE, env_tv_at hc hE,
      env_tab_at hc hE]
    first
    | done
    | with_reducible rfl
    | (apply BitVec.eq_of_toNat_eq; kit_disch)
    | (with_reducible apply un_congr; kit_disch)
    | (with_reducible apply un_congr; with_reducible apply un_congr; kit_disch)))

set_option hygiene false in
/-- An address side condition through pointer loads. -/
macro_rules
  | `(tactic| at_side_ext) => `(tactic| (
    simp (disch := kit_disch) only [sext64_id, env_cl_at hc, env_uv_at hc hE, env_tv_at hc hE,
      env_tab_at hc hE]
    kit_disch))

end Lua.Vm.Sim.At
