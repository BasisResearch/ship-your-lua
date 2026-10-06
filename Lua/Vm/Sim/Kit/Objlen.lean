import Lua.Vm.Sim.Kit.Str
import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Arms.Segs.HluaV_objlen

/-!
# `luaV_objlen` on a string at the Lua ELF's address (lane F1-2)

`luaV_objlen(L, ra, rb)` (`0x8001bae0`, lvm.c): `ttypetag(rb)` is `LUA_VSHRSTR`
(4: `setivalue(s2v(ra), tsvalue(rb)->shrlen)`, `0x8001bbb8`) or `LUA_VLNGSTR`
(20: `u.lnglen`, `0x8001bb58`); a table and the metamethod path are not F1
values of `δ .len`. The prologue saves `ra` at `sp - 8`; the stores of
`R[A]` are a tag byte `3` and the length. The summary is exact in memory
(`olMem`), as the location-list route's logs need.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- `luaV_objlen`'s entry pins: `L`, the slots `ra`, `rb`. -/
abbrev olPre (L r : BitVec 64) (na nb sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x10, L⟩ :: ⟨Register.x11, BitVec.ofNat 64 na⟩ :: ⟨Register.x12, BitVec.ofNat 64 nb⟩ ::
    ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins

/-- **The memory on return**: `ra` saved at `sp - 8`, then `R[A]` the integer
`len`. -/
def olMem (m : Mem) (na sp : Nat) (r : BitVec 64) (len : Nat) : Mem :=
  writeMap8 ((writeMap8 m (sp - 8) (sdData_val r)).insert (na + 8) (stData 1 (0x3#64)))
    na (sdData_val (BitVec.ofNat 64 len))

/-- What `luaV_objlen` needs: `R[B]` a viewed string `ts` apart from the
frame, the slots below the callee frame. -/
structure OlCtx (m : Mem) (na nb sp : Nat) (r : BitVec 64) (ts : Nat) (s : List UInt8) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 64 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  na_lo : tohostAddr + 16 ≤ na
  na_hi : na + 16 + 64 ≤ sp
  na_al : na % 8 = 0
  nb_lo : tohostAddr + 16 ≤ nb
  nb_hi : nb + 16 + 64 ≤ sp
  tag : slotTag m nb = BitVec.ofNat 8 (strTag s)
  val : slotVal m nb = BitVec.ofNat 64 ts
  view : StrView m ts s
  apart : StrApart ts s (sp - 64) sp

/-- A load through `ra`'s save, as the segments state it. -/
theorem ol_ld {m : Mem} {K a x : Nat} {r v : BitVec 64} (hK : x + 8 ≤ K ∨ K + 8 ≤ x) (ha : a = x)
    (hv : bytesT8 m x = v) :
    sign_extend (m := 64) (bytesT8 (writeMap8 m K (sdData_val r)) a : BitVec (8 * 8)) = v := by
  subst ha; rw [sext64_id, bytesT8_wm8_out hK, hv]

theorem ol_ld0 {m : Mem} {a x : Nat} {v : BitVec 64} (ha : a = x) (hv : bytesT8 m x = v) :
    sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)) = v := by
  subst ha; rw [sext64_id, hv]

/-- The string's length word (`u.lnglen`) through `ra`'s save. -/
theorem ol_lng {m : Mem} {K a ts : Nat} {r : BitVec 64} {s : List UInt8} (hv : StrView m ts s)
    (hl : maxShortLen < s.length) (hK : ts + 16 + 8 ≤ K ∨ K + 8 ≤ ts + 16) (ha : a = ts + 16) :
    sign_extend (m := 64) (bytesT8 (writeMap8 m K (sdData_val r)) a : BitVec (8 * 8)) =
      BitVec.ofNat 64 s.length :=
  ol_ld hK ha (hv.lnglen hl)

/-- The string's length byte (`shrlen`) through `ra`'s save. -/
theorem ol_shr {m : Mem} {K a ts : Nat} {r : BitVec 64} {s : List UInt8} (hv : StrView m ts s)
    (hl : ¬ maxShortLen < s.length) (hK : ts + 11 < K ∨ K + 8 ≤ ts + 11) (ha : a = ts + 11) :
    zero_extend (m := 64) (bytesT1 (writeMap8 m K (sdData_val r)) a : BitVec (8 * 1)) =
      BitVec.ofNat 64 s.length := by
  subst ha
  rw [bytesT1_writeMap8_out m K (sdData_val r) (by omega)]
  have e := hv.shrlen
  simp only [tstringShrlenOff, hl, ↓reduceIte] at e
  rw [e]
  have : s.length < 256 := by simp only [maxShortLen] at hl; omega
  apply BitVec.eq_of_toNat_eq
  simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt this]

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
    | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, bytesT1_writeMap8_out,
        htag, hst]
       decide)
    | (simp (disch := kit_disch) only [bytesT8_ins]
       rw [ld_ra, Vsa.Sim.ret_tgt _ hra]; exact hra)
    | (simp (disch := kit_disch) only [ol_ld (x := nb) (hv := hval), ol_ld0 (x := nb) (hv := hval)]; kit_disch))

theorem olMem_eq {m : Mem} {na sp k1 k2 k3 : Nat} {r d : BitVec 64} {len : Nat} (h1 : k1 = sp - 8) (h2 : k2 = na + 8)
    (h3 : k3 = na) (hd : d = BitVec.ofNat 64 len) :
    writeMap8 ((writeMap8 m k1 (sdData_val r)).insert k2 (stData 1 (0x3#64))) k3 (sdData_val d) =
      olMem m na sp r len := by
  subst h1 h2 h3 hd; rfl

set_option hygiene false in
/-- The return: `ra` read back through the tag store, `sp` restored, the
memory `olMem`. -/
local macro "ol_ret " lem:ident : tactic => `(tactic| (
  have hk1 : (BitVec.ofNat 64 sp + sign_extend (m := 64) 4048#12 + sign_extend (m := 64) 40#12).toNat = sp - 8 := by
    kit_disch
  simp (disch := kit_disch) only [bytesT8_ins] at h
  simp (disch := kit_disch) only [ol_ld (x := nb) (hv := hval), ol_ld0 (x := nb) (hv := hval),
    $lem:ident hx.view hl] at h
  rw [ld_ra, Vsa.Sim.ret_tgt _ hra, sp_back] at h
  rw [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x003#12)) = 0x3#64 by decide] at h
  exact ⟨_, acc, (h.repin (by pins_of h)).mem_eq (olMem_eq hk1 (by kit_disch) (by kit_disch) rfl)⟩))

theorem objlen_long (L r : BitVec 64) (na nb sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (ts : Nat) (s : List UInt8) (hx : OlCtx m na nb sp r ts s) (hl : maxShortLen < s.length) :
    Triple (SegSt 0x8001bae0#64 (olPre L r na nb sp f) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (olMem m na sp r s.length) o)) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := hx.ra; have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.na_lo
  have := hx.na_hi; have := hx.nb_lo; have := hx.nb_hi; have := hx.na_al
  have := hx.view.lo; have := hx.view.hi; have hap := hx.apart
  simp only [StrApart, DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at *
  have hst : strTag s = vLngStr := by unfold strTag; simp only [Nat.not_le.mpr hl, ite_false]
  have htag : bytesT1 m (nb + 8) = BitVec.ofNat 8 (strTag s) := hx.tag
  have hval : bytesT8 m nb = BitVec.ofNat 64 ts := by have := hx.val; simpa [slotVal, tvalueValOff] using this
  kit_seg h acc Lua.Vm.Arms.seg_8001bae0_8001bb04_n
  kit_seg h acc Lua.Vm.Arms.seg_8001bb04_8001bb0c_t
  kit_seg h acc Lua.Vm.Arms.seg_8001bb58_8001bb78
  ol_ret ol_lng

set_option hygiene false in
/-- The prologue's facts. -/
local macro "ol_pre" : tactic => `(tactic| (
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := hx.ra; have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.na_lo
  have := hx.na_hi; have := hx.nb_lo; have := hx.nb_hi; have := hx.na_al
  have := hx.view.lo; have := hx.view.hi; have hap := hx.apart
  simp only [StrApart, DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at *
  have htag : bytesT1 m (nb + 8) = BitVec.ofNat 8 (strTag s) := hx.tag
  have hval : bytesT8 m nb = BitVec.ofNat 64 ts := by have := hx.val; simpa [slotVal, tvalueValOff] using this))

theorem objlen_short (L r : BitVec 64) (na nb sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (ts : Nat) (s : List UInt8) (hx : OlCtx m na nb sp r ts s) (hl : ¬ maxShortLen < s.length) :
    Triple (SegSt 0x8001bae0#64 (olPre L r na nb sp f) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (olMem m na sp r s.length) o)) := by
  ol_pre
  have hst : strTag s = vShrStr := by unfold strTag; simp only [Nat.not_lt.mp hl, ite_true]
  kit_seg h acc Lua.Vm.Arms.seg_8001bae0_8001bb04_n
  kit_seg h acc Lua.Vm.Arms.seg_8001bb04_8001bb0c_n
  kit_seg h acc Lua.Vm.Arms.seg_8001bb0c_8001bb14_t
  kit_seg h acc Lua.Vm.Arms.seg_8001bbb8_8001bbd8
  ol_ret ol_shr

/-- **`luaV_objlen` on a string, the call-node summary**: `R[A] := #s`, the
memory `olMem` (`ra`'s save and the integer). -/
theorem objlen_sum (L r : BitVec 64) (na nb sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (ts : Nat) (s : List UInt8) (hx : OlCtx m na nb sp r ts s) :
    Triple (SegSt 0x8001bae0#64 (olPre L r na nb sp f) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (olMem m na sp r s.length) o)) :=
  if hl : maxShortLen < s.length then objlen_long L r na nb sp f m o ts s hx hl
  else objlen_short L r na nb sp f m o ts s hx hl

end Lua.Vm.Sim.Kit
