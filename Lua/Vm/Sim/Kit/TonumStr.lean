import Lua.Vm.Sim.Kit.TointF
import Lua.Vm.Sim.Kit.Str2int
import Lua.Vm.Sim.Kit.Str
import Lua.Vm.Sim.Kit.AtFloat
import Lua.Vm.AtF.TonumSS
import Lua.Vm.AtF.TonumSL
import Lua.Vm.AtF.TointSS
import Lua.Vm.AtF.TointSL

/-!
# `luaV_tonumber_` and `luaV_tointeger` on a string integer numeral (lane F1-F9)

`l_strton` (`lvm.c:91`, inlined in both): on a string `TValue` (`tt & 15 =
4`), `luaO_str2num(getstr(ts), &v)` and the size test `== tsslen(ts) + 1`;
then `luaV_tonumber_` converts `v` (`__floatdidf` of the integer) and
`luaV_tointeger` reads it (`luaV_tointegerns` on an integer: `*p = i`).

The machine side is the generated callee-context at-lemmas
(`Lua/Vm/AtF/Tonum{SS,SL}.lean`, `Lua/Vm/AtF/Toint{SS,SL}.lean`: a short and
a long string each, `scripts/gen_lua_at.py --fn`), whose root after the call
is `luaO_str2num`'s return; the call is spliced by `str2num_int`
(`Kit/Str2int.lean`) on a string `Lua.Num.str2int` accepts. The string is
live (`StrView`) and apart from the callee frames.

The summaries (`tons_sum`, `tois_sum`) state the answer and the memory: the
callee frames `[sp - 80, sp)` patched (`tonsW`, `toisW`: the generated
memories of the run), then `*q`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

-- the lifted functions are compared by their arguments, never unfolded
attribute [local irreducible] Lua.Vm.Fn.Floatdidf.F Lua.Vm.Fn.Floatdidf.Fm

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-- **The context of the string at-lemmas** (`gen_lua_at.py`'s `tons`,
`tois`): `sp`, the `TValue`, the out-parameter, the `TString`, its length;
`ra`, the caller's `s0`–`s11`, the integer, the mode. -/
abbrev tsCx (r : BitVec 64) (n q sp ts len : Nat) (f : HFrame) (v md : BitVec 64) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, n, q, ts, len]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, v, md] m o

/-- **A string `TValue` at `n`**: its `TString` `ts` holds `s`, live and
apart from the callee frames `[sp - 80, sp)`. -/
structure TsCtx (m : Mem) (n ts sp : Nat) (s : List UInt8) : Prop where
  ptr : slotVal m n = BitVec.ofNat 64 ts
  tag : slotTag m n = BitVec.ofNat 8 (strTag s)
  view : StrView m ts s
  apart : StrApart ts s (sp - 80) sp

/-- A live string's bytes as `luaO_str2num` reads them (`Kit.StrAt`). -/
theorem _root_.Lua.Vm.Sim.StrView.kstr {m : Mem} {ts : Nat} {s : List UInt8} (h : StrView m ts s) :
    Lua.Vm.Sim.Kit.StrAt m (ts + tstringContentsOff) s where
  byte k hk := by
    rcases Nat.lt_or_ge k s.length with hk' | hk'
    · rw [h.bytes k hk']
      simp only [sb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, UInt8.toNat_toBitVec]
      exact Nat.mod_eq_of_lt (s[k]'hk').toNat_lt
    · have e : k = s.length := by omega
      subst e; rw [h.term, sb_len]
  lo := by have := h.lo; have hTH : tohostAddr = 0x8005c6c0 := rfl; simp only [tstringContentsOff]; omega
  hi := by have := h.lo; simp only [tstringContentsOff]; omega
  top := by
    have := h.hi
    simp only [DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at *
    omega

/-! ## `luaV_tonumber_` -/

/-- The callee frames of `luaV_tonumber_` on a string integer numeral
(`[sp - 80, sp)`: `ra`, the out-parameter's address, the `TString`, the
result `TValue` `luaO_str2num` stores, `__floatdidf`'s frame). -/
noncomputable def tonsW (r : BitVec 64) (n q sp : Nat) (m : Mem) (v : BitVec 64) : Mem :=
  Lua.Vm.AtF.TonumSS.m3 (FCx.mk' [sp, n, q] [r, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, v]
    (s2Mem (Lua.Vm.AtF.TonumSS.m1 (FCx.mk' [sp, n, q, (bytesT8 m n).toNat] [r] m #[])) (sp - 32) v) #[])


/-- A short string's length byte, zero-extended. -/
theorem zext_len8 {k : Nat} (h : k < 256) :
    zero_extend (m := 64) ((BitVec.ofNat 8 k : BitVec 8) : BitVec (8 * 1)) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem ofNat_add1 (k : Nat) :
    BitVec.ofNat 64 k + sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (k + 1) := by
  rw [show sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add_ofNat]

theorem s2_tag3 : (stData 1 (3#64) : BitVec 8) = 0x3#8 := by decide

set_option hygiene false in
/-- The live string through the frame stores of the path (`StrView.wm8`,
`.ins`: each store inside `[sp - 80, sp)`). -/
macro "ts_view" : tactic => `(tactic| (
  repeat (first
    | with_reducible exact hw
    | (refine StrView.wm8 ?_ hap (by omega) (by omega) _)
    | (refine StrView.frame ?_ fun x hx => ?_
       · exact hw
       · simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff] at hx
         simp only [bytesT1, getElem?_insert_out (show x ≠ _ by omega)]))))

set_option hygiene false in
/-- The size test's reads of the live string `hw2` in the post-call memory
`M` (`tsslen`): a short string's `shrlen` (not `0xff`, and `len + 1` after
the increment), or a long string's `0xff` and `lnglen`. -/
macro "ts_len " M:term : tactic => `(tactic| (
  first
  | (have hlen : bytesT1 $M (ts + 11) = BitVec.ofNat 8 s.length := by
      have := hw2.shrlen
      simp only [tstringShrlenOff, maxShortLen, show ¬ 40 < s.length by omega, ↓reduceIte] at this
      exact this
     have hg_5 : (zero_extend (m := 64) (bytesT1 $M (ts + 11) : BitVec (8 * 1)) != 0xff#64) = true := by
      rw [hlen, zext_len8 (by omega), show (0xff#64 : BitVec 64) = BitVec.ofNat 64 255 from rfl,
        fbne (by omega) (by omega)]
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
     have hg_6 : (zero_extend (m := 64) (bytesT1 $M (ts + 11) : BitVec (8 * 1)) == 0xff#64) = false := by
      rw [hlen, zext_len8 (by omega), show (0xff#64 : BitVec 64) = BitVec.ofNat 64 255 from rfl,
        fbeq (by omega) (by omega)]
      simp only [decide_eq_false_iff_not]; omega
     have hg_2 : ((BitVec.ofNat 64 (s.length + 1)) != ((zero_extend (m := 64)
        (bytesT1 $M (ts + 11) : BitVec (8 * 1))) + sign_extend (m := 64) (0x001#12))) = false := by
      rw [hlen, zext_len8 (by omega), ofNat_add1]; simp)
  | (have hcl1 : bytesT1 $M (ts + 11) = 0xff#8 := by
      have := hw2.shrlen
      simp only [tstringShrlenOff, maxShortLen, show 40 < s.length by omega, ↓reduceIte] at this
      exact this
     have hcl2 : bytesT8 $M (ts + 16) = BitVec.ofNat 64 s.length := by
      have := hw2.lnglen (by simp only [maxShortLen]; omega)
      simpa only [tstringLnglenOff] using this
     have hg_2 : ((BitVec.ofNat 64 (s.length + 1)) != ((bytesT8 $M (ts + 16)) +
        sign_extend (m := 64) (0x001#12))) = false := by
      rw [hcl2, ofNat_add1]; simp)))

set_option hygiene false in
/-- The string summaries' set-up: the context's facts, the frame
destructured, the live string's bounds, the tag and pointer as root facts. -/
macro "ts_setup" : tactic => `(tactic| (
  intro c h
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  obtain ⟨hp, ht, hw, hap⟩ := hs
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hwl := hw.lo; have hwh := hw.hi; have hap' := hap
  simp only [DlHeap.heapEnd, symHeapEnd, tstringContentsOff, StrApart] at hwh hap'
  obtain ⟨sp', gp', s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [HFrame.pins] at h hsp hgp ⊢
  subst hsp hgp
  have acc := Steps.refl c
  have hc1 : bytesT8 m n = BitVec.ofNat 64 ts := by simpa only [slotVal, tvalueValOff, Nat.add_zero] using hp))

set_option hygiene false in
/-- The tag as a root fact, by the string's kind (`hsh`). -/
macro "ts_tag" : tactic => `(tactic| (
  first
  | (have hc0 : bytesT1 m (n + 8) = 0x44#8 := by
      have := ht; simp only [slotTag, tvalueTagOff, strTag, hsh, ↓reduceIte, vShrStr] at this; exact this)
  | (have hc0 : bytesT1 m (n + 8) = 0x54#8 := by
      have := ht; simp only [slotTag, tvalueTagOff, strTag, hsh, ↓reduceIte, vLngStr] at this; exact this)
  simp only [maxShortLen] at hsh))

set_option hygiene false in
/-- **`tons_go ns`**: `luaV_tonumber_`'s string path over the at-lemmas of
`ns` (`TonumSS`, `TonumSL`), after `ts_setup`: the run to the call,
`str2num_int` spliced in, the root after it, the run to the return, the
memory (`tonsW`, `__floatdidf`'s answer). -/
macro "tons_go " ns:ident : tactic => `(tactic| (
  have hX : $(Lean.mkIdent (ns.getId ++ `Ok)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64,
      s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0 m o) := by fcx_ok
  have h : SegSt 0x8001ab58#64 ($(Lean.mkIdent (ns.getId ++ `r0)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp,
      0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0 m o))
      (ArmPay (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8,
        s9, s10, s11⟩ v 0 m o).m (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3,
        s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0 m o).o) c :=
    h.repin (by pins_of h)
  fat_run $ns h acc until [0x80011998]
  fcx_unfold at h
  -- `luaO_str2num(getstr(ts), &v)`: `str2num_int`
  have hw1 : StrView (writeMap8 (writeMap8 (writeMap8 m (sp - 8) (sdData_val r)) (sp - 40)
      (sdData_val (BitVec.ofNat 64 q))) (sp - 48) (sdData_val (BitVec.ofNat 64 ts))) ts s := by ts_view
  have hro1 : RodataRead (writeMap8 (writeMap8 (writeMap8 m (sp - 8) (sdData_val r)) (sp - 40)
      (sdData_val (BitVec.ofNat 64 q))) (sp - 48) (sdData_val (BitVec.ofNat 64 ts))) := by
    refine Lua.Vm.Sim.RodataRead.wm8 (Lua.Vm.Sim.RodataRead.wm8 (Lua.Vm.Sim.RodataRead.wm8 hro ?_) ?_) ?_ <;> omega
  obtain ⟨c2, s2', h2⟩ := str2num_int (ts + 24) (sp - 32) s 0x8001abc4#64
    ⟨BitVec.ofNat 64 (sp - 48), 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ _ o
    ⟨hro1, hw1.kstr, by decide, by omega, by omega, by omega⟩ hv _ (h.repin (by pins_of h))
  have acc := acc.trans s2'
  -- the root after the call
  generalize hM1 : writeMap8 (writeMap8 (writeMap8 m (sp - 8) (sdData_val r)) (sp - 40)
      (sdData_val (BitVec.ofNat 64 q))) (sp - 48) (sdData_val (BitVec.ofNat 64 ts)) = M1 at hw1 hro1 h2
  have hw2 : StrView (s2Mem M1 (sp - 32) v) ts s :=
    (hw1.wm8 (a := sp - 32) hap (by omega) (by omega) (sdData_val v)).frame fun x hx => by
      simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff] at hx
      simp only [bytesT1, getElem?_insert_out (show x ≠ sp - 32 + 8 by omega)]
  have hro2 : RodataRead (s2Mem M1 (sp - 32) v) :=
    Lua.Vm.Sim.At.RodataRead.ins (Lua.Vm.Sim.RodataRead.wm8 hro1 (by omega)) (by omega)
  have hY : $(Lean.mkIdent (ns.getId ++ `Ok)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64,
      s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0 (s2Mem M1 (sp - 32) v) o) := by fcx_ok
  simp only [s2Post, HFrame.pins] at h2
  have h : SegSt 0x8001abc4#64 ($(Lean.mkIdent (ns.getId ++ `r3)) (tsCx r n q sp ts s.length
      ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0
      (s2Mem M1 (sp - 32) v) o))
      (ArmPay (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8,
        s9, s10, s11⟩ v 0 (s2Mem M1 (sp - 32) v) o).m (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp,
        0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v 0 (s2Mem M1 (sp - 32) v) o).o) c2 :=
    h2.repin (by pins_of h2)
  have hc2 : bytesT8 (s2Mem M1 (sp - 32) v) (sp - 48) = BitVec.ofNat 64 ts := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc3 : bytesT8 (s2Mem M1 (sp - 32) v) (sp - 40) = BitVec.ofNat 64 q := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc4 : bytesT8 (s2Mem M1 (sp - 32) v) (sp - 8) = r := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc5 : bytesT1 (s2Mem M1 (sp - 32) v) (sp - 24) = 0x3#8 := by rw [fw1_same (by omega), s2_tag3]
  have hc6 : bytesT8 (s2Mem M1 (sp - 32) v) (sp - 32) = v := by
    simp (disch := omega) only [fw8_ins, fw8_same]
  ts_len (s2Mem M1 (sp - 32) v)
  fat_run $ns h acc
  fcx_unfold at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h (by pins_of h)).mem_eq ?_⟩
  have hsf : FnSp (sp - 48) 32 := ⟨by omega, by omega, by omega⟩
  rw [Lua.Vm.Fn.Floatdidf.spec_proved _ _ _ _ hsf]
  subst hM1
  have e : tonsW r n q sp m v = memPatch (writeMap8 (s2Mem (writeMap8 (writeMap8 (writeMap8 m (sp - 8)
      (sdData_val r)) (sp - 40) (sdData_val (BitVec.ofNat 64 q))) (sp - 48) (sdData_val (BitVec.ofNat 64 ts)))
      (sp - 32) v) (sp - 48) (sdData_val (BitVec.ofNat 64 q))) (Lua.Vm.Fn.Floatdidf.Fm (writeMap8 (s2Mem
      (writeMap8 (writeMap8 (writeMap8 m (sp - 8) (sdData_val r)) (sp - 40) (sdData_val (BitVec.ofNat 64 q)))
      (sp - 48) (sdData_val (BitVec.ofNat 64 ts))) (sp - 32) v) (sp - 48) (sdData_val (BitVec.ofNat 64 q)))
      (sp - 48) 0x8001ac0c#64 v) (sp - 80) 32 := by
    simp only [tonsW, at_row, FCx.mk', List.getD_cons_zero, List.getD_cons_succ, hc1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show ts < 2 ^ 64 by omega)]
  rw [e, memPatch_of_out (m := m) (lo := sp - 80) (n := 80) (fun x hx => by
    repeat rw [getElem?_memPatch_out (by omega)]
    simp (disch := omega) only [getElem?_writeMap8_out, getElem?_insert_out])]))

/-- **`luaV_tonumber_` on a string integer numeral, the call-node summary**:
`a0 = 1`, the callee frames `tonsW`, `*q` the converted integer
(`__floatdidf`). -/
abbrev TonsSum (n q sp : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String) (v : BitVec 64) :
    Prop :=
  Triple (SegSt 0x8001ab58#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
      ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
    (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
      (ArmPay (writeMap8 (memPatch m (tonsW r n q sp m v) (sp - 80) 80) q
        (sdData_val (Lua.Vm.Fn.Floatdidf.S v))) o))

/-- `TonsSum` on a short string (`TonumSS`); one declaration per kind, the
heartbeat budget being per declaration. -/
theorem tons_short (n q sp ts : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v)
    (hsh : s.length ≤ maxShortLen) : TonsSum n q sp r f m o v := by
  ts_setup; ts_tag; tons_go Lua.Vm.AtF.TonumSS

/-- `TonsSum` on a long string (`TonumSL`). -/
theorem tons_long (n q sp ts : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v)
    (hsh : ¬ s.length ≤ maxShortLen) : TonsSum n q sp r f m o v := by
  ts_setup; ts_tag; tons_go Lua.Vm.AtF.TonumSL

/-- **`luaV_tonumber_` on a string integer numeral**, either kind. -/
theorem tons_sum (n q sp ts : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v) :
    TonsSum n q sp r f m o v :=
  if hsh : s.length ≤ maxShortLen then tons_short n q sp ts s r f m o hx hsp hgp hs hv hsh
  else tons_long n q sp ts s r f m o hx hsp hgp hs hv hsh

/-! ## `luaV_tointeger` -/

/-- The callee frame of `luaV_tointeger` on a string integer numeral
(`[sp - 80, sp)`: the caller's `s1`, `ra`, the `TValue`, the mode, the
`TString`, the result `TValue` `luaO_str2num` stores). -/
def toisW (r s1 md : BitVec 64) (n q sp : Nat) (m : Mem) (v : BitVec 64) : Mem :=
  s2Mem (Lua.Vm.AtF.TointSS.m1 (FCx.mk' [sp, n, q, (bytesT8 m n).toNat]
    [r, 0, s1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, md] m #[])) (sp - 48) v

set_option hygiene false in
/-- **`tois_go ns`**: `luaV_tointeger`'s string path over the at-lemmas of
`ns` (`TointSS`, `TointSL`), after `ts_setup`: as `tons_go`, the frame
`[sp - 80, sp)` and the integer stored at `q`. -/
macro "tois_go " ns:ident : tactic => `(tactic| (
  have hX : $(Lean.mkIdent (ns.getId ++ `Ok)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64,
      s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v md m o) := by fcx_ok
  have h : SegSt 0x8001ade8#64 ($(Lean.mkIdent (ns.getId ++ `r0)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp,
      0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v md m o))
      (ArmPay (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8,
        s9, s10, s11⟩ v md m o).m (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3,
        s4, s5, s6, s7, s8, s9, s10, s11⟩ v md m o).o) c :=
    h.repin (by pins_of h)
  fat_run $ns h acc until [0x80011998]
  fcx_unfold at h
  have hw1 : StrView (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp - 24) (sdData_val s1))
      (sp - 8) (sdData_val r)) (sp - 64) (sdData_val (BitVec.ofNat 64 n))) (sp - 56) (sdData_val md))
      (sp - 72) (sdData_val (BitVec.ofNat 64 ts))) ts s := by ts_view
  have hro1 : RodataRead (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp - 24) (sdData_val s1))
      (sp - 8) (sdData_val r)) (sp - 64) (sdData_val (BitVec.ofNat 64 n))) (sp - 56) (sdData_val md))
      (sp - 72) (sdData_val (BitVec.ofNat 64 ts))) := by
    refine Lua.Vm.Sim.RodataRead.wm8 (Lua.Vm.Sim.RodataRead.wm8 (Lua.Vm.Sim.RodataRead.wm8
      (Lua.Vm.Sim.RodataRead.wm8 (Lua.Vm.Sim.RodataRead.wm8 hro ?_) ?_) ?_) ?_) ?_ <;> omega
  obtain ⟨c2, s2', h2⟩ := str2num_int (ts + 24) (sp - 48) s 0x8001ae68#64
    ⟨BitVec.ofNat 64 (sp - 80), 0x8005ced0#64, s0, BitVec.ofNat 64 q, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    _ o ⟨hro1, hw1.kstr, by decide, by omega, by omega, by omega⟩ hv _ (h.repin (by pins_of h))
  have acc := acc.trans s2'
  generalize hM1 : writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp - 24) (sdData_val s1))
      (sp - 8) (sdData_val r)) (sp - 64) (sdData_val (BitVec.ofNat 64 n))) (sp - 56) (sdData_val md))
      (sp - 72) (sdData_val (BitVec.ofNat 64 ts)) = M1 at hw1 hro1 h2
  have hw2 : StrView (s2Mem M1 (sp - 48) v) ts s :=
    (hw1.wm8 (a := sp - 48) hap (by omega) (by omega) (sdData_val v)).frame fun x hx => by
      simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff] at hx
      simp only [bytesT1, getElem?_insert_out (show x ≠ sp - 48 + 8 by omega)]
  have hro2 : RodataRead (s2Mem M1 (sp - 48) v) :=
    Lua.Vm.Sim.At.RodataRead.ins (Lua.Vm.Sim.RodataRead.wm8 hro1 (by omega)) (by omega)
  have hY : $(Lean.mkIdent (ns.getId ++ `Ok)) (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64,
      s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v md (s2Mem M1 (sp - 48) v) o) := by fcx_ok
  simp only [s2Post, HFrame.pins] at h2
  have h : SegSt 0x8001ae68#64 ($(Lean.mkIdent (ns.getId ++ `r3)) (tsCx r n q sp ts s.length
      ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v md
      (s2Mem M1 (sp - 48) v) o))
      (ArmPay (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8,
        s9, s10, s11⟩ v md (s2Mem M1 (sp - 48) v) o).m (tsCx r n q sp ts s.length ⟨BitVec.ofNat 64 sp,
        0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ v md (s2Mem M1 (sp - 48) v) o).o) c2 :=
    h2.repin (by pins_of h2)
  have hc2 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 72) = BitVec.ofNat 64 ts := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc3 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 64) = BitVec.ofNat 64 n := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc4 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 56) = md := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc5 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 8) = r := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc6 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 24) = s1 := by
    subst hM1; simp (disch := omega) only [fw8_ins, fw8_wm8, fw8_same]
  have hc7 : bytesT1 (s2Mem M1 (sp - 48) v) (sp - 40) = 0x3#8 := by rw [fw1_same (by omega), s2_tag3]
  have hc8 : bytesT8 (s2Mem M1 (sp - 48) v) (sp - 48) = v := by
    simp (disch := omega) only [fw8_ins, fw8_same]
  ts_len (s2Mem M1 (sp - 48) v)
  fat_run $ns h acc
  fcx_unfold at h
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h (by pins_of h)).mem_eq ?_⟩
  subst hM1
  have e : toisW r s1 md n q sp m v = s2Mem (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp - 24)
      (sdData_val s1)) (sp - 8) (sdData_val r)) (sp - 64) (sdData_val (BitVec.ofNat 64 n))) (sp - 56)
      (sdData_val md)) (sp - 72) (sdData_val (BitVec.ofNat 64 ts))) (sp - 48) v := by
    simp only [toisW, at_row, FCx.mk', List.getD_cons_zero, List.getD_cons_succ, hc1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show ts < 2 ^ 64 by omega)]
  rw [e, memPatch_of_out (m := m) (lo := sp - 80) (n := 80) (fun x hx => by
    simp (disch := omega) only [getElem?_writeMap8_out, getElem?_insert_out])]))

/-- **`luaV_tointeger` on a string integer numeral, the call-node summary**:
`a0 = 1`, the callee frame `toisW`, `*q` the integer (whatever the mode). -/
abbrev ToisSum (n q sp : Nat) (r md : BitVec 64) (f : HFrame) (m : Mem) (o : Array String) (v : BitVec 64) :
    Prop :=
  Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
      ⟨Register.x12, md⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
    (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
      (ArmPay (writeMap8 (memPatch m (toisW r f.s1 md n q sp m v) (sp - 80) 80) q (sdData_val v)) o))

/-- `ToisSum` on a short string (`TointSS`). -/
theorem tois_short (n q sp ts : Nat) (s : List UInt8) (r md : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v)
    (hsh : s.length ≤ maxShortLen) : ToisSum n q sp r md f m o v := by
  ts_setup; ts_tag; tois_go Lua.Vm.AtF.TointSS

/-- `ToisSum` on a long string (`TointSL`). -/
theorem tois_long (n q sp ts : Nat) (s : List UInt8) (r md : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v)
    (hsh : ¬ s.length ≤ maxShortLen) : ToisSum n q sp r md f m o v := by
  ts_setup; ts_tag; tois_go Lua.Vm.AtF.TointSL

/-- **`luaV_tointeger` on a string integer numeral**, either kind. -/
theorem tois_sum (n q sp ts : Nat) (s : List UInt8) (r md : BitVec 64) (f : HFrame) (m : Mem)
    (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (hs : TsCtx m n ts sp s) {v : BitVec 64} (hv : str2int s = some v) :
    ToisSum n q sp r md f m o v :=
  if hsh : s.length ≤ maxShortLen then tois_short n q sp ts s r md f m o hx hsp hgp hs hv hsh
  else tois_long n q sp ts s r md f m o hx hsp hgp hs hv hsh

end Lua.Vm.Sim.Kit
