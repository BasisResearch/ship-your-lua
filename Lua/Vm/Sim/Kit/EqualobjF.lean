import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.Sim.Kit.AtFnFlt
import Lua.Vm.AtF.EqobjFF
import Lua.Vm.AtF.EqobjIF
import Lua.Vm.AtF.EqobjFI
import Lua.Vm.Fn.SfRefCmp
import Lua.Vm.Fn.SfRefInt
import Lua.Vm.Fn.SfRefFloorSpec

/-!
# `luaV_equalobj` on its float paths: the call-node summary (lane F1-F4)

`luaV_equalobj(L, t1, t2)` with a float among `t1`, `t2` (`lvm.c:569`):

* two floats: the jump table's `LUA_VNUMFLT` arm (`0x8001b90c`),
  `luai_numeq` by `__eqdf2`;
* an integer and a float, either way (`0x8001b810`): `luaV_tointegerns(F2Ieq)`
  of the float inlined (`floor`, `__eqdf2` of the float and its floor, the
  range against `.rodata`'s `(double)LUA_MININTEGER` and its negation,
  `__fixdfdi`), then the integers compared;
* a float and any other F1 value: different types, `0` (`eqo_diff_gen`).

The machine side of the first three is the generated callee-context
at-lemmas (`Lua/Vm/AtF/Eqobj{FF,IF,FI}.lean`, `scripts/gen_lua_at.py --fn`,
soft-float call nodes) run by `fat_walk` (forks on the routines' answers);
each leaf's answer is the kernel's `eqNum` by `eqf_res` (the routines'
specifications, `floor`'s model (`floorSpec_proved`), `__fixdfdi`'s value under
the range fact). The summary `equalobj_flt_sum` states the answer as
`Value.rawEq` and the memory as `eqfMem` (the callee frames `[sp - 160, sp)`,
`eqfMem_out`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

-- the lifted functions are compared by their arguments, never unfolded
attribute [local irreducible] Lua.Vm.Fn.Eqdf2.F Lua.Vm.Fn.Gedf2.F Lua.Vm.Fn.Ledf2.F
  Lua.Vm.Fn.Fixdfdi.F Lua.Vm.Fn.Floor.F Lua.Vm.Fn.Floor.Fm

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-- **The context of `luaV_equalobj`'s float at-lemmas** (`gen_lua_at.py`'s
`eqf`): `sp`, the two `TValue`s; `ra`, the caller's frame (`KFrame`), `L`. -/
abbrev eqCx (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, n1, n2] [r, f.gp, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s7, f.s8, f.s9, f.s11, L] m o

/-- The facts the float paths use: `EqCtx`'s, with room for `floor`'s frame
below `luaV_equalobj`'s (`[sp - 160, sp)`). -/
structure EqfCtx (m : Mem) (n1 n2 sp : Nat) (r : BitVec 64) : Prop where
  ro : RodataRead m
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 160 ≤ sp
  sp_hi : sp < 2 ^ 32
  sp_al : sp % 8 = 0
  n1_lo : tohostAddr + 16 ≤ n1
  n1_hi : n1 + 16 + 160 ≤ sp
  n2_lo : tohostAddr + 16 ≤ n2
  n2_hi : n2 + 16 + 160 ≤ sp

/-! ## The leaves' answers -/

/-- `seqz` of a difference: the operands equal, as `0`/`1`. -/
theorem seqz_sub (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (a - b) (sign_extend (m := 64) (0x001#12)))) =
      if b = a then 1#64 else 0#64 := by
  have key : zopz0zI_u (a - b) (sign_extend (m := 64) (0x001#12)) = decide (b = a) := by
    unfold zopz0zI_u
    simp only [Sail.BitVec.toNatInt, show (sign_extend (m := 64) (0x001#12)).toNat = 1 by decide]
    apply decide_eq_decide.mpr
    constructor
    · intro h; have : (a - b).toNat < 1 := Int.ofNat_lt.mp h
      bv_omega
    · intro h; subst h; simp
  rw [key]; by_cases h : b = a <;> simp [h] <;> decide

/-- `seqz` of `__eqdf2`: `luai_numeq` as `0`/`1`. -/
theorem seqz_eqdf2 (a b : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (Lua.Vm.Fn.Eqdf2.S a b) (sign_extend (m := 64) (0x001#12)))) =
      if F64.eq a b then 1#64 else 0#64 := by
  unfold Lua.Vm.Fn.Eqdf2.S; cases F64.eq a b <;> decide

/-- `bnez` on `__eqdf2`. -/
theorem bnez_eqdf2 (a b : BitVec 64) : (Lua.Vm.Fn.Eqdf2.S a b != 0x0#64) = !F64.eq a b := by
  unfold Lua.Vm.Fn.Eqdf2.S; cases F64.eq a b <;> decide

/-- The kernel's mixed equality (`luaV_tointegerns(F2Ieq)` of the float):
integral and in range, and the integers equal. -/
theorem eqNum_fi (a : Float.Model) (b : BitVec 64) :
    eqNum (.flt a) (.int b) = (At.f2iOk a && decide (At.f2iVal a = b)) := by
  show (match flttointeger a .eq, some b with | some i, some j => decide (i = j) | _, _ => false) = _
  rw [At.flttointeger_eq]
  by_cases h : At.f2iOk a = true <;> simp only [h, ↓reduceIte, Bool.true_and, Bool.false_and] <;> rfl

theorem eqNum_if (a : BitVec 64) (b : Float.Model) :
    eqNum (.int a) (.flt b) = (At.f2iOk b && decide (a = At.f2iVal b)) := by
  show (match some a, flttointeger b .eq with | some i, some j => decide (i = j) | _, _ => false) = _
  rw [At.flttointeger_eq]
  by_cases h : At.f2iOk b = true <;> simp only [h, ↓reduceIte, Bool.true_and, Bool.false_and] <;> rfl

theorem eqNum_ff (a b : Float.Model) : eqNum (.flt a) (.flt b) = Float.Model.beq a b := rfl

/-- `__fixdfdi` of a value whose model is `A`, in range: `A`'s integer. -/
theorem fix_of_model {x : BitVec 64} {A : Float.Model} (hm : F64.toModel x = A)
    (h : Float.Model.le minIntF A = true) : Lua.Vm.Fn.Fixdfdi.S x = A.toInt64.toBitVec := by
  rw [At.fixdfdi_model x (hm ▸ h), hm]

/-- `floor`'s result model at a frame with room (`floorSpec_proved`), as a rewrite. -/
theorem floor_model {m : Mem} {s : Nat} {r x : BitVec 64} (hs : FnSp s 112) :
    F64.toModel (Lua.Vm.Fn.Floor.F m s r x) = floor (F64.toModel x) :=
  Lua.Vm.Fn.Floor.spec floorSpec_proved m s r x hs

open Lean Elab Tactic Meta in
/-- **A leaf's answer** (`kit_val` here): the machine's `0`/`1` (a constant,
`seqz` of `__eqdf2`, or of the integer against `__fixdfdi`'s) is the
kernel's `eqNum`, from the path's fork facts `hf_*`: the routines'
specifications, `floor`'s model (`floor_model`, its frame by `hsp`), the
range constants, `__fixdfdi`'s value under the range fact (`fix_of_model`). -/
elab "eqf_res" : tactic => withMainContext do
  let mut hs : Array Ident := #[]
  let mut ms : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
    #[← `(Lean.Parser.Tactic.simpLemma| Bool.and_self)]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.toString.startsWith "hf_" then
      hs := hs.push (mkIdent d.userName)
      ms := ms.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):term))
  let hsp := mkIdent `hsp
  evalTactic (← `(tactic| (
    try fcx_unfold at $hs:ident* ⊢
    try simp only [List.getElem_cons_succ, List.getElem_cons_zero]
    try simp only [slotVal, tvalueValOff, Nat.add_zero, eqNum_fi, eqNum_if, eqNum_ff, At.f2iOk, At.f2iVal]
    try simp (disch := exact $hsp) only [Lua.Vm.Fn.Eqdf2.spec_proved, Lua.Vm.Fn.Gedf2.spec_proved,
      Lua.Vm.Fn.Ledf2.spec_proved, Lua.Vm.Fn.Fixdfdi.spec_proved, bnez_eqdf2, At.bltz_gedf2,
      At.bgez_ledf2, seqz_eqdf2, seqz_sub, F64.eq_eq_model, F64.le_eq_model, F64.lt_eq_model,
      At.toModel_min, At.toModel_max, floor_model, Bool.not_eq_true', Bool.not_eq_false']
      at $hs:ident* ⊢
    first
      | done
      | rfl
      | (simp only [$ms,*, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
          Bool.false_eq_true, ↓reduceIte]; done)
      | (rw [fix_of_model (floor_model $hsp) (by simp only [$ms,*])]
         simp only [$ms,*, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
           decide_eq_true_eq]; done))))

/-- The leaf's close: the return row, the answer by `eqf_res` (`pins_of`'s
`kit_val`). -/
local macro_rules | `(tactic| kit_val) => `(tactic| eqf_res)

/-! ## The three float classes -/

set_option hygiene false in
/-- The at-lemmas' context facts and the root facts a float class reads
(the tags, `.rodata`), `floor`'s frame (`hsp`), `h` at the entry row. -/
macro "eqf_setup " ns:ident : tactic => `(tactic| (
  intro c h
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : $(Lean.mkIdent (ns.getId ++ `Ok)) (eqCx L r n1 n2 sp f m o) := by fcx_ok
  have h : SegSt 0x8001b780#64 ($(Lean.mkIdent (ns.getId ++ `r0)) (eqCx L r n1 n2 sp f m o))
      (ArmPay (eqCx L r n1 n2 sp f m o).m (eqCx L r n1 n2 sp f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT1 m (n1 + 8) = _ := ht1
  have hc1 : bytesT1 m (n2 + 8) = _ := ht2
  have hc2 := At.rod_min hro
  have hc3 := At.rod_max hro
  have hsp : FnSp (sp - 48) 112 := ⟨by omega, by omega, by omega⟩
  fat_walk $ns h acc
  all_goals
    try fcx_unfold at h
    exact ⟨_, acc, Vsa.Sim.SegSt.repin h (by pins_of h)⟩))

/-- **A float and an integer** (`0x8001b9b4`). -/
theorem eqo_fi (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqfCtx m n1 n2 sp r) (ht1 : slotTag m n1 = 19#8) (ht2 : slotTag m n2 = 3#8) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if eqNum (.flt (F64.toModel (slotVal m n1))) (.int (slotVal m n2))
          then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (Lua.Vm.AtF.EqobjFI.m2 (eqCx L r n1 n2 sp f m o)) o)) := by
  eqf_setup Lua.Vm.AtF.EqobjFI

/-- **An integer and a float** (`0x8001ba68`). -/
theorem eqo_if (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqfCtx m n1 n2 sp r) (ht1 : slotTag m n1 = 3#8) (ht2 : slotTag m n2 = 19#8) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if eqNum (.int (slotVal m n1)) (.flt (F64.toModel (slotVal m n2)))
          then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (Lua.Vm.AtF.EqobjIF.m2 (eqCx L r n1 n2 sp f m o)) o)) := by
  eqf_setup Lua.Vm.AtF.EqobjIF

/-- **Two floats** (the jump table's `LUA_VNUMFLT` arm, `0x8001b90c`). -/
theorem eqo_ff (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqfCtx m n1 n2 sp r) (ht1 : slotTag m n1 = 19#8) (ht2 : slotTag m n2 = 19#8) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if eqNum (.flt (F64.toModel (slotVal m n1))) (.flt (F64.toModel (slotVal m n2)))
          then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (writeMap8 m (sp - 8) (sdData_val r)) o)) := by
  have hj : bytesT4 m 0x8005335c = 0xfffc85fc#32 :=
    (eqWord_eq hx.ro (v := 19) (by decide)).trans (by decide +kernel)
  eqf_setup Lua.Vm.AtF.EqobjFF

/-! ## The summary -/

/-- **`luaV_equalobj`'s memory at the return on its float paths**: on a
float and an integer either way, its five saves and `floor`'s frame
(`Eqobj{FI,IF}.m2`); else `ra` saved below `sp`. Only `[sp - 160, sp)`
changes (`eqfMem_out`). -/
noncomputable def eqfMem (r s0 : BitVec 64) (n1 n2 sp : Nat) (m : Mem) : Mem :=
  if slotTag m n1 = 19#8 ∧ slotTag m n2 = 3#8 then
    Lua.Vm.AtF.EqobjFI.m2 (eqCx 0 r n1 n2 sp ⟨0, s0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ m #[])
  else if slotTag m n1 = 3#8 ∧ slotTag m n2 = 19#8 then
    Lua.Vm.AtF.EqobjIF.m2 (eqCx 0 r n1 n2 sp ⟨0, s0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ m #[])
  else writeMap8 m (sp - 8) (sdData_val r)

/-- The callee frames are below `sp`: `eqfMem` is `m` outside `[sp - 160, sp)`. -/
theorem eqfMem_out {r s0 : BitVec 64} {n1 n2 sp : Nat} {m : Mem} {x : Nat} (hs : 160 ≤ sp)
    (hx : x < sp - 160 ∨ sp ≤ x) : (eqfMem r s0 n1 n2 sp m)[x]? = m[x]? := by
  unfold eqfMem
  split
  · simp only [Lua.Vm.AtF.EqobjFI.m2, eqCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [getElem?_memPatch_out (by omega)]
    simp (disch := omega) only [getElem?_writeMap8_out]
  split
  · simp only [Lua.Vm.AtF.EqobjIF.m2, eqCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [getElem?_memPatch_out (by omega)]
    simp (disch := omega) only [getElem?_writeMap8_out]
  · exact getElem?_writeMap8_out _ _ _ _ (by omega)

/-- `ra`'s save below `sp` (`eqMem`), its address over `Nat`. -/
theorem eqMem_nat {m : Mem} {sp : Nat} {r : BitVec 64} (h1 : 48 ≤ sp) (h2 : sp < 2 ^ 32) :
    eqMem(m, sp, r) = writeMap8 m (sp - 8) (sdData_val r) := by
  rw [show ((BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x028#12)).toNat
    = sp - 8 by kit_disch]

/-- **`luaV_equalobj`, the float call-node summary**: on two represented
values, one a float, `a0` is `Value.rawEq`'s answer as 0/1 (`eqNum` on
numbers); the memory changes only in the callee frames (`eqfMem`). -/
theorem equalobj_flt_sum (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem)
    (o : Array String) (hx : EqfCtx m n1 n2 sp r) {mo : Mem} {ι : Strs} {v1 v2 : Value}
    (hv1 : ValRepr mo ι (slotTag m n1) (slotVal m n1) v1)
    (hv2 : ValRepr mo ι (slotTag m n2) (slotVal m n2) v2) (hf : ¬ (v1.NotFlt ∧ v2.NotFlt)) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if v1.rawEq v2 then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
        f.pins) (ArmPay (eqfMem r f.s0 n1 n2 sp m) o)) := by
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hs1 := hx.sp_lo; have hs2 := hx.sp_hi; have hs3 := hx.sp_al
  have hc : EqCtx m n1 n2 sp r :=
    ⟨hx.ro, hx.ra, by omega, by omega, by omega, hx.n1_lo, by have := hx.n1_hi; omega, hx.n2_lo,
      by have := hx.n2_hi; omega⟩
  -- an operand: an integer, a float, or another type (raw-unequal to a float)
  have other : ∀ {t : BitVec 8} {x : BitVec 64} {v : Value}, ValRepr mo ι t x v →
      (t = 3#8 ∧ v = .int x) ∨ (t = 19#8 ∧ v = .flt (F64.toModel x) x.msb) ∨
        (t ∈ f1Tags ∧ t ≠ 3#8 ∧ t ≠ 19#8 ∧ v.NotFlt ∧
          ∀ a n, v.rawEq (.flt a n) = false ∧ (Value.flt a n).rawEq v = false) := by
    intro t x v h
    cases h with
    | int => exact .inl ⟨rfl, rfl⟩
    | flt => exact .inr (.inl ⟨rfl, rfl⟩)
    | str => exact .inr (.inr ⟨by rcases strTag_lit _ with e | e <;> rw [e] <;> decide,
        by rcases strTag_lit _ with e | e <;> rw [e] <;> decide,
        by rcases strTag_lit _ with e | e <;> rw [e] <;> decide, (fun _ _ e => by cases e),
        (fun _ _ => by simp [Value.rawEq])⟩)
    | _ => exact .inr (.inr ⟨by decide, by decide, by decide, (fun _ _ e => by cases e),
        (fun _ _ => by simp [Value.rawEq])⟩)
  -- the different-types path (`eqo_diff_gen`) with the memory over `Nat`
  have diff : slotTag m n1 ∈ allTags → slotTag m n2 ∈ allTags → slotTag m n1 ≠ slotTag m n2 →
      ¬ MixTags (slotTag m n1) (slotTag m n2) →
      Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
        (SegSt r (⟨Register.x10, 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
          (ArmPay (writeMap8 m (sp - 8) (sdData_val r)) o)) := fun a b c d c0 h0 =>
    let ⟨c', s', h'⟩ := eqo_diff_gen L r n1 n2 sp f m o hc a b c d c0 h0
    ⟨c', s', h'.mem_eq (eqMem_nat (by omega) (by omega))⟩
  rcases other hv1 with ⟨t1, rfl⟩ | ⟨t1, rfl⟩ | ⟨t1, t1', t1'', hn1, hr1⟩ <;>
  rcases other hv2 with ⟨t2, rfl⟩ | ⟨t2, rfl⟩ | ⟨t2, t2', t2'', hn2, hr2⟩
  · exact absurd ⟨notFlt_int _, notFlt_int _⟩ hf
  · -- an integer and a float
    have hm : eqfMem r f.s0 n1 n2 sp m = Lua.Vm.AtF.EqobjIF.m2 (eqCx L r n1 n2 sp f m o) := by
      rw [eqfMem, if_neg fun e => absurd (t1.symm.trans e.1) (by decide), if_pos ⟨t1, t2⟩]; rfl
    rw [hm]; exact eqo_if L r n1 n2 sp f m o hx t1 t2
  · exact absurd ⟨notFlt_int _, hn2⟩ hf
  · -- a float and an integer
    have hm : eqfMem r f.s0 n1 n2 sp m = Lua.Vm.AtF.EqobjFI.m2 (eqCx L r n1 n2 sp f m o) := by
      rw [eqfMem, if_pos ⟨t1, t2⟩]; rfl
    rw [hm]; exact eqo_fi L r n1 n2 sp f m o hx t1 t2
  · -- two floats
    have hm : eqfMem r f.s0 n1 n2 sp m = writeMap8 m (sp - 8) (sdData_val r) := by
      rw [eqfMem, if_neg fun e => absurd (t2.symm.trans e.2) (by decide),
        if_neg fun e => absurd (t1.symm.trans e.1) (by decide)]
    rw [hm]; exact eqo_ff L r n1 n2 sp f m o hx t1 t2
  · -- a float and another type
    have hm : eqfMem r f.s0 n1 n2 sp m = writeMap8 m (sp - 8) (sdData_val r) := by
      rw [eqfMem, if_neg fun e => t2' e.2, if_neg fun e => t2'' e.2]
    rw [hm, (hr2 _ _).2]
    exact diff (by rw [t1]; decide) (List.mem_cons_of_mem _ t2) (by rw [t1]; exact fun e => t2'' e.symm)
      (by rw [t1]; rintro (⟨e, -⟩ | ⟨-, e⟩) <;> first | exact absurd e (by decide) | exact t2' e)
  · exact absurd ⟨hn1, notFlt_int _⟩ hf
  · -- another type and a float
    have hm : eqfMem r f.s0 n1 n2 sp m = writeMap8 m (sp - 8) (sdData_val r) := by
      rw [eqfMem, if_neg fun e => t1'' e.1, if_neg fun e => t1' e.1]
    rw [hm, (hr1 _ _).1]
    exact diff (List.mem_cons_of_mem _ t1) (by rw [t2]; decide) (by rw [t2]; exact t1'')
      (by rw [t2]; rintro (⟨e, -⟩ | ⟨e, -⟩) <;> first | exact t1' e | exact t1'' e)
  · exact absurd ⟨hn1, hn2⟩ hf

end Lua.Vm.Sim.Kit
