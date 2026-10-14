import Lua.Vm.Sim.Kit.EqualobjF
import Lua.Vm.AtF.TointF1
import Lua.Vm.AtF.TointF2
import Lua.Vm.AtF.TonumI

/-!
# `luaV_tointeger` on a float: the call-node summary (lane F1-F8)

`FORPREP`'s `forlimit` calls `luaV_tointeger(lim, &p, mode)` with `mode`
`F2Ifloor` (1, a step `≥ 0`) or `F2Iceil` (2). On a float `lim`
(`LUA_VNUMFLT`), `luaV_tointegerns` → `luaV_flttointeger` is inlined
(`lvm.c:123`): `floor`, `__eqdf2` of the float and its floor, for `F2Iceil`
on a non-integral float `__adddf3(f, 1.0)`, the range against `.rodata`'s
`(double)LUA_MININTEGER` and its negation, `__fixdfdi`, `*p` stored.

The machine side is the generated callee-context at-lemmas
(`Lua/Vm/AtF/TointF{1,2}.lean`, `scripts/gen_lua_at.py --fn`, soft-float call
nodes) run by `fat_walk`; each leaf's answer is the kernel's `flttointeger`
by `tif_res` (the routines' specifications, `floor`'s model, `__fixdfdi`'s
value under the range fact). The summary `toint_flt_sum` states the answer
and the memory: the callee frames `[sp - 192, sp)` patched (`tifW`), then
on success `*q`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

-- the lifted functions are compared by their arguments, never unfolded
attribute [local irreducible] Lua.Vm.Fn.Eqdf2.F Lua.Vm.Fn.Gedf2.F Lua.Vm.Fn.Ledf2.F
  Lua.Vm.Fn.Fixdfdi.F Lua.Vm.Fn.Floor.F Lua.Vm.Fn.Floor.Fm Lua.Vm.Fn.Adddf3.F Lua.Vm.Fn.Adddf3.Fm
  Lua.Vm.Fn.Floatdidf.F Lua.Vm.Fn.Floatdidf.Fm

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-- **The context of `luaV_tointeger`'s float at-lemmas** (`gen_lua_at.py`'s
`tif`): `sp`, the `TValue`, the out-parameter; `ra`, the caller's `s0`–`s11`. -/
abbrev tifCx (r : BitVec 64) (n q sp : Nat) (f : HFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, n, q] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- The facts the float path uses: room for `floor`'s frame below
`luaV_tointeger`'s (`[sp - 192, sp)`), the `TValue` below it, the
out-parameter at or above `sp`. -/
structure TifCtx (m : Mem) (n q sp : Nat) (r : BitVec 64) : Prop where
  ro : RodataRead m
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 192 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  n_lo : tohostAddr + 16 ≤ n
  n_hi : n + 16 + 192 ≤ sp
  q_lo : sp ≤ q
  q_hi : q + 8 ≤ 2 ^ 32
  q_al : q % 8 = 0

/-! ## The kernel's conversion -/

/-- The machine's `mode` argument (`1`: `F2Ifloor`, `2`: `F2Iceil`). -/
def tifMode (md : Nat) : F2Imod := if md = 2 then .ceil else .floor

/-- `luaV_flttointeger`'s float before the range test: the floor, or for
`F2Iceil` on a non-integral float the floor plus `1.0`. -/
def tifG (md : Nat) (x : Float.Model) : Float.Model :=
  if md = 2 ∧ Float.Model.beq x (floor x) = false then Float.Model.add (floor x) (.ofNat 1) else floor x

theorem flttointeger_tif {md : Nat} (hmd : md = 1 ∨ md = 2) (x : Float.Model) :
    flttointeger x (tifMode md) = numberToInteger (tifG md x) := by
  unfold flttointeger tifG tifMode
  rcases hmd with rfl | rfl <;> cases h : Float.Model.beq x (floor x) <;> simp [h]

/-- The answer of the call, on the context. -/
noncomputable def tifRes (md : Nat) (X : FCx) : Option (BitVec 64) :=
  flttointeger (F64.toModel (bytesT8 X.m (X.n 1))) (tifMode md)

/-- The callee frames' contents at the return (the window `[sp - 192, sp)`):
`luaV_tointeger`'s saves and `floor`'s frame, and for `F2Iceil` on a
non-integral float `__adddf3`'s. -/
noncomputable def tifW (md : Nat) (X : FCx) : Mem :=
  if md = 2 then
    (if (Lua.Vm.Fn.Eqdf2.F (bytesT8 X.m (X.n 1)) (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X)
        (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) == 0x0#64) = true
     then Lua.Vm.AtF.TointF2.m2 X else Lua.Vm.AtF.TointF2.m4 X)
  else Lua.Vm.AtF.TointF1.m2 X

/-- **The memory at the return**: the callee frames patched, then `*q` on
success. -/
noncomputable def tifMem (md : Nat) (X : FCx) : Mem :=
  match tifRes md X with
  | some i => writeMap8 (memPatch X.m (tifW md X) (X.n 0 - 192) 192) (X.n 2) (sdData_val i)
  | none => memPatch X.m (tifW md X) (X.n 0 - 192) 192


/-! ## The answer on the machine's tests -/

/-- `lua_numbertointeger` on the machine's tests (`bltz` of `__gedf2` against
`(double)LUA_MININTEGER`, `bgez` of `__ledf2` against its negation,
`__fixdfdi`), for a float `g` whose model is `G`. -/
theorem numberToInteger_m {g : BitVec 64} {G : Float.Model} (hg : F64.toModel g = G) :
    numberToInteger G =
      if zopz0zI_s (Lua.Vm.Fn.Gedf2.F g 0xc3e0000000000000#64) 0x0#64 = true then none
      else if zopz0zKzJ_s (Lua.Vm.Fn.Ledf2.F g 0x43e0000000000000#64) 0x0#64 = true then none
      else some (Lua.Vm.Fn.Fixdfdi.F g) := by
  rw [Lua.Vm.Fn.Gedf2.spec_proved, Lua.Vm.Fn.Ledf2.spec_proved, Lua.Vm.Fn.Fixdfdi.spec_proved,
    At.bltz_gedf2, At.bgez_ledf2, F64.le_eq_model, F64.lt_eq_model, At.toModel_min, At.toModel_max, hg]
  unfold numberToInteger
  cases h1 : Float.Model.le minIntF G <;> cases h2 : Float.Model.lt G minIntF.neg <;>
    simp only [Bool.and_false, Bool.and_true, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.and_self]
  rw [At.fixdfdi_model g (hg ▸ h1), hg]

/-- **Mode 1 (`F2Ifloor`) on the machine's tests**: the floor's range and
conversion. -/
theorem tifRes_1 (X : FCx) (hsp : FnSp (X.n 0 - 80) 112) :
    tifRes 1 X =
      if zopz0zI_s (Lua.Vm.Fn.Gedf2.F (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF1.m1 X) (X.n 0 - 80)
          0x8001aeb0#64 (bytesT8 X.m (X.n 1))) 0xc3e0000000000000#64) 0x0#64 = true then none
      else if zopz0zKzJ_s (Lua.Vm.Fn.Ledf2.F (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF1.m1 X) (X.n 0 - 80)
          0x8001aeb0#64 (bytesT8 X.m (X.n 1))) 0x43e0000000000000#64) 0x0#64 = true then none
      else some (Lua.Vm.Fn.Fixdfdi.F (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF1.m1 X) (X.n 0 - 80)
          0x8001aeb0#64 (bytesT8 X.m (X.n 1)))) := by
  unfold tifRes
  rw [flttointeger_tif (.inl rfl)]
  exact numberToInteger_m (by rw [floor_model hsp]; simp [tifG])

/-- `beqz` on `__eqdf2`. -/
theorem beqz_eqdf2 (a b : BitVec 64) : (Lua.Vm.Fn.Eqdf2.S a b == 0x0#64) = F64.eq a b := by
  unfold Lua.Vm.Fn.Eqdf2.S; cases F64.eq a b <;> decide

/-- **Mode 2 (`F2Iceil`) on the machine's tests**: on an integral float the
floor, else `__adddf3(floor, 1.0)`; its range and conversion. -/
theorem tifRes_2 (X : FCx) (hsp : FnSp (X.n 0 - 80) 112) (hsa : FnSp (X.n 0 - 80) 48) :
    tifRes 2 X =
      if zopz0zI_s (Lua.Vm.Fn.Gedf2.F (if (Lua.Vm.Fn.Eqdf2.F (bytesT8 X.m (X.n 1)) (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) == 0x0#64) = true then Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))
        else Lua.Vm.Fn.Adddf3.F (Lua.Vm.AtF.TointF2.m2 X) (X.n 0 - 80) 0x8001aee8#64 (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) 0x3ff0000000000000#64) 0xc3e0000000000000#64) 0x0#64 = true then none
      else if zopz0zKzJ_s (Lua.Vm.Fn.Ledf2.F (if (Lua.Vm.Fn.Eqdf2.F (bytesT8 X.m (X.n 1)) (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) == 0x0#64) = true then Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))
        else Lua.Vm.Fn.Adddf3.F (Lua.Vm.AtF.TointF2.m2 X) (X.n 0 - 80) 0x8001aee8#64 (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) 0x3ff0000000000000#64) 0x43e0000000000000#64) 0x0#64 = true then none
      else some (Lua.Vm.Fn.Fixdfdi.F (if (Lua.Vm.Fn.Eqdf2.F (bytesT8 X.m (X.n 1)) (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) == 0x0#64) = true then Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))
        else Lua.Vm.Fn.Adddf3.F (Lua.Vm.AtF.TointF2.m2 X) (X.n 0 - 80) 0x8001aee8#64 (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) 0x3ff0000000000000#64)) := by
  unfold tifRes
  rw [flttointeger_tif (.inr rfl)]
  refine numberToInteger_m ?_
  have hfl : F64.toModel (Lua.Vm.Fn.Floor.F (Lua.Vm.AtF.TointF2.m1 X) (X.n 0 - 80) 0x8001aeb0#64 (bytesT8 X.m (X.n 1))) = floor (F64.toModel (bytesT8 X.m (X.n 1))) := floor_model hsp
  rw [Lua.Vm.Fn.Eqdf2.spec_proved, beqz_eqdf2, F64.eq_eq_model, hfl]
  unfold tifG
  cases hb : Float.Model.beq (F64.toModel (bytesT8 X.m (X.n 1))) (floor (F64.toModel (bytesT8 X.m (X.n 1))))
  · simp only [↓reduceIte, Bool.false_eq_true, and_self]
    rw [Lua.Vm.Fn.Adddf3.spec_proved _ _ _ _ _ hsa]
    simp only [Lua.Vm.Fn.Adddf3.S, F64.add_eq_model, At.toModel_toBits, At.toModel_one, hfl]
  · simp only [↓reduceIte, Bool.true_eq_false, and_false, hfl]

/-! ## The window -/

/-- A memory that differs from `m` only inside `[lo, lo + n)` is `m` patched
with itself there. -/
theorem memPatch_of_out {m M : Mem} {lo n : Nat} (h : ∀ x, x < lo ∨ lo + n ≤ x → M[x]? = m[x]?) :
    memPatch m M lo n = M :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch]
    split
    · rfl
    · exact (h x (by omega)).symm

set_option hygiene false in
/-- The window lemma's goal: the leaf's memory off `[sp - 192, sp)` is the
root's (its saves, `floor`'s and `__adddf3`'s frames lie inside). -/
macro "tif_out" : tactic => `(tactic| (
  intro x hx
  simp only [at_row, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] at hx ⊢
  repeat rw [getElem?_memPatch_out (by omega)]
  simp (disch := omega) only [getElem?_writeMap8_out]))

open Lean Elab Tactic Meta in
/-- The path's fork facts `hf_*` as `simp` lemmas. -/
def tifForks : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := withMainContext do
  let mut ms := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.toString.startsWith "hf_" then
      ms := ms.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):term))
  return ms

open Lean Elab Tactic Meta in
/-- **A leaf's answer**: `tifRes` on the machine's tests (`tifRes_1`,
`tifRes_2`), each test by the path's fork facts `hf_*`. -/
elab "tif_res" : tactic => do
  let ms ← tifForks
  let hsp := mkIdent `hsp; let hsa := mkIdent `hsa
  evalTactic (← `(tactic| (
    (first | rw [tifRes_1] | rw [tifRes_2]) <;> (try exact $hsp) <;> (try exact $hsa) <;>
    simp only [$ms,*, ↓reduceIte, Bool.false_eq_true, Option.isSome_some, Option.isSome_none])))

open Lean Elab Tactic Meta in
/-- **A leaf's memory**: `tifMem` by `tif_res`, the window (`tifW`, its
mode-2 fork by the fork facts) by `memPatch_of_out`. -/
elab "tif_mem" : tactic => do
  let ms ← tifForks
  evalTactic (← `(tactic| (
    unfold tifMem
    tif_res
    simp only [tifW, show ((1 : Nat) = 2) = False from by decide, ↓reduceIte, Bool.false_eq_true, $ms,*]
    rw [memPatch_of_out (by tif_out)])))

set_option hygiene false in
/-- **A leaf's close**: the return row (the answer by `tif_res`), the memory
by `tif_mem`. -/
macro "tif_close" : tactic => `(tactic| (
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h ?_).mem_eq ?_⟩
  · pins_of h
  · tif_mem))

/-- The answer as the leaf's `0`/`1` (`pins_of`'s `kit_val`). -/
local macro_rules
  | `(tactic| kit_val) => `(tactic| (tif_res <;> rfl))

/-! ## The two modes -/

set_option hygiene false in
/-- The at-lemmas' context facts and the root facts the float path reads
(the tag, `.rodata`), the callees' frames (`hsp`, `hsa`), `h` at the entry
row, then `fat_walk`. -/
macro "tif_setup " ns:ident : tactic => `(tactic| (
  intro c h
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : $(Lean.mkIdent (ns.getId ++ `Ok)) (tifCx r n q sp f m o) := by fcx_ok
  obtain ⟨sp', gp', s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [HFrame.pins] at h hsp hgp ⊢
  subst hsp hgp
  have h : SegSt 0x8001ade8#64 ($(Lean.mkIdent (ns.getId ++ `r0)) (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o))
      (ArmPay (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o).m (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT1 m (n + 8) = _ := ht
  have hc1 := At.rod_min hro
  have hc2 := At.rod_max hro
  have hc3 := At.rod_one hro
  have hsp : FnSp (sp - 80) 112 := ⟨by omega, by omega, by omega⟩
  have hsa : FnSp (sp - 80) 48 := ⟨by omega, by omega, by omega⟩
  fat_walk $ns h acc))

theorem toint_flt1 (n q sp : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (ht : slotTag m n = 19#8) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x12, 0x1#64⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, if (tifRes 1 (tifCx r n q sp f m o)).isSome then 1#64 else 0#64⟩ :: f.pins)
        (ArmPay (tifMem 1 (tifCx r n q sp f m o)) o)) := by
  tif_setup Lua.Vm.AtF.TointF1
  all_goals tif_close

theorem toint_flt2 (n q sp : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (ht : slotTag m n = 19#8) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x12, 0x2#64⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, if (tifRes 2 (tifCx r n q sp f m o)).isSome then 1#64 else 0#64⟩ :: f.pins)
        (ArmPay (tifMem 2 (tifCx r n q sp f m o)) o)) := by
  tif_setup Lua.Vm.AtF.TointF2
  all_goals tif_close

/-! ## The two outcomes -/

theorem tifMem_some {md : Nat} {X : FCx} {i : BitVec 64} (h : tifRes md X = some i) :
    tifMem md X = writeMap8 (memPatch X.m (tifW md X) (X.n 0 - 192) 192) (X.n 2) (sdData_val i) := by
  simp only [tifMem, h]

theorem tifMem_none {md : Nat} {X : FCx} (h : tifRes md X = none) :
    tifMem md X = memPatch X.m (tifW md X) (X.n 0 - 192) 192 := by
  simp only [tifMem, h]

/-- **`luaV_tointeger` on a float, the call-node summary**: with `mode` 1
or 2, `a0` is whether `flttointeger` converts, the callee frames
`[sp - 192, sp)` are `tifW`'s, and on success `*q` is the integer. -/
theorem toint_flt_sum {md : Nat} (hmd : md = 1 ∨ md = 2) (n q sp : Nat) (r : BitVec 64) (f : HFrame)
    (m : Mem) (o : Array String) (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp)
    (hgp : f.gp = 0x8005ced0#64) (ht : slotTag m n = 19#8) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 md⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, if (tifRes md (tifCx r n q sp f m o)).isSome then 1#64 else 0#64⟩ :: f.pins)
        (ArmPay (tifMem md (tifCx r n q sp f m o)) o)) := by
  rcases hmd with rfl | rfl
  · exact toint_flt1 n q sp r f m o hx hsp hgp ht
  · exact toint_flt2 n q sp r f m o hx hsp hgp ht

/-! ## `luaV_tonumber_` on an integer -/

/-- The callee frames of `luaV_tonumber_` on an integer (`[sp - 80, sp)`:
`ra`, the out-parameter's address, `__floatdidf`'s frame). -/
noncomputable def toniW (X : FCx) : Mem := Lua.Vm.AtF.TonumI.m2 X

/-- **`luaV_tonumber_` on an integer, the call-node summary**: `a0 = 1`,
the callee frames `toniW`, `*q` the converted float (`__floatdidf`). -/
theorem tonum_int_sum (n q sp : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hx : TifCtx m n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (hgp : f.gp = 0x8005ced0#64)
    (ht : slotTag m n = 3#8) :
    Triple (SegSt 0x8001ab58#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins)
        (ArmPay (writeMap8 (memPatch m (toniW (tifCx r n q sp f m o)) (sp - 80) 80) q
          (sdData_val (Lua.Vm.Fn.Floatdidf.S (bytesT8 m n)))) o)) := by
  intro c h
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.TonumI.Ok (tifCx r n q sp f m o) := by fcx_ok
  obtain ⟨sp', gp', s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [HFrame.pins] at h hsp hgp ⊢
  subst hsp hgp
  have h : SegSt 0x8001ab58#64 (Lua.Vm.AtF.TonumI.r0 (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o))
      (ArmPay (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o).m
        (tifCx r n q sp ⟨BitVec.ofNat 64 sp, 0x8005ced0#64, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT1 m (n + 8) = _ := ht
  have hsf : FnSp (sp - 48) 32 := ⟨by omega, by omega, by omega⟩
  fat_walk Lua.Vm.AtF.TonumI h acc
  refine ⟨_, acc, (Vsa.Sim.SegSt.repin h (by pins_of h)).mem_eq ?_⟩
  simp only [toniW]
  rw [memPatch_of_out (by tif_out)]
  fcx_unfold
  rw [Lua.Vm.Fn.Floatdidf.spec_proved _ _ _ _ hsf]

end Lua.Vm.Sim.Kit
