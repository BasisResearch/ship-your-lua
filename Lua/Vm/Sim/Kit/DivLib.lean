import Lua.Vm.Sim.Kit.Moddi3
import Lua.Vm.Sim.Kit.DivBits
import Lua.Vm.Sim.Kit.ModEq
import Lua.Vm.Sim.Kit.K

/-!
# The kit's division arms (`luaV_mod`, `luaV_idiv` inlined)

`OP_MOD`/`OP_MODK`/`OP_IDIV`/`OP_IDIVK` share one shape: both operands
integers, then `n + 1 ≤ 1` (unsigned) splits off `n = 0` (the kernel's stuck
case) and `n = -1`; the general case calls the C division helper and corrects
the result by a sign test. This file gives that shape once:

* `DivPath B dv q`: the operands' tags (`B`: `BothInt` or `BothIntK`) and a
  condition `q` on the dividend `R[B]` and the divisor at the address
  `dv w ins` (`R[C]`'s slot or `K[C]`'s);
* `sim_div`: `SimArm o` from the five paths (zero, minus one, and three
  general cases split by two tests `P` and `Q`) and the fall-through;
* `kit_div_zero`, `kit_div_gen`: the path proofs' common prefix (the
  setup, the kernel's value restated by an equation such as `imodC_eq`, the
  run to the helper's call node), parametrised by the arm's setup tactic
  and the divisor's address.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- A path of a division arm: the operands' tags `B`, and `q` of the dividend
`R[B]` and the divisor at `dv w ins`. -/
def DivPath (B : Proto → Config → State → RelPtrs → Word → Prop) (dv : RelPtrs → Word → Nat)
    (q : BitVec 64 → BitVec 64 → Prop) (p : Proto) (c : Config) (s : State) (w : RelPtrs)
    (ins : Word) : Prop :=
  B p c s w ins ∧ q (slotVal c.σ.mem (w.slot ins.b)) (slotVal c.σ.mem (dv w ins))

/-- The divisor of the general case: neither `0` nor `-1`. -/
abbrev DivGen (y : BitVec 64) : Prop := ¬ (y = 0#64 ∨ y = -1#64)

/-- The `R[C]` and `K[C]` divisor addresses. -/
abbrev dvR (w : RelPtrs) (ins : Word) : Nat := w.slot ins.c
abbrev dvK (w : RelPtrs) (ins : Word) : Nat := w.k + stackValueSize * ins.c

/-- **A division arm from its paths.** -/
theorem sim_div {o : OpCode} (ho : o.toNat < Arms.jtEntries)
    {B : Proto → Config → State → RelPtrs → Word → Prop} {dv : RelPtrs → Word → Nat}
    (P Q : BitVec 64 → BitVec 64 → Prop)
    (h0 : ArmBody o (DivPath B dv fun _ y => y = 0#64))
    (h1 : ArmBody o (DivPath B dv fun _ y => y = -1#64))
    (h2 : ArmBody o (DivPath B dv fun x y => DivGen y ∧ P x y))
    (h3 : ArmBody o (DivPath B dv fun x y => DivGen y ∧ ¬ P x y ∧ Q x y))
    (h4 : ArmBody o (DivPath B dv fun x y => DivGen y ∧ ¬ P x y ∧ ¬ Q x y))
    (hfall : ArmBody o fun p c s w ins => ¬ B p c s w ins) : SimArm o :=
  sim_arm ho fun {p} hS {c s s' w ins} hA hf hop hstep => by
    by_cases hI : B p c s w ins
    · by_cases hz : slotVal c.σ.mem (dv w ins) = 0#64
      · exact h0 hS hA hf hop hstep ⟨hI, hz⟩
      by_cases hm : slotVal c.σ.mem (dv w ins) = -1#64
      · exact h1 hS hA hf hop hstep ⟨hI, hm⟩
      have hy : DivGen (slotVal c.σ.mem (dv w ins)) := fun h => h.elim hz hm
      by_cases hP : P (slotVal c.σ.mem (w.slot ins.b)) (slotVal c.σ.mem (dv w ins))
      · exact h2 hS hA hf hop hstep ⟨hI, hy, hP⟩
      by_cases hQ : Q (slotVal c.σ.mem (w.slot ins.b)) (slotVal c.σ.mem (dv w ins))
      · exact h3 hS hA hf hop hstep ⟨hI, hy, hP, hQ⟩
      · exact h4 hS hA hf hop hstep ⟨hI, hy, hP, hQ⟩
    · exact hfall hS hA hf hop hstep hI

set_option hygiene false in
/-- The value facts of a division arm's guards: the operands' payloads read
through the `savestate` stores (the divisor's by `hdvLd`, which the path
macros put in context), the `bgeu`/sign tests as `decide`. -/
macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| (try kitk_rd); try simp (disch := kit_disch) only [
      ld_slot_gen (w.slot ins.b), hdvLd, slotVal_wm8, Vsa.Sim.sext_zero,
      Vsa.Sim.sext_one, BitVec.add_zero, BitVec.zero_add, bgeu_one, slt_zero, sge_zero,
      BitVec.msb_xor])

set_option hygiene false in
/-- **`kit_div_zero st dv`**: the `n = 0` path, where the kernel is stuck
(`luaG_opinterror`): `st` is the arm's setup, `dv` the divisor's address. -/
macro "kit_div_zero " "(" st:tacticSeq ")" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hz⟩
  simp only [dvR, dvK] at hz
  ($st)
  simp [Opnd.fill, δ, BinOp.int, imod, idiv, stackValueSize, hz] at hk))

set_option hygiene false in
/-- **`kit_div_close [facts]`**: the close of a division path: `R[A]` stored
(`sd`, then `sb 3`), the kernel's `if`s decided by the path `facts`. -/
macro "kit_div_close " "[" fs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (by kit_frame)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
          slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add]
        simp only [ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false,
          and_self, ite_false, ite_true, stData_three, sdData_id, $fs,*]
        exact .int), h0.pcAt⟩)

/-- `luaV_mod`'s `n = -1` exit. -/
theorem imod_m1 (m : BitVec 64) : imod m (-1#64) = some 0#64 := by
  rw [imodC_eq _ _ (by decide), srem_neg_one]; simp

set_option hygiene false in
/-- **`kit_div_m1 st eq`**: the `n = -1` path (no helper call): the setup
`st`, the kernel's value by `eq : ∀ m, op m (-1) = some _`, the run, the
close. -/
macro "kit_div_m1 " "(" st:tacticSeq ")" dv:term:max eq:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hm⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a $dv
  simp only [dvR, dvK] at hm
  ($st)
  simp only [Opnd.fill, δ, BinOp.int, stackValueSize, hm, $eq:ident] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  kit_run h0 acc
  kit_div_close []))

/-! ## Splitting a path at a helper's return

A general division path runs the arm to a helper call and back, then the
correction and the store. One declaration for the whole run exceeds the
default heartbeat budget, so a path is two: `ArmPre` (the arm's entry to the
helper's return, shared by the paths after it) and `ArmPost` (from the
return to the fetch head), joined by `armBody_split`. The state at the
return is `AtRet`: the helper's result in `a0`, the caller's registers
(`HFrame`, given per arm by `divFrame`) and `savestate`'s memory. -/

/-- `R[A]`'s address as the arms compute it (`srliw s6,s4,7; zext.b; slli s6,s6,4; add s6,s9,s6`). -/
abbrev raAddr (w : RelPtrs) (ins : Word) : BitVec 64 :=
  BitVec.ofNat 64 w.base + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
    (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0) (0x07#5))) &&& sign_extend (m := 64) (0x0ff#12))
    (Sail.BitVec.extractLsb (0x04#6) 5 0)

/-- The memory after `savestate` (`sd s3,32(s7)`: `ci->u.l.savedpc`;
`sd a4,16(s0)`: `L->top := ci->top`). -/
abbrev saveMem (c : Config) (s : State) (w : RelPtrs) : Mem :=
  writeMap8 (writeMap8 c.σ.mem ((BitVec.ofNat 64 w.ci + sign_extend (m := 64) (0x020#12)).toNat)
    (sdData_val (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1)))))
    ((BitVec.ofNat 64 w.L + sign_extend (m := 64) (0x010#12)).toNat)
    (sdData_val (sign_extend (m := 64)
      (bytesT8 c.σ.mem (BitVec.ofNat 64 w.ci + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))))

/-- The caller's registers at a helper's return: the fetch-head registers,
`s6` = `R[A]`'s address, and the arm's temporaries `s3`, `s4`, `s10`. -/
abbrev divFrame (s : State) (w : RelPtrs) (ins : Word) (s3 s4 s10 : BitVec 64) : HFrame :=
  ⟨BitVec.ofNat 64 w.sp, BitVec.ofNat 64 symGlobalPointer, BitVec.ofNat 64 w.L,
   BitVec.ofNat 64 (Arms.jtEntries - 1), BitVec.ofNat 64 vNumInt, s3, s4, 0#64, raAddr w ins,
   BitVec.ofNat 64 w.ci, BitVec.ofNat 64 Arms.jtBase, BitVec.ofNat 64 w.base, s10,
   BitVec.ofNat 64 (w.code + 4 * s.pc)⟩

/-- **At a helper's return** `pc`: `a0 = r`, the frame `f`, `savestate`'s memory. -/
structure AtRet (c : Config) (s : State) (w : RelPtrs) (pc : BitVec 64) (f : HFrame) (r : BitVec 64)
    (c1 : Config) : Prop where
  seg : SegSt pc (⟨Register.x10, r⟩ :: f.pins) (ArmPay (saveMem c s w) c.σ.sailOutput) c1

/-- An arm's run from its entry to a helper's return (under `Q`). -/
def ArmPre (o : OpCode) (Q : Proto → Config → State → RelPtrs → Word → Prop) (pc : BitVec 64)
    (F : Config → State → RelPtrs → Word → HFrame) (R : Config → RelPtrs → Word → BitVec 64) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs} {ins : Word},
    ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
    Q p c s w ins → ∃ c1, Steps c c1 ∧ AtRet c s w pc (F c s w ins) (R c w ins) c1

/-- An arm's run from a helper's return to the fetch head (under `Q`). -/
def ArmPost (o : OpCode) (Q : Proto → Config → State → RelPtrs → Word → Prop) (pc : BitVec 64)
    (F : Config → State → RelPtrs → Word → HFrame) (R : Config → RelPtrs → Word → BitVec 64) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs} {ins : Word},
    ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
    Q p c s w ins → ∀ c1, AtRet c s w pc (F c s w ins) (R c w ins) c1 →
    ∃ c', Steps c1 c' ∧ VmRelAt p c' s' w

/-- **A path from its two halves.** -/
theorem armBody_split {o : OpCode} {Q Q' : Proto → Config → State → RelPtrs → Word → Prop}
    {pc : BitVec 64} {F : Config → State → RelPtrs → Word → HFrame}
    {R : Config → RelPtrs → Word → BitVec 64}
    (hQ : ∀ {p c s w ins}, Q p c s w ins → Q' p c s w ins)
    (pre : ArmPre o Q' pc F R) (post : ArmPost o Q pc F R) : ArmBody o Q :=
  fun {_} hS {_ _ _ _ _} hA hf hop hstep hq =>
    let ⟨c1, hs1, h1⟩ := pre hS hA hf hop hstep (hQ hq)
    let ⟨c', hs2, hR⟩ := post hS hA hf hop hstep hq c1 h1
    ⟨c', hs1.trans hs2, hR⟩

set_option hygiene false in
/-- **`kit_div_pre st dv stop call`**: an `ArmPre` proof: the setup `st`,
the run to the helper's entry `stop`, the call node `call` (its summary),
and the return state as `AtRet`. -/
macro "kit_div_pre " "(" st:tacticSeq ")" dv:term:max stop:num call:term:max : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a $dv
  simp only [dvR, dvK] at hy
  ($st)
  have hz := fun e => hy (Or.inl e)
  kit_run h0 acc until [$stop]
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0) $call
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩))

set_option hygiene false in
/-- **`kit_div_post st dv eq [facts]`**: an `ArmPost` proof: the setup `st`,
the kernel's value by `eq`, the run from the return, the close. -/
macro "kit_div_post " "(" st:tacticSeq ")" dv:term:max eq:term:max
    "[" fs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩ c1 ⟨h1⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a $dv
  simp only [dvR, dvK] at hy hq
  ($st)
  have hz := fun e => hy (Or.inl e)
  have heq := fun m => $eq m _ hz
  simp only [Opnd.fill, δ, BinOp.int, heq] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  clear h0 acc
  have acc := Steps.refl c1
  have h0 := h1
  kit_run h0 acc
  kit_div_close [$fs,*]))

end Lua.Vm.Sim.Kit
