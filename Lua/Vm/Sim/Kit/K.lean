import Lua.Vm.Sim.Kit.Close

/-!
# The kit's `K` operand (`op_arithK`, `op_bitwiseK`)

The `K` arms read `K[C]` as `luaV_execute` does: `ld a5,0(sp)` (the constant
array `k`, `Core.kptr`), then the slot `k + 16·C`. This file adds, once:

* `BothIntK` and `sim_arithK`: `sim_arith` with the second operand `K[C]`;
* `Core.kptr_ld`: the `ld 0(sp)` value, which the runner's normaliser
  (`kit_norm`) rewrites to `w.k` after every segment, so that the `K` slot's
  guards and loads are slot arithmetic like a register's;
* `kitk_ints pc` and `kitk_fall pc`: `kit_arith_ints` and `kit_arith_fall`
  with `K[C]`. The kernel's `none` case (`kval` is `none`: a float `K`) has
  no `Step`. The `K` slot's representation is `Core.kconst` (`hvk`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `R[B]` and `K[C]` both have the integer tag. -/
def BothIntK (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt ∧
    slotTag c.σ.mem (w.k + stackValueSize * ins.c) = BitVec.ofNat 8 vNumInt

/-- **An `op_arithK`/`op_bitwiseK` arm from its two paths.** -/
theorem sim_arithK {o : OpCode} (ho : o.toNat < Arms.jtEntries) (hint : ArmBody o BothIntK)
    (hfall : ArmBody o fun p c s w ins => ¬ BothIntK p c s w ins) : SimArm o :=
  sim_arm ho fun {p} hS {c s s' w ins} hA hf hop hstep =>
    (Classical.em (BothIntK p c s w ins)).elim (hint hS hA hf hop hstep) (hfall hS hA hf hop hstep)

/-- `ld a5,0(sp)`: the constant array `k`, read from any memory that agrees
with the entry's on the eight bytes at `sp`. -/
theorem Core.kptr_ld {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {m : Mem} (hm : bytesT8 m w.sp = bytesT8 c.σ.mem w.sp) :
    sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 w.sp + sign_extend (m := 64) (0x000#12)).toNat
      : BitVec (8 * 8)) = BitVec.ofNat 64 w.k := by
  have := hc.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry] at this
  rw [add_imm _ 0 (by decide), Nat.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    sext64_id, hm]
  exact hc.kptr

set_option hygiene false in
/-- The `ld 0(sp)` in a segment state's pins, as `w.k` (through `Scratch`
stores, which miss `sp`). -/
macro_rules
  | `(tactic| kit_norm $h) => `(tactic|
      simp only [hc.kptr_ld rfl] at $h:ident)

set_option hygiene false in
/-- **`kitk_const`**: the kernel's `K[C]` (`y`; `none` has no `Step`), its
slot's representation `hvk`, and the constant array's bounds. -/
macro "kitk_const" : tactic => `(tactic| (
  rcases hkv : kval p ins.c with _ | y
  · simp [hkv] at hk
  simp [hkv, opArith, Kernel.regTop, Opnd.ports] at hk htop
  have hvk := hc.kconst hkv
  have hKc := kval_lt hkv
  have hklo := hr.k_lo; have hkhi := hr.k_hi; have hkal := hr.k_al
  simp only [Word.c, Word.field, Nat.shiftRight_eq_div_pow, stackValueSize] at hKc hkhi))

set_option hygiene false in
/-- **`kitk_ints pc`**: `kit_arith_ints` with `K[C]` (`BothIntK` as `hI`). -/
macro "kitk_ints " pc:num : tactic => `(tactic| (
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hb vb hvb ins.b
  have hB := hI.1; have hC := hI.2
  obtain rfl := hvb.int_of_tag hI.1
  obtain rfl := hvk.int_of_tag hI.2))

set_option hygiene false in
/-- **`kitk_fall pc`**: `kit_arith_fall` with `K[C]` (`¬ BothIntK` as `hI`). -/
macro "kitk_fall " pc:num : tactic => `(tactic| (
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hb vb hvb ins.b
  simp [Opnd.fill] at hk; split at hk
  · rename_i heq
    obtain ⟨e1, e2⟩ := pair_eq heq; subst e1 e2
    exact absurd ⟨hvb.tag_of_int.1, hvk.tag_of_int.1⟩ hI
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · have hC : ¬ slotTag c.σ.mem (w.k + stackValueSize * ins.c) = BitVec.ofNat 8 vNumInt :=
      fun hC => hI ⟨hB, hC⟩
    kit_next; kit_same
  · kit_next; kit_same))

end Lua.Vm.Sim
