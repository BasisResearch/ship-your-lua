import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.At.Forprep

/-!
# `OP_FORPREP` on the location-list route (B-SEGLOCAL, held-out case)

`savestate`, then `forprep` inlined: the three tags, `R[A+3] := init`, the
spill of `ra` to `sp+16`, `forlimit`'s `luaV_tointeger(&R[A+1], sp+40, mode)`
(`toint_sum`), the comparison, and the count `__udivdi3` (`udivdi3_sum`)
stored in place of the limit. The kernel (`forprepK`) is stuck unless the
three registers are integers and the step is nonzero, so the machine paths
are the step's sign × run/skip; each is the kernel's case and `at_go`. The
spill cell and the out-parameter are entries of the path's log
(`Lua/Vm/At/Forprep.lean`): the reloads read them back by forwarding, and
the close (`AtFin`, C-frame writes allowed) states no frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `count /= l_castS2U(-(step + 1)) + 1u` is a division by `-step`. -/
theorem neg_step (st : BitVec 64) : -(st + 1#64) + 1#64 = -st := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega

/-- A `FORPREP` path: a condition on the values of `R[A]`, `R[A+1]`, `R[A+2]`
(init, limit, step). -/
def FpQ (q : BitVec 64 → BitVec 64 → BitVec 64 → Prop) (_p : Proto) (c : Config) (_s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  q (slotVal c.σ.mem (w.slot ins.a)) (slotVal c.σ.mem (w.slot (ins.a + 1)))
    (slotVal c.σ.mem (w.slot (ins.a + 2)))

/-- A `FORPREP` path on three integers (`¬ ForCoerce`). -/
def FpQN (q : BitVec 64 → BitVec 64 → BitVec 64 → Prop) (p : Proto) (c : Config) (s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  FpQ q p c s w ins ∧ ¬ ForCoerce p s ins

set_option hygiene false in
/-- The kit's setup for `FORPREP`: the kernel forward, its three registers
integers (`¬ ForCoerce`: the coerced and float loops are `FloatArms.FORPREP`). -/
local macro "fp_setup" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hq, hN⟩
  simp only [FpQ] at hq
  obtain ⟨⟨i, hi⟩, ⟨l, hl⟩, ⟨st, hs⟩⟩ := Classical.not_not.1 hN
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  kit_reg h1 vi hvi ins.a
  kit_reg h2 vl hvl (ins.a + 1)
  kit_reg h3 vs hvs (ins.a + 2)
  obtain rfl := Option.some.inj (h1.symm.trans hi)
  obtain rfl := Option.some.inj (h2.symm.trans hl)
  obtain rfl := Option.some.inj (h3.symm.trans hs)
  simp at hk
  obtain ⟨hTi, rfl⟩ := hvi.tag_of_int
  obtain ⟨hTl, rfl⟩ := hvl.tag_of_int
  obtain ⟨hTs, rfl⟩ := hvs.tag_of_int))

theorem msb_of_pos {x : BitVec 64} (h : 0 < x.toInt) : x.msb = false := by
  rw [BitVec.msb_eq_toInt]; simp; omega

theorem msb_of_neg {x : BitVec 64} (h0 : x ≠ 0#64) (h : ¬ 0 < x.toInt) : x.msb = true := by
  have : x.toInt ≠ 0 := fun e => h0 (BitVec.eq_of_toInt_eq (by rw [e]; rfl))
  rw [BitVec.msb_eq_toInt]; simp; omega

theorem fp_zero : ArmBody .FORPREP
    (FpQN (fun _ _ st => st = 0#64)) := by
  fp_setup; simp [hq] at hk

theorem fp_up_skip : ArmBody .FORPREP
    (FpQN (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ l.toInt < i.toInt)) := by
  fp_setup; obtain ⟨hst, hpos, hgt⟩ := hq; have hmsb := msb_of_pos hpos
  simp [hst, forCount, hpos, hgt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP

theorem fp_up_run : ArmBody .FORPREP
    (FpQN (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ ¬ l.toInt < i.toInt)) := by
  fp_setup; obtain ⟨hst, hpos, hgt⟩ := hq; have hmsb := msb_of_pos hpos
  simp [hst, forCount, hpos, hgt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP

theorem fp_down_skip : ArmBody .FORPREP
    (FpQN (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ i.toInt < l.toInt)) := by
  fp_setup; obtain ⟨hst, hpos, hlt⟩ := hq; have hmsb := msb_of_neg hst hpos
  simp [hst, forCount, hpos, hlt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP

theorem fp_down_run : ArmBody .FORPREP
    (FpQN (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ ¬ i.toInt < l.toInt)) := by
  fp_setup; obtain ⟨hst, hpos, hlt⟩ := hq; have hmsb := msb_of_neg hst hpos
  simp [hst, forCount, hpos, hlt, VState.apply, writeDefs, KEdge.kills, neg_step] at hk; subst hk
  at_go Lua.Vm.At.FORPREP

/-- **`OP_FORPREP`** on the location-list route, on three integers (its
coerced and float loops are `FloatArms.FORPREP`). -/
theorem sim_FORPREP : SimArmOn .FORPREP (Off ForCoerce) :=
    sim_arm_on (o := .FORPREP) (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hN => by
  have h := fun {q : BitVec 64 → BitVec 64 → BitVec 64 → Prop} (b : ArmBody .FORPREP (FpQN q))
      (hq : FpQ q p c s w ins) =>
    b hS hA hf hop hstep ⟨hq, hN⟩
  by_cases hst : slotVal c.σ.mem (w.slot (ins.a + 2)) = 0#64
  · exact h fp_zero hst
  by_cases hpos : 0 < (slotVal c.σ.mem (w.slot (ins.a + 2))).toInt
  · by_cases hgt : (slotVal c.σ.mem (w.slot (ins.a + 1))).toInt < (slotVal c.σ.mem (w.slot ins.a)).toInt
    · exact h fp_up_skip ⟨hst, hpos, hgt⟩
    · exact h fp_up_run ⟨hst, hpos, hgt⟩
  · by_cases hlt : (slotVal c.σ.mem (w.slot ins.a)).toInt < (slotVal c.σ.mem (w.slot (ins.a + 1))).toInt
    · exact h fp_down_skip ⟨hst, hpos, hlt⟩
    · exact h fp_down_run ⟨hst, hpos, hlt⟩

end Lua.Vm.Sim.At
