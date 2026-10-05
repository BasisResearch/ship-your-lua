import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.Sim.Kit.Shift

/-!
# The shift arms on the at-lemma route (`luaV_shiftl` inlined)

`OP_SHL`/`OP_SHR`/`OP_SHLI`/`OP_SHRI` are `opArith` kernels whose integer
case is `shiftl`/`shiftr`. The machine computes them by two branches on the
amount (`Kit/Shift.lean`), so an arm has four integer paths and the
fall-through, given once here:

* `ShPath B v q`: the operands' tags `B` and `q` of the amount `v` (the
  value the machine branches on: `R[C]`, `0 - R[C]`, `R[B]`, or the field
  `C`);
* `sim_shift`: `SimArm o` from the four paths (the guards `P`, then `Q` or
  `R`, as the machine's `Bool`s) and the fall-through;
* `at_shift (setup) NS eq`: a path, the kernel restated by `eq h1 h2`
  (`shiftlC_run`, `shiftrK_neg_big`, …; `sC` by `sc_eq`), then `at_go`.

The amount `C` is an affine location (`.nat`): the closers here unfold it
(`at_hyp` by `at_unfold`, `at_new` with `Aff.den`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- A shift path: the tags `B`, and `q` of the amount `v`. -/
def ShPath (B : Proto → Config → State → RelPtrs → Word → Prop)
    (v : Config → RelPtrs → Word → BitVec 64) (q : BitVec 64 → Prop)
    (p : Proto) (c : Config) (s : State) (w : RelPtrs) (ins : Word) : Prop :=
  B p c s w ins ∧ q (v c w ins)

/-- The four integer paths of a shift arm: the guard `P`, then `Q` or `R`. -/
abbrev Sh1 (B : Proto → Config → State → RelPtrs → Word → Prop) (v : Config → RelPtrs → Word → BitVec 64)
    (P Q : BitVec 64 → Bool) := ShPath B v fun y => P y = false ∧ Q y = true
abbrev Sh2 (B : Proto → Config → State → RelPtrs → Word → Prop) (v : Config → RelPtrs → Word → BitVec 64)
    (P Q : BitVec 64 → Bool) := ShPath B v fun y => P y = false ∧ Q y = false
abbrev Sh3 (B : Proto → Config → State → RelPtrs → Word → Prop) (v : Config → RelPtrs → Word → BitVec 64)
    (P R : BitVec 64 → Bool) := ShPath B v fun y => P y = true ∧ R y = true
abbrev Sh4 (B : Proto → Config → State → RelPtrs → Word → Prop) (v : Config → RelPtrs → Word → BitVec 64)
    (P R : BitVec 64 → Bool) := ShPath B v fun y => P y = true ∧ R y = false

/-- The guards of `luaV_shiftl` on a register amount (`bltz`; `blt 63, y`;
`blt y, -63`) and on the field `C` (`bltu 127, c`; `bgeu 63, c`;
`bltu 190, c`). -/
abbrev qL (y : BitVec 64) : Bool := zopz0zI_s 0x3f#64 y
abbrev rL (y : BitVec 64) : Bool := zopz0zI_s y 0xffffffffffffffc1#64
abbrev pU (y : BitVec 64) : Bool := zopz0zI_u 0x7f#64 y
abbrev qU (y : BitVec 64) : Bool := zopz0zKzJ_u 0x3f#64 y
abbrev rU (y : BitVec 64) : Bool := zopz0zI_u 0xbe#64 y

/-- The amounts: `R[C]`, `0 - R[C]` (`OP_SHR`), `R[B]` (`OP_SHLI`), `C`. -/
abbrev amtC (c : Config) (w : RelPtrs) (ins : Word) : BitVec 64 := slotVal c.σ.mem (w.slot ins.c)
abbrev amtNC (c : Config) (w : RelPtrs) (ins : Word) : BitVec 64 :=
  0x0#64 - slotVal c.σ.mem (w.slot ins.c)
abbrev amtB (c : Config) (w : RelPtrs) (ins : Word) : BitVec 64 := slotVal c.σ.mem (w.slot ins.b)
abbrev amtF (_c : Config) (_w : RelPtrs) (ins : Word) : BitVec 64 := BitVec.ofNat 64 ins.c

/-- **A shift arm from its paths**: `P` (`bltz`, or `C > 127`), then `Q`
(the left shift's bound) or `R` (the right shift's), and the fall-through. -/
theorem sim_shift {o : OpCode} (ho : o.toNat < Arms.jtEntries)
    {B : Proto → Config → State → RelPtrs → Word → Prop} {v : Config → RelPtrs → Word → BitVec 64}
    (P Q R : BitVec 64 → Bool)
    (h1 : ArmBody o (Sh1 B v P Q)) (h2 : ArmBody o (Sh2 B v P Q))
    (h3 : ArmBody o (Sh3 B v P R)) (h4 : ArmBody o (Sh4 B v P R))
    (hfall : ArmBody o fun p c s w ins => ¬ B p c s w ins) : SimArm o :=
  sim_arm ho fun {p} hS {c s s' w ins} hA hf hop hstep => by
    by_cases hI : B p c s w ins
    · cases hp : P (v c w ins)
      · cases hq : Q (v c w ins)
        · exact h2 hS hA hf hop hstep ⟨hI, hp, hq⟩
        · exact h1 hS hA hf hop hstep ⟨hI, hp, hq⟩
      · cases hr : R (v c w ins)
        · exact h4 hS hA hf hop hstep ⟨hI, hp, hr⟩
        · exact h3 hS hA hf hop hstep ⟨hI, hp, hr⟩
    · exact hfall hS hA hf hop hstep hI

set_option hygiene false in
/-- **`at_shift (st) NS eq`**: a shift path: the setup `st`, the kernel's
`shiftl`/`shiftr` restated by `eq h1 h2` (and `sC` by `sc_eq`), the
at-lemmas. -/
macro "at_shift " "(" st:tacticSeq ")" ns:ident eq:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep hq
  dsimp only [Sh1, Sh2, Sh3, Sh4, ShPath, qL, rL, pU, qU, rU, amtC, amtNC, amtB, amtF] at hq
  obtain ⟨hI, h1, h2⟩ := hq
  ($st)
  simp only [Opnd.fill, δ, BinOp.int, $eq:ident h1 h2] at hk
  try simp only [sc_eq] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go $ns))

set_option hygiene false in
/-- The closer of an at-lemma's hypothesis about an affine location (the
amount `C`): the locations unfolded, then the path's guards `h1`, `h2`, or
`at_vals`. -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| (at_unfold; first | (simp only [slt_zero, h1, h2]; done) | at_vals))

set_option hygiene false in
/-- `at_new` with affine locations (a stored value computed from `C`). -/
macro_rules
  | `(tactic| at_new) => `(tactic| (
  intro e he v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  all_goals rcases he with he | he | he <;>
  ( try subst he
    try simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den] at hv
    try simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den, Aff.den, Aff.sum, Atom.den, Nat.one_mul,
      Nat.sub_zero]
    try simp at hv
    try subst hv
    try simp only [stData_three_lit, stData_three_n]
    exact .int)))

end Lua.Vm.Sim.At
