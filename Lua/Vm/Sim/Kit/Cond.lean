import Lua.Vm.Sim.Kit.Close

/-!
# The kit's `docondjump` (lane KIT-2)

Every test arm (`EQ`, `EQK`, `LT`, `LE`, …) ends in `lvm.c`'s
`docondjump`: the test's truth `c` against the `k` bit either skips the
following `OP_JMP` (`pc += 2`) or takes it (`donextjump`). `kit_cond c`
does both exits once: it splits on `c = k`, evaluates the kernel's edge (M1),
runs the arm's segments to the fetch head (`kit_run`, the guard `bne k, c`
closed by `bne_ite`) and closes with `Core.bleach_same` (the `take` exit
after `nextjump_pc`, reading `ci->u.l.trap` and the `JMP` word through the
`Scratch` stores).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- The `bne k, c` of `docondjump` on 0/1 values. -/
theorem bne_ite (k c : Bool) :
    ((if k then 1#64 else 0#64) != (if c then 1#64 else 0#64)) = (k != c) := by
  cases k <;> cases c <;> decide

/-- `bne k, c` against a 0/1 answer decided by a proposition
(`luaV_equalobj`'s `if v1 = v2 then 1 else 0`). -/
theorem bne_ite_prop (k : Bool) (P : Prop) [Decidable P] :
    ((if k then 1#64 else 0#64) != (if P then 1#64 else 0#64)) = (k != decide P) := by
  by_cases h : P <;> cases k <;> simp [h] <;> decide

/-- `ci->u.l.trap` read through the `Scratch` stores. -/
theorem Core.trap_at' {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {a : Nat} (ha : a = w.ci + 40) : bytesT4 c.σ.mem a = 0 := by
  subst ha; exact hc.trap

/-- An instruction word read through `Scratch` stores. -/
theorem Core.fetch_scratch' {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {m : Mem} (h : ∀ x, ¬ Scratch w x → m[x]? = c.σ.mem[x]?) {pc : Nat} {ins : Word}
    (hf : p.fetch pc = some ins) : bytesT4 m (w.code + 4 * pc) = ins := by
  have hlt := fetch_lt hf
  refine (bytesT4_congr fun i hi => h _ fun hs => ?_).trans (hc.fetch hf)
  exact hc.ranges.code_out _ (by omega) (by omega) (.inr (.inr hs))

theorem bytesT4_wm8_out' {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 4 ≤ a ∨ a + 8 ≤ x) :
    bytesT4 (writeMap8 m a d) x = bytesT4 m x :=
  bytesT4_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

set_option hygiene false in
/-- **`kit_nj`**: the jump target `t` of the following `OP_JMP` (`nextJump`;
none: no kernel, the arm is stuck), and the register bound `htop`. -/
macro "kit_nj" : tactic => `(tactic| (
  rcases hnj : nextJump p s.pc with _ | t <;> simp [hnj] at hk htop))

set_option hygiene false in
/-- `updatetrap`'s reload of `ci->u.l.trap` (0, read through the `Scratch`
stores), if the exit has one. -/
macro "kit_trap" : tactic => `(tactic| (
  try simp (disch := kit_disch) only [bytesT4_wm8_out'] at h0
  try (simp (disch := kit_disch) only [Core.trap_at' hc] at h0; simp only [trap_zero] at h0)))

set_option hygiene false in
/-- **`kit_cond c`**: both exits of `docondjump` on the test `c`, from
`kit_setup`, `kit_nj` and the operands read. -/
macro "kit_cond " c:term : tactic => `(tactic| (
  by_cases hkk : $c = ins.k
  · have hg : (ins.k != $c) = false := by rw [hkk]; exact bne_self_eq_false _
    simp [Opnd.fill, δ, Value.rawEq, VState.apply, writeDefs, KEdge.kills, Value.isFalse, hkk] at hk
    subst hk
    obtain ⟨ni, hni, hjt⟩ : ∃ ni, p.fetch (s.pc + 1) = some ni ∧ jumpTo (s.pc + 2) ni.sj = some t := by
      simp only [nextJump, Option.bind_eq_some_iff] at hnj; exact hnj
    have hlt1 := fetch_lt hni
    have hjt' := jumpTo_eq hjt
    have hsj : ni.sj < 2 ^ 25 := by
      simp only [Word.sj, Word.ax, Word.field, Word.offsetSJ]; have := ni.isLt; omega
    kit_run h0 acc
    kit_trap
    rw [nextjump_pc ?_ (Core.fetch_scratch' hc (by kit_frame) hni) hjt (by kit_disch) (by kit_disch)]
      at h0
    · exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩
    · kit_disch
  · have hg : (ins.k != $c) = true := by
      simpa only [bne_iff_ne, ne_eq, eq_comm (a := ins.k)] using hkk
    simp [Opnd.fill, δ, Value.rawEq, VState.apply, writeDefs, KEdge.kills, Value.isFalse, hkk] at hk
    subst hk
    kit_run h0 acc
    kit_trap
    exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩))

/-- `R[A]` and `R[B]` have the integer tag. -/
def BothIntAB (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  slotTag c.σ.mem (w.slot ins.a) = BitVec.ofNat 8 vNumInt ∧
    slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt

/-- `R[A]` and `R[B]` hold strings (`l_strcmp`'s path of `LT`/`LE`). -/
def BothStrAB (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ x y, s.regs ins.a = some (.str x) ∧ s.regs ins.b = some (.str y)

set_option hygiene false in
/-- **`kit_order_int pc c`**: an order arm (`LT`, `LE`) at `pc` on two
integers (`BothIntAB` as `hI`), the test `c` over the payloads. -/
macro "kit_order_int " pc:num c:term : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  have hIa := hI.1; have hIb := hI.2
  obtain rfl := hva.int_of_tag hI.1
  obtain rfl := hvb.int_of_tag hI.2
  kit_cond $c))

set_option hygiene false in
/-- **`kit_order_stuck pc`**: an order arm at `pc` on anything but two
integers (`hI`), two strings (`hT`) or a float (`hN`): `δ` is `none`, no
step. -/
macro "kit_order_stuck " pc:num : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  exfalso
  rcases va with _ | _ | x | ⟨x, nx⟩ | x | _ <;> rcases vb with _ | _ | y | ⟨y, ny⟩ | y | _ <;>
    simp [Opnd.fill, δ, Value.toNum?] at hk
  all_goals first
    | exact hI ⟨hva.tag_of_int.1, hvb.tag_of_int.1⟩
    | exact hT ⟨_, _, hba, hbb⟩
    | exact hN (.inl ⟨_, _, hba⟩)
    | exact hN (.inr ⟨_, _, hbb⟩)))

/-- **An order arm off its float paths, from its paths**: two integers
(`int`), two strings (`str`); anything else but a float is stuck
(`stuck`). -/
theorem sim_order {o : OpCode} (ho : o.toNat < Arms.jtEntries) (int : ArmBody o BothIntAB)
    (str : ArmBody o BothStrAB)
    (stuck : ArmBody o fun p c s w ins =>
      ¬ BothIntAB p c s w ins ∧ ¬ BothStrAB p c s w ins ∧ ¬ FltAB p s ins) :
    SimArmOn o fun p s ins => ¬ FltAB p s ins :=
  sim_arm_on ho fun {p} hS {c s s' w ins} hA hf hop hstep hN =>
    open Classical in
    if hI : BothIntAB p c s w ins then int hS hA hf hop hstep hI
    else if hT : BothStrAB p c s w ins then str hS hA hf hop hstep hT
    else stuck hS hA hf hop hstep ⟨hI, hT, hN⟩

end Lua.Vm.Sim
