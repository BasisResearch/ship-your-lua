import Lua.Vm.Sim.Kit.AtJoin
import Lua.Vm.Sim.Kit.K
import Lua.Vm.Sim.Kit.FltNeg

/-!
# Kernel-shape set-ups for the join route (lane F2)

The join route (`Kit/AtJoin.lean`) runs an arm's float paths once, splits
at the machine's forks, and refutes each leaf by one closed `decide` over
the pair atoms. What is left per kernel shape is the set-up before the
walk: which registers are read through which view, and the kernel evaluated
on them. These macros name that set-up once per `opKernel` combinator, so
an arm is its jump-table target and its at-lemma namespace:

* `at_jorderI pc NS`: `op_orderI` (`LTI`, `LEI`, `GTI`, `GEI`): a float
  `R[A]` (`FltA`) against the 8-bit immediate;
* `at_jarith pc NS`: `op_arith` (`ADD`, `SUB`, …): `FltBC`, the float
  operand by its view and the other by its per-operand view (`num_reg`);
* `at_jarithK pc NS`: `op_arithK` (`ADDK`, `SUBK`, …): `FltBK`, with the
  constant's views `flt_k_q`, `num_k`;
* the stored float of `luai_numunm` (`ValRepr.flt_neg`, an `at_new_ext` rule).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
/-- **`at_jorderI pc NS`**: `op_orderI` on a float `R[A]` (`hT : FltA`):
the immediate's conversion (`l_intfitsf` of an 8-bit immediate holds) and
the kernel's test evaluated, then `at_walk NS`. -/
macro "at_jorderI " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  try simp [immB, Opnd.ports] at htop
  try simp only [immB, Opnd.ports] at hk
  kit_bound hAt ins.a
  have hbb := Word.b_lt ins
  flt_views
  flt_reg_s ins.a, hT
  simp [Opnd.fill, Opnd.ports, immB, Word.sb, Word.offsetSC, δ, Value.toNum?, ltNum, leNum, ltIntFloat,
    leIntFloat, ltFloatInt, leFloatInt, intfitsf_imm _ hbb] at hk
  at_walk $ns))

/-- `op_order` on an integer outside `l_intfitsf` and a float (`LTintfloat`,
`LEfloatint`, …: `luaV_flttointeger`'s chain). -/
def FltF2I (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  (∃ i x n, s.regs ins.a = some (.int i) ∧ s.regs ins.b = some (.flt x n) ∧ intfitsf i = false) ∨
  (∃ i x n, s.regs ins.a = some (.flt x n) ∧ s.regs ins.b = some (.int i) ∧ intfitsf i = false)

set_option hygiene false in
/-- **`at_jorder pc NS f2i`**: `op_order` (`LT`, `LE`) with a float operand
(`hT : FltAB`): the float by its view, the other by `num_regf` (an integer
split by the kernel's `l_intfitsf`); a non-number partner is refuted by the
kernel (the order error has no `Step`); an integer outside `l_intfitsf` is
handed to `f2i` (`LTintfloat`/`LEintfloat`'s `luaV_flttointeger` chain, an
`ArmBody o Q` over `Q := FltF2I`); the rest by `at_walk NS`. -/
macro "at_jorder " pc:num ns:ident f2i:term : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  refine hT.elim (fun hq => ?fa) (fun hq => ?fb)
  case' fa => flt_reg_s ins.a, hq; num_regf ins.b, hn
  case' fb => num_regf ins.a, hn; all_goals flt_reg_s ins.b, hq
  all_goals simp only [Opnd.fill] at hk
  all_goals try (rcases v with _ | _ | _ | _ | _ | _ <;> simp [δ, Value.toNum?] at hk hn <;> done)
  all_goals simp [δ, Value.toNum?, ltNum, leNum, ltIntFloat, ltFloatInt, leIntFloat, leFloatInt] at hk
  all_goals try simp only [hfit, ite_true] at hk
  all_goals first
    | exact $f2i hS hA hf hop hstep (by first
        | exact .inl ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩
        | exact .inr ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩)
    | skip
  all_goals at_walk $ns))

set_option hygiene false in
/-- **`at_jarith pc NS`**: `op_arith`'s float case (`hT : FltBC`): the float
operand by its view (`flt_reg_q`), the other by its per-operand view
(`num_reg`: a float, an integer through `__floatdidf`, or no number, the
fall-through to `MMBIN`); the kernel's `rawArith`, then `at_walk NS`. A
commuted soft-float call (`luai_numadd` as `__adddf3(c, b)`) is the
kernel's sum by `model_add_comm` in the stored-float rule. -/
macro "at_jarith " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  refine hT.elim (fun hq => ?fb) (fun hq => ?fc)
  case' fb => flt_reg_q x ins.b, hq; num_reg ins.c, hn
  case' fc => flt_reg_q x ins.c, hq; num_reg ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_walk $ns))

set_option hygiene false in
/-- **`flt_k_q x, hT`**: the constant `K[C]`, a float by the operand
predicate (`hT : FltK p ins.c`): its tag and model join `hta`, `hxm`
(`kitk_const`'s `hkv`, `hvk`). -/
macro "flt_k_q " x:ident "," hq:term : tactic => `(tactic| (
  obtain ⟨$x, _, hst⟩ := $hq
  rw [hst] at hkv; cases hkv
  obtain ⟨hta', hxm', -⟩ := hvk.flt_parts
  have hta := And.intro hta' hta
  have hxm := And.intro hxm' hxm
  clear hta' hxm'))

set_option hygiene false in
/-- **`num_k hn`**: the constant `K[C]` by its per-operand view (`num_reg`'s
three goals over `kitk_const`'s `hvk`). -/
macro "num_k " hn:ident : tactic => `(tactic| (
  rcases hvk.numView with ⟨rfl, htn, $hn⟩ | ⟨rfl, htn, $hn⟩ | ⟨$hn, htn, htn'⟩))

set_option hygiene false in
/-- **`at_jarithK pc NS`**: `op_arithK`'s float case (`hT : FltBK`):
`at_jarith` with the constant `K[C]` (`kitk_const`, `flt_k_q`, `num_k`). -/
macro "at_jarithK " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  refine hT.elim (fun hq => ?fb) (fun hq => ?fk)
  case' fb => flt_reg_q x ins.b, hq; num_k hn
  case' fk => flt_k_q x, hq; num_reg ins.b, hn
  all_goals
    simp only [Opnd.fill, fastArith, hn] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_walk $ns))

set_option hygiene false in
/-- `luai_numunm`'s stored float: the sign bit flipped inline, under the
operand's float tag (`hta`). -/
macro_rules | `(tactic| at_new_ext) => `(tactic| exact ValRepr.flt_neg
  (by first | decide | (simp only [stData_zext, Nat.add_zero, hta]; done)) _)

end Lua.Vm.Sim.At
