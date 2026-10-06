import Lua.Vm.Sim.Kit.AtCond
import Lua.Vm.Sim.Kit.Le
import Lua.Vm.Sim.Kit.Lt
import Lua.Vm.Sim.Kit.Eqk
import Lua.Vm.At.Le
import Lua.Vm.At.Lt
import Lua.Vm.At.Eqk

/-!
# `OP_LE` and `OP_LT` on two strings on the location-list route (lane F1-2)

`lessequalothers`/`lessthanothers` inlined in the arm: the string tags
(`tt & 15 = 4`, the guards of the generated at-lemmas closed from the
registers' strings), `savestate`, the call node `l_strcmp` with its
observation (`slti 1`, `srliw 31`: `le_obs`, `lt_obs`), then `docondjump`
(`trap_ld`, `kraw_eq`, `jmp_at`), all in the generated at-lemmas
`Lua/Vm/At/{Le,Lt}.lean`. Each exit of `docondjump` is one declaration and
one `at_go`. With the kit's integer and stuck paths (`le_int`, `le_stuck`,
`lt_int`, `lt_stuck`) this closes `sim_LE_of_str` and `sim_LT_of_str`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- A string tag's variant test (`andi 15`). -/
theorem str_and15' (s : List UInt8) :
    zero_extend (m := 64) (BitVec.ofNat 8 (strTag s) : BitVec (8 * 1)) &&& 0xf#64 = 4#64 := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem str_zext (s : List UInt8) :
    zero_extend (m := 64) (BitVec.ofNat 8 (strTag s) : BitVec (8 * 1)) = BitVec.ofNat 64 (strTag s) := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem str_ne_int' (s : List UInt8) : (BitVec.ofNat 64 (strTag s) != BitVec.ofNat 64 vNumInt) = true := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem bool_ne_not {a b : Bool} (h : ¬ b = a) : a = !b := by cases a <;> cases b <;> simp_all

theorem not_bne_self' (b : Bool) : ((!b) != b) = true := by cases b <;> rfl

set_option hygiene false in
/-- The string path's guards: the tags are string tags; the test against
`k` (`e`: `k` as the test, or its negation); `donextjump`'s `JMP` (`hnj`). -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| (
      simp only [Loc.den, Fld.den, Nat.add_zero, hta, htb, str_and15', hsx, hsy, bne_ite, e, hnj,
        beq_self_eq_true, bne_self_eq_false, not_bne_self', Option.isSome_some]
      first
        | done
        | decide
        | (simp only [str_zext, str_ne_int']; done)))

set_option hygiene false in
/-- **`at_str_path pc ns e`**: an order arm on two strings (`hT`: `x = R[A]`,
`y = R[B]`), one exit of `docondjump`: `e` states the `k` bit as the test
(the jump) or its negation (the skip); the run by `at_go ns`. -/
macro "at_str_path " pc:num ns:ident e:term : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  obtain ⟨⟨x, y, hx, hy⟩, hkk⟩ := hT
  rw [hx] at hba; rw [hy] at hbb; cases hba; cases hbb
  have hkk := hkk x y hx hy
  have e : ins.k = _ := $e
  have hta : slotTag c.σ.mem (w.slot ins.a) = BitVec.ofNat 8 (strTag x) := hva.tag_eq
  have htb : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 (strTag y) := hvb.tag_eq
  have hsx : sOf ⟨p, c, s, w, ins⟩ .a = x := by simp [sOf, Fld.den, hx]
  have hsy : sOf ⟨p, c, s, w, ins⟩ .b = y := by simp [sOf, Fld.den, hy]
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, e] at hk
  subst hk
  at_go $ns))

/-- Two strings, the test `c x y` equal (`take`) or not (`skip`) to `k`. -/
def StrTest (t : List UInt8 → List UInt8 → Bool) (take : Bool) (p : Proto) (c : Config) (s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  BothStrAB p c s w ins ∧
    ∀ x y, s.regs ins.a = some (.str x) → s.regs ins.b = some (.str y) → (t x y = ins.k ↔ take = true)

/-- An order arm on two strings from its two exits. -/
theorem str_cond {o : OpCode} {t : List UInt8 → List UInt8 → Bool} (take : ArmBody o (StrTest t true))
    (skip : ArmBody o (StrTest t false)) : ArmBody o BothStrAB :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  obtain ⟨x, y, hx, hy⟩ := hT
  by_cases hk : t x y = ins.k
  · exact take hS hA hf hop hstep ⟨⟨x, y, hx, hy⟩, fun x' y' hx' hy' => by
      rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; simp [hk]⟩
  · exact skip hS hA hf hop hstep ⟨⟨x, y, hx, hy⟩, fun x' y' hx' hy' => by
      rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; simp [hk]⟩

/-- `OP_LE` on two strings, the jump taken. -/
theorem le_str_take : ArmBody .LE (StrTest (fun x y => !lexLt y x) true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_str_path 0x8001c60c Lua.Vm.At.LE ((hkk.2 rfl).symm)

/-- `OP_LE` on two strings, the jump skipped. -/
theorem le_str_skip : ArmBody .LE (StrTest (fun x y => !lexLt y x) false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_str_path 0x8001c60c Lua.Vm.At.LE (bool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`sim_LE`**: `OP_LE` simulates its kernel, every path proved. -/
theorem sim_LE : SimArm .LE := sim_LE_of_str (str_cond le_str_take le_str_skip)

/-- `OP_LT` on two strings, the jump taken. -/
theorem lt_str_take : ArmBody .LT (StrTest (fun x y => lexLt x y) true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_str_path 0x8001c894 Lua.Vm.At.LT ((hkk.2 rfl).symm)

/-- `OP_LT` on two strings, the jump skipped. -/
theorem lt_str_skip : ArmBody .LT (StrTest (fun x y => lexLt x y) false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_str_path 0x8001c894 Lua.Vm.At.LT (bool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`sim_LT`** on the location-list route. -/
theorem sim_LT : SimArm .LT := sim_LT_of_str (str_cond lt_str_take lt_str_skip)


/-! ## `OP_EQK` on two long strings -/

/-- `R[A]` and `K[B]` long strings, the test `R[A] = K[B]` equal (`take`)
or not (`skip`) to `k`. -/
def EqkTest (take : Bool) (p : Proto) (c : Config) (s : State) (w : RelPtrs) (ins : Word) : Prop :=
  ¬ EqkShort p c s w ins ∧
    ∀ x y, s.regs ins.a = some (.str x) → kval p ins.b = some (.str y) → (decide (x = y) = ins.k ↔ take = true)

set_option hygiene false in
/-- `OP_EQK`'s test against `k`: `luaV_equalobj`'s 0/1 answer on a
proposition. -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| (
      simp only [Loc.den, hsx, hsy, bne_ite_prop, e, decide_not, bne_self_eq_false, not_bne_self']
      done))

set_option hygiene false in
/-- **`at_eqk_path e`**: `OP_EQK` on two long strings (`hT`), one exit of
`docondjump` (`e`: the `k` bit as the test or its negation), by `at_go`. -/
macro "at_eqk_path " e:term : tactic => `(tactic| (
  kit_setup 0x8001c850
  rcases hkv : kval p ins.b with _ | vk <;> simp [hkv] at hk htop
  kit_nj
  kit_bound hAt ins.a
  have hkb := kval_lt hkv
  kit_reg hba va hva ins.a
  have hvk := hc.kconst hkv
  obtain ⟨hl, hkk⟩ := hT
  simp only [EqkShort, Classical.not_not] at hl
  have hta := hl.1; have htb := hl.2
  rw [hta] at hva; rw [htb] at hvk
  obtain ⟨x, rfl, -⟩ := hva.long_of_tag
  obtain ⟨y, rfl, -⟩ := hvk.long_of_tag
  have hkk := hkk x y hba hkv
  have e : ins.k = _ := $e
  have hsx : sOf ⟨p, c, s, w, ins⟩ .a = x := by simp [sOf, Fld.den, hba]
  have hsy : kOf ⟨p, c, s, w, ins⟩ = y := by simp [kOf, hkv]
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, e] at hk
  subst hk
  at_go Lua.Vm.At.EQK))

/-- `OP_EQK` on two long strings, the jump taken. -/
theorem eqk_long_take : ArmBody .EQK (EqkTest true) := fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqk_path ((hkk.2 rfl).symm)

/-- `OP_EQK` on two long strings, the jump skipped. -/
theorem eqk_long_skip : ArmBody .EQK (EqkTest false) := fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqk_path (bool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- `OP_EQK` on two long strings: both exits. -/
theorem eqk_long : ArmBody .EQK fun p c s w ins => ¬ EqkShort p c s w ins :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hl => by
  by_cases hk : ∀ x y, s.regs ins.a = some (.str x) → kval p ins.b = some (.str y) → decide (x = y) = ins.k
  · exact eqk_long_take hS hA hf hop hstep ⟨hl, fun x y hx hy => by simp [hk x y hx hy]⟩
  · refine eqk_long_skip hS hA hf hop hstep ⟨hl, fun x y hx hy => ⟨fun e => (hk fun x' y' hx' hy' => ?_).elim, by simp⟩⟩
    rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; exact e

/-- **`sim_EQK`**: `OP_EQK` simulates its kernel, every path proved. -/
theorem sim_EQK : SimArm .EQK := sim_EQK_of_long eqk_long

end Lua.Vm.Sim.At
