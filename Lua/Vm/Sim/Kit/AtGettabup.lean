import Lua.Vm.Sim.Kit.AtEnv
import Lua.Vm.At.Gettabup

/-!
# `OP_GETTABUP _ENV "print"` on the location-list route (lane F1-7)

The kernel steps only for `B = 0` (upvalue 0, `_ENV`) and `K[C] = "print"`
(`opKernel`), and writes `print` to `R[A]`. The arm (`0x8001cf84`) loads the
closure from `8(sp)`, `cl->upvals[0]`, `uv->v`, tests `_ENV`'s tag
(`LUA_VTABLE`: else `luaV_finishget`, refuted by `EnvMem.tag`), calls
`luaH_getshortstr` (`gss_at`), tests the found slot's tag (not empty: else
`luaV_finishget`, refuted by `EnvMem.ptag`), and stores its tag and value in
`R[A]` (`setobj2s`). The at-lemmas are `Lua/Vm/At/Gettabup.lean`; the facts
the arm adds are `_ENV`'s (`Complement.env` at the key's intern pointer).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.Kit
open Vsa.Machine (Config Steps)

set_option hygiene false in
/-- The arm's hypotheses: the `_ENV` facts by name, the guards on `_ENV`'s
tag and the found node's tag from `EnvMem` (`env_tag_m`, `env_ptag_m`). -/
local macro_rules
  | `(tactic| at_hyp) => `(tactic| first
    | assumption
    | (simp only [Loc.den, Aff.den, Aff.sum, Atom.den, Nat.one_mul, Nat.add_zero, Nat.sub_zero,
        htagm, hptagm]; decide))

set_option hygiene false in
/-- `R[A]` holds `print`: the found node's tag and value (`env_ptag_m`, `env_pval_m`). -/
local macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
    simp only [Loc.den, Aff.den, Aff.sum, Atom.den, Nat.one_mul, Nat.add_zero, Nat.sub_zero,
      stData_zext, hptagm, hpvalm, tvalueValOff] at *
    exact .print rfl))

/-- **`sim_GETTABUP`**: `OP_GETTABUP` simulates its kernel (`_ENV.print`),
every path proved: the kernel has no step but for `B = 0` and `K[C] = "print"`. -/
theorem sim_GETTABUP : SimArm .GETTABUP := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001cf84
  by_cases hcond : ins.b = 0 ∧ p.const ins.c = some (Const.str printKey)
  · simp only [hcond, and_self, ite_true] at hk htop
    obtain ⟨hb0, hkc0⟩ := hcond
    have hkc : kval p ins.c = some (.str printKey) := by
      simp only [kval, hkc0, Option.bind_some]; rfl
    simp [move, setR, Opnd.ports, List.foldr] at htop
    kit_bound hAt ins.a
    have hK := kval_lt hkc
    obtain ⟨hown, hptr⟩ := (hc.kconst hkc).str_parts
    rw [hptr (by decide)] at hown
    have hE := hc.comp.env _ hown
    have htagm := env_tag_m hc hE
    have hptagm := env_ptag_m hc hE
    have hpvalm := env_pval_m hc hE
    simp [move, setR, Opnd.ports, Opnd.fill, VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_go Lua.Vm.At.GETTABUP
  · simp only [hcond, ite_false] at hk
    simp at hk

end Lua.Vm.Sim.At
