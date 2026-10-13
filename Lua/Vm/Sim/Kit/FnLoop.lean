import Lua.Vm.Sim.Kit.FnCall

/-!
# Loops in lifted functions (lane float-sf5)

`scripts/gen_lua_fn.py` lifts a routine whose segment graph has cycles
(`__ieee754_fmod`: six loops) by **fuel**: every node of a cycle (a strongly
connected component of the node graph) takes a fuel argument, its lifted
function `N_<pc> fuel …` is defined by structural recursion on it (a
`mutual` block per cycle, every edge inside the cycle consuming one unit),
and a node outside a cycle enters one with `fnFuel`. Fuel 0 gives a junk
value; whether the fuel sufficed is the node's **termination function**
`T_<pc> fuel … : Bool`, defined by the same recursion (`false` at fuel 0,
`true` at a return), and every node lemma that reaches a cycle takes
`hT : T_<pc> … = true`. The node lemmas of a cycle are a `mutual` block by
the same structural recursion, so no measure appears at level (a).

The summary is therefore conditional on `T … = true`; that every input
terminates within `fnFuel` (a loop's measure) is a level-(b) fact about the
lifted functions, proved with the reference (`T_true`), never a machine
fact.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Sim

namespace Lua.Vm.Sim

/-- **The fuel a lifted function enters a loop with**: `2^64` node visits. -/
def fnFuel : Nat := 2 ^ 64

/-! ## Side conditions in the termination function

A segment's side condition that holds only on the paths into it (an address
over a register its node does not bound; `gen_lua_fn.py`'s `SIDE`) is a
conjunct `decide c` of its node's `T_<pc>`: `T = (R && decide c₁ && … &&
decide c_k)`, read back by these two projections. -/

theorem fn_and_l {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

theorem fn_and_r {a : Bool} {p : Prop} [Decidable p] (h : (a && decide p) = true) : p := by
  cases a <;> simp_all

/-- **An address `kit_disch` does not fold**: a literal base (`auipc`/`lui`
parts) plus a bounded index (`e_fmod.c`'s `Zero[sx]`, the sign bit shifted
by 3). The literal parts are reduced by the `BitVec` simprocs, the index is a
`Nat` term over a `toNat` atom, whose range `omega` knows. -/
macro "fn_disch" : tactic => `(tactic| first
  | kit_disch
  | (have hTH : tohostAddr = 0x8005c6c0 := rfl
     simp (config := { decide := true }) only [extract_sext, sext_shr, shl_ofNat, add_imm,
       BitVec.ofNat_add_ofNat, Nat.shiftRight_eq_div_pow]
     simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_add, BitVec.toNat_ofNat,
       BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceToNat, Nat.reduceMod,
       Nat.reducePow, Nat.reduceAdd]
     omega))

end Lua.Vm.Sim
