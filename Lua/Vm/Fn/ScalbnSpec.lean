import Lua.Vm.Fn.PowLens

/-!
# `scalbn` at level (b) (lane float-sf7)

`s_scalbn.c` on the machine (`Lua.Vm.Fn.Scalbn.F`, generated) is
`Lua.Num.Pow.scalbn` on the model: the walk of `Lua/Vm/Fn/PowLens.lean`
(`pw_walk`) over the routine's fork tree, cut at the join `0x8002d104` (the
normal and the scaled subnormal operand meet at `s_scalbn.c:95`), whose
lemma is the stage `scalbnTail` (`Lua/Vm/Fn/PowStage.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Scalbn

/-- **`s_scalbn.c:95-106`**: the join `0x8002d104` (after `k == 0x7ff`) is
`scalbnTail` of the operand `x`, its exponent `k` and the scale `n`. -/
theorem tail_d104 (m : Mem) (s : Nat) (r : BitVec 64) (x : Float.Model) (n k : Int)
    (hro : RodataRead m) (hs : FnSp s 112)
    (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31) (hk1 : -54 ≤ k) (hk2 : k < 2047) :
    N_8002d104 m s r (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 n)
        (BitVec.ofInt 64 (W x % 18446744073709551616 / 4294967296)) (BitVec.ofInt 64 k) =
      BitVec.ofInt 64 (W (Pow.scalbnTail x (Int32.ofInt (W x / 4294967296)) (Int32.ofInt k) (Int32.ofInt n))) := by
  fn_sp_factsW
  unfold Pow.scalbnTail
  pw_lens_r
  pw_front
  pw_walk

/-- **`scalbn` at level (b)**: the lifted routine is `Lua.Num.Pow.scalbn`'s
datum, on every model operand and every scale. -/
theorem F_model (m : Mem) (s : Nat) (r : BitVec 64) (x : Float.Model) (n : Int)
    (hro : RodataRead m) (hs : FnSp s 112) (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31) :
    F m s r (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 n) =
      BitVec.ofInt 64 (W (Pow.scalbn x (Int32.ofInt n))) := by
  fn_sp_factsW
  unfold F
  rw [Pow.scalbn_stage]
  pw_lens_r
  pw_front
  pw_walk using [tail_d104]

end Lua.Vm.Fn.Scalbn
