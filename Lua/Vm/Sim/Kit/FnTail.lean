import Lua.Vm.Sim.Kit.FnOuter

/-!
# Tail calls in lifted routines (lane float-sf6)

A routine that ends in `j <callee>` (its frame popped, `ra` restored:
`__ieee754_pow`'s `sqrt(x)` and `__math_oflow`/`__math_uflow` exits,
`xflow`'s `with_errno`) returns what the callee returns, at the caller's
`sp` and return address. `scripts/gen_lua_fn.py` makes the jump a **tail
node**: its lifted value is the callee summary's value, its memory function
the callee summary's memory over the node's memory. The routine's summary
patches its window `[s - W, s)` (and its outer word) from that memory, which
is the callee's patch of the same memory inside the window:

* `memPatch_tail`: the callee's window inside the routine's;
* `memPatch_tail_outer`: both with an outer word (`OUTER`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Sim

namespace Lua.Vm.Sim

/-- **A tail callee's patch inside the window** is the routine's patch. -/
theorem memPatch_tail {m X : Mem} {lo n lo' n' : Nat} (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    memPatch m (memPatch m X lo' n') lo n = memPatch m X lo' n' :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch m (memPatch m X lo' n') lo x n]
    split
    · rfl
    · rw [getElem?_memPatch_out (by omega)]

/-- **A tail callee's two patches** (its window and the outer word) inside the
routine's. -/
theorem memPatch_tail_outer {m X : Mem} {lo n lo' n' A k : Nat} (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    memPatch (memPatch m (memPatch (memPatch m X lo' n') X A k) lo n) (memPatch (memPatch m X lo' n') X A k) A k =
      memPatch (memPatch m X lo' n') X A k :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch (memPatch m (memPatch (memPatch m X lo' n') X A k) lo n)]
    split
    · rfl
    · rw [getElem?_memPatch m _ lo x n]
      split
      · rfl
      · rw [getElem?_memPatch_out (by omega), getElem?_memPatch_out (by omega)]

end Lua.Vm.Sim
