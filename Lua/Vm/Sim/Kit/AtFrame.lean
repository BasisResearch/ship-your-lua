import Lua.Vm.Sim.Kit.At

/-!
# Address side conditions through a callee's frame (lane F3)

An at-lemma's address side condition that reads memory (`ld a4,0(sp)`, the
constant array `k`, then `K[C]`) is discharged by `kptr_at` at the entry
memory. After a framed helper's call (`floor`, 112 bytes: the log entry
`Ent.clob`, `memPatch m m' (sp - 112) 112`) the load is of the patched
memory, so `kptr_at` does not apply and the address is left to `omega`.

`at_side_ext`'s rule here forwards every load of the goal through the
path's stores and frames first (`at_fwd`: `atFwd`, the forwarding `at_eq`
uses, `ld8_patch` past a frame by `at_sep`), then reads `0(sp)` as `k`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lean Elab Tactic in
/-- Every load of the goal forwarded through the path's stores and callee
frames (`atFwd`). -/
elab "at_fwd" : tactic => atFwd

open Lean Elab Tactic in
/-- **`at_fwd_k`**: forward the goal's loads (`atFwd`), read `0(sp)` as `k`
(`kptr_at`), and forward again: a load whose address is itself a load
(`K[C]` at `bytesT8 M sp + 16 C`) is forwarded once its address is `k`'s.
Fails when the goal is unchanged. -/
elab "at_fwd_k" : tactic => withMainContext do
  let t0 ← instantiateMVars (← getMainTarget)
  atFwd
  evalTactic (← `(tactic| try simp (disch := kit_disch) only [kptr_at $(mkIdent `hc)]))
  evalTactic (← `(tactic| try simp only [sext64_id]))
  if (← getUnsolvedGoals).isEmpty then return
  atFwd
  if (← getUnsolvedGoals).isEmpty then return
  let t1 ← instantiateMVars (← getMainTarget)
  if t0 == t1 then throwError "at_fwd_k: no progress"

set_option hygiene false in
/-- A value read through a load whose address is a load past a callee's
frame (`K[C]`'s value after `floor`): forwarded (`at_fwd_k`), then `at_eq`. -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (at_fwd_k; at_eq))

set_option hygiene false in
/-- An address side condition through a load past the path's stores and a
callee's frame (`K[C]` after `floor`). -/
macro_rules
  | `(tactic| at_side_ext) => `(tactic| (
    at_fwd
    simp (disch := kit_disch) only [kptr_at hc]
    try simp only [sext64_id]
    kit_disch))

end Lua.Vm.Sim.At
