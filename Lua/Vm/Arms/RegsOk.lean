import Lua.Vm.RegsOk
import Vsa.Sim.ObsAvoid

/-!
# `RegsOk` across one step, per step class

What `scripts/syi/gen_segment.py`'s `"ok"` option emits after each step of a
segment: `RegsOk σ → RegsOk σ'` from the step's observation. A step writes at
most one GPR (`rd`, present afterwards) and no HTIF mailbox register (the
segments' stores are off `tohost`: their `hht`/`hwin` side conditions), so both
halves survive.
-/

open LeanRV64DExecutable Vsa Vsa.Sim
open Vsa.Machine (MState)

namespace Lua.Vm.RegsOk

variable {σ σ' : MState} {pc vm : BitVec 64}

theorem isSome_of {R : Register} {x y : Option (RegisterType R)}
    (h : ∀ w, x = some w → y = some w) (hx : x.isSome) : y.isSome := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hx
  rw [h w hw]; rfl

theorem alu {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (hrd : (rd == Register.htif_payload_writes) = false) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R ⟨d1, d2, d3, d4, d5, d6, d7⟩ hσ => by
      cases hR : (rd == R)
      · exact isSome_of (fun w hw => obs_alu_other hobs R d1 d2 d3 d4 d5 hR d6 d7 hw) hσ
      · obtain rfl := beq_iff_eq.1 hR
        rw [obs_alu_rd hobs d1 d2 d3 d4 d5]; rfl)
    (obs_alu_other hobs _ (by decide) (by decide) (by decide) (by decide) (by decide) hrd
      (by decide) (by decide) h.htifIdle)

theorem jal {imm : BitVec 21} {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd link))
    (hrd : (rd == Register.htif_payload_writes) = false) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R ⟨d1, d2, d3, d4, d5, d6, d7⟩ hσ => by
      cases hR : (rd == R)
      · exact isSome_of (fun w hw => obs_jal_other_env hobs R d1 d2 d3 d4 d5 hR d6 d7 hw) hσ
      · obtain rfl := beq_iff_eq.1 hR
        rw [obs_jal_rd_env hobs d1 d2 d3 d4 d5]; rfl)
    (obs_jal_other_env hobs _ (by decide) (by decide) (by decide) (by decide) (by decide) hrd
      (by decide) (by decide) h.htifIdle)

theorem store {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R hq hσ => isSome_of (fun w hw => obs_store_other' hobs R hq hw) hσ)
    (obs_store_other' hobs _ (by decide) h.htifIdle)

theorem btaken {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R hq hσ => isSome_of (fun w hw => obs_btaken_other' hobs R hq hw) hσ)
    (obs_btaken_other' hobs _ (by decide) h.htifIdle)

theorem bnottaken
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R hq hσ => isSome_of (fun w hw => obs_bnottaken_other' hobs R hq hw) hσ)
    (obs_bnottaken_other' hobs _ (by decide) h.htifIdle)

theorem jr {tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R hq hσ => isSome_of (fun w hw => obs_jr_other' hobs R hq hw) hσ)
    (obs_jr_other' hobs _ (by decide) h.htifIdle)

end Lua.Vm.RegsOk
