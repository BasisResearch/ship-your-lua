import Lua.Vm.Arms.RegsOk
import Vsa.Sim.SnprintfSitesRet5

/-!
# `RegsOk` across a linking `jalr` (an indirect call)

The `jalr` step class of `scripts/syi/gen_segment.py` (`jalr ra, 0(a5)`: stdio
calling a `FILE`'s hook). Apart from `Lua/Vm/Arms/RegsOk.lean` so that only the
segment modules with such a step import the copied `jalr` observation layer
(`Vsa/Sim/SnprintfSitesRet5.lean`).
-/

open LeanRV64DExecutable Vsa Vsa.Sim
open Vsa.Machine (MState)

namespace Lua.Vm.RegsOk

variable {σ σ' : MState} {pc vm : BitVec 64}

theorem jalr {tgt : BitVec 64} {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd link))
    (hrd : (rd == Register.htif_payload_writes) = false) (h : RegsOk σ) : RegsOk σ' :=
  h.of_step (fun R ⟨d1, d2, d3, d4, d5, d6, d7⟩ hσ => by
      cases hR : (rd == R)
      · exact isSome_of (fun w hw => obs_jalr_other hobs R d1 d2 d3 d4 d5 hR d6 d7 hw) hσ
      · obtain rfl := beq_iff_eq.1 hR
        rw [obs_jalr_rd hobs d1 d2 d3 d4 d5]; rfl)
    (obs_jalr_other hobs _ (by decide) (by decide) (by decide) (by decide) (by decide) hrd
      (by decide) (by decide) h.htifIdle)

end Lua.Vm.RegsOk
