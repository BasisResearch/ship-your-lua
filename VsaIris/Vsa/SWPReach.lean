import VsaIris.Vsa.SymRun
import VsaIris.Adequacy

/-!
# A local run reaches its end condition, exactly (lane F1-A0-M)

`LocalRun.reach`: from a concrete configuration holding the owned values, a
local run over `vsaModel` reaches, in finitely many Sail steps, a configuration
whose owned values satisfy `Q`, with every register off `rs` unchanged, every
byte off `S` unchanged *exactly* (`σ.mem[a]?`, from `LocalStep.pres_frame`)
and the console exactly as it was (`OutStep none`'s `quiet`).

This is how an `SWP` proof (the allocator's, `VsaIris/Vsa/{Malloc,Free}*.lean`)
lands on the Lua route's segment states (`Vsa.Sim.SegSt`), which pin the
memory and the console exactly (`Lua.Vm.Sim.ArmPay`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config Steps)

/-- An option is determined by its total read and its presence. -/
theorem opt_eq_of_getD {o o' : Option (BitVec 8)} (hd : o'.getD 0 = o.getD 0)
    (hp : (o'.isSome = true) ↔ (o.isSome = true)) : o' = o := by
  cases o <;> cases o' <;> simp_all

/-- **What a local run leaves** at its end `c'`, from `c`. -/
structure RunEnd (live : Nat → Prop) (rs : List Nat) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (c c' : Config) : Prop where
  steps : Steps c c'
  ok : VsaOk live c'
  regs : ∀ k, k ∉ rs → vsaReg c' k = vsaReg c k
  mem : ∀ a, ¬ S a → c'.σ.mem[a]? = c.σ.mem[a]?
  out : c'.σ.sailOutput = c.σ.sailOutput
  /-- the end condition, at owned values the end configuration holds -/
  post : ∃ rv mv, Q rv mv ∧ (∀ r ∈ rs, vsaReg c' r = rv r) ∧
    (∀ a, S a → (c'.σ.mem[a]?).getD 0 = mv a)

theorem RunEnd.refl {live : Nat → Prop} {rs : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {c : Config} (hok : VsaOk live c)
    {rv : Nat → BitVec 64} {mv : Nat → BitVec 8} (hq : Q rv mv)
    (hr : ∀ r ∈ rs, vsaReg c r = rv r) (hm : ∀ a, S a → (c.σ.mem[a]?).getD 0 = mv a) :
    RunEnd live rs S Q c c :=
  ⟨.refl c, hok, fun _ _ => rfl, fun _ _ => rfl, rfl, rv, mv, hq, hr, hm⟩

/-- **A local run reaches its end condition**, with exact frames. The text is
off the owned bytes and `gp` off the owned registers (the read-only cells
survive every segment). -/
theorem LocalRun.reach {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (htext : ∀ p ∈ text, ¬ S p.1) (hgp : gp ∉ rs) :
    ∀ n rv mv, LocalRun (vsaModel live) roR text rs S Q n rv mv →
    ∀ c : Config, VsaOk live c → ROHolds (vsaModel live) c roR text →
      (∀ r ∈ rs, vsaReg c r = rv r) → (∀ a, S a → (c.σ.mem[a]?).getD 0 = mv a) →
      ∃ c', RunEnd live rs S Q c c'
  | 0, _, _, h, c, hok, _, hr, hm => ⟨c, RunEnd.refl hok h hr hm⟩
  | n + 1, rv, mv, h, c, hok, hro, hr, hm => by
    rcases h with h | ⟨k, hseg⟩
    · exact ⟨c, RunEnd.refl hok h hr hm⟩
    obtain ⟨c1, hre, hok1, hregs1, hmems1, hout1, hP⟩ := hseg c hok hro hr hm
    have hro1 : ROHolds (vsaModel live) c1 roR text := by
      refine ⟨fun p hp => ?_, fun p hp => ?_⟩
      · simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact (hregs1 gp hgp).trans (hro.1 (gp, gpV) (by simp [roR]))
      · exact (hmems1 p.1 (htext p hp)).1.trans (hro.2 p hp)
    obtain ⟨c', E⟩ := LocalRun.reach htext hgp n _ _ hP c1 hok1 hro1 (fun _ _ => rfl)
      (fun _ _ => rfl)
    refine ⟨c', ⟨(steps_of_reaches hre.reaches).trans E.steps, E.ok, fun k hk => ?_, fun a ha => ?_,
      E.out.trans hout1.2, E.post⟩⟩
    · exact (E.regs k hk).trans (hregs1 k hk)
    · exact (E.mem a ha).trans (opt_eq_of_getD (hmems1 a ha).1 (hmems1 a ha).2)

end VsaIris.Sym
