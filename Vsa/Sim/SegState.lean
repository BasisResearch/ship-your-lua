import Vsa.Sim.RegPins

/-!
# `SegState`: a generic segment-state record over `RegPins`

The generic part of ship-your-interpreter's `Vsa/Sim/SegState.lean` (its
`StMvF0` bridge and worked example are memmove instances and stay there).
`scripts/syi/gen_segment.py` with `"boundary": "segst"` states every
generated segment as `Triple (SegSt entry L P) (SegSt exit L' P')`.

`SegSt pcv L P c` holds the five harness facts every segment state carries,
`GoodState`, the PC pin, the tracked-register pins `L` (`RegPins`), minstret
existence and the tick bound, plus a payload `P : MState → Prop` (code bytes
loaded, the memory as an expression over the segment's parameters).
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- Generic segment state: the machine sits at `pcv` with the tracked pins
`L`, the standard harness facts, and the segment payload `P`. -/
structure SegSt (pcv : BitVec 64) (L : List Pin) (P : MState → Prop) (c : Config) : Prop where
  good : GoodState c.σ
  pcAt : c.σ.regs.get? Register.PC = some pcv
  pins : PinsHold c.σ L
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  extra : P c.σ

/-- Pins for a sublist still hold (drop stale pins, or thin the list at a
segment boundary). -/
theorem pinsHold_sublist {σ : MState} {L' L : List Pin}
    (hs : List.Sublist L' L) (h : PinsHold σ L) : PinsHold σ L' := by
  induction hs with
  | slnil => trivial
  | cons _ _ ih => exact ih h.2
  | cons_cons _ _ ih => exact ⟨h.1, ih h.2⟩

/-- Extend a pin list with a freshly written register. -/
theorem pins_cons {σ : MState} {R : Register} {v : RegisterType R} {L : List Pin}
    (h1 : σ.regs.get? R = some v) (h : PinsHold σ L) :
    PinsHold σ (⟨R, v⟩ :: L) := ⟨h1, h⟩

/-- Weaken a `SegSt` in place: thin the pin list, weaken the payload. -/
theorem SegSt.weaken {pcv : BitVec 64} {L L' : List Pin} {P P' : MState → Prop} {c : Config}
    (h : SegSt pcv L P c) (hsub : List.Sublist L' L) (hP : P c.σ → P' c.σ) :
    SegSt pcv L' P' c :=
  ⟨h.good, h.pcAt, pinsHold_sublist hsub h.pins, h.minstret, h.tick, hP h.extra⟩

end Vsa.Sim
