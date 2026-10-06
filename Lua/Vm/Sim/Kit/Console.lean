import Lua.Vm.Sim.Kit.Scan
import Vsa.Sim.HtifStepObs

/-!
# The HTIF console store as a segment step (A0.2, lane F1-6)

A console store is one `sd rs2, imm(rs1)` whose effective address is
`tohost`. It is MMIO: memory is unchanged and the Sail HTIF registers append
the character to `sailOutput` (`stepObs_tohost_putchar`). The generated
segments stop before it (`gen_lua_arms.py` `TOHOST_SEAMS`); this file is the
seam: `segSt_putc` takes a `SegSt` state at the store to the state after it,
the pins and memory unchanged and the console one character longer. It is the
`SegSt` face of `VsaIris.Inst.putc_runFact` (the Iris route's console rule,
`VsaIris/Vsa/Console.lean`), stated over the store's decoded fields so that
each site is one instance (`putcSite_write`: htif.c's `htif_putc`, inlined in
`_write`).

`pushes o bs` is the console after the characters `bs`, and `output_pushes`
reads it as a string.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- The HTIF putchar command word for byte `c` (device 1, command 1). -/
abbrev putcWord (c : BitVec 8) : BitVec 64 := 0x0101000000000000#64 ||| BitVec.zeroExtend 64 c

/-- What one putchar store prints. -/
abbrev putcStr (c : BitVec 8) : String := toString (Char.ofNat c.toNat)

/-- **The console after the characters `bs`**, one chunk per store. -/
def pushes (o : Array String) : List (BitVec 8) → Array String
  | [] => o
  | c :: cs => pushes (o.push (putcStr c)) cs

theorem pushes_append (o : Array String) (as bs : List (BitVec 8)) :
    pushes o (as ++ bs) = pushes (pushes o as) bs := by
  induction as generalizing o with
  | nil => rfl
  | cons a as ih => exact ih _

theorem pushes_snoc (o : Array String) (bs : List (BitVec 8)) (c : BitVec 8) :
    pushes o (bs ++ [c]) = (pushes o bs).push (putcStr c) := by
  rw [pushes_append]; rfl

/-- The characters of a byte list, one `Char` per byte (the console's view). -/
def charsOf (bs : List (BitVec 8)) : String := String.ofList (bs.map fun c => Char.ofNat c.toNat)

/-- **The console's text after `pushes`**: the old text and the bytes. -/
theorem output_pushes (o : Array String) (bs : List (BitVec 8)) :
    String.join (pushes o bs).toList = String.join o.toList ++ charsOf bs := by
  induction bs generalizing o with
  | nil => simp [pushes, charsOf]
  | cons c cs ih =>
    rw [pushes, ih, Array.toList_push, String.join_append]
    simp [charsOf, String.ofList_cons, putcStr, String.append_assoc]
    rfl

/-- A register the putchar step leaves alone (the frame of
`stepObs_tohost_putchar`). -/
def putcQuiet (R : Register) : Bool :=
  !(Register.PC == R) && !(Register.minstret == R) && !(Register.minstret_increment == R) &&
    !(Register.nextPC == R) && !(Register.htif_cmd_write == R) && !(Register.htif_payload_writes == R) &&
    !(Register.htif_tohost == R) && !(Register.mip == R) && !(Register.mtime == R) &&
    !(Register.mcycle == R)

/-- Pins of quiet registers survive the putchar step. -/
theorem pinsHold_putcFrame {σ' σ : MState}
    (hframe : ∀ R : Register,
      (Register.PC == R) = false → (Register.minstret == R) = false →
      (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
      (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_tohost == R) = false →
      (Register.mip == R) = false → (Register.mtime == R) = false →
      (Register.mcycle == R) = false →
      σ'.regs.get? R = σ.regs.get? R) :
    ∀ {L : List Pin}, L.all (fun p => putcQuiet p.1) = true → PinsHold σ L → PinsHold σ' L
  | [], _, _ => trivial
  | p :: L, hq, ⟨h1, h2⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hq
    obtain ⟨hq, hL⟩ := hq
    simp only [putcQuiet, Bool.and_eq_true, Bool.not_eq_true'] at hq
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩, q6⟩, q7⟩, q8⟩, q9⟩, q10⟩ := hq
    exact ⟨(hframe _ q1 q2 q3 q4 q5 q6 q7 q8 q9 q10).trans h1, pinsHold_putcFrame hframe hL h2⟩

/-- GPRs through the putchar step's register frame. -/
theorem gprGet_putcFrame {σ' σ : MState}
    (hframe : ∀ R : Register,
      (Register.PC == R) = false → (Register.minstret == R) = false →
      (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
      (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_tohost == R) = false →
      (Register.mip == R) = false → (Register.mtime == R) = false →
      (Register.mcycle == R) = false →
      σ'.regs.get? R = σ.regs.get? R) (n : Nat) :
    gprGet σ' n = gprGet σ n := by
  unfold gprGet
  split <;> first
    | rfl
    | exact hframe _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **A console store as a segment step.** At a store `sd rs2, imm(rs1)` whose
address `base + imm` is `tohost` and whose data is the putchar word of `c`,
one step goes to the next instruction with the pins (quiet registers) and the
memory unchanged and `c` appended to the console. -/
theorem segSt_putc {pc base data : BitVec 64} {w : BitVec 32} {imm : BitVec 12} {r1 r2 : Nat}
    {b0 b1 b2 b3 c : BitVec 8} {L : List Pin} {m : Mem} {o : Array String}
    (hword : ((b3.append b2).append b1).append b0 = w)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0 = (0b11#2 : BitVec 2))
    (hdec : ∀ σ : MState, GoodState σ → (ext_decode w).run (afterPrelude σ) =
      .ok (instruction.STORE (imm, gprIdx r2, gprIdx r1, 8)) (afterPrelude σ))
    (hcode : ∀ mem : Mem, Lua.Vm.Arms.TextLoaded mem → mem[pc.toNat]? = some b0 ∧
      mem[pc.toNat + 1]? = some b1 ∧ mem[pc.toNat + 2]? = some b2 ∧ mem[pc.toNat + 3]? = some b3)
    (haddr : base + sign_extend (m := 64) imm = BitVec.ofNat 64 tohostAddr)
    (hr1 : r1 ≤ 31) (hr2 : r2 ≤ 31)
    (hp1 : ∀ σ : MState, PinsHold σ L → srcPin σ r1 base)
    (hp2 : ∀ σ : MState, PinsHold σ L → srcPin σ r2 data)
    (hdata : data = putcWord c)
    (hlo : 0x80000000 ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ tohostAddr) (hal : pc.toNat % 4 = 0)
    (hq : L.all (fun p => putcQuiet p.1) = true) :
    Triple (SegSt pc L (ArmPay m o)) (SegSt (BitVec.addInt pc 4) L (ArmPay m (o.push (putcStr c)))) := by
  intro cf h
  obtain ⟨hT, hM, hO, hR⟩ := h.extra
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨th, hth⟩ := h.good.htif_tohost
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hcode _ hT
  obtain ⟨σ', i', hstep, hi', hG', hmem', hout', hpc', hmi', hpw', _, hframe⟩ :=
    stepObs_tohost_putchar cf.σ cf.tick cf.steps pc vm w imm (gprIdx r2) (gprIdx r1) base data
      (putcWord c) c th b0 b1 b2 b3 h.good h.pcAt hvm hword hnotrvc (hdec _ h.good)
      (rX_src cf.σ pc r1 hr1 base (hp1 _ h.pins)) (rX_src cf.σ pc r2 hr2 data (hp2 _ h.pins))
      haddr hdata hR.htifIdle hth rfl hb0 hb1 hb2 hb3 hlo hhi hal h.tick
  have hgpr := gprGet_putcFrame hframe
  refine ⟨⟨σ', i', cf.steps + 1⟩, .head hstep (.refl _), ?_⟩
  refine ⟨hG', hpc', pinsHold_putcFrame hframe hq h.pins, hmi', hi', ?_, ?_, ?_, ?_⟩
  · show Lua.Vm.Arms.TextLoaded σ'.mem
    rw [hmem']; exact hT
  · show σ'.mem = m
    rw [hmem']; exact hM
  · show σ'.sailOutput = o.push (putcStr c)
    rw [hout', hO]
  · exact ⟨fun n h1 h2 => by rw [hgpr n]; exact hR.gpr n h1 h2, hpw'⟩

end Lua.Vm.Sim.Kit
