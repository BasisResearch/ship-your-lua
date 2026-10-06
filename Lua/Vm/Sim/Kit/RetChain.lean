import Lua.Vm.Sim.Kit.RetArm
import Lua.Vm.Arms.Segs.HluaD_callnoyield
import Lua.Vm.Arms.Segs.HluaD_rawrunprotected
import Lua.Vm.Arms.Segs.HluaD_pcall
import Lua.Vm.Arms.Segs.Hlua_pcallk
import Lua.Vm.Arms.Segs.Hmain
import Lua.Vm.Arms.Segs.Hstart

/-!
# The C return chain: `ccall` → … → `main` → `_start` → `exit` (lane F1-4)

After `luaV_execute` returns into `ccall` (`AtCcall`), the C callers return in
turn, each reloading its saved registers from the caller frames above the
entry `sp`, which the boot left in place (`Complement.callers`, the words
`ChainMem` names, read off `RuntimeData.callerFrames` by `framesRd`):

* `ccall` (`luaD_callnoyield`'s tail): `L->nCcalls -= 0x10001`, `s0` = `L`;
* `luaD_rawrunprotected`: `L->nCcalls`, `L->errorJmp` restored, the status
  `lj.status = 0`;
* `luaD_pcall`: status 0 (`bnez` not taken), `L->errfunc` restored;
* `lua_pcallk`: `nresults = 0` (`bltz` not taken);
* `main`: status 0, `return 0`;
* `_start`: `j exit` with `a0 = 0`.

The stores go through the caller frames' copies of `L`
(`Complement.callerL`) and are dirty words (`RetDirty`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- A segment's bytes as a partial view. -/
def segView (s : Nat × List UInt8) : View := fun k =>
  if s.1 ≤ k ∧ k < s.1 + s.2.length then some (BitVec.ofNat 8 (s.2.getD (k - s.1) 0).toNat) else none

/-- **A little-endian read of the caller frames' boot bytes**, if inside one segment. -/
def framesRd (a n : Nat) : Option Nat :=
  RuntimeData.callerFrames.findSome? fun s =>
    if s.1 ≤ a ∧ a + n ≤ s.1 + s.2.length then rdLEf (segView s) a n else none

theorem framesRd_rdLE {m : Mem} (h : SegsAt m RuntimeData.callerFrames) {a n x : Nat}
    (hr : framesRd a n = some x) : rdLE m a n = some x := by
  obtain ⟨s, hs, he⟩ := List.exists_of_findSome?_eq_some hr
  split at he
  · rename_i hc
    have := (h s hs).rdLE (o := a - s.1) (n := n) (x := x)
      (by rw [show s.1 + (a - s.1) = a by omega]; exact he)
    rwa [show s.1 + (a - s.1) = a by omega] at this
  · cases he

/-- **The caller-frame words the chain reads**, through the agreement. -/
structure ChainMem (w : RelPtrs) (M : Mem) : Prop where
  ccall_s0 : bytesT8 M 0x87fffe30 = BitVec.ofNat 64 w.L
  ccall_ra : bytesT8 M 0x87fffe38 = 0x80009c38#64
  rawrun_L : bytesT8 M 0x87fffe40 = BitVec.ofNat 64 w.L
  status : bytesT4 M 0x87ffff38 = 0#32
  rawrun_ra : bytesT8 M 0x87ffff48 = 0x8000b4c0#64
  pcall_s1 : bytesT8 M 0x87ffff88 = 0#64
  pcall_ra : bytesT8 M 0x87ffff98 = 0x8000413c#64
  pcallk_ra : bytesT8 M 0x87ffffd8 = 0x80001808#64
  main_ra : bytesT8 M 0x87fffff8 = 0x80000038#64

/-- The machine's reads of the caller frames are the complement's. -/
theorem _root_.Lua.Vm.Sim.Core.callers8 {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {M : Mem} (hM : RAgree w c.σ.mem M) {a : Nat} (h1 : RuntimeData.spEntry ≤ a)
    (h2 : a + 8 ≤ 0x88000000) : bytesT8 M a = bytesT8 w.mo a := by
  have hr := hc.ranges
  have a1 := hr.ci_top; have a2 := hr.L_top; have a3 := hr.sp_eq; have a4 := hr.slots_top
  rw [hM.bytesT8 fun i hi => by
    simp only [RetDirty, ciFuncOff, ciSavedpcOff, ciNresOff, stateTopOff, stateCiOff,
      stateErrorJmpOff, stateErrfuncOff, stateNCcallsOff, ciSize, stateSize, execFrame] at a1 a2 a3 ⊢
    omega]
  exact hc.mo8 fun i hi => by
    simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, execFrame, ciSavedpcOff,
      stateTopOff, ciSize, stateSize] at a1 a2 a3 a4 ⊢
    omega

theorem _root_.Lua.Vm.Sim.Core.callers4 {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {M : Mem} (hM : RAgree w c.σ.mem M) {a : Nat} (h1 : RuntimeData.spEntry ≤ a)
    (h2 : a + 4 ≤ 0x88000000) : bytesT4 M a = bytesT4 w.mo a := by
  have hr := hc.ranges
  have a1 := hr.ci_top; have a2 := hr.L_top; have a3 := hr.sp_eq; have a4 := hr.slots_top
  rw [hM.bytesT4 fun i hi => by
    simp only [RetDirty, ciFuncOff, ciSavedpcOff, ciNresOff, stateTopOff, stateCiOff,
      stateErrorJmpOff, stateErrfuncOff, stateNCcallsOff, ciSize, stateSize, execFrame] at a1 a2 a3 ⊢
    omega]
  exact hc.mo4 fun i hi => by
    simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, execFrame, ciSavedpcOff,
      stateTopOff, ciSize, stateSize] at a1 a2 a3 a4 ⊢
    omega

theorem chainMem {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {M : Mem} (hM : RAgree w c.σ.mem M) : ChainMem w M := by
  have hf := hc.comp.callers
  have hL := hc.comp.callerL
  have e8 : ∀ a x, framesRd a 8 = some x → RuntimeData.spEntry ≤ a → a + 8 ≤ 0x88000000 →
      bytesT8 M a = BitVec.ofNat 64 x := fun a x hx h1 h2 => by
    rw [hc.callers8 hM h1 h2]; exact bytesT8_of_rd64 (framesRd_rdLE hf hx)
  have eL : ∀ a, a ∈ RuntimeData.callerLSlots → bytesT8 M a = BitVec.ofNat 64 w.L := fun a ha => by
    have := callerLSlots_above a ha
    rw [hc.callers8 hM this.1 this.2]; exact hL a ha
  exact ⟨eL _ (by decide), e8 _ _ (by decide +kernel) (by decide) (by decide),
    eL _ (by decide),
    by rw [hc.callers4 hM (by decide) (by decide)]
       exact bytesT4_of_rd32 (framesRd_rdLE hf (x := 0) (by decide +kernel)),
    e8 _ _ (by decide +kernel) (by decide) (by decide), e8 _ _ (by decide +kernel) (by decide) (by decide),
    e8 _ _ (by decide +kernel) (by decide) (by decide), e8 _ _ (by decide +kernel) (by decide) (by decide),
    e8 _ _ (by decide +kernel) (by decide) (by decide)⟩

/-- The registers at `exit`'s entry: `a0 = 0`, `sp = __stack_top`, `ra` after
`_start`'s `jal main`, `gp`, and some callee-saved values. -/
abbrev exitRow (q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64) : List Pin :=
  [⟨Register.x10, 0#64⟩, ⟨Register.x1, 0x80000038#64⟩, ⟨Register.x2, 0x88000000#64⟩,
   ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩, ⟨Register.x8, q8⟩, ⟨Register.x9, q9⟩,
   ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩, ⟨Register.x21, q21⟩,
   ⟨Register.x22, q22⟩, ⟨Register.x23, q23⟩, ⟨Register.x24, q24⟩, ⟨Register.x25, q25⟩,
   ⟨Register.x26, q26⟩, ⟨Register.x27, q27⟩]

/-- **At `exit(0)`**: the memory in agreement with the head's. -/
def AtExit (w : RelPtrs) (m0 : Mem) (o : Array String) (c : Config) : Prop :=
  ∃ M q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27, RAgree w m0 M ∧
    SegSt (BitVec.ofNat 64 symCExit) (exitRow q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27)
      (ArmPay M o) c

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    bytesT8_wm8_out', bytesT8_wm4_out', bytesT4_wm8_out'', bytesT4_wm4_out', sext64_id,
    hT.ccall_s0, hT.ccall_ra, hT.rawrun_L, hT.status, hT.rawrun_ra, hT.pcall_s1, hT.pcall_ra,
    hT.pcallk_ra, hT.main_ra, sext32_zero, Nat.reduceAdd] at $h:ident)

set_option hygiene false in
local macro_rules | `(tactic| kit_side_pre) => `(tactic|
  simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.reduceAdd,
    sext64_id, bytesT8_wm8_out', bytesT8_wm4_out', hT.ccall_s0, hT.rawrun_L])

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.reduceAdd,
          sext64_id, Vsa.Sim.sext_zero, BitVec.add_zero, hT.ccall_ra, hT.rawrun_ra, hT.pcall_ra,
          hT.pcallk_ra, hT.main_ra, bytesT8_wm8_out', bytesT8_wm4_out']
         rw [rtgt _ (by decide)]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.reduceAdd,
          sext64_id, sext32_zero, hT.status, hT.pcall_s1, bytesT8_wm8_out', bytesT8_wm4_out',
          bytesT4_wm8_out'', bytesT4_wm4_out']; decide))

/-- **The C return chain**: from the return into `ccall` to `exit(0)`. -/
theorem ret_chain {p : Proto} {c0 : Config} {s : State} {w : RelPtrs} (hc : Core p c0 s w)
    (o : Array String) : Triple (AtCcall w c0.σ.mem o) (AtExit w c0.σ.mem o) := by
  rintro c ⟨M, hM, h⟩
  have acc := Steps.refl c
  have hT := chainMem hc hM
  have hr := hc.ranges
  ret_facts hr
  simp only [retRow, RuntimeData.retCcall, RuntimeData.spEntry] at h
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc until [0x8002f85c]
  exact ⟨_, acc, _, _, _, _, _, _, _, _, _, _, _, _, _, hM.trans (by ret_agree),
    h.repin (by pins_of h)⟩

end Lua.Vm.Sim.Ret
