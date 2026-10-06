import Lua.Vm.Sim.Kit.Eq
import Lua.Vm.Sim.Kit.Lngstr
import Lua.Vm.Sim.Kit.Cond

/-!
# `OP_EQ` on two long strings, and `sim_EQ` (round-4 bake-off, S-SCAN, held out)

`luaV_equalobj` on two long strings (variant 20) jumps to `0x8001b8f8`,
which tail-calls `luaS_eqlngstr` (`eqlngstr_sum`, through `memcmp_sum`).
The strings' bytes are live by M-str (`Core.str_at`: owned objects outside
the window, so the arm's `savestate` stores and the callee frames below
`sp` miss them). `eq_long` is the arm's path; `sim_EQ` closes
`sim_EQ_of_long`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- The jump table's entry for long strings (variant 20). -/
theorem eq_jump_lng {m : Mem} (hro : RodataRead m) {V : BitVec 64} (hV : V = BitVec.ofNat 64 20) :
    BitVec.update (((sign_extend (m := 64) (bytesT4 m (((shift_bits_left V
      (Sail.BitVec.extractLsb (0x02#6) 5 0)) + eqTB) + sign_extend (m := 64) (0x000#12)).toNat :
        BitVec (8 * 4))) + eqTB) + sign_extend (m := 64) (0x000#12)) 0 0#1 = 0x8001b8f8#64 := by
  subst hV
  rw [show ((shift_bits_left (BitVec.ofNat 64 20) (Sail.BitVec.extractLsb (0x02#6) 5 0)) + eqTB +
    sign_extend (m := 64) (0x000#12)).toNat = 0x80053310 + 4 * 20 by decide +kernel,
    eqWord_eq hro (by decide)]
  decide +kernel

/-- **Two live long strings** at `luaV_equalobj`'s entry: their views, apart
from the callee frames below `sp`, one object for one content. -/
structure LngPair (m : Mem) (sp t1 t2 : Nat) (s1 s2 : List UInt8) : Prop where
  a1 : StrAt m t1 s1 (sp - 64) sp
  a2 : StrAt m t2 s2 (sp - 64) sp
  inj : t1 = t2 → s1 = s2

/-- A long string's tag. -/
theorem _root_.Lua.Vm.Sim.ValRepr.long_of_tag {mo : Mem} {ι : Strs} {x : BitVec 64} {v : Value}
    (h : ValRepr mo ι 84#8 x v) : ∃ s, v = .str s ∧ maxShortLen < s.length := by
  generalize ht : (84#8 : BitVec 8) = t at h
  cases h with
  | str =>
    rename_i s _ _ _
    refine ⟨s, rfl, ?_⟩
    unfold strTag at ht; split at ht
    · exact absurd ht (by decide)
    · omega
  | _ => exact absurd ht (by decide)

/-- **Two represented long strings are live** at a call made after the
arm's `Scratch` stores. -/
theorem _root_.Lua.Vm.Sim.Core.lng_pair {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {t1 t2 : BitVec 8} {x1 x2 : BitVec 64} {s1 s2 : List UInt8}
    (h1 : ValRepr w.mo w.ι t1 x1 (.str s1)) (h2 : ValRepr w.mo w.ι t2 x2 (.str s2)) {m : Mem}
    (hm : ∀ a, ¬ Scratch w a → m[a]? = c.σ.mem[a]?) : LngPair m w.sp x1.toNat x2.toNat s1 s2 := by
  have a1 := hc.str_at h1 hm; have a2 := hc.str_at h2 hm
  have hsp := hc.ranges.sp_eq
  simp only [RuntimeData.spEntry, cStackBudget, execFrame] at hsp a1 a2
  exact ⟨⟨a1.view, a1.apart.mono (by omega) (by omega)⟩, ⟨a2.view, a2.apart.mono (by omega) (by omega)⟩,
    fun e => TStringRepr.inj h1.tsr (e ▸ h2.tsr)⟩

theorem bv_ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- `AgreeOut` through the caller's store below the callee's frame. -/
theorem AgreeOut.wm8_trans {m m' : Mem} {lo hi a : Nat} {d : BitVec (8 * 8)} (h : AgreeOut m' (writeMap8 m a d) lo hi)
    {lo' : Nat} (h1 : lo' ≤ lo) (h2 : lo' ≤ a) (h3 : a + 8 ≤ hi) : AgreeOut m' m lo' hi := fun x hx => by
  rw [h x (by omega), getElem?_writeMap8_out m a d x (by omega)]

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [bytesT1_writeMap8_out,
      bytesT1_tag n1, bytesT1_tag n2, slotTag_wm8, ht1, ht2])

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
    | (kit_bv_norm; decide)
    | (rw [eq_jump_lng hro' (by kit_bv_norm; decide)]; decide))

/-- **`luaV_equalobj` on two long strings**: `a0` is `1` iff the contents
are equal; the memory changes only in the callee frames `[sp - 48, sp)`. -/
theorem eqo_long_ex (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) {s1 s2 : List UInt8} (ht1 : slotTag m n1 = 84#8)
    (ht2 : slotTag m n2 = 84#8) (hl1 : maxShortLen < s1.length) (hl2 : maxShortLen < s2.length)
    (hp : LngPair m sp (slotVal m n1).toNat (slotVal m n2).toNat s1 s2) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (RetAt r (BitVec.ofNat 64 sp) f (writeMap8 m (sp - 8) (sdData_val r)) o
        (if s1 = s2 then 1#64 else 0#64)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hro' : RodataRead (eqMem(m, sp, r)) :=
    RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch)
  kit_run h acc
  have h := h.at (pc' := 0x8001b8f8#64) (by rw [eq_jump_lng hro' (by kit_bv_norm; decide)])
  kit_run h acc until [0x80017184]
  simp only [ld_ra, sp_back] at h
  have e1 : (BitVec.ofNat 64 n1 + sign_extend (m := 64) (0x000#12) + sign_extend (m := 64) (0x000#12)).toNat = n1 := by kit_disch
  have e2 : (BitVec.ofNat 64 n2 + sign_extend (m := 64) (0x000#12) + sign_extend (m := 64) (0x000#12)).toNat = n2 := by kit_disch
  rw [e1, e2] at h
  simp (disch := kit_disch) only [bytesT8_wm8_out] at h
  rw [sext64_id, sext64_id, show bytesT8 m n1 = slotVal m n1 from rfl, show bytesT8 m n2 = slotVal m n2 from rfl,
    ← bv_ofNat_toNat (slotVal m n1), ← bv_ofNat_toNat (slotVal m n2)] at h
  have hk : ((BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x028#12)).toNat
      = sp - 8 := by kit_disch
  have v1 := hp.a1.view; have v2 := hp.a2.view
  have := v1.lo; have := v2.lo
  obtain ⟨_, acc, ⟨m', hm', h⟩⟩ := h.call acc (by pins_of h)
    (eqlngstr_sum _ _ s1 s2 r sp f _ o
      ⟨hra, by omega, by omega, by omega, by rw [hk]; exact v1.wm8 hp.a1.apart (by omega) (by omega) _,
        by rw [hk]; exact v2.wm8 hp.a2.apart (by omega) (by omega) _, hl1, hl2,
        hp.a1.apart.mono (by omega) (by omega), hp.a2.apart.mono (by omega) (by omega), hp.inj⟩)
  have e : m' = writeMap8 m (sp - 8) (sdData_val r) := by
    rcases hm' with rfl | rfl <;> simp only [hk, writeMap8_idem]
  exact ⟨_, acc, e ▸ h⟩

/-- **`luaV_equalobj` on two long strings**, the memory as a frame: changed
only in `[sp - 48, sp)`. -/
theorem eqo_long (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) {s1 s2 : List UInt8} (ht1 : slotTag m n1 = 84#8)
    (ht2 : slotTag m n2 = 84#8) (hl1 : maxShortLen < s1.length) (hl2 : maxShortLen < s2.length)
    (hp : LngPair m sp (slotVal m n1).toNat (slotVal m n2).toNat s1 s2) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (RetOut r (BitVec.ofNat 64 sp) f m o (sp - 48) sp (if s1 = s2 then 1#64 else 0#64)) := fun c h =>
  have := hx.sp_lo
  let ⟨c', hs, h'⟩ := eqo_long_ex L r n1 n2 sp f m o hx ht1 ht2 hl1 hl2 hp c h
  ⟨c', hs, ⟨⟨_, AgreeOut.writeMap8 (AgreeOut.refl m (sp - 48) sp) (sdData_val r) (k := sp - 8) (by omega)
    (by omega), h'⟩⟩⟩

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [kraw_eq, bne_ite_prop])

set_option hygiene false in
/-- Reads after the call: from `luaV_equalobj`'s output memory `m'` back to
the arm's (`hO`, outside the callee frames). -/
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [AgreeOut.bytesT4 hO] at $h:ident)

set_option hygiene false in
/-- The frame through `luaV_equalobj`'s output memory. -/
local macro_rules | `(tactic| kit_frame) => `(tactic| (
  intro x hx
  simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget, not_or,
    not_and, Nat.not_lt] at hx
  rw [hO x (by omega)]
  simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]))

/-- **`OP_EQ` on two long strings** (`luaS_eqlngstr` → `memcmp`): both exits
of `docondjump`. -/
theorem eq_long : ArmBody .EQ fun p c s w ins => ¬ EqShort p c s w ins :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hl => by
  kit_setup 0x8001c690
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  simp only [EqShort, Classical.not_not] at hl
  rw [hl.1] at hva; rw [hl.2] at hvb
  obtain ⟨s1, rfl, hl1⟩ := hva.long_of_tag
  obtain ⟨s2, rfl, hl2⟩ := hvb.long_of_tag
  kit_run h0 acc until [0x8001b780]
  have hro : RodataRead c.σ.mem := hc.rodata
  obtain ⟨_, acc, ⟨m', hO, h0⟩⟩ := h0.call acc (by pins_of h0)
    (eqo_long _ _ (w.slot ins.a) (w.slot ins.b) w.sp kframe? _ _
      ⟨RodataRead.wm8 (RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch))
          (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch),
        by decide, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch, by kit_disch,
        by kit_disch⟩
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl.1)
      (by simp (disch := kit_disch) only [slotTag_wm8]; exact hl.2) hl1 hl2
      (by simp (disch := kit_disch) only [slotVal_wm8]
          exact hc.lng_pair hva hvb (by kit_frame)))
  dsimp only [RetAt] at h0
  have hLci := hr.L_sep_ci; simp only [stateSize, ciSize] at hLci
  kit_cond (decide (s1 = s2))

/-- **`sim_EQ`**: `OP_EQ` simulates its kernel off its float paths
(`FloatArms.EQ`), every such path proved. -/
theorem sim_EQ : SimArmOn .EQ (Off FltAB) := sim_EQ_of_long eq_long

end Lua.Vm.Sim.Kit
