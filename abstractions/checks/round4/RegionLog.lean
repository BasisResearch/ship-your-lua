import Lua.Vm.Sim.Kit.Modk

/-!
# Round 4 falsifier: a region-tagged write log for `savestate`

Measurement only (not imported by `Lua`). The claim under test (round-1
ontologists): with the path's memory as a region-tagged write log, a guarded
load through `savestate`'s two stores costs under 10k heartbeats (likely
1–3k), against 15–20k (and 38k / 42k per segment) on the kit route
(`ProfModk.lean`).

The minimum built here, once:

* `Rgn` (the register slots, `K`, `ci->u.l.savedpc`, `L->top`, the C frame),
  their bases and sizes;
* `Ent`, `applyLog` (8-byte stores at `region base + offset`), the Boolean
  forwarder `fwd` and `fwd_sound` (+ `rl_load1`, `rl_load8`);
* `RSep` and `rsep_of_ranges`: the regions pairwise disjoint, from `Ranges`;
* `saveMem_log`: `savestate`'s memory (`saveMem`) as a two-entry log;
* `kslot_toNat`: `K[C]`'s address as the arm computes it, `k + (16·C + j)`;
* `kArr_ram`: the `K` region inside RAM and apart from `tohost`.

Measured (2026-10-02, base 26fa7a6; ROUND-4.md §2c): a guarded load through
`savestate` costs 0.18–0.53k on the region log against 16.9–18.2k with the
kit's closers; seg2/seg4 6.6/6.4k against 38.3/42.3k (`kit_run`); MODK's
general path as ONE declaration (`modk_rz_one`) 138.8k under the default
200k budget.

    lake env lean abstractions/checks/round4/RegionLog.lean
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.RegionLog

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (Config)

/-- The regions a `K` arm's path touches. -/
inductive Rgn | slots | kArr | savedpc | ltop | cframe
  deriving DecidableEq

/-- A region's base address. -/
def Rgn.base (w : RelPtrs) : Rgn → Nat
  | .slots => w.base
  | .kArr => w.k
  | .savedpc => w.ci + ciSavedpcOff
  | .ltop => w.L + stateTopOff
  | .cframe => w.sp

/-- A region's size. -/
def Rgn.size (p : Proto) : Rgn → Nat
  | .slots => stackValueSize * p.maxstacksize
  | .kArr => stackValueSize * p.k.length
  | .savedpc => 8
  | .ltop => 8
  | .cframe => execFrame

/-- `a` lies in region `r`. -/
def RIn (p : Proto) (w : RelPtrs) (r : Rgn) (a : Nat) : Prop :=
  r.base w ≤ a ∧ a < r.base w + r.size p

/-- The regions are pairwise disjoint. -/
def RSep (p : Proto) (w : RelPtrs) : Prop :=
  ∀ r r' a, RIn p w r a → RIn p w r' a → r = r'

/-- A log entry: an 8-byte store at `region base + off`. -/
structure Ent where
  r : Rgn
  off : Nat
  d : BitVec (8 * 8)

/-- The log applied, oldest entry first. -/
def applyLog (w : RelPtrs) (m : Mem) : List Ent → Mem
  | [] => m
  | e :: es => applyLog w (writeMap8 m (e.r.base w + e.off) e.d) es

/-- Every entry inside its region. -/
def LogOk (p : Proto) : List Ent → Prop
  | [] => True
  | e :: es => e.off + 8 ≤ e.r.size p ∧ LogOk p es

/-- **The forwarder**: the `n` bytes at `r + off` miss every entry (another
region, or disjoint offsets). Region tags first, so a cross-region read
reduces by tags alone (offsets may be symbolic). -/
def fwd (r : Rgn) (off n : Nat) : List Ent → Bool
  | [] => true
  | e :: es => (e.r != r || (decide (off + n ≤ e.off) || decide (e.off + 8 ≤ off))) && fwd r off n es

/-- **`fwd_sound`**: a forwarded byte is the base memory's. -/
theorem fwd_sound {p : Proto} {w : RelPtrs} (hs : RSep p w) {r : Rgn} {off n : Nat}
    (hr : off + n ≤ r.size p) {i : Nat} (hi : i < n) :
    ∀ (log : List Ent) (m : Mem), LogOk p log → fwd r off n log = true →
      (applyLog w m log)[r.base w + off + i]? = m[r.base w + off + i]?
  | [], _, _, _ => rfl
  | e :: es, m, ⟨he, hes⟩, hf => by
    simp only [fwd, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [applyLog, fwd_sound hs hr hi es _ hes hf2]
    apply getElem?_writeMap8_out
    by_cases heq : e.r = r
    · rw [heq] at he ⊢
      rcases hf1 with h | h
      · exact absurd heq h
      · omega
    · exact Classical.byContradiction fun hc =>
        heq (hs e.r r (r.base w + off + i) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)

/-- A forwarded `lbu`. -/
theorem rl_load1 {p : Proto} {w : RelPtrs} (hs : RSep p w) {log : List Ent} (hok : LogOk p log)
    {m M : Mem} (hM : M = applyLog w m log) {r : Rgn} {off X : Nat} (hX : X = r.base w + off)
    (hr : off + 1 ≤ r.size p) (hf : fwd r off 1 log = true) :
    bytesT1 M X = bytesT1 m (r.base w + off) := by
  subst hM hX
  simp only [bytesT1]
  rw [← Nat.add_zero (r.base w + off), fwd_sound hs hr (by decide) log m hok hf]

/-- A forwarded `ld`. -/
theorem rl_load8 {p : Proto} {w : RelPtrs} (hs : RSep p w) {log : List Ent} (hok : LogOk p log)
    {m M : Mem} (hM : M = applyLog w m log) {r : Rgn} {off X : Nat} (hX : X = r.base w + off)
    (hr : off + 8 ≤ r.size p) (hf : fwd r off 8 log = true) :
    bytesT8 M X = bytesT8 m (r.base w + off) := by
  subst hM hX
  exact bytesT8_congr fun i hi => fwd_sound hs hr hi log m hok hf

/-- **Region separation, once, from `Ranges`.** -/
theorem rsep_of_ranges {p : Proto} {w : RelPtrs} (hr : Ranges p w) : RSep p w := by
  have ko := hr.k_out
  have := hr.k_sep; have := hr.ci_sep; have := hr.L_sep; have := hr.frame_sep
  have := hr.L_sep_ci; have := hr.L_top; have := hr.ci_top; have := hr.sp_eq
  simp only [Win, Slots, Scratch, RuntimeData.spEntry, cStackBudget, execFrame,
    ciSavedpcOff, stateTopOff, ciSize, stateSize, stackValueSize] at *
  intro r r' a h h'
  cases r <;> cases r' <;> simp only [RIn, Rgn.base, Rgn.size, ciSavedpcOff, stateTopOff,
    execFrame, stackValueSize] at h h' <;> first
    | rfl
    | (exfalso; omega)
    | (exfalso; exact ko a (by omega) (by omega) (by omega))

/-- `savestate`'s two stores as a log. -/
abbrev saveLog (c : Config) (s : State) (w : RelPtrs) : List Ent :=
  [⟨.savedpc, 0, sdData_val (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1)))⟩,
   ⟨.ltop, 0, sdData_val (sign_extend (m := 64)
      (bytesT8 c.σ.mem (BitVec.ofNat 64 w.ci + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8)))⟩]

theorem saveLog_ok (p : Proto) (c : Config) (s : State) (w : RelPtrs) : LogOk p (saveLog c s w) :=
  ⟨Nat.le_refl 8, Nat.le_refl 8, trivial⟩

/-- **`saveMem` is the log** (once, for every path). -/
theorem saveMem_log {p : Proto} {w : RelPtrs} (hr : Ranges p w) (c : Config) (s : State) :
    Kit.saveMem c s w = applyLog w c.σ.mem (saveLog c s w) := by
  have := hr.ci_hi; have := hr.L_top
  simp only [ciSize, stateSize, RuntimeData.spEntry, cStackBudget] at *
  simp only [Kit.saveMem, applyLog, Rgn.base, ciSavedpcOff, stateTopOff, Nat.add_zero]
  rw [add_imm _ 32 (by decide), add_imm _ 16 (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **`K[C]`'s address** (`srliw 24`, `slli 4`, `add k`, `+ j`). -/
theorem kslot_toNat (k j : Nat) (x : BitVec 32) (hk : k < 2 ^ 32) (hj : j < 2048) :
    (BitVec.ofNat 64 k + shift_bits_left (sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (BitVec.ofNat 5 24)))
      (Sail.BitVec.extractLsb (0x04#6) 5 0) + sign_extend (m := 64) (BitVec.ofNat 12 j)).toNat
      = k + (16 * Word.c x + j) := by
  rw [extract_sext, sext_shr x 24 (by decide) (by decide), shl_ofNat _ 4 (by decide),
    BitVec.ofNat_add_ofNat, add_imm _ j hj, BitVec.toNat_ofNat]
  have hx := x.isLt
  have : x.toNat >>> 24 < 2 ^ 8 := by rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [Word.c, Word.field, Nat.mod_eq_of_lt this]
  omega

/-- `K[C]`'s address, for the arm's `w`. -/
theorem kslot_addr {w : RelPtrs} (j : Nat) (x : BitVec 32) (hk : w.k < 2 ^ 32) (hj : j < 2048) :
    (BitVec.ofNat 64 w.k + shift_bits_left (sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (BitVec.ofNat 5 24)))
      (Sail.BitVec.extractLsb (0x04#6) 5 0) + sign_extend (m := 64) (BitVec.ofNat 12 j)).toNat
      = Rgn.kArr.base w + (16 * Word.c x + j) :=
  kslot_toNat w.k j x hk hj

/-- The `K` region is RAM, apart from `tohost` (the segments' bus checks). -/
structure RamOk (a n : Nat) : Prop where
  lo : 0x80000000 ≤ a
  hi : a + n ≤ 0x100000000
  ht : a + n ≤ tohostAddr ∨ tohostAddr + 8 ≤ a

theorem kArr_ram {p : Proto} {w : RelPtrs} (hr : Ranges p w) {off n : Nat}
    (h : off + n ≤ Rgn.kArr.size p) : RamOk (Rgn.kArr.base w + off) n := by
  have := hr.k_lo; have := hr.k_hi
  simp only [Rgn.base, Rgn.size, tohostAddr, stackValueSize] at *
  have ht : tohostAddr = 0x8005c6c0 := rfl
  exact ⟨by omega, by omega, .inr (by omega)⟩

/-- A read inside `K[C]`'s slot. -/
theorem kin {c S j n : Nat} (h : 16 * c + 16 ≤ S) (hj : j + n ≤ 16) : 16 * c + j + n ≤ S := by
  omega

/-- `K[C]`'s tag, from the arm's fact about it. -/
theorem ktag_eq {m : Mem} {w : RelPtrs} {c : Nat} {t : BitVec 8}
    (h : slotTag m (w.k + stackValueSize * c) = t) : bytesT1 m (Rgn.kArr.base w + (16 * c + 8)) = t := by
  rw [← h]; simp only [slotTag, Rgn.base, stackValueSize, tvalueTagOff, Nat.add_assoc]

/-- `K[C]`'s payload, as `ld` reads it. -/
theorem kval_eq8 {m : Mem} {w : RelPtrs} {c : Nat} :
    sign_extend (m := 64) (bytesT8 m (Rgn.kArr.base w + (16 * c + 0)) : BitVec (8 * 8)) =
      slotVal m (w.k + 16 * c) := by
  rw [sext64_id]; simp only [slotVal, Rgn.base, tvalueValOff, Nat.add_zero]

theorem one_imm : (0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12) = 1#64 := by decide

/-! ## Measurement

`hb` logs the heartbeat counter (thousands). Three versions of `modk_call`'s
pre half (`ProfModk.modk_call'`), identical but for seg2 (`e46c–e474`, the
`lbu` of `K[C]`'s tag and `bne`) and seg4 (`f7a0–f7b0`, the `ld` of `K[C]`'s
payload and `bgeu`):

* `pre_kit`: the kit as is (`kit_run`);
* `pre_kitd`: the segment applied directly (the right polarity named), its
  side conditions by `kit_side`, then `kit_norm`: the kit's closers without
  the polarity search;
* `pre_rl`: the same direct application, its side conditions by the region
  log (`rl_load1`/`rl_load8` + `fwd` by `rfl`, `kslot_addr`, `kArr_ram`). -/

elab "hb " s:str : tactic => do
  let n ← IO.getNumHeartbeats
  Lean.logInfo m!"HB {s.getString} {n / 1000}"

open Lua.Vm.Sim.Kit
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
theorem pre_kit : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "kit start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvK] at hy
  kitk_ints 0x8001dad0
  hb "kit setup"
  have hz := fun e => hy (Or.inl e)
  kit_run h0 acc until [0x8001e46c]
  hb "kit seg1"
  kit_run h0 acc until [0x8001e474]
  hb "kit seg2"
  kit_run h0 acc until [0x8001f7a0]
  hb "kit seg3"
  kit_run h0 acc until [0x8001f7b0]
  hb "kit seg4"
  kit_run h0 acc until [0x8002f7b0]
  hb "kit seg5"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "kit normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "kit call node"
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩

set_option hygiene false in
theorem pre_kitd : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "kitd start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvK] at hy
  kitk_ints 0x8001dad0
  hb "kitd setup"
  have hz := fun e => hy (Or.inl e)
  kit_run h0 acc until [0x8001e46c]
  hb "kitd seg1"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001e46c_8001e474_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "kitd s2 lo <"; kit_side; hb "kitd s2 lo >")
      (by hb "kitd s2 hi <"; kit_side; hb "kitd s2 hi >")
      (by hb "kitd s2 ht <"; kit_side; hb "kitd s2 ht >")
      (by hb "kitd s2 guard <"; kit_side; hb "kitd s2 guard >"))
  hb "kitd seg2 applied"
  try kit_norm h0
  hb "kitd seg2 normalised"
  kit_run h0 acc until [0x8001f7a0]
  hb "kitd seg3"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001f7a0_8001f7b0_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "kitd s4 lo <"; kit_side; hb "kitd s4 lo >")
      (by hb "kitd s4 hi <"; kit_side; hb "kitd s4 hi >")
      (by hb "kitd s4 ht <"; kit_side; hb "kitd s4 ht >")
      (by hb "kitd s4 guard <"; kit_side; hb "kitd s4 guard >"))
  hb "kitd seg4 applied"
  try kit_norm h0
  hb "kitd seg4 normalised"
  kit_run h0 acc until [0x8002f7b0]
  hb "kitd seg5"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "kitd normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "kitd call node"
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩

set_option hygiene false in
theorem pre_rl : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "rl start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvK] at hy
  kitk_ints 0x8001dad0
  hb "rl setup"
  have hz := fun e => hy (Or.inl e)
  -- the region facts, once per arm
  have hs := rsep_of_ranges hr
  have hlog := saveMem_log hr c s
  have hk32 : w.k < 2 ^ 32 := by omega
  have hK16 : 16 * ins.c + 16 ≤ Rgn.kArr.size p := by
    simp only [Rgn.size, stackValueSize, Word.c, Word.field]; omega
  have hok := saveLog_ok p c s w
  hb "rl region setup"
  kit_run h0 acc until [0x8001e46c]
  hb "rl seg1"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001e46c_8001e474_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "rl s2 lo <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).lo; hb "rl s2 lo >")
      (by hb "rl s2 hi <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).hi; hb "rl s2 hi >")
      (by hb "rl s2 ht <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).ht; hb "rl s2 ht >")
      (by hb "rl s2 guard <"
          rw [rl_load1 hs hok hlog (kslot_addr 8 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
            ktag_eq hC]
          decide
          hb "rl s2 guard >"))
  hb "rl seg2 applied"
  kit_run h0 acc until [0x8001f7a0]
  hb "rl seg3"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001f7a0_8001f7b0_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "rl s4 lo <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).lo; hb "rl s4 lo >")
      (by hb "rl s4 hi <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).hi; hb "rl s4 hi >")
      (by hb "rl s4 ht <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).ht; hb "rl s4 ht >")
      (by hb "rl s4 guard <"
          rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
            kval_eq8, one_imm, bgeu_one]
          exact decide_eq_false hy
          hb "rl s4 guard >"))
  hb "rl seg4 applied"
  rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
    kval_eq8] at h0
  hb "rl seg4 normalised"
  kit_run h0 acc until [0x8002f7b0]
  hb "rl seg5"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "rl normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "rl call node"
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩

set_option hygiene false in
/-- **MODK's general path (`x % y = 0`) as ONE declaration**: `pre_rl`'s run
to `__moddi3`'s return, then `modk_rz`'s post half (`kit_div_post`), under
the default budget. -/
theorem modk_rz_one : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.srem y = 0#64) := by
  hb "one start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvK] at hy hq
  kitk_ints 0x8001dad0
  have hz := fun e => hy (Or.inl e)
  have heq := fun m => imodC_eq m _ hz
  simp only [Opnd.fill, δ, BinOp.int, heq] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  hb "one setup"
  -- the region facts, once per arm
  have hs := rsep_of_ranges hr
  have hlog := saveMem_log hr c s
  have hk32 : w.k < 2 ^ 32 := by omega
  have hK16 : 16 * ins.c + 16 ≤ Rgn.kArr.size p := by
    simp only [Rgn.size, stackValueSize, Word.c, Word.field]; omega
  have hok := saveLog_ok p c s w
  hb "one region setup"
  kit_run h0 acc until [0x8001e46c]
  hb "one seg1"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001e46c_8001e474_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "one s2 lo <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).lo; hb "one s2 lo >")
      (by hb "one s2 hi <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).hi; hb "one s2 hi >")
      (by hb "one s2 ht <"; rw [kslot_addr 8 ins hk32 (by decide)]
          exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).ht; hb "one s2 ht >")
      (by hb "one s2 guard <"
          rw [rl_load1 hs hok hlog (kslot_addr 8 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
            ktag_eq hC]
          decide
          hb "one s2 guard >"))
  hb "one seg2 applied"
  kit_run h0 acc until [0x8001f7a0]
  hb "one seg3"
  obtain ⟨_, acc, h0⟩ := Vsa.Sim.SegSt.run acc h0 (by pins_of h0)
    (Lua.Vm.Arms.seg_8001f7a0_8001f7b0_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (by hb "one s4 lo <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).lo; hb "one s4 lo >")
      (by hb "one s4 hi <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).hi; hb "one s4 hi >")
      (by hb "one s4 ht <"; rw [kslot_addr 0 ins hk32 (by decide)]
          exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).ht; hb "one s4 ht >")
      (by hb "one s4 guard <"
          rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
            kval_eq8, one_imm, bgeu_one]
          exact decide_eq_false hy
          hb "one s4 guard >"))
  hb "one seg4 applied"
  rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
    kval_eq8] at h0
  hb "one seg4 normalised"
  kit_run h0 acc until [0x8002f7b0]
  hb "one seg5"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "one normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "one call node"
  have h1 : AtRet c s w 0x8001f7bc
      (divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
        (slotVal c.σ.mem (w.k + 16 * ins.c)))
      ((slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) _ :=
    ⟨h0.repin (by pins_of h0)⟩
  clear h0
  have h0 := h1.seg
  hb "one at return"
  kit_run h0 acc until [0x8001f7cc]
  hb "one post 2 segs"
  kit_run h0 acc
  hb "one to head"
  kit_div_close [hq]
  hb "one close"

/-! ### The region log inside `kit_run`

`kit_side_pre` and `kit_norm` extended (`macro_rules`, tried before the
kit's) with the region-log closers, so `kit_run` itself (with its polarity
search) runs seg2 and seg4. Last in the file: the extension is global. -/

set_option hygiene false in
macro "rl_addr" : tactic => `(tactic| first
  | rw [kslot_addr 8 ins hk32 (by decide)] | rw [kslot_addr 0 ins hk32 (by decide)])

set_option hygiene false in
macro "rl_side" : tactic => `(tactic| first
  | (rl_addr; first
      | exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).lo
      | exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).hi
      | exact (kArr_ram (n := 1) hr (kin hK16 (by decide))).ht
      | exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).lo
      | exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).hi
      | exact (kArr_ram (n := 8) hr (kin hK16 (by decide))).ht)
  | (rw [rl_load1 hs hok hlog (kslot_addr 8 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
        ktag_eq hC]; decide)
  | (rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
        kval_eq8, one_imm, bgeu_one]; exact decide_eq_false hy))

macro_rules | `(tactic| kit_side_pre) => `(tactic| rl_side)

set_option hygiene false in
macro_rules | `(tactic| kit_norm $h) => `(tactic| first
  | rw [rl_load8 hs hok hlog (kslot_addr 0 ins hk32 (by decide)) (kin hK16 (by decide)) rfl,
      kval_eq8] at $h:ident
  | rw [rl_load1 hs hok hlog (kslot_addr 8 ins hk32 (by decide)) (kin hK16 (by decide)) rfl] at $h:ident)

set_option hygiene false in
theorem pre_rlk : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  hb "rlk start"
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy⟩
  have hdvLd := fun {m : Mem} {a : Nat} => @ld_slot_gen m a (w.k + 16 * ins.c)
  simp only [dvK] at hy
  kitk_ints 0x8001dad0
  hb "rlk setup"
  have hz := fun e => hy (Or.inl e)
  have hs := rsep_of_ranges hr
  have hlog := saveMem_log hr c s
  have hk32 : w.k < 2 ^ 32 := by omega
  have hK16 : 16 * ins.c + 16 ≤ Rgn.kArr.size p := by
    simp only [Rgn.size, stackValueSize, Word.c, Word.field]; omega
  have hok := saveLog_ok p c s w
  hb "rlk region setup"
  kit_run h0 acc until [0x8001e46c]
  hb "rlk seg1"
  kit_run h0 acc until [0x8001e474]
  hb "rlk seg2"
  kit_run h0 acc until [0x8001f7a0]
  hb "rlk seg3"
  kit_run h0 acc until [0x8001f7b0]
  hb "rlk seg4"
  kit_run h0 acc until [0x8002f7b0]
  hb "rlk seg5"
  try simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), hdvLd,
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] at h0
  hb "rlk normalise"
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0)
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  hb "rlk call node"
  exact ⟨_, acc, ⟨h0.repin (by pins_of h0)⟩⟩

#print axioms fwd_sound
#print axioms rsep_of_ranges
#print axioms saveMem_log
#print axioms pre_rl
#print axioms pre_rlk
#print axioms modk_rz_one

end Lua.Vm.Sim.RegionLog
