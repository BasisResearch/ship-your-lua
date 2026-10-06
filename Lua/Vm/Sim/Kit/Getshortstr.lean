import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Arms.Segs.HluaH_getshortstr

/-!
# `luaH_getshortstr` at the Lua ELF's address (lane F1-7)

`luaH_getshortstr(t, key)` (`0x8001808c`, ltable.c): the main position
`node + sizeof(Node)·(key->hash & (2^lsizenode - 1))` (`0x8001808c`, `sllw`
of `1`, `addiw -1`, `and`, `·24` as `slli 1; add; slli 3`), then the chain
loop at `0x800180d8`: a node whose key tag is `LUA_VSHRSTR` (`lbu 9`) and key
pointer `key` (`ld 16`) is returned (`ret`); otherwise `gnext` (`lw 12`) moves
to the next node, and a zero `gnext` returns `absentkey` (`0x800180ec`, a
stop of the helper segments: the walk `Lua.Vm.shrWalk` the summary assumes
never takes it).

The loop is `seg_loop` over the walk's fuel: one pass either returns at a
hit or re-enters the loop head at the next node with less fuel. The summary
reads only the table header, the key's hash and the node array, and stores
nothing.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## The arithmetic of the main position and of `gnext` -/

/-- `luaH_getshortstr`'s mask `(1 << lsizenode) - 1`, as `sllw`/`addiw` compute it. -/
abbrev gsMask (b : BitVec 8) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (shift_bits_left
    (Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x001#12)) 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (zero_extend (m := 64) (b : BitVec (8 * 1))) 31 0) 4 0)))
    + sign_extend (m := 64) (0xfff#12)) 31 0)

/-- The mask for every `lsizenode` below 31, one kernel check. -/
theorem gsMask_all : ∀ b : BitVec 8, b.toNat < 31 → gsMask b = BitVec.ofNat 64 (2 ^ b.toNat - 1) := by
  decide

theorem gsMask_eq {b : BitVec 8} (h : b.toNat < 31) : gsMask b = BitVec.ofNat 64 (2 ^ b.toNat - 1) :=
  gsMask_all b h

/-- `lw`'s sign extension. -/
theorem sext32_toNat (g : BitVec 32) : (sign_extend (m := 64) g).toNat =
    if g.toNat < 2 ^ 31 then g.toNat else g.toNat + (2 ^ 64 - 2 ^ 32) := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  have := g.isLt
  rw [BitVec.msb_eq_decide]
  by_cases hm : g.toNat < 2 ^ 31 <;> simp [hm] <;> split <;> omega

/-- A sign-extended word keeps its low 32 bits. -/
theorem sext32_mod (h : BitVec 32) {l : Nat} (hl : l ≤ 32) :
    (sign_extend (m := 64) h).toNat % 2 ^ l = h.toNat % 2 ^ l := by
  have e : (sign_extend (m := 64) h).toNat % 2 ^ 32 = h.toNat := by
    rw [sext32_toNat]; have := h.isLt; split <;> omega
  have hd : 2 ^ l ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hl
  rw [← Nat.mod_mod_of_dvd _ hd, e]

/-- The masked hash. -/
theorem gs_and {l : Nat} (hl : l < 31) (h : BitVec 32) :
    BitVec.ofNat 64 (2 ^ l - 1) &&& sign_extend (m := 64) h = BitVec.ofNat 64 (h.toNat % 2 ^ l) := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ l ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) (by omega)
  have hm := Nat.mod_lt h.toNat (Nat.two_pow_pos l)
  have h1 : (2 ^ l - 1) % 2 ^ 64 = 2 ^ l - 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : h.toNat % 2 ^ l % 2 ^ 64 = h.toNat % 2 ^ l := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1, h2, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, sext32_mod h (by omega)]

/-- `x · 24` as `slli 1; add; slli 3`, added to a node pointer. -/
theorem gs_x24 (n x : Nat) :
    BitVec.ofNat 64 n + shift_bits_left (shift_bits_left (BitVec.ofNat 64 x)
      (Sail.BitVec.extractLsb (0x01#6) 5 0) + BitVec.ofNat 64 x) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (n + nodeSize * x) := by
  rw [shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, nodeSize]
  rw [show n + (x * 2 ^ 1 + x) * 2 ^ 3 = n + 24 * x by omega]

/-- **The main position** of `luaH_getshortstr`'s first segment. -/
theorem gs_mpos (n : Nat) (b : BitVec 8) (h : BitVec 32) (hb : b.toNat < 31) :
    BitVec.ofNat 64 n + shift_bits_left (shift_bits_left (gsMask b &&& sign_extend (m := 64) h)
      (Sail.BitVec.extractLsb (0x01#6) 5 0) + (gsMask b &&& sign_extend (m := 64) h))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (n + nodeSize * (h.toNat % 2 ^ b.toNat)) := by
  rw [gsMask_eq hb, gs_and hb, gs_x24]

/-- **`gnext`**: the next node, `n + 24·sext(gnext)` with the 64-bit wrap
(`Lua.Vm.nodeNext`). -/
theorem gs_next (n : Nat) (g : BitVec 32) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n + shift_bits_left (shift_bits_left (sign_extend (m := 64) g)
      (Sail.BitVec.extractLsb (0x01#6) 5 0) + sign_extend (m := 64) g) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (nodeNext n g.toNat) := by
  have e : sign_extend (m := 64) g =
      BitVec.ofNat 64 (if g.toNat < 2 ^ 31 then g.toNat else g.toNat + (2 ^ 64 - 2 ^ 32)) := by
    apply BitVec.eq_of_toNat_eq
    rw [sext32_toNat, BitVec.toNat_ofNat]
    have := g.isLt
    split <;> omega
  rw [e, gs_x24]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, nodeNext, Nat.mod_mod]

/-! ## The guards -/

theorem gs_addr {n k : Nat} (hk : k < 2048) (h : n + k < 2 ^ 64) :
    (BitVec.ofNat 64 n + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat = n + k := by
  rw [add_imm _ _ hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gs_68 : (0#64 : BitVec 64) + sign_extend (m := 64) (0x044#12) =
    zero_extend (m := 64) ((BitVec.ofNat 8 vShrStr : BitVec 8) : BitVec (8 * 1)) := by decide

/-- The key tag against `LUA_VSHRSTR`. -/
theorem gs_tt {m : Mem} {n : Nat} (hn : n + 9 < 2 ^ 64) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 n + sign_extend (m := 64) (0x009#12)).toNat :
      BitVec (8 * 1))) != (0#64) + sign_extend (m := 64) (0x044#12)) =
      !decide (bytesT1 m (n + nodeKeyTtOff) = BitVec.ofNat 8 vShrStr) := by
  rw [gs_addr (by decide) hn, gs_68, bne, zext8_beq]; rfl

theorem bne_dec {x y : BitVec 64} : (x != y) = !decide (x = y) := by
  by_cases h : x = y <;> simp [h]

/-- The key pointer against `key`. -/
theorem gs_kv {m : Mem} {n : Nat} {key : BitVec 64} (hn : n + 16 < 2 ^ 64) :
    ((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 n + sign_extend (m := 64) (0x010#12)).toNat :
      BitVec (8 * 8))) != key) = !decide (bytesT8 m (n + nodeKeyValOff) = key) := by
  rw [gs_addr (by decide) hn, sext64_id, bne_dec]; rfl

/-- `gnext` against zero. -/
theorem gs_g {m : Mem} {n : Nat} (hn : n + 12 < 2 ^ 64) :
    ((sign_extend (m := 64) (bytesT4 m (BitVec.ofNat 64 n + sign_extend (m := 64) (0x00c#12)).toNat :
      BitVec (8 * 4))) == (0#64)) = decide (bytesT4 m (n + nodeNextOff) = 0#32) := by
  rw [gs_addr (by decide) hn]
  have : ∀ g : BitVec 32, (sign_extend (m := 64) g == 0#64) = decide (g = 0#32) := by
    intro g
    by_cases h : g = 0#32
    · subst h; decide
    · simp only [h, decide_false, beq_eq_false_iff_ne]
      intro e; apply h
      apply BitVec.eq_of_toNat_eq
      have := congrArg (fun x : BitVec 64 => x.toNat % 2 ^ 32) e
      simp only [sext32_mod g (Nat.le_refl 32)] at this
      simpa [Nat.mod_eq_of_lt g.isLt] using this
  exact this _

/-! ## The summary -/

/-- What the walk needs: `EnvMem`'s table for the closure `cl`, the key `ts`,
the return address, and the objects in RAM above `tohost`. -/
structure GsCtx (m : Mem) (cl ts : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  tab_lo : tohostAddr + 16 ≤ Env.tab m cl
  tab_hi : Env.tab m cl + 32 ≤ 2 ^ 32
  key_lo : tohostAddr + 16 ≤ ts
  key_hi : ts + 16 ≤ 2 ^ 32
  node_lo : tohostAddr + 16 ≤ Env.node m cl
  node_hi : Env.node m cl + Env.size m cl ≤ 2 ^ 32
  lsz_lt : Env.lsz m cl < 31
  found : Env.find m cl ts = some (Env.pnode m cl ts)

/-- `luaH_getshortstr`'s entry pins. -/
abbrev gsPre (t : Nat) (key r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 t⟩ :: ⟨Register.x11, key⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- The loop head `0x800180d8` at node `n`. -/
abbrev gsHead (n : Nat) (key r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x13, (0#64) + sign_extend (m := 64) (0x044#12)⟩ ::
    ⟨Register.x1, r⟩ :: ⟨Register.x11, key⟩ :: f.pins

/-- The return: `a0` the found node. -/
abbrev gsRet (pn : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String) : Config → Prop :=
  SegSt r (⟨Register.x10, BitVec.ofNat 64 pn⟩ :: f.pins) (ArmPay m o)

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
/-- The loop's guards, from the pass's facts about the node. -/
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | (rw [gs_tt (by omega)]; simp only [htt, decide_true, decide_false, Bool.not_true, Bool.not_false])
      | (rw [gs_kv (by omega)]; simp only [hkv, decide_true, decide_false, Bool.not_true, Bool.not_false])
      | (rw [gs_g (by omega)]; simp only [hg, decide_false])
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

/-- **The chain loop** from the loop head at node `n` with walk fuel `f`: it
returns the node the walk finds. -/
theorem gs_loop (ts lo hi pn : Nat) (key r : BitVec 64) (fr : HFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hk : key = BitVec.ofNat 64 ts) (hts : ts < 2 ^ 64)
    (hlo : tohostAddr + 16 ≤ lo) (hhi : hi ≤ 2 ^ 32) :
    ∀ fn : Nat × Nat, Triple (fun c => shrWalk (totR m) ts lo hi fn.1 fn.2 = some pn ∧
        SegSt 0x800180d8#64 (gsHead fn.2 key r fr) (ArmPay m o) c) (gsRet pn r fr m o) := by
  refine seg_loop (fun fn => fn.1) fun fn c ⟨hw, h⟩ => ?_
  obtain ⟨f, n⟩ := fn
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  cases f with
  | zero => simp [shrWalk] at hw
  | succ f =>
  unfold shrWalk at hw
  by_cases hn : lo ≤ n ∧ n + nodeSize ≤ hi
  · rw [if_pos hn] at hw
    simp only [totR] at hw
    obtain ⟨hn1, hn2⟩ := hn
    simp only [nodeSize] at hn2
    rw [bytesT_one_eq, bytesT_eight_eq, bytesT_four_eq] at hw
    have ett : ((bytesT1 m (n + nodeKeyTtOff)).toNat = vShrStr) ↔
        bytesT1 m (n + nodeKeyTtOff) = BitVec.ofNat 8 vShrStr := by
      constructor
      · intro e; apply BitVec.eq_of_toNat_eq; rw [e]; rfl
      · intro e; rw [e]; rfl
    have ekv : ((bytesT8 m (n + nodeKeyValOff)).toNat = ts) ↔ bytesT8 m (n + nodeKeyValOff) = key := by
      rw [hk]; constructor
      · intro e; apply BitVec.eq_of_toNat_eq; rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hts]
      · intro e; rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hts]
    by_cases hhit : (bytesT1 m (n + nodeKeyTtOff)).toNat = vShrStr ∧ (bytesT8 m (n + nodeKeyValOff)).toNat = ts
    · rw [if_pos hhit] at hw
      cases hw
      have htt := ett.1 hhit.1
      have hkv := ekv.1 hhit.2
      kit_seg h acc Lua.Vm.Arms.seg_800180d8_800180e0_n
      kit_seg h acc Lua.Vm.Arms.seg_800180e0_800180e8_n
      kit_seg h acc Lua.Vm.Arms.seg_800180e8_800180ec
      have h := h.at (by simpa [Vsa.Sim.sext_zero] using Vsa.Sim.ret_tgt r hra)
      exact ⟨_, acc, .inr (h.repin (by pins_of h))⟩
    · rw [if_neg hhit] at hw
      by_cases hg0 : (bytesT4 m (n + nodeNextOff)).toNat = 0
      · rw [if_pos hg0] at hw; cases hw
      rw [if_neg hg0] at hw
      have hg : bytesT4 m (n + nodeNextOff) ≠ 0#32 := fun e => hg0 (by rw [e]; rfl)
      -- to `0x800180c0`: a key tag that is not a short string, or another key
      obtain ⟨c1, hs1, h1⟩ : ∃ c1, Steps c c1 ∧ ∃ L, SegSt 0x800180c0#64 L (ArmPay m o) c1 ∧
          PinsHold c1.σ (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x11, key⟩ ::
            ⟨Register.x13, (0#64) + sign_extend (m := 64) (0x044#12)⟩ :: fr.pins) := by
        by_cases htt' : bytesT1 m (n + nodeKeyTtOff) = BitVec.ofNat 8 vShrStr
        · have htt := htt'
          have hkv : bytesT8 m (n + nodeKeyValOff) ≠ key := fun e => hhit ⟨ett.2 htt', ekv.2 e⟩
          kit_seg h acc Lua.Vm.Arms.seg_800180d8_800180e0_n
          kit_seg h acc Lua.Vm.Arms.seg_800180e0_800180e8_t
          exact ⟨_, acc, _, h, by pins_of h⟩
        · have htt := htt'
          kit_seg h acc Lua.Vm.Arms.seg_800180d8_800180e0_t
          exact ⟨_, acc, _, h, by pins_of h⟩
      obtain ⟨L, h, hP⟩ := h1
      have h := h.repin (L' := ⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x11, key⟩ :: ⟨Register.x13, (0#64) + sign_extend (m := 64) (0x044#12)⟩ :: fr.pins)
        hP
      have acc := hs1
      kit_seg h acc Lua.Vm.Arms.seg_800180c0_800180d4_n
      kit_seg h acc Lua.Vm.Arms.seg_800180d4_800180d8
      rw [gs_addr (by decide) (by omega), gs_next n _ (by omega)] at h
      refine ⟨_, acc, .inl ⟨(f, nodeNext n (bytesT4 m (n + nodeNextOff)).toNat), by simp, ?_,
        h.repin (by pins_of h)⟩⟩
      simpa [nodeNextOff] using hw
  · rw [if_neg hn] at hw; cases hw

/-- The main position as the first segment leaves it in `a0`. -/
theorem gs_mp_eq {m : Mem} {cl ts : Nat} (hl : Env.lsz m cl < 31) :
    sign_extend (m := 64) (bytesT8 m (Env.tab m cl + 24) : BitVec (8 * 8)) +
      shift_bits_left (shift_bits_left (gsMask (bytesT1 m (Env.tab m cl + 11)) &&&
        sign_extend (m := 64) (bytesT4 m (ts + 12) : BitVec (8 * 4))) (Sail.BitVec.extractLsb (0x01#6) 5 0) +
        (gsMask (bytesT1 m (Env.tab m cl + 11)) &&& sign_extend (m := 64) (bytesT4 m (ts + 12) : BitVec (8 * 4))))
        (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (Env.mpos m cl ts) := by
  have e : bytesT8 m (Env.tab m cl + 24) = BitVec.ofNat 64 (Env.node m cl) := by
    simp only [Env.node, tableNodeOff, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [sext64_id, e, gs_mpos _ (bytesT1 m (Env.tab m cl + 11)) _ hl]
  rfl

/-- **`luaH_getshortstr`, the call-node summary**: on `EnvMem`'s table and key
(`GsCtx`), it returns the node the walk finds, memory unchanged. -/
theorem getshortstr_sum (cl ts : Nat) (key r : BitVec 64) (fr : HFrame) (m : Mem) (o : Array String)
    (hx : GsCtx m cl ts r) (hk : key = BitVec.ofNat 64 ts) :
    Triple (SegSt 0x8001808c#64 (gsPre (Env.tab m cl) key r fr) (ArmPay m o))
      (gsRet (Env.pnode m cl ts) r fr m o) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hx.tab_lo; have := hx.tab_hi; have := hx.key_lo; have := hx.key_hi
  subst hk
  kit_seg h acc Lua.Vm.Arms.seg_8001808c_800180c0
  rw [gs_addr (by decide) (by omega), gs_addr (by decide) (by omega), gs_addr (by decide) (by omega),
    gs_mp_eq hx.lsz_lt] at h
  have hl := hx.node_lo; have hh := hx.node_hi
  simp only [Env.size] at hh
  obtain ⟨c', hs, h'⟩ := gs_loop ts (Env.node m cl) (Env.node m cl + Env.size m cl) (Env.pnode m cl ts)
    _ r fr m o hx.ra rfl (by omega) hl (by simp only [Env.size]; omega)
    (2 ^ Env.lsz m cl, Env.mpos m cl ts) _ ⟨hx.found, h.repin (by pins_of h)⟩
  exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit
