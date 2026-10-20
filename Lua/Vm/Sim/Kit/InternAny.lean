import Lua.Vm.Sim.Kit.Intern
import Lua.Vm.AtF.InternAny

/-!
# `luaS_newlstr` on any short contents: the walk (lane F1-20)

`luaS_newlstr(L, str, l)` (`0x80017694`, `l ≤ 40`: the tail `j
internshrstr`) on contents in a caller's frame (`luaO_pushvfstring`'s
buffer): the hash loop (`hashFrom`, lane F1-15's `hstep_mach`), the bucket
(`bucket_addr`, run by `kit_run`), and the chain walk with `memcmp` over a
chain that is safe (`StrtSafe`, lane F1-19) and alive (`StrtOff`, lane
F1-20): a match returns the node (alive, so `changewhite` does not run); the
end of the chain reaches the creation path (`0x8001742c`), whose run is the
premise `hN` here and `Kit/InternNew.lean`'s theorem.

The walk is measured by its length (`KWalk`, from the boot-checked chain
facts by `kwalk_of`, an induction on those facts, not on the machine run).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The contexts -/

/-- The contexts of `luaS_newlstr/any`'s rows: Nat atoms `ns`; `ra`, the
caller's frame, the hash (`X.b 13`) and `g->ud` (`X.b 14`); the memory. -/
@[at_row] abbrev iaX (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (hh ud : BitVec 64) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, hh, ud] m o

/-- The hash loop's atoms at the cursor `c` (`sp` the entry's). -/
abbrev iaH (sp L s g c : Nat) (b : List UInt8) : List Nat := [sp - 80, L, s, b.length, g, c]

/-- The chain walk's atoms at node `p` (bucket `bkt`, `memcmp`'s answer `k`,
the table's size). -/
abbrev iaC (sp L s g p bkt k size : Nat) (b : List UInt8) : List Nat :=
  [sp - 80, L, s, b.length, g, 0, p, bkt, k, size]

/-- The creation path's atoms (`nuse`, the new object, the old head). -/
abbrev iaN (sp L s g bkt size nuse np head : Nat) (b : List UInt8) : List Nat :=
  [sp - 80, L, s, b.length, g, 0, 0, bkt, 0, size, nuse, np, head]

/-- **What `internshrstr`'s roots know**: the atoms' bounds, the root memory
`M` (the entry's `m` with the frame stored), the contents `b` at `s` (in the
caller's frame above `sp`, 8-aligned: `memcpy`'s source), the saved
registers. -/
structure IaFacts (m M : Mem) (sp L s g : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame) : Prop where
  sp_lo : 0x87800000 + 16384 + 80 ≤ sp
  sp_hi : sp + 80 ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  s_ge : sp ≤ s
  s_hi : s + b.length + 8 ≤ 2 ^ 32
  s_al : s % 8 = 0
  l_lo : 1 ≤ b.length
  l_hi : b.length ≤ 40
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  keep : ∀ a, ¬ Below sp 80 a → bytesT1 M a = bytesT1 m a
  bytes : ∀ i, i < b.length → bytesT1 M (s + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  sv0 : bytesT8 M (sp - 80 + 72) = r
  sv1 : bytesT8 M (sp - 80 + 64) = f.s0
  sv2 : bytesT8 M (sp - 80 + 56) = f.s1
  sv3 : bytesT8 M (sp - 80 + 48) = f.s2
  sv4 : bytesT8 M (sp - 80 + 40) = f.s3
  sv5 : bytesT8 M (sp - 80 + 32) = f.s4
  sv6 : bytesT8 M (sp - 80 + 24) = f.s5
  sv7 : bytesT8 M (sp - 80 + 16) = f.s6
  sv8 : bytesT8 M (sp - 80 + 8) = f.s7

set_option hygiene false in
local macro "ia_ctx" F:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($F).sp_lo; have := ($F).sp_hi; have := ($F).sp_al; have hra := ($F).ra; have := ($F).L_lo
  have := ($F).L_he; have := ($F).L_al; have := ($F).s_ge; have := ($F).s_hi; have := ($F).l_lo
  have := ($F).l_hi; have := ($F).g_lo; have := ($F).g_hi))

/-! ## The walk over the chain -/

/-- `isdead`'s test on a node `p` at the current white `cw` (`lbu`, `xori 24`,
`and`): zero, as bytes. -/
def AliveB (M : Mem) (p : Nat) (cw : BitVec 8) : Prop := bytesT1 M (p + 9) &&& (cw ^^^ 0x18#8) = 0#8

/-- **The walk from `p`, `d` nodes to its end**, over the total reads of
`M`: each node in RAM above the HTIF mailbox with its header, its `u.hnext`,
the facts `P` the callers read off a node found, and, if its length and
contents are `b`'s, room for them and alive. -/
inductive KWalk (M : Mem) (b : List UInt8) (cw : BitVec 8) (P : Nat → Prop) : Nat → Nat → Prop where
  | nil : KWalk M b cw P 0 0
  | cons {d p nx : Nat} : p ≠ 0 → 0x8005c6d0 ≤ p → p + 24 ≤ 0x87800000 → P p →
      bytesT8 M (p + 16) = BitVec.ofNat 64 nx → nx < 2 ^ 64 →
      (bytesT1 M (p + 11) = BitVec.ofNat 8 b.length → p + 24 + b.length + 8 ≤ 2 ^ 32 ∧
        ((∀ i, i < b.length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat) → AliveB M p cw)) →
      KWalk M b cw P d nx → KWalk M b cw P (d + 1) p

/-- **What a found node gives its callers**: its header tag (`LUA_VSHRSTR`'s
`GCObject.tt`), its object in `K` and off `W`, its mark off `X`. -/
structure IaNode (M : Mem) (K X W : Nat → Prop) (p : Nat) : Prop where
  tt : bytesT1 M (p + 8) = 0x04#8
  obj : ∀ a, p ≤ a → a < p + 24 + (bytesT1 M (p + 11)).toNat + 1 → K a ∧ ¬ W a
  mark : ¬ X (p + 9)

/-- A byte of the fill in RAM, read as `some` of the total read. -/
theorem bT1_of_rd8_fill {M : Mem} {a v : Nat} (h : rd8 (fillZeroMem M) a = some v) (hlo : 0x80000000 ≤ a)
    (hhi : a < 0x88000000) : bytesT1 M a = BitVec.ofNat 8 v := by
  rw [rd8_fill hlo hhi, Option.some.injEq] at h
  rw [← h]; simp

/-- **The walk from the chains' facts** (`StrtSafe`'s `StrChainK`, `StrtOff`'s
`ChainOff`, both of the fill of `M`): its length, every node's facts, alive
where it matches `b` (no literal does: `hnl`). -/
theorem kwalk_of {M : Mem} {K X W T : Nat → Prop} {size j cwn : Nat} {lits : List Nat} {b : List UInt8}
    (hK : ∀ a, K a → 0x8006ecd0 ≤ a ∧ a < 0x87800000)
    (hnl : ∀ p ∈ lits, bytesT1 M (p + 11) = BitVec.ofNat 8 b.length →
      (∀ i, i < b.length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat) → False)
    (hbl : b.length ≤ 40) (hcw : cwn < 256) :
    ∀ {p}, StrChainK (fillZeroMem M) K X W size j p → ChainOff (fillZeroMem M) T cwn lits p →
      ∃ d, KWalk M b (BitVec.ofNat 8 cwn) (IaNode M K X W) d p := by
  intro p hs
  induction hs with
  | nil => intro _; exact ⟨0, .nil⟩
  | @cons ts h nx l h0 htt hl hle hh hmod hnx hobj hmk hhn hrest ih =>
    intro ho
    cases ho with
    | nil => exact absurd rfl h0
    | @cons _ nx' l' _ hl' hnx' _ hal hrest' =>
      have e1 : nx' = nx := Option.some.inj (hnx'.symm.trans hnx)
      have e2 : l' = l := Option.some.inj (hl'.symm.trans hl)
      subst e1 e2
      obtain ⟨d, hd⟩ := ih hrest'
      have hc : tstringContentsOff = 24 := rfl
      have hms : maxShortLen = 40 := rfl
      have k0 := hK _ (hobj ts (Nat.le_refl _) (by omega)).1
      have k1 := hK _ (hobj (ts + 24 + l') (by omega) (by omega)).1
      have bl : bytesT1 M (ts + 11) = BitVec.ofNat 8 l' := bT1_of_rd8_fill hl' (by omega) (by omega)
      have hl8 : (bytesT1 M (ts + 11)).toNat = l' := by rw [bl]; simp; omega
      refine ⟨d + 1, .cons h0 (by omega) (by omega) ⟨bT1_of_rd8_fill htt (by omega) (by omega), ?_, hmk⟩
        (bT8_of_fill (bytesT8_of_rd64 hnx)) (rd64_lt hnx) ?_ hd⟩
      · intro a h1 h2
        rw [hl8] at h2
        exact hobj a h1 (by omega)
      · intro hb
        have e : l' = b.length := by
          have := congrArg BitVec.toNat (bl.symm.trans hb); simp at this; omega
        refine ⟨by omega, fun hcont => ?_⟩
        by_cases hlit : ts ∈ lits
        · exact absurd hcont (fun hc' => hnl ts hlit hb hc')
        · obtain ⟨mk, hm, hz⟩ := hal hlit
          have bm : bytesT1 M (ts + 9) = BitVec.ofNat 8 mk := bT1_of_rd8_fill hm (by omega) (by omega)
          have hmk8 : mk < 256 := by
            have := rd8_fill (m := M) (a := ts + 9) (by omega) (by omega)
            rw [show ts + gcMarkedOff = ts + 9 from rfl, this, Option.some.injEq] at hm
            rw [← hm]; exact (bytesT1 M (ts + 9)).isLt
          simp only [AliveB, bm]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmk8,
            Nat.mod_eq_of_lt hcw]
          simpa using hz

/-- `isdead`'s machine test on an alive node: zero. -/
theorem alive_mach (x y : BitVec 8) (h : x &&& (y ^^^ 0x18#8) = 0#8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1)) &&& (zero_extend (m := 64) (y : BitVec (8 * 1)) ^^^
      sign_extend (m := 64) (0x018#12))) == (0#64)) = true := by
  rw [show sign_extend (m := 64) (0x018#12) = BitVec.ofNat 64 24 by decide, beq_iff_eq]
  have h1 := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h1 ⊢
  have hx := x.isLt; have hy := y.isLt
  rw [Nat.mod_eq_of_lt (show x.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y.toNat < 2 ^ 64 by omega)]
  simpa using h1

/-- The return of a found `ts` from the walk's return row: `wrRet`, every byte
but the frame kept. -/
theorem ia_ret {m M : Mem} {sp L s g ts : Nat} {b : List UInt8} {r : BitVec 64} {f : AbiFrame}
    {o : Array String} {c : Config} (F : IaFacts m M sp L s g b r f)
    (h : SegSt r [⟨Register.x1, r⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 80 + 80)⟩, ⟨Register.x3, 0x8005ced0#64⟩,
      ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x10, BitVec.ofNat 64 ts⟩, ⟨Register.x18, f.s2⟩,
      ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩,
      ⟨Register.x23, f.s7⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩,
      ⟨Register.x27, f.s11⟩] (ArmPay M o) c) :
    ∃ m', wrRet r sp ts f m' o c ∧ ∀ a, ¬ Below sp 80 a → bytesT1 m' a = bytesT1 m a := by
  have := F.sp_lo
  rw [show sp - 80 + 80 = sp by omega] at h
  exact ⟨M, h.repin (by pins_of h), F.keep⟩

/-- **A node found**: its facts, `b`'s length and contents, the return. -/
def IaHit (m M : Mem) (K X W : Nat → Prop) (sp ts : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame)
    (o : Array String) (c : Config) : Prop :=
  IaNode M K X W ts ∧ bytesT1 M (ts + 11) = BitVec.ofNat 8 b.length ∧
    (∀ i, i < b.length → bytesT1 M (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat) ∧
    ∃ m', wrRet r sp ts f m' o c ∧ ∀ a, ¬ Below sp 80 a → bytesT1 m' a = bytesT1 m a

/-- **The chain walk** from node `p` (`0x800173f0`), `d` nodes to the chain's
end: `memcmp` (a call node, `memcmp_sumS`) on an equal length; a match is
alive, returned; the end of the chain is the creation path (`hN`). -/
theorem ia_chain (m M : Mem) (sp L s g bkt size : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame)
    (hh ud : BitVec 64) (o : Array String) (F : IaFacts m M sp L s g b r f) (K X W : Nat → Prop)
    (cw : BitVec 8) (hcw : bytesT1 M (g + 100) = cw)
    (hk1 : 0x8005c6d0 ≤ bkt) (hk2 : bkt + 8 ≤ 0x87800000) (_hsz : size < 2 ^ 32) (Q : Config → Prop)
    (hN : ∀ c, SegSt 0x8001742c#64 (Lua.Vm.AtF.InternAny.r15 (iaX (iaN sp L s g bkt size 0 0 0 b) r f hh ud M o))
        (ArmPay (iaX (iaN sp L s g bkt size 0 0 0 b) r f hh ud M o).m (iaX (iaN sp L s g bkt size 0 0 0 b) r f hh ud M o).o) c → ∃ c', Steps c c' ∧ Q c') :
    ∀ dp : Nat × Nat, Triple (fun c => dp.2 ≠ 0 ∧ KWalk M b cw (IaNode M K X W) dp.1 dp.2 ∧
      SegSt 0x800173f0#64 (Lua.Vm.AtF.InternAny.r6 (iaX (iaC sp L s g dp.2 bkt 0 size b) r f hh ud M o))
        (ArmPay (iaX (iaC sp L s g dp.2 bkt 0 size b) r f hh ud M o).m (iaX (iaC sp L s g dp.2 bkt 0 size b) r f hh ud M o).o) c)
      (fun c => Q c ∨ ∃ ts, IaHit m M K X W sp ts b r f o c) := by
  refine seg_loop (fun dp => dp.1) fun ⟨d, p⟩ c ⟨hp0, hch, h⟩ => ?_
  have acc := Steps.refl c
  ia_ctx F
  simp only at hch hp0
  cases hch with
  | nil => exact absurd rfl hp0
  | @cons d p nx _ hlo hhi hP hnx hnxl hm hrest =>
  -- `memcmp(str, getstr(p), l)` from its call row
  have mc : ∀ (k : Nat) (c1 : Config) (Z : Prop), p + 24 + b.length + 8 ≤ 2 ^ 32 →
      (∀ c', Steps c c' → ∀ v : BitVec 64, (v = 0#64 ↔ ∀ j, j < b.length → McEq M s (p + 24) j) →
        SegSt 0x80017408#64 [⟨Register.x10, v⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 80)⟩,
          ⟨Register.x3, 0x8005ced0#64⟩, ⟨Register.x8, BitVec.ofNat 64 p⟩, ⟨Register.x9, hh⟩,
          ⟨Register.x18, BitVec.ofNat 64 s⟩, ⟨Register.x19, BitVec.ofNat 64 g⟩, ⟨Register.x20, BitVec.ofNat 64 L⟩,
          ⟨Register.x21, BitVec.ofNat 64 b.length⟩, ⟨Register.x22, BitVec.ofNat 64 bkt⟩,
          ⟨Register.x23, BitVec.ofNat 64 size⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩,
          ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩] (ArmPay M o) c' → Z) →
      Steps c c1 → SegSt 0x80036198#64 (Lua.Vm.AtF.InternAny.r9 (iaX (iaC sp L s g p bkt k size b) r f hh ud M o))
        (ArmPay (iaX (iaC sp L s g p bkt k size b) r f hh ud M o).m (iaX (iaC sp L s g p bkt k size b) r f hh ud M o).o) c1 → Z := by
    intro k c1 Z hq hZ acc h
    fcx_unfold at h
    obtain ⟨_, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h)
      (memcmp_sumS s (p + 24) b.length 0x80017408#64 (BitVec.ofNat 64 (sp - 80))
        ⟨0x8005ced0#64, BitVec.ofNat 64 p, hh, BitVec.ofNat 64 s, BitVec.ofNat 64 g, BitVec.ofNat 64 L,
          BitVec.ofNat 64 b.length, BitVec.ofNat 64 bkt, BitVec.ofNat 64 size, f.s8, f.s9, f.s10, f.s11⟩ M o
        ⟨by decide, by omega, by omega, .inr (by omega), by omega, by omega⟩)
    dsimp only [RetAtS] at h
    exact hZ _ acc v hv (h.repin (by pins_of h))
  -- the next node's guard, either way
  have hg3 : (bytesT8 M (p + 16) == 0x0#64) = decide (nx = 0) := by
    rw [hnx, show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq hnxl (by decide)]
  have hX : Lua.Vm.AtF.InternAny.Ok_C (iaX (iaC sp L s g p bkt 0 size b) r f hh ud M o) := by fcx_ok
  by_cases hl : bytesT1 M (p + 11) = BitVec.ofNat 8 b.length
  · obtain ⟨hq, hal⟩ := hm hl
    have hg2 : (zero_extend (m := 64) (bytesT1 M (p + 11) : BitVec (8 * 1)) != BitVec.ofNat 64 b.length) =
        false := by
      rw [zext8_ofNat_bne (by omega), hl]; simp
    fat_run Lua.Vm.AtF.InternAny h acc until [0x80036198]
    refine mc 0 _ _ hq (fun c' acc v hv h => ?_) acc h
    by_cases hv0 : v = 0#64
    · -- a match: alive, returned
      subst hv0
      have hcont : ∀ i, i < b.length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat := by
        intro i hi
        have := hv.1 rfl i hi
        simp only [McEq] at this
        rw [← this, F.bytes i hi]
      have halv := hal hcont
      have h : SegSt 0x80017408#64 (Lua.Vm.AtF.InternAny.r10 (iaX (iaC sp L s g p bkt 0 size b) r f hh ud M o))
          (ArmPay (iaX (iaC sp L s g p bkt 0 size b) r f hh ud M o).m
            (iaX (iaC sp L s g p bkt 0 size b) r f hh ud M o).o) c' := by
        fcx_unfold; exact h.repin (by pins_of h)
      have hg5 : (((zero_extend (m := 64) (bytesT1 M ((BitVec.ofNat 64 p) + sign_extend (m := 64)
          (0x009#12)).toNat : BitVec (8 * 1))) &&& ((zero_extend (m := 64) (bytesT1 M ((BitVec.ofNat 64 g) +
          sign_extend (m := 64) (0x064#12)).toNat : BitVec (8 * 1))) ^^^ sign_extend (m := 64) (0x018#12))) ==
          (0#64)) = true := by
        rw [gs_addr (by decide) (by omega), gs_addr (by decide) (by omega), hcw]; exact alive_mach _ _ halv
      have sv0 := F.sv0; have sv1 := F.sv1; have sv2 := F.sv2; have sv3 := F.sv3; have sv4 := F.sv4
      have sv5 := F.sv5; have sv6 := F.sv6; have sv7 := F.sv7; have sv8 := F.sv8
      fat_run Lua.Vm.AtF.InternAny h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr (.inr ⟨p, hP, hl, hcont, ia_ret F h⟩)⟩
    · -- a mismatch: `memcmp`'s answer nonzero, the next node
      have hvn : v.toNat ≠ 0 := fun e => hv0 (BitVec.eq_of_toNat_eq (by simp [e]))
      have hvl := v.isLt
      have hX1 : Lua.Vm.AtF.InternAny.Ok_C (iaX (iaC sp L s g p bkt v.toNat size b) r f hh ud M o) := by fcx_ok
      have h : SegSt 0x80017408#64 (Lua.Vm.AtF.InternAny.r14 (iaX (iaC sp L s g p bkt v.toNat size b) r f hh ud M o))
          (ArmPay (iaX (iaC sp L s g p bkt v.toNat size b) r f hh ud M o).m
            (iaX (iaC sp L s g p bkt v.toNat size b) r f hh ud M o).o) c' := by
        fcx_unfold; rw [ofNat_toNat64 v] at h; exact h.repin (by pins_of h)
      by_cases hz : nx = 0
      · rw [decide_eq_true hz] at hg3
        fat_run Lua.Vm.AtF.InternAny h acc until [0x8001742c]
        fcx_unfold at h
        rw [hnx, hz] at h
        obtain ⟨c2, s2, hq2⟩ := hN _ (by fcx_unfold; exact h.repin (by pins_of h))
        exact ⟨c2, acc.trans s2, .inr (.inl hq2)⟩
      · rw [decide_eq_false hz] at hg3
        fat_run Lua.Vm.AtF.InternAny h acc until [0x800173f0]
        fcx_unfold at h
        rw [hnx] at h
        exact ⟨_, acc, .inl ⟨(d, nx), by simp, hz, hrest, by fcx_unfold; exact h.repin (by pins_of h)⟩⟩
  · -- the lengths differ: the next node
    have hg2 : (zero_extend (m := 64) (bytesT1 M (p + 11) : BitVec (8 * 1)) != BitVec.ofNat 64 b.length) =
        true := by
      rw [zext8_ofNat_bne (by omega)]; simp [hl]
    by_cases hz : nx = 0
    · rw [decide_eq_true hz] at hg3
      fat_run Lua.Vm.AtF.InternAny h acc until [0x8001742c]
      fcx_unfold at h
      rw [hnx, hz] at h
      obtain ⟨c2, s2, hq2⟩ := hN _ (by fcx_unfold; exact h.repin (by pins_of h))
      exact ⟨c2, acc.trans s2, .inr (.inl hq2)⟩
    · rw [decide_eq_false hz] at hg3
      fat_run Lua.Vm.AtF.InternAny h acc until [0x800173f0]
      fcx_unfold at h
      rw [hnx] at h
      exact ⟨_, acc, .inl ⟨(d, nx), by simp, hz, hrest, by fcx_unfold; exact h.repin (by pins_of h)⟩⟩

/-! ## The hash loop and the bucket -/

/-- **`g->strt` as `internshrstr` reads it**: the bucket array `hash` of
`size` words, the head `head` of the hash `H`'s bucket, the walk from it. -/
structure IaTab (M : Mem) (g : Nat) (H : UInt32) (b : List UInt8) (cw : BitVec 8) (P : Nat → Prop)
    (size hash head d : Nat) : Prop where
  size_w : bytesT4 M (g + 60) = BitVec.ofNat 32 size
  hash_w : bytesT8 M (g + 48) = BitVec.ofNat 64 hash
  size_pos : 0 < size
  size_hi : size < 2 ^ 30
  size_pow2 : size &&& (size - 1) = 0
  hash_lo : 0x8005c6c0 + 16 ≤ hash
  hash_hi : hash + 8 * size ≤ 0x87800000
  head_w : bytesT8 M (hash + 8 * (H.toNat % size)) = BitVec.ofNat 64 head
  head_lt : head < 2 ^ 64
  walk : KWalk M b cw P d head

set_option hygiene false in
/-- The bucket segment's address and guard, from the facts `hbk`, `hgb`. -/
local macro_rules | `(tactic| kit_side_pre) => `(tactic| simp only [hbk])

set_option hygiene false in
local macro_rules | `(tactic| kit_guard_ext) => `(tactic| exact hgb)

/-- **The hash loop** (`0x800173a4`) from the cursor `s + k - 1`, the bytes
from `k` on folded in (`hashFrom`); at `k = 1` the bucket, then the walk or the
creation path. -/
theorem ia_hash (m M : Mem) (sp L s g size hash head d : Nat) (b : List UInt8) (seed : UInt32)
    (r : BitVec 64) (f : AbiFrame) (ud : BitVec 64) (o : Array String) (F : IaFacts m M sp L s g b r f)
    (K X W : Nat → Prop) (cw : BitVec 8) (hcw : bytesT1 M (g + 100) = cw)
    (T : IaTab M g (luaHash seed b) b cw (IaNode M K X W) size hash head d) (Q : Config → Prop)
    (hN : ∀ c, SegSt 0x8001742c#64 (Lua.Vm.AtF.InternAny.r15 (iaX (iaN sp L s g
        (hash + 8 * ((luaHash seed b).toNat % size)) size 0 0 0 b) r f (hw (luaHash seed b)) ud M o))
        (ArmPay (iaX (iaN sp L s g (hash + 8 * ((luaHash seed b).toNat % size)) size 0 0 0 b) r f (hw (luaHash seed b)) ud M o).m (iaX (iaN sp L s g (hash + 8 * ((luaHash seed b).toNat % size)) size 0 0 0 b) r f (hw (luaHash seed b)) ud M o).o) c → ∃ c', Steps c c' ∧ Q c') :
    ∀ k, Triple (fun c => 1 ≤ k ∧ k ≤ b.length ∧
      SegSt 0x800173a4#64
        (Lua.Vm.AtF.InternAny.r4 (iaX (iaH sp L s g (s + (k - 1)) b) r f (hw (hashFrom seed b k)) ud M o))
        (ArmPay (iaX (iaH sp L s g (s + (k - 1)) b) r f (hw (hashFrom seed b k)) ud M o).m (iaX (iaH sp L s g (s + (k - 1)) b) r f (hw (hashFrom seed b k)) ud M o).o) c)
      (fun c => Q c ∨ ∃ ts, IaHit m M K X W sp ts b r f o c) := by
  refine seg_loop (fun k => k) fun k c ⟨hk1, hkl, h⟩ => ?_
  have acc := Steps.refl c
  ia_ctx F
  have hX : Lua.Vm.AtF.InternAny.Ok_H (iaX (iaH sp L s g (s + (k - 1)) b) r f (hw (hashFrom seed b k)) ud M o) := by
    fcx_ok
  have hstepk : hw (hstep (UInt8.ofBitVec (bytesT1 M (s + (k - 1)))) (hashFrom seed b k)) =
      hw (hashFrom seed b (k - 1)) := by
    rw [F.bytes (k - 1) (by omega), ofBitVec_byte, hashFrom_step seed b (show k - 1 < b.length by omega),
      show k - 1 + 1 = k by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  by_cases hk : k = 1
  · fat_run Lua.Vm.AtF.InternAny h acc until [0x800173c4]
    fcx_unfold at h
    fat_rd at h
    rw [hstep_mach, hstepk, hk, show (1 : Nat) - 1 = 0 from rfl, hashFrom_zero] at h
    -- the bucket `g->strt.hash[h & (size - 1)]` and its head
    have := T.size_pos; have := T.size_hi; have := T.hash_lo; have := T.hash_hi
    have hmod : (luaHash seed b).toNat % size < size := Nat.mod_lt _ T.size_pos
    have hbk : (sign_extend (m := 64) (bytesT8 M (BitVec.ofNat 64 g + sign_extend (m := 64) (0x030#12)).toNat :
        BitVec (8 * 8))) + shift_bits_left (hw (luaHash seed b) &&& sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) (bytesT4 M (BitVec.ofNat 64 g +
          sign_extend (m := 64) (0x03c#12)).toNat : BitVec (8 * 4))) + sign_extend (m := 64) (0xfff#12)) 31 0))
        (Sail.BitVec.extractLsb (0x03#6) 5 0) =
        BitVec.ofNat 64 (hash + 8 * ((luaHash seed b).toNat % size)) := by
      rw [gs_addr (by decide) (by omega), gs_addr (by decide) (by omega), sext64_id, T.hash_w, T.size_w]
      exact bucket_addr _ hash size T.size_pos T.size_hi T.size_pow2
    have hhl := T.head_lt
    by_cases hh0 : head = 0
    · -- an empty bucket: the creation path
      have hgb : ((sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 (hash + 8 * ((luaHash seed b).toNat % size)) +
          sign_extend (m := 64) (0x000#12)).toNat) : BitVec (8 * 8))) != (0#64)) = false := by
        rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), sext64_id,
          T.head_w, hh0]
        rfl
      kit_run h acc until [0x8001742c]
      simp only [hbk] at h
      rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hash + 8 *
        ((luaHash seed b).toNat % size) < 2 ^ 64 by omega), sext64_id, T.head_w, hh0, gs_addr (by decide) (by omega),
        T.size_w, sext_ofNat32 _ (by omega)] at h
      obtain ⟨c2, s2, hq2⟩ := hN _ (by fcx_unfold; exact h.repin (by pins_of h))
      exact ⟨c2, acc.trans s2, .inr (.inl hq2)⟩
    · have hgb : ((sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 (hash + 8 * ((luaHash seed b).toNat % size)) +
          sign_extend (m := 64) (0x000#12)).toNat) : BitVec (8 * 8))) != (0#64)) = true := by
        rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), sext64_id,
          T.head_w, bne, show (0#64 : BitVec 64) = 0x0#64 from rfl, ofNat64_beq0 hhl hh0]
        rfl
      kit_run h acc until [0x800173f0]
      simp only [hbk] at h
      rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hash + 8 *
        ((luaHash seed b).toNat % size) < 2 ^ 64 by omega), sext64_id, T.head_w, gs_addr (by decide) (by omega),
        T.size_w, sext_ofNat32 _ (by omega)] at h
      obtain ⟨c2, s2, hp⟩ := ia_chain m M sp L s g (hash + 8 * ((luaHash seed b).toNat % size)) size b r f
        (hw (luaHash seed b)) ud o F K X W cw hcw (by omega) (by omega) (by omega) Q hN (d, head) _
        ⟨hh0, T.walk, by fcx_unfold; exact h.repin (by pins_of h)⟩
      exact ⟨c2, acc.trans s2, .inr hp⟩
  · fat_run Lua.Vm.AtF.InternAny h acc until [0x800173a4]
    fcx_unfold at h
    fat_rd at h
    rw [hstep_mach, hstepk] at h
    refine ⟨_, acc, .inl ⟨k - 1, by omega, by omega, by omega, ?_⟩⟩
    fcx_unfold
    rw [show s + (k - 1 - 1) = s + (k - 1) - 1 by omega]
    exact h.repin (by pins_of h)

/-! ## The entry -/

/-- **`luaS_newlstr`'s inputs on contents in a caller's frame**: the C frame,
the contents `b` at `s` (above `sp`, 8-aligned, `1 ≤ |b| ≤ 40`), `G(L) = g`,
the seed. -/
structure IaIn (m : Mem) (sp L s g : Nat) (b : List UInt8) (seed : UInt32) (r : BitVec 64) : Prop where
  sp_lo : 0x87800000 + 16384 + 80 ≤ sp
  sp_hi : sp + 80 ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  s_ge : sp ≤ s
  s_hi : s + b.length + 8 ≤ 2 ^ 32
  s_al : s % 8 = 0
  l_lo : 1 ≤ b.length
  l_hi : b.length ≤ 40
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  Lg : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  bytes : ∀ i, i < b.length → bytesT1 m (s + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  seed_w : bytesT4 m (g + 96) = seed.toBitVec

/-- The root memory of `internshrstr`'s loops: the entry's with its frame
stored (`Lua/Vm/AtF/InternAny.lean`'s `m0`). -/
abbrev iaM0 (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : Mem :=
  Lua.Vm.AtF.InternAny.m0 (iaX [sp, 0, 0, 0, 0] r f 0#64 0#64 m o)

/-- A saved register's slot in the loops' root memory. -/
macro "ia_sv" : tactic => `(tactic| (
  simp only [iaM0, Lua.Vm.AtF.InternAny.m0, iaX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw8_same, fw8_wm8]))

/-- **`luaS_newlstr(L, s, l)` up to the creation path**: the hash, the bucket,
the walk; a node found is returned (`IaHit`), else the creation path `hN`
runs from `0x8001742c` at the loops' root memory. -/
theorem ia_walk_sum (sp L s g size hash head d : Nat) (b : List UInt8) (seed : UInt32) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (hI : IaIn m sp L s g b seed r) (K X W : Nat → Prop)
    (cw : BitVec 8)
    (hT : ∀ M : Mem, (∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a) →
      bytesT1 M (g + 100) = cw ∧ IaTab M g (luaHash seed b) b cw (IaNode M K X W) size hash head d)
    (Q : Config → Prop)
    (hN : ∀ c, IaFacts m (iaM0 sp r f m o) sp L s g b r f →
      SegSt 0x8001742c#64 (Lua.Vm.AtF.InternAny.r15 (iaX (iaN sp L s g
        (hash + 8 * ((luaHash seed b).toNat % size)) size 0 0 0 b) r f (hw (luaHash seed b)) (bytesT8 m (g + 8))
        (iaM0 sp r f m o) o)) (ArmPay (iaM0 sp r f m o) o) c → ∃ c', Steps c c' ∧ Q c') :
    Triple (SegSt 0x80017694#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 s⟩,
        ⟨Register.x12, BitVec.ofNat 64 b.length⟩] sp r f) (ArmPay m o))
      (fun c => Q c ∨ ∃ ts, IaHit m (iaM0 sp r f m o) K X W sp ts b r f o c) := by
  intro c h
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hI.sp_lo; have := hI.sp_hi; have := hI.sp_al; have hra := hI.ra; have := hI.L_lo; have := hI.L_he
  have := hI.L_al; have := hI.s_ge; have := hI.s_hi; have := hI.l_lo; have := hI.l_hi; have := hI.g_lo
  have := hI.g_hi; have := hI.s_al
  have hX : Lua.Vm.AtF.InternAny.Ok (iaX [sp, L, s, b.length, g] r f 0#64 0#64 m o) := by fcx_ok
  have hc0 : bytesT8 m (L + 24) = BitVec.ofNat 64 g := hI.Lg
  have hl40 : b.length ≤ 40 := hI.l_hi
  have hg2 : zopz0zKzJ_u (0x28#64) (BitVec.ofNat 64 b.length) = true := by
    rw [show (0x28#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, fuge (by decide) (by omega)]
    simp only [decide_eq_true_eq]; omega
  have hseed : bytesT4 m (g + 96) = seed.toBitVec := hI.seed_w
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80017694#64 (Lua.Vm.AtF.InternAny.r0 (iaX [sp, L, s, b.length, g] r f 0#64 0#64 m o))
      (ArmPay (iaX [sp, L, s, b.length, g] r f 0#64 0#64 m o).m (iaX [sp, L, s, b.length, g] r f 0#64 0#64 m o).o)
      c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.InternAny h acc until [0x800173a4]
  -- the root memory: the entry's with the frame stored
  have hM0 : Lua.Vm.AtF.InternAny.m0 (iaX [sp, L, s, b.length, g] r f 0#64 0#64 m o) = iaM0 sp r f m o := rfl
  rw [hM0] at h
  fcx_unfold at h
  fat_rd at h
  rw [hinit_mach, hw_init, ← hashFrom_len, show s + b.length - 1 = s + (b.length - 1) by omega] at h
  have keep : ∀ a, ¬ Below sp 80 a → bytesT1 (iaM0 sp r f m o) a = bytesT1 m a := by
    intro a ha
    have ha' : a + 80 < sp ∨ sp ≤ a := by simp only [Below] at ha; omega
    simp only [iaM0, Lua.Vm.AtF.InternAny.m0, iaX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
  have hfr : ∀ a, a < 0x87800000 → bytesT1 (iaM0 sp r f m o) a = bytesT1 m a := fun a ha =>
    keep a (by simp only [Below]; omega)
  have F : IaFacts m (iaM0 sp r f m o) sp L s g b r f := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := hra, L_lo := by omega,
    L_he := by omega, L_al := by omega, s_ge := by omega, s_hi := by omega, s_al := by omega,
    l_lo := by omega, l_hi := hl40, g_lo := by omega, g_hi := by omega,
    keep := keep,
    bytes := fun i hi => (keep _ (by simp only [Below]; omega)).trans (hI.bytes i hi),
    sv0 := by ia_sv
    sv1 := by ia_sv
    sv2 := by ia_sv
    sv3 := by ia_sv
    sv4 := by ia_sv
    sv5 := by ia_sv
    sv6 := by ia_sv
    sv7 := by ia_sv
    sv8 := by ia_sv }
  obtain ⟨hcw, T⟩ := hT _ hfr
  obtain ⟨c2, s2, hp⟩ := ia_hash m (iaM0 sp r f m o) sp L s g size hash head d b seed r f (bytesT8 m (g + 8)) o F
    K X W cw hcw T Q (fun c h' => hN c F h') b.length _
    ⟨by omega, Nat.le_refl _, by fcx_unfold; exact h.repin (by pins_of h)⟩
  exact ⟨c2, acc.trans s2, hp⟩

end Lua.Vm.Sim.Kit
