import Lua.Vm.Sim.Kit.PushLit
import Lua.Vm.Sim.Kit.Memcmp
import Lua.Vm.Sim.Kit.HeapFill
import Lua.Vm.Sim.Kit.Getshortstr
import Lua.Vm.Sim.Kit.LuaApi
import Lua.Vm.AtF.Internshrstr
import Lua.Vm.Arms.Segs.HluaS_newlstr

/-!
# `internshrstr` on an interned literal (lane F1-15)

`internshrstr(L, str, l)` (`0x80017350`) on a short C string whose `TString`
was interned at boot (`LitInterned`): the hash loop (`luaS_hash`, from the
last byte, in 32 bits: `hstep`, `hashFrom`), the bucket `g->strt.hash[h &
(size - 1)]`, the chain walk with `memcmp` (`ChainAt`, the walk's length its
`seg_loop` measure), and `isdead`'s `changewhite`. Its at-lemmas are generated
(`Lua/Vm/AtF/Internshrstr.lean`); the bucket segment runs by `kit_run`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `luaS_hash` in 32 bits -/

/-- One step of `luaS_hash` (`h ^= (h << 5) + (h >> 2) + byte`). -/
def hstep (c : UInt8) (h : UInt32) : UInt32 := h ^^^ ((h <<< 5) + (h >>> 2) + c.toUInt32)

/-- The hash once the bytes from `k` on are folded in (`k = 0`: `luaHash`). -/
def hashFrom (seed : UInt32) (b : List UInt8) (k : Nat) : UInt32 :=
  (b.drop k).foldr hstep (seed ^^^ b.length.toUInt32)

theorem hashFrom_zero (seed : UInt32) (b : List UInt8) : hashFrom seed b 0 = luaHash seed b := rfl

theorem hashFrom_len (seed : UInt32) (b : List UInt8) :
    hashFrom seed b b.length = seed ^^^ b.length.toUInt32 := by
  simp [hashFrom]

theorem hashFrom_step (seed : UInt32) (b : List UInt8) {k : Nat} (hk : k < b.length) :
    hashFrom seed b k = hstep b[k] (hashFrom seed b (k + 1)) := by
  simp only [hashFrom, List.drop_eq_getElem_cons hk, List.foldr_cons]

/-- A hash in a register (`addw`'s sign extension). -/
abbrev hw (h : UInt32) : BitVec 64 := sign_extend (m := 64) h.toBitVec

theorem sext_xor32 (a b : BitVec 32) :
    sign_extend (m := 64) (a ^^^ b) = sign_extend (m := 64) a ^^^ sign_extend (m := 64) b := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_xor, BitVec.msb_xor]
  by_cases h : i < 32 <;> simp [h, hi]

theorem ex32_zext8 (c : BitVec 8) :
    Sail.BitVec.extractLsb (zero_extend (m := 64) (c : BitVec (8 * 1))) 31 0 =
      (UInt8.ofBitVec c).toUInt32.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp [Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend, BitVec.extractLsb_toNat]

/-- **One step of the hash loop** (`lbu`, `srliw 2`, `slliw 5`, `addw`,
`addw`, `xor`) on the sign-extended hash: `hstep`. -/
theorem hstep_mach (h : UInt32) (c : BitVec 8) :
    ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (zero_extend (m := 64) (c : BitVec (8 * 1))) 31 0) +
      (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb (sign_extend (m := 64)
        (shift_bits_right (Sail.BitVec.extractLsb (hw h) 31 0) (0x02#5))) 31 0) +
        (Sail.BitVec.extractLsb (sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb (hw h) 31 0)
          (0x05#5))) 31 0))) 31 0))) ^^^ hw h) = hw (hstep (UInt8.ofBitVec c) h) := by
  simp only [hw, extract_sext, ex32_zext8]
  rw [← sext_xor32]
  congr 1
  simp only [hstep, shift_bits_left, shift_bits_right, UInt32.toBitVec_xor, UInt32.toBitVec_add,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
  rw [BitVec.xor_comm]
  congr 1
  rw [BitVec.add_comm, BitVec.add_comm (h.toBitVec >>> _)]
  rfl

/-- The hash's start `seed ^ l` (`lw`, `xor`, `sext.w`). -/
theorem hinit_mach (S : BitVec 32) (l : Nat) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) S ^^^ BitVec.ofNat 64 l) 31 0 = S ^^^ BitVec.ofNat 32 l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.extractLsb, sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_extractLsb,
    BitVec.getLsbD_xor, BitVec.getLsbD_signExtend, BitVec.getLsbD_ofNat]
  simp [show i < 64 by omega, show i < 32 by omega]

theorem hw_init (seed : UInt32) (l : Nat) :
    sign_extend (m := 64) (seed.toBitVec ^^^ BitVec.ofNat 32 l) = hw (seed ^^^ l.toUInt32) := by
  simp only [hw, UInt32.toBitVec_xor]
  rfl

theorem ofBitVec_byte (u : UInt8) : UInt8.ofBitVec (BitVec.ofNat 8 u.toNat) = u := by
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofBitVec]

/-! ## The bucket -/

/-- **The bucket's address** `hash + 8 · (h & (size - 1))` (`lw`, `addiw -1`,
`and`, `slli 3`, `add`), `size` a power of two below `2^30`. -/
theorem bucket_addr (H : BitVec 32) (hash size : Nat) (h0 : 0 < size) (hs : size < 2 ^ 30)
    (hp : size &&& (size - 1) = 0) :
    BitVec.ofNat 64 hash + shift_bits_left (sign_extend (m := 64) H &&& sign_extend (m := 64)
      (Sail.BitVec.extractLsb (sign_extend (m := 64) (BitVec.ofNat 32 size : BitVec (8 * 4)) +
        sign_extend (m := 64) (0xfff#12)) 31 0)) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (hash + 8 * (H.toNat % size)) := by
  obtain ⟨k, rfl⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).1 hp
  have hk : k < 30 := by
    rcases Nat.lt_or_ge k 30 with e | e
    · exact e
    · exact absurd (Nat.pow_le_pow_right (n := 2) (by decide) e) (by omega)
  have e1 : sign_extend (m := 64) (BitVec.ofNat 32 (2 ^ k) : BitVec (8 * 4)) + sign_extend (m := 64) (0xfff#12) =
      BitVec.ofNat 64 (2 ^ k - 1) := by
    apply BitVec.eq_of_toNat_eq
    have hp1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [BitVec.toNat_add, sext32_toNat, show (sign_extend (m := 64) (0xfff#12)).toNat = 2 ^ 64 - 1 by decide,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 ^ k < 2 ^ 32 by omega)]
    rw [if_pos (by omega)]
    omega
  rw [e1, sext32_ofNat _ (by omega), BitVec.and_comm, gs_and (by omega), show (0x03#6 : BitVec 6) =
    BitVec.ofNat 6 3 from rfl, shl_ofNat _ 3 (by decide), BitVec.ofNat_add_ofNat]
  congr 1
  omega

/-! ## The chain, over total reads -/

/-- `internshrstr`'s test fails at `p` (`NoMatch`), over total reads. -/
def NoMatchT (M : Mem) (p : Nat) (b : List UInt8) : Prop :=
  bytesT1 M (p + 11) ≠ BitVec.ofNat 8 b.length ∨
    ∃ i, i < b.length ∧ bytesT1 M (p + 24 + i) ≠ BitVec.ofNat 8 (b.getD i 0).toNat

/-- **`ChainFirst` with its length**, over the total reads of `M`: the walk
from `p` meets `ts` after `d` failed tests (`seg_loop`'s measure). -/
inductive ChainAt (M : Mem) (b : List UInt8) (ts : Nat) : Nat → Nat → Prop where
  | here : ChainAt M b ts 0 ts
  | next {d p nx : Nat} : p ≠ ts → symTohost + 16 ≤ p → p + 128 ≤ symHeapEnd →
      bytesT8 M (p + 16) = BitVec.ofNat 64 nx → nx ≠ 0 → nx < 2 ^ 64 → NoMatchT M p b → ChainAt M b ts d nx →
      ChainAt M b ts (d + 1) p

/-- A byte of the fill in RAM is the total read. -/
theorem rd8_fill {m : Mem} {a : Nat} (hlo : 0x80000000 ≤ a) (hhi : a < 0x88000000) :
    rd8 (fillZeroMem m) a = some (bytesT1 m a).toNat := by
  simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero,
    Option.bind_eq_bind, Option.pure_def, Option.bind_some, fillZeroMem_ram m (a := a) hlo hhi]
  simp [bytesT1]

theorem bytesT1_of_fill_get {m : Mem} {a : Nat} {v : BitVec 8} (h : (fillZeroMem m)[a]? = some v) :
    bytesT1 m a = v := by
  rw [← bytesT1_fill]; simp [bytesT1, h]

/-- **The walk over the memory `M`** that agrees with `m` below the heap's
end: `ChainFirst` of `m`'s fill as `ChainAt` of `M`. -/
theorem ChainFirst.toAt {m M : Mem} {b : List UInt8} {ts : Nat} (hts : ts ≠ 0) (hbl : b.length ≤ 40)
    (keep : ∀ a, a < symHeapEnd → bytesT1 M a = bytesT1 m a) :
    ∀ {p}, ChainFirst (fillZeroMem m) b ts p → ∃ d, ChainAt M b ts d p := by
  intro p hc
  induction hc with
  | here => exact ⟨0, .here⟩
  | @next p nx hp0 hpts hlo hhi hrd hnm hcf ih =>
    obtain ⟨d, hd⟩ := ih
    have hTH : symTohost = 0x8005c6c0 := rfl
    have hHE : symHeapEnd = 0x87800000 := rfl
    have hnx : nx ≠ 0 := by
      cases hcf with
      | here => exact hts
      | next h0 => exact h0
    have k8 : bytesT8 M (p + 16) = bytesT8 m (p + 16) :=
      bytesT8_congrT fun i _ => keep _ (by omega)
    have hw8 : bytesT8 M (p + 16) = BitVec.ofNat 64 nx := by
      rw [k8]; exact bT8_of_fill (bytesT8_of_rd64 hrd)
    refine ⟨d + 1, .next hpts hlo hhi hw8 hnx (rd64_lt hrd) ?_ hd⟩
    rcases hnm with hl | ⟨i, hi, hb⟩
    · refine .inl fun e => hl ?_
      rw [show p + tstringShrlenOff = p + 11 from rfl, rd8_fill (by omega) (by omega), ← keep _ (by omega), e]
      simp only [BitVec.toNat_ofNat, Option.some.injEq]
      exact Nat.mod_eq_of_lt (by omega)
    · refine .inr ⟨i, hi, fun e => hb ?_⟩
      rw [show p + tstringContentsOff + i = p + 24 + i from rfl, rd8_fill (by omega) (by omega),
        ← keep _ (by omega), e]
      simp only [BitVec.toNat_ofNat, Option.some.injEq]
      exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)

/-! ## The roots -/

/-- `internshrstr`'s root contexts: Nat atoms `ns`; `ra`, the caller's frame
and the hash `hh` (`X.b 13`); the root memory. -/
@[at_row] abbrev intX (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (hh : BitVec 64) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, hh] m o

/-- The chain walk's root at node `p` (`X.n 7` the bucket, `X.n 8` `memcmp`'s
answer, `X.n 9` the table's size). -/
abbrev intC (sp L s g p bkt k size : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame) (hh : BitVec 64)
    (M : Mem) (o : Array String) : FCx :=
  intX [sp - 80, L, s, b.length, g, 0, p, bkt, k, size] r f hh M o

/-- The hash loop's root at the cursor `c`. -/
abbrev intH (sp L s g c : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame) (hh : BitVec 64)
    (M : Mem) (o : Array String) : FCx :=
  intX [sp - 80, L, s, b.length, g, c] r f hh M o

/-- **What `internshrstr`'s roots know**: the atoms' bounds, the root memory
`M` (the entry's `m` with the frame stored: `keep`, the saved registers
`sv*`), the string's bytes, the interned string `ts`. -/
structure IntFacts (m M : Mem) (sp L s g : Nat) (b : List UInt8) (ts : Nat) (r : BitVec 64) (f : AbiFrame) :
    Prop where
  sp_lo : 0x87800000 + 16384 + 80 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  s_lo : 0x80000000 ≤ s
  s_th : s + b.length + 8 ≤ 0x8005c6c0
  l_lo : 1 ≤ b.length
  l_hi : b.length ≤ 40
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  ts_lo : 0x8005c6c0 + 16 ≤ ts
  ts_hi : ts + 128 ≤ 0x87800000
  keep : ∀ a, ¬ Below sp 80 a → bytesT1 M a = bytesT1 m a
  bytes : ∀ i, i < b.length → bytesT1 M (s + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  ts_len : bytesT1 M (ts + 11) = BitVec.ofNat 8 b.length
  ts_bytes : ∀ i, i < b.length → bytesT1 M (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  sv0 : bytesT8 M (sp - 80 + 72) = r
  sv1 : bytesT8 M (sp - 80 + 64) = f.s0
  sv2 : bytesT8 M (sp - 80 + 56) = f.s1
  sv3 : bytesT8 M (sp - 80 + 48) = f.s2
  sv4 : bytesT8 M (sp - 80 + 40) = f.s3
  sv5 : bytesT8 M (sp - 80 + 32) = f.s4
  sv6 : bytesT8 M (sp - 80 + 24) = f.s5
  sv7 : bytesT8 M (sp - 80 + 16) = f.s6
  sv8 : bytesT8 M (sp - 80 + 8) = f.s7

/-- **What `internshrstr` leaves**: every byte but `ts`'s mark
(`changewhite`) and its frame below `sp`. -/
structure IntPost (m m' : Mem) (sp ts : Nat) : Prop where
  keep : ∀ a, ¬ (a = ts + gcMarkedOff ∨ Below sp 80 a) → bytesT1 m' a = bytesT1 m a

/-- `internshrstr`'s return: `a0 = ts`. -/
abbrev intPost (r : BitVec 64) (sp ts : Nat) (f : AbiFrame) (m : Mem) (o : Array String) : Config → Prop :=
  fun c => ∃ m', wrRet r sp ts f m' o c ∧ IntPost m m' sp ts

theorem zext8_ofNat_bne {l : Nat} (hl : l < 256) (x : BitVec 8) :
    (zero_extend (m := 64) (x : BitVec (8 * 1)) != BitVec.ofNat 64 l) = !decide (x = BitVec.ofNat 8 l) := by
  rw [show BitVec.ofNat 64 l = zero_extend (m := 64) (BitVec.ofNat 8 l : BitVec (8 * 1)) by
    apply BitVec.eq_of_toNat_eq
    simp [zero_extend, Sail.BitVec.zeroExtend, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt (show l < 2 ^ 64 by omega)],
    bne, zext8_beq]

theorem ofNat64_beq0 {x : Nat} (hx : x < 2 ^ 64) (h0 : x ≠ 0) : (BitVec.ofNat 64 x == 0x0#64) = false := by
  rw [show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq hx (by decide)]
  simp [h0]

theorem ofNat_toNat64 (v : BitVec 64) : v = BitVec.ofNat 64 v.toNat := by simp

set_option hygiene false in
local macro "int_ctx" F:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($F).sp_lo; have := ($F).sp_hi; have := ($F).sp_al; have hra := ($F).ra; have := ($F).L_lo
  have := ($F).L_he; have := ($F).L_al; have := ($F).s_lo; have := ($F).s_th; have := ($F).l_lo
  have := ($F).l_hi; have := ($F).g_lo; have := ($F).g_hi; have := ($F).ts_lo; have := ($F).ts_hi))

/-- The return of a found `ts`, from the walk's return row: `wrRet` and the
keep (`M`, or `M` with `ts`'s mark changed). -/
theorem int_ret {m M M' : Mem} {sp L s g ts : Nat} {b : List UInt8} {r : BitVec 64} {f : AbiFrame}
    {o : Array String} {c : Config} (F : IntFacts m M sp L s g b ts r f)
    (hM : ∀ a, a ≠ ts + 9 → bytesT1 M' a = bytesT1 M a)
    (h : SegSt r [⟨Register.x1, r⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 80 + 80)⟩, ⟨Register.x3, 0x8005ced0#64⟩,
      ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x10, BitVec.ofNat 64 ts⟩, ⟨Register.x18, f.s2⟩,
      ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩,
      ⟨Register.x23, f.s7⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩,
      ⟨Register.x27, f.s11⟩] (ArmPay M' o) c) :
    intPost r sp ts f m o c := by
  have := F.sp_lo
  rw [show sp - 80 + 80 = sp by omega] at h
  refine ⟨M', h.repin (by pins_of h), ⟨fun a ha => ?_⟩⟩
  simp only [gcMarkedOff, not_or] at ha
  rw [hM a ha.1, F.keep a ha.2]

/-- **The chain walk** from node `p` (`0x800173f0`), `ts` met after `d`
failed tests: `memcmp` (a call node, `memcmp_sumS`) on an equal length,
`isdead`'s `changewhite`, the return of `ts`. -/
theorem int_chain (m M : Mem) (sp L s g ts bkt size : Nat) (b : List UInt8) (r : BitVec 64) (f : AbiFrame)
    (hh : BitVec 64) (o : Array String) (F : IntFacts m M sp L s g b ts r f)
    (_hbkt : bkt < 2 ^ 32) (_hsz : size < 2 ^ 32) :
    ∀ dp : Nat × Nat, Triple (fun c => ChainAt M b ts dp.1 dp.2 ∧
      SegSt 0x800173f0#64 (Lua.Vm.AtF.Internshrstr.r5 (intC sp L s g dp.2 bkt 0 size b r f hh M o))
        (ArmPay (intC sp L s g dp.2 bkt 0 size b r f hh M o).m (intC sp L s g dp.2 bkt 0 size b r f hh M o).o) c)
      (intPost r sp ts f m o) := by
  refine seg_loop (fun dp => dp.1) fun ⟨d, p⟩ c ⟨hch, h⟩ => ?_
  have acc := Steps.refl c
  int_ctx F
  simp only at hch
  -- `memcmp(str, getstr(p), l)` from its call row
  have mc : ∀ (p k : Nat) (c1 : Config) (Z : Prop), 0x8005c6c0 + 16 ≤ p → p + 128 ≤ 0x87800000 →
      (∀ c', Steps c c' → ∀ v : BitVec 64, (v = 0#64 ↔ ∀ j, j < b.length → McEq M s (p + 24) j) →
        SegSt 0x80017408#64 [⟨Register.x10, v⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 80)⟩,
          ⟨Register.x3, 0x8005ced0#64⟩, ⟨Register.x8, BitVec.ofNat 64 p⟩, ⟨Register.x9, hh⟩,
          ⟨Register.x18, BitVec.ofNat 64 s⟩, ⟨Register.x19, BitVec.ofNat 64 g⟩, ⟨Register.x20, BitVec.ofNat 64 L⟩,
          ⟨Register.x21, BitVec.ofNat 64 b.length⟩, ⟨Register.x22, BitVec.ofNat 64 bkt⟩,
          ⟨Register.x23, BitVec.ofNat 64 size⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩,
          ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩] (ArmPay M o) c' → Z) →
      Steps c c1 → SegSt 0x80036198#64 (Lua.Vm.AtF.Internshrstr.r8 (intC sp L s g p bkt k size b r f hh M o))
        (ArmPay M o) c1 → Z := by
    intro p k c1 Z hp1 hp2 hZ acc h
    fcx_unfold at h
    obtain ⟨_, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h)
      (memcmp_sumS s (p + 24) b.length 0x80017408#64 (BitVec.ofNat 64 (sp - 80))
        ⟨0x8005ced0#64, BitVec.ofNat 64 p, hh, BitVec.ofNat 64 s, BitVec.ofNat 64 g, BitVec.ofNat 64 L,
          BitVec.ofNat 64 b.length, BitVec.ofNat 64 bkt, BitVec.ofNat 64 size, f.s8, f.s9, f.s10, f.s11⟩ M o
        ⟨by decide, by omega, by omega, .inl (by omega), by omega, by omega⟩)
    dsimp only [RetAtS] at h
    exact hZ _ acc v hv (h.repin (by pins_of h))
  cases hch with
  | here =>
    have hX : Lua.Vm.AtF.Internshrstr.Ok_C (intC sp L s g ts bkt 0 size b r f hh M o) := by fcx_ok
    have hg2 : (zero_extend (m := 64) (bytesT1 M (ts + 11) : BitVec (8 * 1)) != BitVec.ofNat 64 b.length) =
        false := by
      rw [zext8_ofNat_bne (by omega), F.ts_len]; simp
    fat_run Lua.Vm.AtF.Internshrstr h acc until [0x80036198]
    refine mc ts 0 _ _ (by omega) (by omega) (fun c' acc v hv h => ?_) acc h
    have hv0 : v = 0#64 := hv.2 fun j hj => by
      simp only [McEq]; rw [F.bytes j hj, F.ts_bytes j hj]
    subst hv0
    have h : SegSt 0x80017408#64 (Lua.Vm.AtF.Internshrstr.r9 (intC sp L s g ts bkt 0 size b r f hh M o))
        (ArmPay (intC sp L s g ts bkt 0 size b r f hh M o).m (intC sp L s g ts bkt 0 size b r f hh M o).o) c' := by
      fcx_unfold; exact h.repin (by pins_of h)
    have sv0 := F.sv0; have sv1 := F.sv1; have sv2 := F.sv2; have sv3 := F.sv3; have sv4 := F.sv4
    have sv5 := F.sv5; have sv6 := F.sv6; have sv7 := F.sv7; have sv8 := F.sv8
    by_cases hd : ((zero_extend (m := 64) (bytesT1 M ((BitVec.ofNat 64 ts) + sign_extend (m := 64) (0x009#12)).toNat :
        BitVec (8 * 1))) &&& ((zero_extend (m := 64) (bytesT1 M ((BitVec.ofNat 64 g) +
        sign_extend (m := 64) (0x064#12)).toNat : BitVec (8 * 1))) ^^^ sign_extend (m := 64) (0x018#12)) ==
        (0#64)) = true
    · fat_run Lua.Vm.AtF.Internshrstr h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr (int_ret F (fun _ _ => rfl) h)⟩
    · simp only [Bool.not_eq_true] at hd
      fat_run Lua.Vm.AtF.Internshrstr h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr (int_ret F (fun a ha => bT1_congr (ins_out _ _ _ _ (by omega))) h)⟩
  | @next d p nx hpts hlo hhi hnx hnx0 hnxl hnm hrest =>
    simp only [symTohost, symHeapEnd] at hlo hhi
    have hg3 : (bytesT8 M (p + 16) == 0x0#64) = false := by rw [hnx]; exact ofNat64_beq0 hnxl hnx0
    by_cases hl : bytesT1 M (p + 11) = BitVec.ofNat 8 b.length
    · have hX : Lua.Vm.AtF.Internshrstr.Ok_C (intC sp L s g p bkt 0 size b r f hh M o) := by fcx_ok
      have hg2 : (zero_extend (m := 64) (bytesT1 M (p + 11) : BitVec (8 * 1)) != BitVec.ofNat 64 b.length) =
          false := by
        rw [zext8_ofNat_bne (by omega), hl]; simp
      fat_run Lua.Vm.AtF.Internshrstr h acc until [0x80036198]
      refine mc p 0 _ _ (by omega) (by omega) (fun c' acc v hv h => ?_) acc h
      have hv0 : v.toNat ≠ 0 := fun e => by
        have e' : v = 0#64 := BitVec.eq_of_toNat_eq (by simp [e])
        have hall := hv.1 e'
        rcases hnm with hn | ⟨i, hi, hb⟩
        · exact hn hl
        · have := hall i hi
          simp only [McEq] at this
          rw [F.bytes i hi] at this
          exact hb this.symm
      have hvl := v.isLt
      have hX1 : Lua.Vm.AtF.Internshrstr.Ok_C (intC sp L s g p bkt v.toNat size b r f hh M o) := by fcx_ok
      have h : SegSt 0x80017408#64 (Lua.Vm.AtF.Internshrstr.r13 (intC sp L s g p bkt v.toNat size b r f hh M o))
          (ArmPay (intC sp L s g p bkt v.toNat size b r f hh M o).m
            (intC sp L s g p bkt v.toNat size b r f hh M o).o) c' := by
        fcx_unfold; rw [ofNat_toNat64 v] at h; exact h.repin (by pins_of h)
      fat_run Lua.Vm.AtF.Internshrstr h acc until [0x800173f0]
      fcx_unfold at h
      rw [hnx] at h
      exact ⟨_, acc, .inl ⟨(d, nx), by simp, hrest, by fcx_unfold; exact h.repin (by pins_of h)⟩⟩
    · have hX : Lua.Vm.AtF.Internshrstr.Ok_C (intC sp L s g p bkt 0 size b r f hh M o) := by fcx_ok
      have hg2 : (zero_extend (m := 64) (bytesT1 M (p + 11) : BitVec (8 * 1)) != BitVec.ofNat 64 b.length) =
          true := by
        rw [zext8_ofNat_bne (by omega)]; simp [hl]
      fat_run Lua.Vm.AtF.Internshrstr h acc until [0x800173f0]
      fcx_unfold at h
      rw [hnx] at h
      exact ⟨_, acc, .inl ⟨(d, nx), by simp, hrest, by fcx_unfold; exact h.repin (by pins_of h)⟩⟩


/-! ## The hash loop and the bucket -/

/-- **`g->strt` as `internshrstr` reads it**: the bucket array `hash` of
`size` words (a power of two below `2^30`), the bucket head `head` of the
hash `H`, and the walk from it (`ChainAt`). -/
structure IntTab (M : Mem) (g : Nat) (H : UInt32) (b : List UInt8) (ts size hash head d : Nat) : Prop where
  size_w : bytesT4 M (g + 60) = BitVec.ofNat 32 size
  hash_w : bytesT8 M (g + 48) = BitVec.ofNat 64 hash
  size_pos : 0 < size
  size_hi : size < 2 ^ 30
  size_pow2 : size &&& (size - 1) = 0
  hash_lo : 0x8005c6c0 + 16 ≤ hash
  hash_hi : hash + 8 * size ≤ 2 ^ 32
  head_w : bytesT8 M (hash + 8 * (H.toNat % size)) = BitVec.ofNat 64 head
  head_lt : head < 2 ^ 64
  walk : ChainAt M b ts d head

theorem ChainAt.ne_zero {M : Mem} {b : List UInt8} {ts d p : Nat} (hts : ts ≠ 0) (h : ChainAt M b ts d p) :
    p ≠ 0 := by
  cases h with
  | here => exact hts
  | next _ hlo => simp only [symTohost] at hlo; omega

theorem sext_ofNat32 (x : Nat) (h : x < 2 ^ 31) :
    sign_extend (m := 64) (BitVec.ofNat 32 x : BitVec (8 * 4)) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [sext32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega),
    if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

set_option hygiene false in
/-- The bucket segment's address and guard, from the facts `hbk`, `hgb`. -/
local macro_rules | `(tactic| kit_side_pre) => `(tactic| simp only [hbk])

set_option hygiene false in
local macro_rules | `(tactic| kit_guard_ext) => `(tactic| exact hgb)

/-- **The hash loop** (`0x800173a4`) from the cursor `s + k - 1`, the bytes
from `k` on folded in (`hashFrom`); at `k = 1` the bucket and the walk. -/
theorem int_hash (m M : Mem) (sp L s g ts size hash head d : Nat) (b : List UInt8) (seed : UInt32)
    (r : BitVec 64) (f : AbiFrame) (o : Array String) (F : IntFacts m M sp L s g b ts r f)
    (T : IntTab M g (luaHash seed b) b ts size hash head d) :
    ∀ k, Triple (fun c => 1 ≤ k ∧ k ≤ b.length ∧
      SegSt 0x800173a4#64
        (Lua.Vm.AtF.Internshrstr.r3 (intH sp L s g (s + (k - 1)) b r f (hw (hashFrom seed b k)) M o))
        (ArmPay (intH sp L s g (s + (k - 1)) b r f (hw (hashFrom seed b k)) M o).m
          (intH sp L s g (s + (k - 1)) b r f (hw (hashFrom seed b k)) M o).o) c)
      (intPost r sp ts f m o) := by
  refine seg_loop (fun k => k) fun k c ⟨hk1, hkl, h⟩ => ?_
  have acc := Steps.refl c
  int_ctx F
  have hX : Lua.Vm.AtF.Internshrstr.Ok_H (intH sp L s g (s + (k - 1)) b r f (hw (hashFrom seed b k)) M o) := by
    fcx_ok
  have hstepk : hw (hstep (UInt8.ofBitVec (bytesT1 M (s + (k - 1)))) (hashFrom seed b k)) =
      hw (hashFrom seed b (k - 1)) := by
    rw [F.bytes (k - 1) (by omega), ofBitVec_byte, hashFrom_step seed b (show k - 1 < b.length by omega),
      show k - 1 + 1 = k by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
  by_cases hk : k = 1
  · fat_run Lua.Vm.AtF.Internshrstr h acc until [0x800173c4]
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
    have hh0 := T.walk.ne_zero (by omega)
    have hhl := T.head_lt
    have hgb : ((sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 (hash + 8 * ((luaHash seed b).toNat % size)) +
        sign_extend (m := 64) (0x000#12)).toNat) : BitVec (8 * 8))) != (0#64)) = true := by
      rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), sext64_id,
        T.head_w, bne, show (0#64 : BitVec 64) = 0x0#64 from rfl, ofNat64_beq0 hhl hh0]
      rfl
    kit_run h acc until [0x800173f0]
    simp only [hbk] at h
    rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show hash + 8 *
      ((luaHash seed b).toNat % size) < 2 ^ 64 by omega), sext64_id, T.head_w, gs_addr (by decide) (by omega),
      T.size_w, sext_ofNat32 _ (by omega)] at h
    obtain ⟨c2, s2, hp⟩ := int_chain m M sp L s g ts (hash + 8 * ((luaHash seed b).toNat % size)) size b r f
      (hw (luaHash seed b)) o F (by omega) (by omega) (d, head) _
      ⟨T.walk, by fcx_unfold; exact h.repin (by pins_of h)⟩
    exact ⟨c2, acc.trans s2, .inr hp⟩
  · fat_run Lua.Vm.AtF.Internshrstr h acc until [0x800173a4]
    fcx_unfold at h
    fat_rd at h
    rw [hstep_mach, hstepk] at h
    refine ⟨_, acc, .inl ⟨k - 1, by omega, by omega, by omega, ?_⟩⟩
    fcx_unfold
    rw [show s + (k - 1 - 1) = s + (k - 1) - 1 by omega]
    exact h.repin (by pins_of h)


/-! ## The entry -/

/-- **`internshrstr`'s inputs**: the C frame, the string's bytes at `s` in
`.rodata` (below `tohost`), `G(L) = g`, and the string interned
(`LitInterned`) in `g`'s table `rt`, its bucket array in RAM. -/
structure InternIn (m : Mem) (sp L s g : Nat) (b : List UInt8) (seed : UInt32) (ts : Nat) (rt : RtPtrs)
    (r : BitVec 64) : Prop where
  sp_lo : 0x87800000 + 16384 + 80 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  s_lo : 0x80000000 ≤ s
  s_th : s + b.length + 8 ≤ 0x8005c6c0
  l_lo : 1 ≤ b.length
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  Lg : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  bytes : ∀ i, i < b.length → bytesT1 m (s + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  lit : LitInterned m rt seed b ts
  rt_g : rt.g = g
  hash_lo : symTohost + 16 ≤ rt.strtHash
  hash_hi : rt.strtHash + 8 * rt.strtSize ≤ symHeapEnd
  size_hi : rt.strtSize < 2 ^ 30

/-- The interned string's length and bytes, as total reads. -/
theorem _root_.Lua.Vm.TStringRepr.total {m : Mem} {ts : Nat} {b : List UInt8} (h : TStringRepr (fillZeroMem m) ts b)
    (hs : b.length ≤ maxShortLen) :
    bytesT1 m (ts + 11) = BitVec.ofNat 8 b.length ∧
      ∀ i, i < b.length → bytesT1 m (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat := by
  cases h with
  | short _ _ hl hb _ =>
    refine ⟨by rw [← bytesT1_fill]; exact bytesT1_of_rd8 hl, fun i hi => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact bytesT1_of_fill_get (hb i hi)
  | long _ hl => exact absurd hs (by omega)

/-- **`internshrstr(L, str, l)` on an interned short C string**: it returns
the boot-interned `ts`, every byte kept but `ts`'s mark and its frame. -/
theorem internshrstr_sum (sp L s g ts : Nat) (b : List UInt8) (seed : UInt32) (rt : RtPtrs) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (hI : InternIn m sp L s g b seed ts rt r) :
    Triple (SegSt 0x80017350#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 s⟩,
        ⟨Register.x12, BitVec.ofNat 64 b.length⟩] sp r f) (ArmPay m o))
      (intPost r sp ts f m o) := by
  intro c h
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hI.sp_lo; have := hI.sp_hi; have := hI.sp_al; have hra := hI.ra; have := hI.L_lo; have := hI.L_he
  have := hI.L_al; have := hI.s_lo; have := hI.s_th; have := hI.l_lo; have := hI.g_lo; have := hI.g_hi
  have hl40 : b.length ≤ 40 := hI.lit.short
  have hts := hI.lit.ts_lo; have hts2 := hI.lit.ts_hi
  simp only [symTohost, symHeapEnd] at hts hts2
  have hX : Lua.Vm.AtF.Internshrstr.Ok (plX [sp, L, s, b.length, g] r f m o) := by fcx_ok
  have hc0 : bytesT8 m (L + 24) = BitVec.ofNat 64 g := hI.Lg
  have hS := hI.lit.strt
  have hseed : bytesT4 m (g + 96) = seed.toBitVec := by
    have e := bT4_of_fill (bytesT4_of_rd32 hI.lit.seed_w)
    rw [hI.rt_g] at e
    rw [show g + 96 = g + gSeedOff from rfl, e]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt seed.toBitVec.isLt]
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80017350#64 (Lua.Vm.AtF.Internshrstr.r0 (plX [sp, L, s, b.length, g] r f m o))
      (ArmPay (plX [sp, L, s, b.length, g] r f m o).m (plX [sp, L, s, b.length, g] r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Internshrstr h acc until [0x800173a4]
  generalize hM : Lua.Vm.AtF.Internshrstr.m0 (plX [sp, L, s, b.length, g] r f m o) = M at h
  fcx_unfold at h
  fat_rd at h
  rw [hinit_mach, hw_init, ← hashFrom_len, show s + b.length - 1 = s + (b.length - 1) by omega] at h
  -- the root memory: the entry's with the frame stored
  have keep : ∀ a, ¬ Below sp 80 a → bytesT1 M a = bytesT1 m a := by
    intro a ha
    have ha' : a + 80 < sp ∨ sp ≤ a := by simp only [Below] at ha; omega
    rw [← hM]; fcx_unfold
    exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
  have hfr : ∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a := fun a ha =>
    keep a (by simp only [Below]; omega)
  obtain ⟨tl, tb⟩ := hI.lit.repr.total hI.lit.short
  have F : IntFacts m M sp L s g b ts r f := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := hra, L_lo := by omega,
    L_he := by omega, L_al := by omega, s_lo := by omega, s_th := by omega, l_lo := by omega,
    l_hi := hl40, g_lo := by omega, g_hi := by omega, ts_lo := by omega, ts_hi := by omega,
    keep := keep,
    bytes := fun i hi => (hfr _ (by omega)).trans (hI.bytes i hi),
    ts_len := (hfr _ (by omega)).trans tl,
    ts_bytes := fun i hi => (hfr _ (by omega)).trans (tb i hi),
    sv0 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv1 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv2 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv3 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv4 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv5 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv6 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv7 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    sv8 := by rw [← hM]; fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8] }
  -- `g->strt`
  have hsz := hS.size_pos
  have hmod : (luaHash seed b).toNat % rt.strtSize < rt.strtHeads.length := by
    rw [hS.heads_len]; exact Nat.mod_lt _ hsz
  obtain ⟨d, hch⟩ := ChainFirst.toAt (M := M) (by omega) (by omega) hfr (hI.lit.first hmod)
  have hb8 : ∀ a v, rd64 (fillZeroMem m) a = some v → a + 8 ≤ 0x87800000 → bytesT8 M a = BitVec.ofNat 64 v :=
    fun a v e ha => (bytesT8_congrT fun i _ => hfr _ (by omega)).trans (bT8_of_fill (bytesT8_of_rd64 e))
  have hhd := hS.bucket _ hmod
  have hsize := hS.size
  have hhash := hS.hash
  rw [hI.rt_g] at hsize hhash
  have hhh : rt.strtHash + 8 * rt.strtSize ≤ 0x87800000 := hI.hash_hi
  have hml := Nat.mod_lt (luaHash seed b).toNat hsz
  have T : IntTab M g (luaHash seed b) b ts rt.strtSize rt.strtHash
      rt.strtHeads[(luaHash seed b).toNat % rt.strtSize] d := {
    size_w := (bytesT4_congrT fun i _ => hfr _ (by omega)).trans (bT4_of_fill (bytesT4_of_rd32 hsize))
    hash_w := hb8 _ _ hhash (by omega)
    size_pos := hsz, size_hi := hI.size_hi, size_pow2 := hS.size_pow2
    hash_lo := by have := hI.hash_lo; simp only [symTohost] at this; omega
    hash_hi := by omega
    head_w := hb8 _ _ hhd (by omega)
    head_lt := rd64_lt hhd
    walk := hch }
  obtain ⟨c2, s2, hp⟩ := int_hash m M sp L s g ts _ _ _ d b seed r f o F T b.length _
    ⟨by omega, Nat.le_refl _, by fcx_unfold; exact h.repin (by pins_of h)⟩
  exact ⟨c2, acc.trans s2, hp⟩


/-! ## `luaS_newlstr` -/

set_option hygiene false in
local macro_rules | `(tactic| kit_guard_ext) => `(tactic| exact hg40)

/-- **`luaS_newlstr(L, str, l)` on an interned short C string**: `l ≤ 40`, the
tail `j internshrstr` (`internshrstr_sum`). -/
theorem newlstr_sum (sp L s g ts : Nat) (b : List UInt8) (seed : UInt32) (rt : RtPtrs) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (hI : InternIn m sp L s g b seed ts rt r) :
    Triple (SegSt 0x80017694#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 s⟩,
        ⟨Register.x12, BitVec.ofNat 64 b.length⟩] sp r f) (ArmPay m o))
      (intPost r sp ts f m o) := by
  intro c h
  have acc := Steps.refl c
  have hl : b.length ≤ 40 := hI.lit.short
  have hg40 : zopz0zKzJ_u ((0#64) + sign_extend (m := 64) (0x028#12)) (BitVec.ofNat 64 b.length) = true := by
    rw [show (0#64 : BitVec 64) + sign_extend (m := 64) (0x028#12) = BitVec.ofNat 64 40 by decide,
      fuge (by decide) (by omega)]
    simp only [decide_eq_true_eq]; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  kit_run h acc until [0x80017350]
  obtain ⟨c2, s2, hp⟩ := internshrstr_sum sp L s g ts b seed rt r f m o hI _
    (by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  exact ⟨c2, acc.trans s2, hp⟩

end Lua.Vm.Sim.Kit
