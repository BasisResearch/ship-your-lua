import Lua.Vm.Sim.Kit.PushLitProof
import Lua.Vm.Sim.Kit.FltValLt
import Lua.Vm.AtF.LuaHGetMiss
import Lua.Vm.AtF.GmfMiss

/-!
# `luaH_get` missing a short-string key (lane F1-17)

`luaL_tolstring` on a string asks the string library's metatable for
`"__tostring"` (`luaL_callmeta` → `luaL_getmetafield` → `lua_rawget` →
`luaH_get`), which misses (the boot fact `StrMtMiss`). This file proves the
miss on the callee-context route (`Lua/Vm/AtF/LuaHGetMiss.lean`,
`gen_lua_at.py --fn luaH_get/miss`): the main position (`gs_mpos`, lane
F1-7's arithmetic), then the chain walk as `seg_loop` over the walk's length
(`HMissAt`, from the boot fact's `NodeMiss` by `NodeMiss.toAt`, an induction
on the boot fact), returning `absentkey` (`0x80053160`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The walk over total reads -/

/-- **A node whose key is not the short string `ts`** (`lbu 9` against
`LUA_VSHRSTR`, `ld 16` against `ts`), over total reads. -/
def KeyNe (M : Mem) (ts n : Nat) : Prop :=
  bytesT1 M (n + 9) ≠ 0x44#8 ∨ bytesT8 M (n + 16) ≠ BitVec.ofNat 64 ts

/-- **`luaH_get`'s walk misses `ts` from node `n` after `d` more nodes**
(`seg_loop`'s measure), over total reads: past keys that are not `ts`, to a
node whose `gnext` is 0. -/
inductive HMissAt (M : Mem) (ts : Nat) : Nat → Nat → Prop where
  | last {n : Nat} : 0x8005c6d0 ≤ n → n + 24 ≤ 2 ^ 32 → KeyNe M ts n → bytesT4 M (n + 12) = 0#32 →
      HMissAt M ts 0 n
  | next {d n g : Nat} : 0x8005c6d0 ≤ n → n + 24 ≤ 2 ^ 32 → KeyNe M ts n →
      bytesT4 M (n + 12) = BitVec.ofNat 32 g → g ≠ 0 → g < 2 ^ 32 → HMissAt M ts d (nodeNext n g) →
      HMissAt M ts (d + 1) n

/-- A non-zero total byte is present in the fill. -/
theorem fill_of_bytesT1 {M : Mem} {a : Nat} {v : BitVec 8} (h : bytesT1 M a = v) (hv : v ≠ 0#8) :
    (fillZeroMem M)[a]? = some v := by
  rw [fillZeroMem_get]
  simp only [bytesT1] at h
  split
  · rw [← h]
  · cases e : M[a]? with
    | none => rw [e] at h; exact absurd h.symm (by simpa using hv)
    | some x => rw [e] at h; simp at h; rw [h]

/-- **The boot fact's walk over total reads**: `NodeMiss` of the fill (`StrMtMiss`)
as `HMissAt` of the memory, the array above `tohost` and below `2 ^ 32`. -/
theorem NodeMiss.toAt {M : Mem} {ts lo hi : Nat} (hts : ts < 2 ^ 64) (hlo : 0x8005c6d0 ≤ lo)
    (hhi : hi ≤ 2 ^ 32) : ∀ {n}, NodeMiss (fillZeroMem M) ts lo hi n → ∃ d, HMissAt M ts d n := by
  have kne : ∀ n, (rd8 (fillZeroMem M) (n + nodeKeyTtOff) ≠ some vShrStr ∨
      ∃ kv, rd64 (fillZeroMem M) (n + nodeKeyValOff) = some kv ∧ kv ≠ ts) → KeyNe M ts n := by
    intro n h
    rcases h with h | ⟨kv, hkv, hne⟩
    · refine .inl fun e => h ?_
      have := fill_of_bytesT1 e (by decide)
      simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero, Option.bind_eq_bind,
        Option.pure_def, nodeKeyTtOff, this, Option.bind_some, vShrStr]
      rfl
    · refine .inr fun e => hne ?_
      have e2 := bT8_of_fill (bytesT8_of_rd64 hkv)
      simp only [nodeKeyValOff] at e2
      rw [e2] at e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rd64_lt hkv), Nat.mod_eq_of_lt hts] at this
      exact this
  intro n h
  induction h with
  | last h1 h2 h3 h4 =>
    refine ⟨0, .last (by omega) (by simp only [nodeSize] at h2; omega) (kne _ h3) ?_⟩
    have := bT4_of_fill (bytesT4_of_rd32 h4)
    simpa [nodeNextOff] using this
  | @next n g h1 h2 h3 h4 h5 _ ih =>
    obtain ⟨d, hd⟩ := ih
    have hg := bT4_of_fill (bytesT4_of_rd32 h4)
    simp only [nodeNextOff] at hg
    exact ⟨d + 1, .next (by omega) (by simp only [nodeSize] at h2; omega) (kne _ h3) hg h5
      (rdLE_spec 4 _ _ _ h4).1 hd⟩

/-! ## The rows -/

/-- `luaH_get`'s root contexts: `sp`, the table `t`, the key `k`, the
string `ts`, `t->node`, the walk's node `n`; `ra` and the frame. -/
@[at_row] abbrev hgX (sp t k ts node n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) :
    FCx :=
  FCx.mk' [sp, t, k, ts, node, n] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11]
    m o

/-- `lbu`'s byte against `LUA_VSHRSTR`. -/
theorem zext8_ne_44 (b : BitVec 8) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) != 0x44#64) = !decide (b = 0x44#8) :=
  zext8_ofNat_bne (l := 0x44) (by decide) b

/-- `ld`'s key against `ts`. -/
theorem kv_ne (ts : Nat) (v : BitVec 64) : (BitVec.ofNat 64 ts != v) = !decide (v = BitVec.ofNat 64 ts) := by
  have : (BitVec.ofNat 64 ts == v) = decide (v = BitVec.ofNat 64 ts) := by
    by_cases h : v = BitVec.ofNat 64 ts
    · subst h; simp
    · simp only [h, decide_false]; exact beq_false_of_ne (Ne.symm h)
  rw [bne, this]

/-- `lw`'s `gnext` against zero. -/
theorem sext32_beq0 (g : BitVec 32) : (sign_extend (m := 64) g == 0x0#64) = decide (g = 0#32) := by
  by_cases h : g = 0#32
  · subst h; decide
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro e; apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg (fun x : BitVec 64 => x.toNat % 2 ^ 32) e
    simp only [sext32_mod g (Nat.le_refl 32)] at this
    simpa [Nat.mod_eq_of_lt g.isLt] using this

/-- **The main position** as the first segments leave it in `a0`. -/
theorem hg_mp {m : Mem} {t k ts node lsz hh : Nat} (hk : bytesT8 m k = BitVec.ofNat 64 ts)
    (hn : bytesT8 m (t + 24) = BitVec.ofNat 64 node) (hl : bytesT1 m (t + 11) = BitVec.ofNat 8 lsz)
    (hh' : bytesT4 m (ts + 12) = BitVec.ofNat 32 hh) (hhl : hh < 2 ^ 32) (hlsz : lsz < 31) (ht : t + 32 ≤ 2 ^ 32)
    (hk' : k + 16 ≤ 2 ^ 32) (hts : ts + 16 ≤ 2 ^ 32) :
    ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 (t)) + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8))) + (shift_bits_left ((shift_bits_left ((sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x001#12)) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (zero_extend (m := 64) (bytesT1 (m) ((BitVec.ofNat 64 (t)) + sign_extend (m := 64) (0x00b#12)).toNat : BitVec (8 * 1))) 31 0) 4 0))) + sign_extend (m := 64) (0xfff#12)) 31 0)) &&& (sign_extend (m := 64) (bytesT4 (m) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 (k)) + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))) + sign_extend (m := 64) (0x00c#12)).toNat : BitVec (8 * 4)))) (Sail.BitVec.extractLsb (0x01#6) 5 0)) + ((sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x001#12)) 31 0) (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (zero_extend (m := 64) (bytesT1 (m) ((BitVec.ofNat 64 (t)) + sign_extend (m := 64) (0x00b#12)).toNat : BitVec (8 * 1))) 31 0) 4 0))) + sign_extend (m := 64) (0xfff#12)) 31 0)) &&& (sign_extend (m := 64) (bytesT4 (m) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 (k)) + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8))) + sign_extend (m := 64) (0x00c#12)).toNat : BitVec (8 * 4))))) (Sail.BitVec.extractLsb (0x03#6) 5 0)))
      = BitVec.ofNat 64 (node + nodeSize * (hh % 2 ^ lsz)) := by
  rw [gs_addr (k := 24) (by decide) (by omega), gs_addr (k := 11) (by decide) (by omega),
    gs_addr (k := 0) (by decide) (by omega), Nat.add_zero k, hk]
  simp only [sext64_id]
  rw [gs_addr (k := 12) (by decide) (by omega), hh', hn, hl]
  have hb : (BitVec.ofNat 8 lsz).toNat = lsz := by simp only [BitVec.toNat_ofNat]; omega
  have := gs_mpos node (BitVec.ofNat 8 lsz) (BitVec.ofNat 32 hh) (by omega)
  rw [hb] at this
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhl]

/-! ## The walk and the summary -/

/-- **The chain walk** from the loop head `0x80018278` at node `n`, the miss
`d` nodes on: `absentkey` returned, the memory unchanged. -/
theorem hget_loop (sp t k ts node : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) (ht : 0x8005c6d0 ≤ t) (ht' : t + 32 ≤ 2 ^ 32)
    (hk : 0x8005c6d0 ≤ k) (hk' : k + 16 ≤ 2 ^ 32) (hs : 0x8005c6d0 ≤ ts) (hs' : ts + 16 ≤ 2 ^ 32) :
    ∀ dn : Nat × Nat, Triple (fun c => HMissAt M ts dn.1 dn.2 ∧
        SegSt 0x80018278#64 (Lua.Vm.AtF.LuaHGetMiss.r3 (hgX sp t k ts node dn.2 r f M o))
          (ArmPay (hgX sp t k ts node dn.2 r f M o).m (hgX sp t k ts node dn.2 r f M o).o) c)
      (wrRet r sp 0x80053160 f M o) := by
  refine seg_loop (fun dn => dn.1) fun ⟨d, n⟩ c ⟨hm, h⟩ => ?_
  have acc := Steps.refl c
  simp only at hm
  have h : SegSt 0x80018278#64 (Lua.Vm.AtF.LuaHGetMiss.r3 (hgX sp t k ts node n r f M o))
      (ArmPay (hgX sp t k ts node n r f M o).m (hgX sp t k ts node n r f M o).o) c := h
  cases hm with
  | last hn1 hn2 hne hg0 =>
    have hX : Lua.Vm.AtF.LuaHGetMiss.Ok_C (hgX sp t k ts node n r f M o) := by fcx_ok
    have hg5 : (sign_extend (m := 64) (bytesT4 M (n + 12) : BitVec (8 * 4)) == 0x0#64) = true := by
      rw [sext32_beq0, hg0]; rfl
    by_cases htt : bytesT1 M (n + 9) = 0x44#8
    · have hg2 : (zero_extend (m := 64) (bytesT1 M (n + 9) : BitVec (8 * 1)) != 0x44#64) = false := by
        rw [zext8_ne_44, htt]; rfl
      have hkv : (BitVec.ofNat 64 ts != bytesT8 M (n + 16)) = true := by
        rw [kv_ne]; rcases hne with h' | h'
        · exact absurd htt h'
        · simp only [h', decide_false, Bool.not_false]
      fat_run Lua.Vm.AtF.LuaHGetMiss h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr (h.repin (by pins_of h))⟩
    · have hg2 : (zero_extend (m := 64) (bytesT1 M (n + 9) : BitVec (8 * 1)) != 0x44#64) = true := by
        rw [zext8_ne_44]; simp [htt]
      fat_run Lua.Vm.AtF.LuaHGetMiss h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr (h.repin (by pins_of h))⟩
  | @next d n g hn1 hn2 hne hgw hg0 hgl hrest =>
    have hX : Lua.Vm.AtF.LuaHGetMiss.Ok_C (hgX sp t k ts node n r f M o) := by fcx_ok
    have hg5 : (sign_extend (m := 64) (bytesT4 M (n + 12) : BitVec (8 * 4)) == 0x0#64) = false := by
      rw [sext32_beq0, hgw]
      simp only [decide_eq_false_iff_not]
      intro e; apply hg0
      have := congrArg BitVec.toNat e
      simpa [Nat.mod_eq_of_lt hgl] using this
    have hstep : ∀ c1, Steps c c1 →
        SegSt 0x80018260#64 (Lua.Vm.AtF.LuaHGetMiss.r6 (hgX sp t k ts node n r f M o))
          (ArmPay (hgX sp t k ts node n r f M o).m (hgX sp t k ts node n r f M o).o) c1 ∨
        SegSt 0x80018260#64 (Lua.Vm.AtF.LuaHGetMiss.r9 (hgX sp t k ts node n r f M o))
          (ArmPay (hgX sp t k ts node n r f M o).m (hgX sp t k ts node n r f M o).o) c1 →
        ∃ c', Steps c c' ∧ ((∃ a' : Nat × Nat, a'.1 < d + 1 ∧ HMissAt M ts a'.1 a'.2 ∧
          SegSt 0x80018278#64 (Lua.Vm.AtF.LuaHGetMiss.r3 (hgX sp t k ts node a'.2 r f M o))
            (ArmPay (hgX sp t k ts node a'.2 r f M o).m (hgX sp t k ts node a'.2 r f M o).o) c') ∨
          wrRet r sp 0x80053160 f M o c') := by
      intro c1 acc h1
      rcases h1 with h | h
      all_goals
        fat_run Lua.Vm.AtF.LuaHGetMiss h acc until [0x80018278]
        fcx_unfold at h
        rw [gs_addr (k := 12) (by decide) (by omega), hgw, gs_next n _ (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hgl] at h
        exact ⟨_, acc, .inl ⟨(d, nodeNext n g), by simp, hrest, h.repin (by pins_of h)⟩⟩
    by_cases htt : bytesT1 M (n + 9) = 0x44#8
    · have hg2 : (zero_extend (m := 64) (bytesT1 M (n + 9) : BitVec (8 * 1)) != 0x44#64) = false := by
        rw [zext8_ne_44, htt]; rfl
      have hkv : (BitVec.ofNat 64 ts != bytesT8 M (n + 16)) = true := by
        rw [kv_ne]; rcases hne with h' | h'
        · exact absurd htt h'
        · simp only [h', decide_false, Bool.not_false]
      fat_run Lua.Vm.AtF.LuaHGetMiss h acc until [0x80018260]
      exact hstep _ acc (.inr h)
    · have hg2 : (zero_extend (m := 64) (bytesT1 M (n + 9) : BitVec (8 * 1)) != 0x44#64) = true := by
        rw [zext8_ne_44]; simp [htt]
      fat_run Lua.Vm.AtF.LuaHGetMiss h acc until [0x80018260]
      exact hstep _ acc (.inl h)

/-- **What `luaH_get`'s miss reads**: the table `t` (`lsizenode`, `node`),
the key `TValue` at `k` (`LUA_VSHRSTR`, the string `ts`), the string's hash,
the walk from the main position missing. -/
structure HGetIn (M : Mem) (t k ts node lsz hh : Nat) : Prop where
  t_lo : 0x8005c6d0 ≤ t
  t_hi : t + 32 ≤ 2 ^ 32
  k_lo : 0x8005c6d0 ≤ k
  k_hi : k + 16 ≤ 2 ^ 32
  s_lo : 0x8005c6d0 ≤ ts
  s_hi : ts + 16 ≤ 2 ^ 32
  key_w : bytesT8 M k = BitVec.ofNat 64 ts
  tag_w : bytesT1 M (k + 8) = 0x44#8
  node_w : bytesT8 M (t + 24) = BitVec.ofNat 64 node
  lsz_w : bytesT1 M (t + 11) = BitVec.ofNat 8 lsz
  lsz_lt : lsz < 31
  hash_w : bytesT4 M (ts + 12) = BitVec.ofNat 32 hh
  hash_lt : hh < 2 ^ 32
  miss : ∃ d, HMissAt M ts d (node + nodeSize * (hh % 2 ^ lsz))

/-- **`luaH_get(t, key)` on a short-string key that misses** (`0x800181a0`):
`absentkey` returned, the memory unchanged. -/
theorem hget_miss_sum (sp t k ts node lsz hh : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) (hx : HGetIn M t k ts node lsz hh) :
    Triple (SegSt 0x800181a0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 t⟩, ⟨Register.x11, BitVec.ofNat 64 k⟩]
        sp r f) (ArmPay M o))
      (wrRet r sp 0x80053160 f M o) := by
  intro c h
  have := hx.t_lo; have := hx.t_hi; have := hx.k_lo; have := hx.k_hi; have := hx.s_lo; have := hx.s_hi
  have hX : Lua.Vm.AtF.LuaHGetMiss.Ok (hgX sp t k ts node 0 r f M o) := by fcx_ok
  have hc0 := hx.tag_w; have hc1 := hx.key_w; have hc2 := hx.node_w
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800181a0#64 (Lua.Vm.AtF.LuaHGetMiss.r0 (hgX sp t k ts node 0 r f M o))
      (ArmPay (hgX sp t k ts node 0 r f M o).m (hgX sp t k ts node 0 r f M o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.LuaHGetMiss h acc until [0x80018278]
  fcx_unfold at h
  rw [hg_mp hx.key_w hx.node_w hx.lsz_w hx.hash_w hx.hash_lt hx.lsz_lt hx.t_hi hx.k_hi hx.s_hi] at h
  obtain ⟨d, hd⟩ := hx.miss
  obtain ⟨c', s', h'⟩ := hget_loop sp t k ts node r f M o hsp hra hx.t_lo hx.t_hi hx.k_lo hx.k_hi hx.s_lo
    hx.s_hi (d, node + nodeSize * (hh % 2 ^ lsz)) _ ⟨hd, h.repin (by pins_of h)⟩
  exact ⟨c', acc.trans s', h'⟩

/-! ## The string metatable's miss, from the boot fact -/

/-- **`StrMtMiss` as `luaH_get` reads it**: the boot fact of the fill, the key
slot `k` holding `"__tostring"` (`LUA_VSHRSTR`), the string in RAM. -/
theorem _root_.Lua.Vm.StrMtMiss.hgetIn {M : Mem} {g ts smt node lsz hh k : Nat}
    (hm : StrMtMiss (fillZeroMem M) g ts smt node lsz hh) (hk : 0x8005c6d0 ≤ k) (hk' : k + 16 ≤ 2 ^ 32)
    (hs : 0x8005c6d0 ≤ ts) (hs' : ts + 16 ≤ 2 ^ 32) (hkey : bytesT8 M k = BitVec.ofNat 64 ts)
    (htag : bytesT1 M (k + 8) = 0x44#8) : HGetIn M smt k ts node lsz hh := by
  have e1 := hm.smt_lo; have e2 := hm.smt_hi; have e3 := hm.node_lo; have e4 := hm.node_hi
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hpos : 0 < 2 ^ lsz := Nat.two_pow_pos lsz
  refine ⟨by omega, by omega, hk, hk', hs, hs', hkey, htag, ?_, ?_, hm.lsz_lt, ?_,
    (rdLE_spec 4 _ _ _ hm.hash_w).1, ?_⟩
  · exact bT8_of_fill (bytesT8_of_rd64 hm.node_w)
  · rw [← bytesT1_fill]; exact bytesT1_of_rd8 hm.lsz_w
  · exact bT4_of_fill (bytesT4_of_rd32 hm.hash_w)
  · exact NodeMiss.toAt (by omega) (by omega) e4 hm.miss

/-! ## `luaL_getmetafield.part.0(L, "__tostring")` -/

/-- `absentkey` (`LUA_VABSTKEY`, value 0) in `.rodata`. -/
theorem rod_absent {m : Mem} (h : RodataRead m) :
    bytesT8 m 0x80053160 = 0x0#64 ∧ bytesT1 m 0x80053168 = 0x20#8 := by
  refine ⟨?_, ?_⟩
  · have := At.rod8 h (0x80053160 - Image.rodataBase) (by decide)
    rw [show Image.rodataBase + (0x80053160 - Image.rodataBase) = 0x80053160 by decide] at this
    rw [this]; decide
  · have := h (0x80053168 - Image.rodataBase) (by decide)
    rw [show Image.rodataBase + (0x80053168 - Image.rodataBase) = 0x80053168 by decide] at this
    rw [this]; decide

/-- `luaL_getmetafield.part.0`'s root contexts: `sp`, `L`, `L->top` after the
push, the metatable, `L->tbclist`; `ra` and the frame. -/
@[at_row] abbrev gmX (sp L t smt tbc : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, L, t, smt, 0, tbc] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11]
    m o

/-- **What `luaL_getmetafield.part.0(L, "__tostring")` needs**: `L->top` at
`t` with the string metatable `smt` below it, `G(L)`, `L->tbclist` below the
metatable's slot, `lua_pushstring`'s objects (`PushCx`) and literals (frozen
on `FL`, off what the push writes), the slots `[t - 16, t + 16)` apart from
`L`, `g` and `"__tostring"`'s string. -/
structure GmfIn (m : Mem) (sp L t g sl smt tbc : Nat) (ls : LitPtrs) (FL : Nat → Prop) : Prop where
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 t
  g_w : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  mt_w : bytesT8 m (t - 16) = BitVec.ofNat 64 smt
  tbc_w : bytesT8 m (L + 64) = BitVec.ofNat 64 tbc
  tbc_lt : tbc < t - 16
  smt : smt = ls.smt
  cx : PushCx (sp - 32) L t g 0x80020544#64
  sp_al : sp % 16 = 0
  sp_hi : sp ≤ 2 ^ 32
  t_lo : 0x8005c6d0 + 16 ≤ t
  sL : Apart (t - 16) 48 L stateSize
  sg : Apart (t - 16) 32 g gEnd
  st : Apart ls.tos 30 (t - 16) 32
  lit_ap : LitApart ls.tos L g t
  room : t + 32 ≤ sl
  ro : RodataRead m
  lits : Frozen FL (fun M => LitsHold M g sl ls) m
  foot : ∀ a, FL a → a < heapEnd ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a
  fl_ap : ∀ a, FL a → ¬ (Rng (L + 16) 8 a ∨ Rng t 16 a ∨ Rng (g + gTotalbytesOff) 8 a ∨
    Rng (g + gGCdebtOff) 8 a ∨ a = ls.tos + gcMarkedOff)
  cache : LitCache m g ls
  gcstp : bytesT1 m (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr

/-- **What `luaL_getmetafield.part.0` leaves on a miss**: `L->top` one slot
below its entry's (the metatable popped), the cache's candidates, every byte
kept off `L->top`, the slot `[t, t + 16)`, `g`'s string cache, `totalbytes`,
`GCdebt`, `"__tostring"`'s mark and the callee frames below `sp`. -/
structure GmfPost (m m' : Mem) (sp L g t : Nat) (ls : LitPtrs) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (t - 16)
  cache : LitCache m' g ls
  keep : ∀ a, sp ≤ a ∨ (a + 16384 + 64 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng t 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + gTotalbytesOff) 8 a ∧
      ¬ Rng (g + gGCdebtOff) 8 a ∧ ¬ Rng (ls.tos + gcMarkedOff) 1 a) →
    bytesT1 m' a = bytesT1 m a

set_option hygiene false in
/-- `GmfIn`'s numbers in context (`omega`'s facts). -/
local macro "gmf_ctx" : tactic => `(tactic| (
  have hcx := hx.cx
  have := hcx.sp_lo; have := hcx.sp_hi; have := hcx.sp_al; have := hcx.L_lo; have := hcx.L_hi; have := hcx.L_al
  have := hcx.g_lo; have := hcx.g_hi; have := hcx.g_al; have := hcx.t_lo; have := hcx.t_hi; have := hcx.t_al
  have := hx.t_lo; have := hx.sp_al; have := hx.sp_hi; have := hx.tbc_lt
  have hHE : heapEnd = 0x87800000 := rfl
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hgE : gEnd = 1400 := rfl
  have hSS : stateSize = 200 := rfl
  have hsp : 0x87800000 + 16384 + 1024 + 32 ≤ sp := by omega))

set_option hygiene false in
/-- `GmfIn`'s separations (disjunctions: only where `omega` needs them). -/
local macro "gmf_ap" : tactic => `(tactic| (
  have hsL := hx.sL; have hsg := hx.sg; have hst := hx.st
  have hLg := hcx.Lg; have htg := hcx.tg; have htL := hcx.tL
  have hlL := hx.lit_ap.L; have hlg := hx.lit_ap.g; have hlt := hx.lit_ap.top
  simp only [Apart] at hsL hsg hst hLg htg htL hlL hlg hlt))

/-- **The memory after `luaL_getmetafield`'s push**: `L->top` one slot up,
`"__tostring"` in the new slot, the metatable below it, `L->tbclist`, the
frame's saved words, `.rodata`, the literals (frozen on `FL`, below the
heap's end). -/
structure GmfMid (m1 : Mem) (sp L t g sl smt tbc : Nat) (r : BitVec 64) (f : AbiFrame) (ls : LitPtrs)
    (FL : Nat → Prop) : Prop where
  top_w : bytesT8 m1 (L + 16) = BitVec.ofNat 64 (t + 16)
  mt_w : bytesT8 m1 (t - 16) = BitVec.ofNat 64 smt
  val_w : bytesT8 m1 t = BitVec.ofNat 64 ls.tos
  tag_w : bytesT1 m1 (t + 8) = 0x44#8
  tbc_w : bytesT8 m1 (L + 64) = BitVec.ofNat 64 tbc
  ra_w : bytesT8 m1 (sp - 8) = r
  s0_w : bytesT8 m1 (sp - 16) = f.s0
  s1_w : bytesT8 m1 (sp - 24) = f.s1
  ro : RodataRead m1
  lits : Frozen FL (fun M => LitsHold M g sl ls) m1

/-- **What `lua_rawget` and `lua_settop(L, -3)` leave**: `L->top` at the
metatable's slot, every byte kept off `L->top`, the key's slot and the
frames `[sp - 64, sp)`. -/
structure GmfRest (m1 m' : Mem) (sp L t : Nat) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (t - 16)
  keep : ∀ a, ¬ (Rng (L + 16) 8 a ∨ Rng t 16 a ∨ (sp - 64 ≤ a ∧ a < sp)) → bytesT1 m' a = bytesT1 m1 a

/-- **The memory at `lua_rawget`'s return from `luaH_get`**: `L->top`,
`L->tbclist`, `lua_rawget`'s and `luaL_getmetafield`'s saved words, `.rodata`. -/
structure GmfTail (M : Mem) (sp L t tbc : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  top_w : bytesT8 M (L + 16) = BitVec.ofNat 64 (t + 16)
  tbc_w : bytesT8 M (L + 64) = BitVec.ofNat 64 tbc
  ra_w : bytesT8 M (sp - 8) = r
  s0_w : bytesT8 M (sp - 16) = f.s0
  s1_w : bytesT8 M (sp - 24) = f.s1
  rra_w : bytesT8 M (sp - 40) = 0x80020550#64
  rs0_w : bytesT8 M (sp - 48) = BitVec.ofNat 64 L
  ro : RodataRead M

/-- **`lua_rawget` after the miss and `lua_settop(L, -3)`** (the root
`0x800035a8`): `L->top` at the metatable's slot, returning `LUA_TNIL`. -/
theorem gmf_tail {sp L t g sl smt tbc : Nat} {ls : LitPtrs} {FL : Nat → Prop} {r : BitVec 64}
    {f : AbiFrame} {m M : Mem} {o : Array String} (hra : r.toNat % 4 = 0)
    (hx : GmfIn m sp L t g sl smt tbc ls FL) (hT : GmfTail M sp L t tbc r f) :
    Triple (SegSt 0x800035a8#64 (Lua.Vm.AtF.GmfMiss.r5 (gmX sp L (t + 16) smt tbc r f M o))
        (ArmPay (gmX sp L (t + 16) smt tbc r f M o).m (gmX sp L (t + 16) smt tbc r f M o).o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ GmfRest M m' sp L t) := by
  intro c2 h
  gmf_ctx
  have hX3 : Lua.Vm.AtF.GmfMiss.Ok (gmX sp L (t + 16) smt tbc r f M o) := by
    have hsL := hx.sL; simp only [Apart] at hsL; fcx_ok
  obtain ⟨hc2, hc3⟩ := rod_absent hT.ro
  have hc0 := hT.top_w; have hc6 := hT.tbc_w; have hc4 := hT.rra_w; have hc5 := hT.rs0_w
  have hc7 := hT.ra_w; have hc8 := hT.s0_w; have hc9 := hT.s1_w
  have acc := Steps.refl c2
  fat_run Lua.Vm.AtF.GmfMiss h acc
  fcx_unfold at h
  refine ⟨_, acc, _, h.repin (by pins_of h), ⟨?_, fun a ha => ?_⟩⟩
  · rw [fw8_same rfl, show t + 16 - 32 = t - 16 by omega]
  · simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    simp (disch := omega) only [fw1_wm8, fw1_ins]

/-- **`luaL_getmetafield.part.0` after the push** (the root `0x80020544`):
`lua_rawget(L, -2)` with `luaH_get`'s miss (`hget_miss_sum`, the boot fact
`StrMtMiss`), then `gmf_tail`. -/
theorem gmf_rest {sp L t g sl smt tbc : Nat} {ls : LitPtrs} {FL : Nat → Prop} {r : BitVec 64}
    {f : AbiFrame} {m m1 : Mem} {o : Array String} (hra : r.toNat % 4 = 0)
    (hx : GmfIn m sp L t g sl smt tbc ls FL) (hm : GmfMid m1 sp L t g sl smt tbc r f ls FL) :
    Triple (SegSt 0x80020544#64 (Lua.Vm.AtF.GmfMiss.r2 (gmX sp L (t + 16) smt tbc r f m1 o))
        (ArmPay (gmX sp L (t + 16) smt tbc r f m1 o).m (gmX sp L (t + 16) smt tbc r f m1 o).o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ GmfRest m1 m' sp L t) := by
  intro c1 h
  gmf_ctx
  have hX2 : Lua.Vm.AtF.GmfMiss.Ok (gmX sp L (t + 16) smt tbc r f m1 o) := by
    have hsL := hx.sL; simp only [Apart] at hsL; fcx_ok
  have hc0 := hm.top_w
  have hc1 : bytesT8 m1 (t + 16 - 32) = BitVec.ofNat 64 smt := by
    rw [show t + 16 - 32 = t - 16 by omega]; exact hm.mt_w
  have acc := Steps.refl c1
  fat_run Lua.Vm.AtF.GmfMiss h acc until [0x800181a0]
  -- `luaH_get(smt, &key)`: the miss
  have hM1 : ∀ a, (a + 49 ≤ sp ∨ sp - 32 ≤ a) →
      bytesT1 (Lua.Vm.AtF.GmfMiss.m1 (gmX sp L (t + 16) smt tbc r f m1 o)) a = bytesT1 m1 a := by
    intro a ha; fcx_unfold; simp (disch := omega) only [fw1_wm8]
  generalize hM1e : Lua.Vm.AtF.GmfMiss.m1 (gmX sp L (t + 16) smt tbc r f m1 o) = M1 at h hM1
  fcx_unfold at h
  rw [show t + 16 - 16 = t by omega] at h
  obtain ⟨rt, hli⟩ := (hm.lits.trans fun a ha => hM1 a (.inl (by have := (hx.foot a ha).1; omega))).self
  have hts := hli.tos
  have hT1 := hts.ts_lo; have hT2 := hts.ts_hi
  have hkey : bytesT8 M1 t = BitVec.ofNat 64 ls.tos := by
    rw [bytesT8_congrT fun j _ => hM1 _ (.inl (by omega))]; exact hm.val_w
  have htag : bytesT1 M1 (t + 8) = 0x44#8 := by rw [hM1 _ (.inl (by omega))]; exact hm.tag_w
  have hin := (hli.strmt).hgetIn (k := t) (by omega) (by omega) (by simp only [symTohost] at hT1; omega)
    (by simp only [symHeapEnd] at hT2; omega) hkey htag
  rw [← hx.smt] at hin
  obtain ⟨c2, s2, hret2⟩ := hget_miss_sum (sp - 48) smt t ls.tos ls.smtNode ls.smtLsz ls.tosHash 0x800035a8#64
    ⟨BitVec.ofNat 64 L, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M1 o (by omega)
    (by decide) hin _ (by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  simp only [wrRet] at hret2
  have hT : GmfTail M1 sp L t tbc r f := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun o' ho => ?_⟩
    · rw [bytesT8_congrT fun j _ => hM1 _ (.inl (by omega))]; exact hm.top_w
    · rw [bytesT8_congrT fun j _ => hM1 _ (.inl (by omega))]; exact hm.tbc_w
    · rw [bytesT8_congrT fun j _ => hM1 _ (.inr (by omega))]; exact hm.ra_w
    · rw [bytesT8_congrT fun j _ => hM1 _ (.inr (by omega))]; exact hm.s0_w
    · rw [bytesT8_congrT fun j _ => hM1 _ (.inr (by omega))]; exact hm.s1_w
    · rw [← hM1e]; fcx_unfold; rw [fw8_wm8 (by omega), fw8_same rfl]
    · rw [← hM1e]; fcx_unfold; rw [fw8_same rfl]
    · have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl
      rw [hM1 _ (.inl (by omega))]; exact hm.ro o' ho
  obtain ⟨c3, s3, m', hret3, hrest⟩ := gmf_tail hra hx hT _ (hret2.repin (by pins_of hret2))
  refine ⟨c3, (acc.trans s2).trans s3, m', hret3, hrest.top_w, fun a ha => (hrest.keep a ha).trans ?_⟩
  simp only [Rng, not_or, not_and, Nat.not_lt] at ha
  exact hM1 a (by omega)

/-- **`luaL_getmetafield.part.0(L, "__tostring")` on the string metatable**
(`0x8002052c`): `lua_pushstring` (`pushLit_proved`), then `gmf_rest`
(`lua_rawget(L, -2)` with `luaH_get`'s miss, `lua_settop(L, -3)`); returns
`LUA_TNIL`. -/
theorem gmf_miss_sum {sp L t g sl smt tbc : Nat} {ls : LitPtrs} {FL : Nat → Prop} {r : BitVec 64}
    (f : AbiFrame) {m : Mem} (o : Array String) (hra : r.toNat % 4 = 0) (hx : GmfIn m sp L t g sl smt tbc ls FL) :
    Triple (SegSt 0x8002052c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 litTosAddr⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ GmfPost m m' sp L g t ls) := by
  intro c h
  gmf_ctx
  -- the entry: the frame, then `lua_pushstring(L, "__tostring")`
  have hX : Lua.Vm.AtF.GmfMiss.Ok (gmX sp L (t + 16) smt tbc r f m o) := by
    have hsL := hx.sL; simp only [Apart] at hsL; fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8002052c#64 (Lua.Vm.AtF.GmfMiss.r0 (gmX sp L (t + 16) smt tbc r f m o))
      (ArmPay (gmX sp L (t + 16) smt tbc r f m o).m (gmX sp L (t + 16) smt tbc r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.GmfMiss h acc until [0x80002fe4]
  have hM0 : ∀ a, (a + 32 ≤ sp ∨ sp ≤ a) →
      bytesT1 (Lua.Vm.AtF.GmfMiss.m0 (gmX sp L (t + 16) smt tbc r f m o)) a = bytesT1 m a := by
    intro a ha; fcx_unfold; simp (disch := omega) only [fw1_wm8]
  generalize hM0e : Lua.Vm.AtF.GmfMiss.m0 (gmX sp L (t + 16) smt tbc r f m o) = M0 at h hM0
  fcx_unfold at h
  have hLI := hx.lits.trans fun a ha => hM0 a (.inl (by have := (hx.foot a ha).1; omega))
  have hcall := pushLit_proved (sp - 32) L t g sl ⟨litTosAddr, tosB, ls.tos⟩ ls FL 0x80020544#64
    ⟨BitVec.ofNat 64 L, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M0 o
    (by simp [LitPtrs.table]) hcx hx.lit_ap
    ((bytesT8_congrT fun j _ => hM0 _ (by omega)).trans hx.top_w)
    ((bytesT8_congrT fun j _ => hM0 _ (by omega)).trans hx.g_w) (by have := hx.room; omega)
    (fun o' ho => (hM0 _ (.inl (by
      have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl; omega))).trans
      (hx.ro o' ho))
    hLI hx.foot (hx.cache.congr fun a h1 h2 => hM0 a (.inl (by omega)))
    ((hM0 _ (.inl (by simp only [gGcstpOff]; omega))).trans hx.gcstp)
  simp only [callPre, List.cons_append, List.nil_append] at hcall
  obtain ⟨c1, s1, m1, hret, hpp⟩ := hcall _ (h.repin (by pins_of h))
  have acc := acc.trans s1
  simp only [wrRet] at hret
  -- what the push keeps, from the entry memory
  have hK : ∀ a, (sp ≤ a ∨ (a + 16384 + 64 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng t 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + gTotalbytesOff) 8 a ∧
      ¬ Rng (g + gGCdebtOff) 8 a ∧ ¬ Rng (ls.tos + gcMarkedOff) 1 a)) → bytesT1 m1 a = bytesT1 m a := by
    intro a ha
    rcases ha with ha | ⟨h1, h2⟩
    · rw [hpp.keep a (.inl (by omega)), hM0 a (.inr ha)]
    · rw [hpp.keep a (.inr ⟨by omega, h2⟩), hM0 a (.inl (by omega))]
  -- the slots and `L`'s words the rest reads, off what the push writes
  have kN : ∀ a, ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + gTotalbytesOff) 8 a ∧
      ¬ Rng (g + gGCdebtOff) 8 a ↔ ¬ (g + 16 ≤ a ∧ a < g + 32) ∧ ¬ (g + 552 ≤ a ∧ a < g + 1400) := by
    intro a; simp only [Rng, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff]; omega
  -- the slots and `L`'s words the rest reads, off what the push writes
  have kS : ∀ a, Rng (t - 16) 16 a → bytesT1 m1 a = bytesT1 m a := by
    intro a ha
    have hsL := hx.sL; have hsg := hx.sg; have hst := hx.st
    simp only [Apart, Rng] at hsL hsg hst ha
    refine hK a (.inr ⟨by omega, by simp only [Rng]; omega, by simp only [Rng]; omega,
      ((kN a).2 ⟨by omega, by omega⟩).1, ((kN a).2 ⟨by omega, by omega⟩).2.1, ((kN a).2 ⟨by omega, by omega⟩).2.2,
      by simp only [Rng, gcMarkedOff]; omega⟩)
  have kL : ∀ a, Rng (L + 64) 8 a → bytesT1 m1 a = bytesT1 m a := by
    intro a ha
    have hLg := hcx.Lg; have htL := hcx.tL; have hlL := hx.lit_ap.L
    simp only [Apart, Rng] at hLg htL hlL ha
    refine hK a (.inr ⟨by omega, by simp only [Rng]; omega, by simp only [Rng]; omega,
      ((kN a).2 ⟨by omega, by omega⟩).1, ((kN a).2 ⟨by omega, by omega⟩).2.1, ((kN a).2 ⟨by omega, by omega⟩).2.2,
      by simp only [Rng, gcMarkedOff]; omega⟩)
  obtain ⟨rt0, hli0⟩ := hx.lits.self
  have hts0 := hli0.tos.ts_lo
  have kR : ∀ a, a < symTohost → bytesT1 m1 a = bytesT1 m a := by
    intro a ha
    refine hK a (.inr ⟨by omega, by simp only [Rng]; omega, by simp only [Rng]; omega,
      ((kN a).2 ⟨by omega, by omega⟩).1, ((kN a).2 ⟨by omega, by omega⟩).2.1, ((kN a).2 ⟨by omega, by omega⟩).2.2,
      by simp only [Rng, gcMarkedOff]; omega⟩)
  have hmid : GmfMid m1 sp L t g sl smt tbc r f ls FL := by
    refine ⟨hpp.top_w, ?_, hpp.val_w, hpp.tag_w, ?_, ?_, ?_, ?_, fun o' ho => ?_, hx.lits.trans fun a ha => ?_⟩
    · rw [bytesT8_congrT fun j _ => kS _ (by simp only [Rng]; omega)]; exact hx.mt_w
    · rw [bytesT8_congrT fun j _ => kL _ (by simp only [Rng]; omega)]; exact hx.tbc_w
    · rw [bytesT8_congrT fun j _ => (hpp.keep _ (.inl (by omega)))]; rw [← hM0e]; fcx_unfold; fat_rd
    · rw [bytesT8_congrT fun j _ => (hpp.keep _ (.inl (by omega)))]; rw [← hM0e]; fcx_unfold; fat_rd
    · rw [bytesT8_congrT fun j _ => (hpp.keep _ (.inl (by omega)))]; rw [← hM0e]; fcx_unfold; fat_rd
    · have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl
      rw [kR _ (by omega)]; exact hx.ro o' ho
    · have h1 := hx.foot a ha; have h2 := hx.fl_ap a ha
      simp only [not_or] at h2
      obtain ⟨h3, h4, h5, h6, h7⟩ := h2
      exact hK a (.inr ⟨by omega, h3, h4, h1.2, h5, h6, by simp only [Rng]; omega⟩)
  have hX2 : Lua.Vm.AtF.GmfMiss.Ok (gmX sp L (t + 16) smt tbc r f m1 o) := by
    have hsL := hx.sL; simp only [Apart] at hsL; fcx_ok
  obtain ⟨c3, s3, m', hret3, hrest⟩ := gmf_rest hra hx hmid _ (hret.repin (by pins_of hret))
  refine ⟨c3, acc.trans s3, m', hret3, hrest.top_w, ?_, fun a ha => ?_⟩
  · refine hpp.cache.congr fun a h1 h2 => hrest.keep a ?_
    gmf_ap
    simp only [Rng, not_or, not_and, Nat.not_lt]
    refine ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
  · rcases ha with ha | ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · rw [hrest.keep a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega), hK a (.inl ha)]
    · rw [hrest.keep a (by simp only [Rng, not_or, not_and, Nat.not_lt] at h2 h3 ⊢; omega),
        hK a (.inr ⟨h1, h2, h3, h4, h5, h6, h7⟩)]

end Lua.Vm.Sim.Kit
