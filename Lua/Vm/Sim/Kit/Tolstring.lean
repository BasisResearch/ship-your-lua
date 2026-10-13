import Lua.Vm.Sim.Kit.PrintS
import Lua.Vm.AtF.TolTop
import Lua.Vm.AtF.TolNil
import Lua.Vm.AtF.TolTrue
import Lua.Vm.AtF.TolFalse

/-!
# `luaL_tolstring` on nil and booleans (lane F1-12)

`luaL_tolstring(L, i, &l)` (`0x80021b2c`) on a nil, `true` or `false`
argument, on the callee-context route (`Lua/Vm/AtF/{TolNil,TolTrue,TolFalse}.lean`,
`gen_lua_at.py --fn luaL_tolstring/<class>`): `lua_absindex` (a positive index
is its own), `luaL_callmeta` → `lua_getmetatable` (no metatable for nil and
booleans: `G(L)->mt[t]` NULL) → 0, `lua_type`, `lua_toboolean` (booleans),
`lua_pushstring` of the literal `"nil"`, `"true"`, `"false"` (its summary the
named premise `PushLit_Statement`: `luaS_new` finds the interned string, which
`luaX_init` created at boot), then the tail `lua_tolstring(L, -1, &l)` of the
short string at the top (`toltop_sum`, `Lua/Vm/AtF/TolTop.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `lua_tolstring(L, -1, &l)` of the short string at the top -/

/-- The context of `lua_tolstring`'s rows: `sp`, `L`, `&l`, `L->top`, the
string; `ra` and the frame. -/
@[at_row] abbrev ttX (sp L lenp top ts : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) :
    FCx :=
  FCx.mk' [sp, L, lenp, top, ts] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11]
    m o

/-- **A short string at the top**: `L->top`, the slot below it a short
string (`LUA_VSHRSTR`) at `ts` of length `len`. -/
structure TopStr (m : Mem) (L top ts len : Nat) : Prop where
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  tag_w : bytesT1 m (top - 8) = 0x44#8
  val_w : bytesT8 m (top - 16) = BitVec.ofNat 64 ts
  len_w : bytesT1 m (ts + 11) = BitVec.ofNat 8 len
  len_lt : len < 255

/-- The numbers of `lua_tolstring`'s objects. -/
structure TopNums (sp L lenp top ts : Nat) (r : BitVec 64) : Prop where
  sp_hi : sp ≤ 2 ^ 32
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_hi : L + 256 ≤ 2 ^ 32
  L_al : L % 8 = 0
  l_lo : 0x8005c6d0 ≤ lenp
  l_hi : lenp + 8 ≤ 2 ^ 32
  l_al : lenp % 8 = 0
  t_lo : 0x8005c6d0 + 16 ≤ top
  t_hi : top ≤ 2 ^ 32
  s_lo : 0x8005c6d0 ≤ ts
  s_hi : ts + 64 ≤ 2 ^ 32

/-- `zext` of a byte below 255 is not 255. -/
theorem zext_ne_ff (len : Nat) (h : len < 255) :
    (zero_extend (m := 64) (BitVec.ofNat 8 len : BitVec (8 * 1)) == 0xff#64) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e
  have := congrArg BitVec.toNat e
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  omega

/-- `zext` of a byte as a `Nat`. -/
theorem zext_ofNat8 (len : Nat) (h : len < 256) :
    zero_extend (m := 64) (BitVec.ofNat 8 len : BitVec (8 * 1)) = BitVec.ofNat 64 len := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- **`lua_tolstring(L, -1, &l)` of a short string at the top**: `l` the
length, the contents returned. -/
theorem toltop_sum {sp L lenp top ts len : Nat} {r : BitVec 64} (f : AbiFrame) {m : Mem} (o : Array String)
    (hx : TopNums sp L lenp top ts r) (ht : TopStr m L top ts len) :
    Triple (SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (wrRet r sp (ts + 24) f (writeMap8 m lenp (sdData_val (BitVec.ofNat 64 len))) o) := by
  intro c h
  have := hx.sp_hi; have := hx.ra; have := hx.L_lo; have := hx.L_hi; have := hx.L_al; have := hx.l_lo
  have := hx.l_hi; have := hx.l_al; have := hx.t_lo; have := hx.t_hi; have := hx.s_lo; have := hx.s_hi
  have hX : Lua.Vm.AtF.TolTop.Ok (ttX sp L lenp top ts r f m o) := by fcx_ok
  have hc0 := ht.top_w; have hc1 := ht.tag_w; have hc2 := ht.val_w
  have hg_3 : (zero_extend (m := 64) (bytesT1 m (ts + 11) : BitVec (8 * 1)) == 0xff#64) = false := by
    rw [ht.len_w]; exact zext_ne_ff len ht.len_lt
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80002994#64 (Lua.Vm.AtF.TolTop.r0 (ttX sp L lenp top ts r f m o))
      (ArmPay (ttX sp L lenp top ts r f m o).m (ttX sp L lenp top ts r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TolTop h acc
  fcx_unfold at h
  rw [ht.len_w, zext_ofNat8 len (by have := ht.len_lt; omega)] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ## `lua_pushstring` of an interned literal: the named premise -/

/-- **What `lua_pushstring` of an interned literal leaves**: the string at the
top (`L->top` one slot up, `LUA_VSHRSTR`, `ts`), its length, and every byte
kept off `L->top`, the new slot, `g`'s string cache and GC words, the
string's mark byte and the callee frames below `sp`. -/
structure PushPost (m m' : Mem) (sp L g top ts len : Nat) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (top + 16)
  tag_w : bytesT1 m' (top + 8) = 0x44#8
  val_w : bytesT8 m' top = BitVec.ofNat 64 ts
  len_w : bytesT1 m' (ts + 11) = BitVec.ofNat 8 len
  keep : ∀ a, sp ≤ a ∨ (a + 16384 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng top 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + 16) 48 a ∧ ¬ Rng (ts + gcMarkedOff) 1 a) →
    bytesT1 m' a = bytesT1 m a

/-- **Named premise: `lua_pushstring(L, s)` of an interned literal**
(`0x80002fe4`): `s` the NUL-terminated bytes `b`, interned as `ts`
(`LitInterned`, of any memory that agrees with the current one below
`__heap_end`); `luaS_new` finds `ts` (the string cache, or `internshrstr`'s
bucket walk: no allocation), pushes it, and `luaC_checkGC` at most resets the
debt (the collector is stopped). Returns `getstr(ts)`. Open (lane F1-12):
the at-lemmas of `lua_pushstring`, `luaS_new` (`strcmp`), `luaS_newlstr`,
`internshrstr` (the hash loop, the bucket walk with `memcmp`) and
`luaC_step`'s stopped path. -/
def PushLit_Statement : Prop :=
  ∀ (sp L top s ts : Nat) (b : List UInt8) (rt : RtPtrs) (seed : UInt32) (r : BitVec 64) (f : AbiFrame)
    (m m0 : Mem) (o : Array String),
    r.toNat % 4 = 0 → sp % 16 = 0 → sp ≤ 2 ^ 32 → heapEnd + 16384 ≤ sp →
    bytesT8 m (L + 16) = BitVec.ofNat 64 top → bytesT8 m (L + 24) = BitVec.ofNat 64 rt.g →
    top + 16 + 16 ≤ rt.stackLast →
    bytesAt m s (b.length + 1) = b.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8] →
    LitInterned m0 rt seed b ts → (∀ a, a < heapEnd → bytesT1 m a = bytesT1 m0 a) →
    Triple (SegSt 0x80002fe4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 s⟩]
        sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ts + 24) f m' o c ∧ PushPost m m' sp L rt.g top ts b.length)

/-! ## `luaL_tolstring` on a nil or boolean argument -/

/-- `lua_absindex`'s test `(unsigned)(idx + 1000999) > 1000999` on a
positive index: true. -/
theorem absindex_pos (i : Nat) (h1 : 1 ≤ i) (h2 : i < 2 ^ 20) :
    zopz0zI_u ((sign_extend (m := 64) ((0x000f4#20) +++ 0x000#12)) + sign_extend (m := 64) (0x627#12))
      (sign_extend (m := 64) ((Sail.BitVec.extractLsb (BitVec.ofNat 64 i) 31 0) +
        (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb
          ((sign_extend (m := 64) ((0x000f4#20) +++ 0x000#12)) + sign_extend (m := 64) (0x627#12)) 31 0)) 31 0)))
      = true := by
  have hK : (sign_extend (m := 64) ((0x000f4#20) +++ 0x000#12)) + sign_extend (m := 64) (0x627#12)
      = BitVec.ofNat 64 1000999 := by decide
  have hK2 : Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 1000999) 31 0))
      31 0 = BitVec.ofNat 32 1000999 := by decide
  have hi : Sail.BitVec.extractLsb (BitVec.ofNat 64 i) 31 0 = BitVec.ofNat 32 i := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [hK, hK2, hi, BitVec.ofNat_add_ofNat]
  have hs : sign_extend (m := 64) (BitVec.ofNat 32 (i + 1000999)) = BitVec.ofNat 64 (i + 1000999) := by
    apply BitVec.eq_of_toNat_eq
    simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth]
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]
    split <;> rename_i hc <;> simp at hc <;> omega
  rw [hs]
  have e1 : (BitVec.ofNat 64 1000999).toNat = 1000999 := by decide
  have e2 : (BitVec.ofNat 64 (i + 1000999)).toNat = i + 1000999 := by
    simp only [BitVec.toNat_ofNat]; omega
  simp only [zopz0zI_u, BitVec.toNatInt, e1, e2, decide_eq_true_eq]
  exact Int.ofNat_lt.mpr (by omega)

/-- `idx > 0` as `lua_type`'s `blez`. -/
theorem sge0_pos (i : Nat) (h1 : 1 ≤ i) (h2 : i < 2 ^ 31) :
    zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 i) = false := by
  rw [show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sge_ofNat 0 i (by omega) (by omega)]
  simp; omega

/-- **What `luaL_tolstring` reads on a nil or boolean argument**: `L->ci`,
its `func`, `L->top`, `G(L)`, no metatable for the argument's type
(`G(L)->mt[t]`), the argument's tag. -/
structure TolCells (m : Mem) (L i nci func top g t : Nat) (tag : BitVec 8) : Prop where
  ci_w : bytesT8 m (L + 32) = BitVec.ofNat 64 nci
  func_w : bytesT8 m nci = BitVec.ofNat 64 func
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  g_w : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  mt_w : bytesT8 m (g + 480 + 8 * t) = 0#64
  tag_w : bytesT1 m (16 * i + func + 8) = tag

/-- **Where `luaL_tolstring`'s objects lie** (its at-lemmas' `Ok`): `L`, the
C `CallInfo`, the frame's slots up to `L->top` (argument `i` below it, not
`G(L)->nilvalue`), `G(L)`, `&l`, the interned string, below the C stack. -/
structure TolNums (sp L i lenp nci func top g ts : Nat) (r : BitVec 64) : Prop where
  sp_lo : 0x8005e7d8 + 4096 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_hi : L + 256 ≤ 2 ^ 32
  L_al : L % 8 = 0
  i_lo : 1 ≤ i
  i_hi : i < 2 ^ 20
  l_lo : sp ≤ lenp
  l_hi : lenp + 8 ≤ 2 ^ 32
  l_al : lenp % 8 = 0
  ci_lo : 0x8005c6d0 ≤ nci
  ci_hi : nci + 64 ≤ 2 ^ 32
  f_lo : 0x8005c6d0 ≤ func
  f_top : func + 16 * i + 16 ≤ top
  t_hi : top + 64 ≤ 2 ^ 32
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1024 ≤ 2 ^ 32
  L_sp : L + 256 + 4096 ≤ sp
  ci_sp : nci + 64 + 4096 ≤ sp
  t_sp : top + 64 + 4096 ≤ sp
  g_sp : g + 1024 + 4096 ≤ sp
  t_lo : 0x8005c6d0 ≤ top
  nil_ne : 16 * i + func ≠ g + 80
  s_lo : 0x8005c6d0 ≤ ts
  s_hi : ts + 64 ≤ 2 ^ 32
  h_sp : heapEnd + 16384 + 64 ≤ sp

/-- The context of `luaL_tolstring`'s rows: `sp`, `L`, `i`, `&l`, `L->ci`,
`func`, `L->top`, `G(L)`; `ra` and the frame. -/
@[at_row] abbrev tlX (sp L i lenp nci func top g : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, L, i, lenp, nci, func, top, g]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- The frame `lua_pushstring` sees from `luaL_tolstring`: `s0 = L`,
`s1 = i`, `s2 = &l`. -/
abbrev tlFr (L i lenp : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 i, BitVec.ofNat 64 lenp, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9,
    f.s10, f.s11⟩

/-- **What `luaL_tolstring` leaves on a literal argument**: the literal's
string at the top (`L->top` one slot up), `l` its length, every byte kept off
`L->top`, the new slot, `g`'s string cache and GC words, the string's mark,
`&l` and the callee frames below `sp`. -/
structure TolLitPost (m m' : Mem) (sp L lenp g top ts len : Nat) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (top + 16)
  tag_w : bytesT1 m' (top + 8) = 0x44#8
  val_w : bytesT8 m' top = BitVec.ofNat 64 ts
  len_w : bytesT8 m' lenp = BitVec.ofNat 64 len
  keep : ∀ a, (sp ≤ a ∧ ¬ Rng lenp 8 a) ∨ (a + 16384 + 64 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng top 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + 16) 48 a ∧ ¬ Rng (ts + gcMarkedOff) 1 a) →
    bytesT1 m' a = bytesT1 m a

set_option hygiene false in
/-- **`luaL_tolstring` on a literal argument's proof** over the at-lemmas of
`ns` (`TolNil`, `TolTrue`, `TolFalse`: one module per literal tag, the
generator's cells being literals): the run to `lua_pushstring`, its summary
(`PushLit_Statement`), the run to the tail `lua_tolstring`, `toltop_sum`. -/
macro "tol_lit_run " ns:ident lit:term:max b:ident mto:num len:num : tactic => do
  let okN := Lean.mkIdent (ns.getId ++ `Ok)
  let r0N := Lean.mkIdent (ns.getId ++ `r0)
  let m1N := Lean.mkIdent (ns.getId ++ `m1)
  let r3N := Lean.mkIdent (ns.getId ++ `r3)
  `(tactic| (
    intro c h
    have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.ra; have := hx.L_lo; have := hx.L_hi
    have := hx.L_al; have := hx.i_lo; have := hx.i_hi; have := hx.l_lo; have := hx.l_hi; have := hx.l_al
    have := hx.ci_lo; have := hx.ci_hi; have := hx.f_lo; have := hx.f_top; have := hx.t_hi; have := hx.g_lo
    have := hx.g_hi; have := hx.L_sp; have := hx.ci_sp; have := hx.t_sp; have := hx.g_sp; have := hx.t_lo
    have := hx.s_lo; have := hx.s_hi
    have hhs := hx.h_sp
    have hX : $okN (tlX sp L i lenp nci func top rt.g r f m o) := by fcx_ok
    have hc0 := hc.ci_w; have hc1 := hc.func_w; have hc2 := hc.top_w; have hc3 := hc.tag_w; have hc4 := hc.g_w
    have hc5 : bytesT8 m (rt.g + $mto) = 0#64 := hc.mt_w
    have hf0 : 16 * i + func < top := by omega
    have hf1 := hx.nil_ne
    have hg_6 := absindex_pos i hx.i_lo hx.i_hi
    have hg_2 := sge0_pos i hx.i_lo (by omega)
    simp only [callPre, List.cons_append, List.nil_append] at h
    have h : SegSt 0x80021b2c#64 ($r0N (tlX sp L i lenp nci func top rt.g r f m o))
        (ArmPay (tlX sp L i lenp nci func top rt.g r f m o).m (tlX sp L i lenp nci func top rt.g r f m o).o) c :=
      h.repin (by pins_of h)
    have acc := Steps.refl c
    fat_run $ns h acc until [0x80002fe4]
    -- `lua_pushstring(L, "nil")`
    have hM1 : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) →
        ($m1N (tlX sp L i lenp nci func top rt.g r f m o))[a]? = m[a]? := by
      intro a ha; fcx_unfold; simp (disch := omega) only [getElem?_writeMap8_out]
    generalize hM1e : $m1N (tlX sp L i lenp nci func top rt.g r f m o) = M1 at h hM1
    fcx_unfold at h
    have hM1T : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) → bytesT1 M1 a = bytesT1 m a := fun a ha => bT1_congr (hM1 a ha)
    obtain ⟨c1, s1, m', hret, hpp⟩ := hPL (sp - 48) L top $lit ts $b rt seed 0x80021be8#64
      (tlFr L i lenp f) M1 m0 o (by decide) (by omega) (by omega) (by omega)
      ((bytesT8_congrT fun j _ => hM1T _ (by omega)).trans hc2)
      ((bytesT8_congrT fun j _ => hM1T _ (by omega)).trans hc4) hroom
      ((bytesAt_congr fun j hj => hM1T _ (.inl (by simp only [$b:ident, List.length] at hj; omega))).trans hlit)
      hI (fun a ha => (hM1T a (by omega)).trans (hag a ha)) _ (by
        simp only [callPre, List.cons_append, List.nil_append]
        exact h.repin (by pins_of h))
    have acc := acc.trans s1
    simp only [wrRet] at hret
    -- the root after it: `luaL_tolstring`'s saved words, kept by `lua_pushstring`
    have hY : $okN (tlX sp L i lenp nci func top rt.g r f m' o) :=
      ⟨hX.sp_lo, hX.sp_hi, hX.sp_al, hX.ra, hX.L_lo, hX.L_hi, hX.L_al, hX.i_lo, hX.i_hi, hX.l_lo, hX.l_hi,
        hX.ci_lo, hX.ci_hi, hX.f_lo, hX.f_top, hX.t_hi, hX.g_lo, hX.g_hi, hX.L_sp, hX.ci_sp, hX.t_sp, hX.g_sp⟩
    have hk : ∀ a, sp - 48 ≤ a → bytesT1 m' a = bytesT1 M1 a := fun a ha => hpp.keep a (.inl ha)
    have hc6 : bytesT8 m' (sp - 16) = f.s0 := by
      rw [bytesT8_congrT fun j _ => hk _ (by omega), ← hM1e]; fcx_unfold; fat_rd
    have hc7 : bytesT8 m' (sp - 8) = r := by
      rw [bytesT8_congrT fun j _ => hk _ (by omega), ← hM1e]; fcx_unfold; fat_rd
    have hc8 : bytesT8 m' (sp - 24) = f.s1 := by
      rw [bytesT8_congrT fun j _ => hk _ (by omega), ← hM1e]; fcx_unfold; fat_rd
    have hc9 : bytesT8 m' (sp - 32) = f.s2 := by
      rw [bytesT8_congrT fun j _ => hk _ (by omega), ← hM1e]; fcx_unfold; fat_rd
    have h : SegSt 0x80021be8#64 ($r3N (tlX sp L i lenp nci func top rt.g r f m' o))
        (ArmPay (tlX sp L i lenp nci func top rt.g r f m' o).m (tlX sp L i lenp nci func top rt.g r f m' o).o) c1 :=
      hret.repin (by pins_of hret)
    fat_run $ns h acc until [0x80002994]
    fcx_unfold at h
    -- the tail `lua_tolstring(L, -1, &l)`
    obtain ⟨c2, s2, hret2⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (ts := ts) (top := top + 16) (len := $len) f o
      ⟨by omega, hx.ra, by omega, by omega, hx.L_al, by omega, by omega, hx.l_al, by omega, by omega, hx.s_lo,
        hx.s_hi⟩
      ⟨hpp.top_w, by rw [show top + 16 - 8 = top + 8 by omega]; exact hpp.tag_w,
        by rw [show top + 16 - 16 = top by omega]; exact hpp.val_w, hpp.len_w, by decide⟩ _
      (by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
    refine ⟨c2, acc.trans s2, _, hret2, ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩⟩
    · rw [fw8_wm8 (by omega)]; exact hpp.top_w
    · rw [fw1_wm8 (by omega)]; exact hpp.tag_w
    · rw [fw8_wm8 (by omega)]; exact hpp.val_w
    · rw [fw8_same rfl]
    · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
      · simp only [Rng, not_and, Nat.not_lt] at h2
        rw [fw1_wm8 (by omega), hpp.keep a (.inl (by omega)), hM1T a (.inr h1)]
      · rw [fw1_wm8 (by omega), hpp.keep a (.inr ⟨by omega, h2, h3, h4, h5, h6⟩), hM1T a (.inl (by omega))]))

/-- **`luaL_tolstring(L, i, &l)` on a nil argument**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 3`, its
contents returned. -/
theorem tol_nil (hPL : PushLit_Statement) {sp L i lenp nci func top ts : Nat} {seed : UInt32} {rt : RtPtrs}
    {r : BitVec 64} (f : AbiFrame) {m m0 : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top rt.g ts r) (hc : TolCells m L i nci func top rt.g 0 0#8)
    (hlit : bytesAt m 0x8004f2b8 4 = nilB.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])
    (hI : LitInterned m0 rt seed nilB ts) (hag : ∀ a, a < heapEnd → bytesT1 m a = bytesT1 m0 a)
    (hroom : top + 32 ≤ rt.stackLast) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ts + 24) f m' o c ∧ TolLitPost m m' sp L lenp rt.g top ts 3) := by
  tol_lit_run Lua.Vm.AtF.TolNil 0x8004f2b8 nilB 480 3

/-- **`luaL_tolstring(L, i, &l)` on `true`**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 4`, its
contents returned. -/
theorem tol_true (hPL : PushLit_Statement) {sp L i lenp nci func top ts : Nat} {seed : UInt32} {rt : RtPtrs}
    {r : BitVec 64} (f : AbiFrame) {m m0 : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top rt.g ts r) (hc : TolCells m L i nci func top rt.g 1 0x11#8)
    (hlit : bytesAt m 0x8004f2e8 5 = trueB.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])
    (hI : LitInterned m0 rt seed trueB ts) (hag : ∀ a, a < heapEnd → bytesT1 m a = bytesT1 m0 a)
    (hroom : top + 32 ≤ rt.stackLast) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ts + 24) f m' o c ∧ TolLitPost m m' sp L lenp rt.g top ts 4) := by
  tol_lit_run Lua.Vm.AtF.TolTrue 0x8004f2e8 trueB 488 4

/-- **`luaL_tolstring(L, i, &l)` on `false`**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 5`, its
contents returned. -/
theorem tol_false (hPL : PushLit_Statement) {sp L i lenp nci func top ts : Nat} {seed : UInt32} {rt : RtPtrs}
    {r : BitVec 64} (f : AbiFrame) {m m0 : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top rt.g ts r) (hc : TolCells m L i nci func top rt.g 1 0x01#8)
    (hlit : bytesAt m 0x8004f280 6 = falseB.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8])
    (hI : LitInterned m0 rt seed falseB ts) (hag : ∀ a, a < heapEnd → bytesT1 m a = bytesT1 m0 a)
    (hroom : top + 32 ≤ rt.stackLast) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ts + 24) f m' o c ∧ TolLitPost m m' sp L lenp rt.g top ts 5) := by
  tol_lit_run Lua.Vm.AtF.TolFalse 0x8004f280 falseB 488 5

/-! ## The literal classes for `luaB_print` (`TolPost`) -/

/-- **Where a literal argument's objects lie** for `luaB_print`'s state:
the pushed slot, `g`'s string cache and GC words, the interned string, all
kept bytes (in chunks in use, apart from `stdout`'s buffer), and apart from
what the state reads. -/
structure TolLitAt (L nci top g ts len : Nat) (Fa : Nat → Prop) (H : HeapIx) (ph : StdoutPh) : Prop where
  slot : ∀ a, Rng top 16 a → Kept H ph a
  cache : ∀ a, Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a → Kept H ph a
  gw : ∀ a, Rng g 64 a → Kept H ph a
  str : ∀ a, ts ≤ a → a < ts + 24 + len + 1 → Kept H ph a
  sep : ∀ a, ApiFoot L nci a ∨ Fa a → ¬ Rng top 16 a ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧
    ¬ Rng (g + 16) 48 a ∧ ¬ Rng (ts + gcMarkedOff) 1 a
  str_sep : ∀ a, ts + 24 ≤ a → a < ts + 24 + len → ¬ Rng (L + 16) 8 a ∧ ¬ Rng top 16 a ∧
    ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + 16) 48 a
  nci_sep : nci + 8 ≤ L + 16 ∨ L + 24 ≤ nci

/-- A kept byte is below the C stack. -/
theorem Kept.hi' {H : HeapIx} {ph : StdoutPh} {a : Nat} (h : Kept H ph a) : a < heapEnd := h.hi

/-- `omega` with `__heap_end` an atom (its literal unfolded past the
recursion limit otherwise). -/
macro "homega" : tactic => `(tactic| ((try generalize heapEnd = E at *); omega))

/-- **`TolPost` from a literal argument's run** (`tol_nil`, `tol_true`,
`tol_false`): the state with one more value (the literal at the top), `stdout`
as it was, the frame but the length word, the length, the literal's bytes,
where they lie. -/
theorem tolPost_of_lit {sp0 L nci func tbc n : Nat} {A : Mem → Prop} {Fa : Nat → Prop} {ph : StdoutPh}
    {H : HeapIx} {m m' : Mem} {g top ts len : Nat} {b : List (BitVec 8)}
    (hA : ArgPred L A Fa) (hS : PrS L nci func tbc A Fa n ph H m) (hP : PrintSt m ph H)
    (hT : TolLitPost m m' (sp0 - 64) L (sp0 - 56) g top ts len) (hW : TolLitAt L nci top g ts len Fa H ph)
    (htop : top = func + 16 * n + 16) (hlen : b.length = len) (hbytes : bytesAt m (ts + 24) len = b)
    (hsp : heapEnd + 16384 + 64 + 4096 + 64 ≤ sp0) (hsp2 : sp0 ≤ 2 ^ 32) :
    TolPost sp0 n (PrS L nci func tbc A Fa) b ph m m' (ts + 24) H H := by
  have hHE : 0x8006ecd0 ≤ heapEnd := by decide
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hts : ts + 24 + len + 1 ≤ heapEnd := by
    have := (hW.str (ts + 24 + len) (by homega) (by homega)).hi'; homega
  have htsl : heapStart ≤ ts := (hW.str ts (Nat.le_refl _) (by homega)).lo
  -- what the state and `stdout` read is no store of the run
  have hkeepK : ∀ a, (ApiFoot L nci a ∨ Fa a) → ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a := by
    intro a ha hL
    have hk := hS.kept a ha
    have := hk.hi'
    obtain ⟨h1, h2, h3, h4⟩ := hW.sep a ha
    exact hT.keep a (.inr ⟨by homega, hL, h1, h2, h3, h4⟩)
  have hkeepP : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have hlo : a + 16384 + 64 ≤ sp0 - 64 ∨ False := by
      left
      rcases ha with hg | hb | ⟨hr, _⟩ | hr
      · simp only [StdioGlob] at hg; homega
      · have := hP.io.buf_hi a hb; homega
      · simp only [HeapReads] at hr
        have e4 : symMallocAv = 0x8005c6d0 := rfl
        have e5 : symMallocSbrkBase = 0x8005d388 := rfl
        have e6 : symBrk = 0x8005d3b8 := rfl
        have e7 : symMallocTopPad = 0x8005d3d8 := rfl
        have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
        have e9 : symMallocMallinfo = 0x8005e560 := rfl
        homega
      · homega
    rcases hlo with hlo | hlo
    · refine hT.keep a (.inr ⟨hlo, fun hr => ?_, fun hr => ?_, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩)
      · exact (hS.kept a (.inl (.inl hr))).not_printFoot ha
      · exact (hW.slot a hr).not_printFoot ha
      · exact (hW.cache a hr).not_printFoot ha
      · exact (hW.gw a (by simp only [Rng] at hr ⊢; omega)).not_printFoot ha
      · simp only [Rng, gcMarkedOff] at hr
        exact (hW.str a (by homega) (by homega)).not_printFoot ha
    · exact hlo.elim
  have hapi := hS.api
  refine
    { lua := ⟨⟨?_, ?_, ?_, ?_, by have := hapi.tbc_lt; homega⟩, hS.kept, hA.congr m m' hS.args fun a ha =>
        hkeepK a (.inr ha) (hA.apart a ha)⟩
      io := hP.keep hkeepP
      kept := fun c hc _ => hc
      frame := fun a h1 h2 => hT.keep a (.inl ⟨by homega, by simp only [Rng]; homega⟩)
      len := by rw [hT.len_w, hlen]
      bytes := ?_
      src_lo := SrcLo.of_hi (by have : errnoAddr = 0x8005d408 := rfl; have : heapStart = 0x8006ecd0 := rfl; homega)
      src_hi := by homega
      src_ok := fun a h1 h2 => ?_
      src_out := by have : heapStart = 0x8006ecd0 := rfl; have : stdoutFile = 0x8005e668 := rfl
                    have : fileSize = 184 := rfl; homega
      src_buf := fun a h1 h2 => (hW.str a (by homega) (by homega)).nbuf }
  · exact (bytesT8_congrT fun j _ => hkeepK _ (.inl (.inr (.inl ⟨by homega, by homega⟩))) (by
      simp only [Rng]; homega)).trans hapi.ci_w
  · exact (bytesT8_congrT fun j _ => hkeepK _ (.inl (.inr (.inr (.inr ⟨by homega, by homega⟩)))) (by
      intro hr; have := hW.nci_sep; simp only [Rng] at hr; homega)).trans hapi.func_w
  · rw [hT.top_w, htop]; congr 1
  · exact (bytesT8_congrT fun j _ => hkeepK _ (.inl (.inr (.inr (.inl ⟨by homega, by homega⟩)))) (by
      simp only [Rng]; homega)).trans hapi.tbc_w
  · rw [← hbytes, show (bytesAt m (ts + 24) len).length = len by simp [bytesAt]]
    refine bytesAt_congr fun j hj => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hW.str_sep (ts + 24 + j) (by homega) (by homega)
    exact hT.keep _ (.inr ⟨by homega, h1, h2, h3, h4, by simp only [Rng, gcMarkedOff]; homega⟩)
  · have hk := hW.str a (by homega) (by homega)
    exact ⟨fun hg => hk.not_printW (sp := sp0 - 64) (ph' := ph) (by homega) (fun _ h => .inl h) (.inl (.inl hg)),
      fun hm => hk.not_printW (sp := sp0 - 64) (ph' := ph) (by homega) (fun _ h => .inl h) (.inl (.inr (.inl hm))),
      fun hs => hk.not_printW (sp := sp0 - 64) (ph' := ph) (by homega) (fun _ h => .inl h)
        (.inl (.inr (.inr (.inl hs))))⟩

end Lua.Vm.Sim.Kit
