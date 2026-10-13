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

/-! ## `lua_pushstring` of a C literal: the named premise -/

/-- **What `lua_pushstring` of a C literal leaves** (lane F1-15): the string
at the top (`L->top` one slot up, `LUA_VSHRSTR`, `ts`), its length, the
string cache's candidates again (`LitCache`), and every byte kept off
`L->top`, the new slot, `g`'s string cache, `totalbytes` and `GCdebt`
(`luaE_setdebt`, when `luaC_step` runs with the collector stopped), the
string's mark byte (`changewhite`) and the callee frames below `sp`. -/
structure PushPost (m m' : Mem) (sp L g top ts len : Nat) (ls : LitPtrs) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (top + 16)
  tag_w : bytesT1 m' (top + 8) = 0x44#8
  val_w : bytesT8 m' top = BitVec.ofNat 64 ts
  len_w : bytesT1 m' (ts + 11) = BitVec.ofNat 8 len
  cache : LitCache m' g ls
  keep : ∀ a, sp ≤ a ∨ (a + 16384 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng top 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + gTotalbytesOff) 8 a ∧
      ¬ Rng (g + gGCdebtOff) 8 a ∧ ¬ Rng (ts + gcMarkedOff) 1 a) →
    bytesT1 m' a = bytesT1 m a

/-- **Where `lua_pushstring`'s objects lie** (lane F1-15): its `sp` and `ra`
(room below for its callees' frames), the `lua_State`, `g` up to its string
cache and the slot at `L->top`, in the arena and apart. -/
structure PushCx (sp L top g : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_al : sp % 16 = 0
  sp_hi : sp ≤ 2 ^ 32
  sp_lo : heapEnd + 16384 + 1024 ≤ sp
  L_lo : symTohost + 16 ≤ L
  L_hi : L + stateSize ≤ heapEnd
  L_al : L % 8 = 0
  g_lo : symTohost + 16 ≤ g
  g_hi : g + gEnd ≤ heapEnd
  g_al : g % 8 = 0
  t_lo : symTohost + 16 ≤ top
  t_hi : top + 32 ≤ heapEnd
  t_al : top % 8 = 0
  tL : Apart top 16 L stateSize
  tg : Apart top 16 g gEnd
  Lg : Apart L stateSize g gEnd

/-- (lane F1-15) **A literal's string apart** from what `lua_pushstring`
writes: the `lua_State`, `g` up to its string cache, the slot at `L->top`. -/
structure LitApart (ts L g top : Nat) : Prop where
  L : Apart ts 30 L stateSize
  g : Apart ts 30 g gEnd
  top : Apart ts 30 top 16

/-- **Named premise: `lua_pushstring(L, s)` of a C literal** (`0x80002fe4`;
lane F1-15 restated): `s` the `.rodata` address of one of `luaL_tolstring`'s
literals `l` (`LitPtrs.table`), the literals interned (`LitsIn`: the walk of
`internshrstr` meets `l.ts` first; frozen on a footprint `FL` below the heap's
end and off the string cache, which `luaS_new` writes before `internshrstr`
reads the table), the string cache's words candidates of
their rows (`LitCache`: no other entry of `l`'s row is `strcmp`-equal), the
collector stopped (`gcstp`): `luaS_new` returns `l.ts` (a cache hit, or
`internshrstr`'s bucket walk: no allocation) and the row holds candidates
again, the string is pushed, and `luaC_checkGC` at most resets the debt.
Returns `getstr(ts)`. Lane F1-12's form (over `LitInterned` with a cache of
strings) was false: a cache entry of equal contents but another pointer, an
earlier chain node of equal contents, or a running collector (`gcstp = 0`)
all break its post. Open: the at-lemmas of `lua_pushstring`, `luaS_new`
(`__umoddi3`, `strcmp`, `strlen`), `internshrstr` (the hash loop, the bucket
walk with `memcmp`) and `luaC_step`'s stopped path. -/
def PushLit_Statement : Prop :=
  ∀ (sp L top g sl : Nat) (l : CLit) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String),
    l ∈ ls.table → PushCx sp L top g r → LitApart l.ts L g top →
    bytesT8 m (L + 16) = BitVec.ofNat 64 top → bytesT8 m (L + 24) = BitVec.ofNat 64 g →
    top + 16 + 16 ≤ sl → RodataRead m →
    Frozen FL (fun M => LitsHold M g sl ls) m →
    (∀ a, FL a → a < heapEnd ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a) → LitCache m g ls →
    bytesT1 m (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr →
    Triple (SegSt 0x80002fe4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 l.addr⟩]
        sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (l.ts + 24) f m' o c ∧ PushPost m m' sp L g top l.ts l.bytes.length ls)

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
string at the top (`L->top` one slot up), `l` its length, the cache's
candidates again, every byte kept off `L->top`, the new slot, `g`'s string
cache, `totalbytes` and `GCdebt`, the string's mark, `&l` and the callee frames
below `sp`. -/
structure TolLitPost (m m' : Mem) (sp L lenp g top ts len : Nat) (ls : LitPtrs) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (top + 16)
  tag_w : bytesT1 m' (top + 8) = 0x44#8
  val_w : bytesT8 m' top = BitVec.ofNat 64 ts
  len_w : bytesT8 m' lenp = BitVec.ofNat 64 len
  cache : LitCache m' g ls
  keep : ∀ a, (sp ≤ a ∧ ¬ Rng lenp 8 a) ∨ (a + 16384 + 64 ≤ sp ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng top 16 a ∧
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∧ ¬ Rng (g + gTotalbytesOff) 8 a ∧
      ¬ Rng (g + gGCdebtOff) 8 a ∧ ¬ Rng (ts + gcMarkedOff) 1 a) →
    bytesT1 m' a = bytesT1 m a

/-- **What `luaL_tolstring` needs of the literals** (lane F1-15): the
literals interned, frozen on `FL` (below `__heap_end`), the cache's
candidates, the collector stopped, `.rodata`, and where `lua_pushstring`'s
objects lie (`PushCx` at `luaL_tolstring`'s callee frame). -/
structure TolLitIn (m : Mem) (sp L top g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) : Prop where
  lits : Frozen FL (fun M => LitsHold M g sl ls) m
  foot : ∀ a, FL a → a < heapEnd
  cache : LitCache m g ls
  gcstp : bytesT1 m (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr
  ro : RodataRead m
  cx : PushCx (sp - 48) L top g 0x80021be8#64
  room : top + 32 ≤ sl
  /-- (lane F1-15) the footprint off the string cache -/
  apart : ∀ a, FL a → ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a
  /-- (lane F1-15) the literals' strings apart from the push's stores -/
  lit_ap : ∀ ts ∈ ls.strs, LitApart ts L g top

set_option hygiene false in
/-- **`luaL_tolstring` on a literal argument's proof** over the at-lemmas of
`ns` (`TolNil`, `TolTrue`, `TolFalse`: one module per literal tag, the
generator's cells being literals): the run to `lua_pushstring`, its summary
(`PushLit_Statement`, the literals of the memory there from `TolLitIn`), the
run to the tail `lua_tolstring`, `toltop_sum`. -/
macro "tol_lit_run " ns:ident addr:term:max b:ident tsf:term:max mto:num len:num : tactic => do
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
    have hX : $okN (tlX sp L i lenp nci func top g r f m o) := by fcx_ok
    have hc0 := hc.ci_w; have hc1 := hc.func_w; have hc2 := hc.top_w; have hc3 := hc.tag_w; have hc4 := hc.g_w
    have hc5 : bytesT8 m (g + $mto) = 0#64 := hc.mt_w
    have hf0 : 16 * i + func < top := by omega
    have hf1 := hx.nil_ne
    have hg_6 := absindex_pos i hx.i_lo hx.i_hi
    have hg_2 := sge0_pos i hx.i_lo (by omega)
    simp only [callPre, List.cons_append, List.nil_append] at h
    have h : SegSt 0x80021b2c#64 ($r0N (tlX sp L i lenp nci func top g r f m o))
        (ArmPay (tlX sp L i lenp nci func top g r f m o).m (tlX sp L i lenp nci func top g r f m o).o) c :=
      h.repin (by pins_of h)
    have acc := Steps.refl c
    fat_run $ns h acc until [0x80002fe4]
    -- `lua_pushstring(L, lit)`
    have hM1 : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) →
        ($m1N (tlX sp L i lenp nci func top g r f m o))[a]? = m[a]? := by
      intro a ha; fcx_unfold; simp (disch := omega) only [getElem?_writeMap8_out]
    generalize hM1e : $m1N (tlX sp L i lenp nci func top g r f m o) = M1 at h hM1
    fcx_unfold at h
    have hM1T : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) → bytesT1 M1 a = bytesT1 m a := fun a ha => bT1_congr (hM1 a ha)
    have hpc := hT.cx
    have hHE : heapEnd = 0x87800000 := rfl
    have hgE : gEnd = 1400 := rfl
    have hgh := hpc.g_hi
    have hLI := hT.lits.trans fun a ha => hM1T a (.inl (by have := hT.foot a ha; omega))
    have hcall := hPL (sp - 48) L top g sl ⟨$addr, $b, $tsf⟩ ls FL 0x80021be8#64
      (tlFr L i lenp f) M1 o (by simp [LitPtrs.table]) hpc (hT.lit_ap _ (by simp [LitPtrs.strs]))
      ((bytesT8_congrT fun j _ => hM1T _ (by omega)).trans hc2)
      ((bytesT8_congrT fun j _ => hM1T _ (by omega)).trans hc4) (by have := hT.room; omega)
      (fun o' ho => (hM1T _ (.inl (by
        have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl; omega))).trans
        (hT.ro o' ho))
      hLI (fun a ha => ⟨hT.foot a ha, hT.apart a ha⟩) (hT.cache.congr fun a h1 h2 => hM1T a (.inl (by omega)))
      ((hM1T _ (.inl (by simp only [gGcstpOff]; omega))).trans hT.gcstp)
    simp only [callPre, List.cons_append, List.nil_append] at hcall
    obtain ⟨c1, s1, m', hret, hpp⟩ := hcall _ (h.repin (by pins_of h))
    have acc := acc.trans s1
    simp only [wrRet] at hret
    -- the root after it: `luaL_tolstring`'s saved words, kept by `lua_pushstring`
    have hY : $okN (tlX sp L i lenp nci func top g r f m' o) :=
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
    have h : SegSt 0x80021be8#64 ($r3N (tlX sp L i lenp nci func top g r f m' o))
        (ArmPay (tlX sp L i lenp nci func top g r f m' o).m (tlX sp L i lenp nci func top g r f m' o).o) c1 :=
      hret.repin (by pins_of hret)
    fat_run $ns h acc until [0x80002994]
    fcx_unfold at h
    -- the tail `lua_tolstring(L, -1, &l)`
    obtain ⟨c2, s2, hret2⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (ts := $tsf) (top := top + 16)
      (len := $len) f o
      ⟨by omega, hx.ra, by omega, by omega, hx.L_al, by omega, by omega, hx.l_al, by omega, by omega, hx.s_lo,
        hx.s_hi⟩
      ⟨hpp.top_w, by rw [show top + 16 - 8 = top + 8 by omega]; exact hpp.tag_w,
        by rw [show top + 16 - 16 = top by omega]; exact hpp.val_w, hpp.len_w, by decide⟩ _
      (by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
    refine ⟨c2, acc.trans s2, _, hret2, ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩⟩
    · rw [fw8_wm8 (by omega)]; exact hpp.top_w
    · rw [fw1_wm8 (by omega)]; exact hpp.tag_w
    · rw [fw8_wm8 (by omega)]; exact hpp.val_w
    · rw [fw8_same rfl]
    · exact hpp.cache.congr fun a h1 h2 => fw1_wm8 (by omega)
    · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩
      · simp only [Rng, not_and, Nat.not_lt] at h2
        rw [fw1_wm8 (by omega), hpp.keep a (.inl (by omega)), hM1T a (.inr h1)]
      · rw [fw1_wm8 (by omega), hpp.keep a (.inr ⟨by omega, h2, h3, h4, h5, h6, h7⟩), hM1T a (.inl (by omega))]))

/-- **`luaL_tolstring(L, i, &l)` on a nil argument**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 3`, its
contents returned. -/
theorem tol_nil (hPL : PushLit_Statement) {sp L i lenp nci func top g sl : Nat} {ls : LitPtrs}
    {FL : Nat → Prop} {r : BitVec 64} (f : AbiFrame) {m : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top g ls.nil r) (hc : TolCells m L i nci func top g 0 0#8)
    (hT : TolLitIn m sp L top g sl ls FL) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ls.nil + 24) f m' o c ∧ TolLitPost m m' sp L lenp g top ls.nil 3 ls) := by
  tol_lit_run Lua.Vm.AtF.TolNil litNilAddr nilB ls.nil 480 3

/-- **`luaL_tolstring(L, i, &l)` on `true`**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 4`, its
contents returned. -/
theorem tol_true (hPL : PushLit_Statement) {sp L i lenp nci func top g sl : Nat} {ls : LitPtrs}
    {FL : Nat → Prop} {r : BitVec 64} (f : AbiFrame) {m : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top g ls.tru r) (hc : TolCells m L i nci func top g 1 0x11#8)
    (hT : TolLitIn m sp L top g sl ls FL) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ls.tru + 24) f m' o c ∧ TolLitPost m m' sp L lenp g top ls.tru 4 ls) := by
  tol_lit_run Lua.Vm.AtF.TolTrue litTrueAddr trueB ls.tru 488 4

/-- **`luaL_tolstring(L, i, &l)` on `false`**, from `lua_pushstring`'s
summary (`PushLit_Statement`): the interned literal at the top, `l = 5`, its
contents returned. -/
theorem tol_false (hPL : PushLit_Statement) {sp L i lenp nci func top g sl : Nat} {ls : LitPtrs}
    {FL : Nat → Prop} {r : BitVec 64} (f : AbiFrame) {m : Mem} (o : Array String)
    (hx : TolNums sp L i lenp nci func top g ls.fls r) (hc : TolCells m L i nci func top g 1 0x01#8)
    (hT : TolLitIn m sp L top g sl ls FL) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp (ls.fls + 24) f m' o c ∧ TolLitPost m m' sp L lenp g top ls.fls 5 ls) := by
  tol_lit_run Lua.Vm.AtF.TolFalse litFalseAddr falseB ls.fls 488 5

end Lua.Vm.Sim.Kit
