import Lua.Vm.Sim.Kit.PushfI
import Lua.Vm.Sim.Kit.TsbF
import Lua.Vm.Sim.Kit.AtAlign
import Lua.Vm.AtF.PushfF

/-!
# `lua_pushfstring(L, "%f", n)` (lane F1-25)

`luaL_tolstring`'s float case: `luaO_pushvfstring` on `"%f"` (`.rodata`):
`strchr`, `addstr2buff` of the empty prefix; `'f'`: the `TValue` `nv` (tag
`LUA_VNUMFLT`) and `addnum2buff` → `tostringbuff`'s float part (a call node:
`tsb_sum`, a bignum computation over `FloatToStr_Statement`); the empty rest;
`luaS_newlstr` of the bytes in the buffer (`pf_newlstr`, found or created),
the push, `luaC_checkGC` (the tail shared with `"%I"` and `"%s: %p"`,
`pf_tail`). Its at-lemmas are generated (`Lua/Vm/AtF/PushfF.lean`): the entry,
the cut after `strchr` (`C`), the returns from `tostringbuff` (`S`),
`luaS_newlstr` (`T`) and `luaC_step`.

The run is cut in two at `S` (`pushfF_pre`, `pushfF_post`): `_dtoa_r`
changes the heap and the bignums before the string is interned, so
`luaS_newlstr`'s table is read at the memory after the cut (the caller's facts
at that memory: `tolPost_of_split`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The bytes -/

/-- `tostringbuff` of a double, as `UInt8`s (`luaS_newlstr`'s contents). -/
def tsbU8 (x : BitVec 64) : List UInt8 := Lua.Num.tostringbuffBits x

theorem tsbU8_map (x : BitVec 64) : (tsbU8 x).map (fun c => BitVec.ofNat 8 c.toNat) = tsbBytes x := rfl

theorem tsbU8_length (x : BitVec 64) : (tsbU8 x).length = (tsbBytes x).length := by
  rw [← tsbU8_map, List.length_map]

/-! ## `.rodata` -/

/-- **The `.rodata` words `lua_pushfstring(L, "%f", n)` reads**: the format
`"%f"` (its word, bytes, terminator), `luaO_pushvfstring`'s conversion table
entry for `'f'`. -/
structure PffRod (m : Mem) : Prop where
  fmt8 : bytesT8 m 0x8004fd60 = 0x6625#64
  fmt0 : bytesT1 m 0x8004fd60 = 0x25#8
  fmt1 : bytesT1 m 0x8004fd61 = 0x66#8
  fmt2 : bytesT1 m 0x8004fd62 = 0x0#8
  jt : bytesT4 m 0x80052c90 = 0xfffbf34c#32

theorem pffRod_of {m : Mem} (h : RodataRead m) : PffRod m := by
  have e : ∀ a, Image.rodataBase ≤ a → a < Image.rodataBase + Image.rodataSize →
      bytesT1 m a = Image.rodataByte (a - Image.rodataBase) := fun a h1 h2 => by
    have := h (a - Image.rodataBase) (by omega)
    rwa [show Image.rodataBase + (a - Image.rodataBase) = a by omega] at this
  have hb : Image.rodataBase = 0x8004ecc8 := rfl
  have hs : Image.rodataSize = 55776 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0x8004fd60 : Nat) = Image.rodataBase + 0x1098 by decide, At.rod8 h _ (by decide)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [show (0x80052c90 : Nat) = Image.rodataBase + 0x3fc8 by decide, rod4 h _ (by decide)]; decide

/-! ## From the entry to the cut after `strchr` -/

/-- **From the entry to the cut** (`0x80011df8`, after `strchr`): the vararg
registers at whatever they hold. -/
theorem pff_cut (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hP : PfIn m sp L g top r) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd60#64⟩,
        ⟨Register.x12, x⟩] sp r f) (ArmPay m o))
      (fun c => ∃ a3 a4 a5 a6 a7, SegSt 0x80011df8#64
        (Lua.Vm.AtF.PushfF.r3 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp)
          (pfM1 sp L g top r f x a3 a4 a5 a6 a7 m o) o))
        (ArmPay (pfM1 sp L g top r f x a3 a4 a5 a6 a7 m o) o) c) := by
  intro c h
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  fat_pin h a3 13 Register.x13
  fat_pin h a4 14 Register.x14
  fat_pin h a5 15 Register.x15
  fat_pin h a6 16 Register.x16
  fat_pin h a7 17 Register.x17
  simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800030a4#64 (Lua.Vm.AtF.PushfF.r0 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 0#64 m o))
      (ArmPay (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 0#64 m o).m
        (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 0#64 m o).o) c := by
    fcx_unfold; exact h.repin (by pins_of h)
  have hX : Lua.Vm.AtF.PushfF.Ok (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 0#64 m o) := by fcx_ok
  have R := pffRod_of hP.rod
  have hc0 : bytesT8 m 0x8004fd60 = 0x6625#64 := R.fmt8
  have hc1 : bytesT1 m 0x8004fd60 = 0x25#8 := R.fmt0
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfF h acc until [0x80011df8]
  exact ⟨_, acc, a3, a4, a5, a6, a7, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-! ## The `'f'` conversion to `tostringbuff`'s return -/

/-- `addnum2buff`'s frame at `tostringbuff`'s call. -/
abbrev pffTsFr (sp L : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 (sp - 424), 0x80052c1c#64, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440),
    BitVec.ofNat 64 (sp - 408), 0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x8004fd60#64, 0x8004fd60#64, f.s11⟩

/-- **The memory after `tostringbuff`** (`S`'s root memory), against the
memory at the cut: the slots, the buffer's length still `0`, `addnum2buff`'s
return address and buffer, `tostringbuff`'s bytes at `sp - 408`. -/
structure PffS (M : Mem) (sp L : Nat) (r x : BitVec 64) (f : AbiFrame) : Prop where
  slots : PfSlots M sp L r f
  blen : bytesT4 M (sp - 412) = 0x0#32
  ra3 : bytesT8 M (sp - 472) = 0x80011f88#64
  bufp : bytesT8 M (sp - 480) = BitVec.ofNat 64 (sp - 40)
  bytes : bytesAt M (sp - 408) (tsbBytes x).length = tsbBytes x
  len_lo : 1 ≤ (tsbBytes x).length
  len_hi : (tsbBytes x).length ≤ 23

/-- **What `tostringbuff`'s bignum computation needs at `lua_pushfstring`'s
entry**: `snprintf`'s static words, the heap and `_dtoa_r`'s bignums, room for
their allocations. -/
structure PffIn (m : Mem) (H : HeapIx) (B : Nat → Prop) : Prop where
  stat : FmtStatic m
  heap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins
  room : H.brk + dtoaRoom ≤ heapEnd
  big : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m
  big_in : ∀ a, B a → InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd

/-- `lua_pushfstring`'s callees' frames: `[sp - 16384, sp)`. -/
def PffFr (sp a : Nat) : Prop := sp ≤ a + 16384 ∧ a < sp

/-- **From the cut to `tostringbuff`'s return** (`S`, `0x800115c0`): the
empty prefix, the `'f'` conversion, `addnum2buff` → `tostringbuff` (`tsb_sum`). -/
theorem pff_tsb (hF : FloatToStr_Statement) (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame)
    (a3 a4 a5 a6 a7 : BitVec 64) (m M1 : Mem) (o : Array String) (H : HeapIx) (B : Nat → Prop)
    (hP : PfIn m sp L g top r) (hI : PffIn m H B) (hC : PfC M1 m sp L r x f) :
    Triple (SegSt 0x80011df8#64 (Lua.Vm.AtF.PushfF.r3 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o))
        (ArmPay M1 o))
      (fun c => ∃ M H' B', PffS M sp L r x f ∧ BigRun (PffFr sp) m M H H' B B' dtoaRoom ∧
        SegSt 0x800115c0#64
          (Lua.Vm.AtF.PushfF.r6 (pfX [sp, L, g, top, (tsbBytes x).length] r f x a3 a4 a5 a6 a7 (pfS8 sp) M o))
          (ArmPay M o) c) := by
  intro c h
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hHE : heapEnd = 0x87800000 := rfl
  have R := pffRod_of hP.rod
  have k1 := hC.low
  have hX : Lua.Vm.AtF.PushfF.Ok_C (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o) := by fcx_ok
  have hc2 : bytesT4 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m
      ((pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 412) = 0x0#32 := hC.blen
  have hc3 : bytesT1 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m 0x8004fd61 = 0x66#8 :=
    (k1 _ (.inl (by omega))).trans R.fmt1
  have hc4 : bytesT4 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m 0x80052c90 = 0xfffbf34c#32 :=
    (bytesT4_congrT fun j _ => k1 _ (.inl (by omega))).trans R.jt
  have hc5 : bytesT8 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m
      ((pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 48) =
      (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).b 13 := hC.argi
  -- `memcpy` of the empty prefix: the pointers aligned alike
  have hg_4 : ((((0x8004fd60#64) ^^^ (BitVec.ofNat 64
      ((pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = false :=
    xor_al _ _ (by decide) (by simp only [pfX, FCx.mk', List.getD_cons_zero]; omega)
  have hg_2 : zopz0zKzJ_u (BitVec.ofNat 64 ((pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408))
      (BitVec.ofNat 64 ((pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408)) = true := uge_self _
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfF h acc until [0x8003b648]
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.PushfF.at_8003b648_8003b658_n_1 _ hX hg_4)
  fat_run Lua.Vm.AtF.PushfF h acc until [0x8001142c]
  generalize hM6 : Lua.Vm.AtF.PushfF.m6 (pfX [sp, L, g, top] r f x a3 a4 a5 a6 a7 (pfS8 sp) M1 o) = M6 at h
  have k6 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) →
      bytesT1 M6 a = bytesT1 M1 a := by
    intro a ha
    rw [← hM6]
    simp only [Lua.Vm.AtF.PushfF.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins]
  have low6 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M6 a = bytesT1 m a := fun a ha =>
    (k6 a (by omega)).trans (k1 a (by omega))
  -- the stack stores before the call are a frame-only bignum step
  have hBh : ∀ a, B a → a < heapEnd := fun a ha => (hI.big_in a ha).2.2
  have hF6 : ∀ a, ¬ PffFr sp a → bytesT1 M6 a = bytesT1 m a := fun a ha =>
    low6 a (by simp only [PffFr, not_and, Nat.not_lt] at ha; omega)
  have hFF : ∀ a, PffFr sp a → heapEnd + 32 ≤ a := fun a ha => by simp only [PffFr] at ha; omega
  have hR6 := BigRun.ofFrame hI.heap hI.big hBh hFF hF6
  have hIn : TsbIn M6 (sp - 496) (sp - 408) 0x800115c0#64 H B := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, b_lo := by omega
    b_hi := by omega
    stat := hI.stat.congr fun a ha => low6 a (.inl (by omega))
    rod := hP.rod.congr_rod fun a h1 h2 => low6 a (.inl (by
      have : Image.rodataBase + Image.rodataSize = 0x8005c6a8 := rfl; omega))
    heap := hR6.heap
    room := hI.room
    big := hR6.big
    big_in := hI.big_in }
  fcx_unfold at h
  obtain ⟨c2, s2, M2, H', B', hret, hpost⟩ := tsb_sum hF (sp - 496) (sp - 408) x 0x800115c0#64 (pffTsFr sp L f)
    M6 o H B hIn _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s2
  -- `M2` off what `tostringbuff` wrote: its frames below `sp - 496`, the buffer
  have kT : ∀ a, sp - 496 ≤ a → (a < sp - 408 ∨ sp - 408 + 44 ≤ a) → bytesT1 M2 a = bytesT1 M6 a :=
    fun a h1 h2 => hpost.big.keep a fun hw => by
      rcases hw with hw | hw | hw | hw
      · rcases hw with hg | ⟨-, hh, -⟩
        · have := hg.lt; omega
        · omega
      · have := hBh a hw; omega
      · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hw; omega
      · simp only [TsbFr, Below, Rng] at hw; omega
  have P : PffS M2 sp L r x f := {
    slots := hC.slots.congr (by omega) fun a ha => (kT a (by omega) (by omega)).trans (k6 a (by omega))
    blen := (bytesT4_congrT fun j _ => kT _ (by omega) (by omega)).trans (by
      rw [← hM6]; simp only [Lua.Vm.AtF.PushfF.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [fw4_wm8, fw4_same, fw4_ins]; decide)
    ra3 := (bytesT8_congrT fun j _ => kT _ (by omega) (by omega)).trans (by
      rw [← hM6]; simp only [Lua.Vm.AtF.PushfF.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4, fw8_ins])
    bufp := (bytesT8_congrT fun j _ => kT _ (by omega) (by omega)).trans (by
      rw [← hM6]; simp only [Lua.Vm.AtF.PushfF.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4, fw8_ins])
    bytes := hpost.bytes
    len_lo := hpost.len_lo
    len_hi := hpost.len_hi }
  have hR : BigRun (PffFr sp) m M2 H H' B B' dtoaRoom := by
    have := hR6.trans (hpost.big.mono (F' := PffFr sp) (fun a ha => by
      simp only [TsbFr, Below, Rng, PffFr] at ha ⊢; omega) (Nat.le_refl _))
    rwa [Nat.zero_add] at this
  simp only [wrRet] at hret
  exact ⟨c2, acc, M2, H', B', P, hR, by fcx_unfold; exact hret.repin (by pins_of hret)⟩

/-! ## From `tostringbuff`'s return to `lua_pushfstring`'s -/

/-- `S`'s context. -/
@[at_row] abbrev pffX2 (sp L g top n : Nat) (r : BitVec 64) (f : AbiFrame) (x a3 a4 a5 a6 a7 : BitVec 64) (M : Mem)
    (o : Array String) : FCx :=
  pfX [sp, L, g, top, n] r f x a3 a4 a5 a6 a7 (pfS8 sp) M o

/-- **From `tostringbuff`'s return to `luaS_newlstr`'s call**: `addsize`, the
second `strchr` (none), `addstr2buff` of the empty suffix (`memcpy` of no
bytes, its alignment test either way), `clearbuff`. -/
theorem pff_nl_reach (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame) (a3 a4 a5 a6 a7 : BitVec 64)
    (M2 : Mem) (o : Array String) (hP : PfIn M2 sp L g top r) (hS : PffS M2 sp L r x f) (n : Nat)
    (hn : (tsbBytes x).length = n) (c : Config)
    (h : SegSt 0x800115c0#64 (Lua.Vm.AtF.PushfF.r6 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o))
      (ArmPay (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80017694#64 (Lua.Vm.AtF.PushfF.r8 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o))
      (ArmPay (Lua.Vm.AtF.PushfF.m10 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o)) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have R := pffRod_of hP.rod
  have hn1 := hS.len_lo
  have hn2 := hS.len_hi
  rw [hn] at hn1 hn2
  have hX : Lua.Vm.AtF.PushfF.Ok_S (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o) := by fcx_ok
  have hc2 : bytesT4 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m
      ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 - 412) = 0x0#32 := hS.blen
  have hc6 : bytesT8 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m
      ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 - 472) = 0x80011f88#64 := hS.ra3
  have hc7 : bytesT8 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m
      ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 - 480) =
      BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 - 40) := hS.bufp
  have hc8 : bytesT1 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m 0x8004fd62 = 0x0#8 := R.fmt2
  have hc9 : bytesT8 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m
      ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 - 424) =
      BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 1) := hS.slots.buffL
  have hc10 : bytesT8 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m
      ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 1 + 16) =
      BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 3) := hP.top_w
  have hg_4 : zopz0zI_s ((BitVec.ofNat 64 (199) - BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 4)))
      (0x0#64) = false := by
    simp only [pffX2, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [ofNat_sub_le (by omega) (by omega)]
    fmt_scmp
  have hg_2 : zopz0zKzJ_u (BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 +
      (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 4 - 408))
      (BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 +
      (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 4 - 408)) = true := uge_self _
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfF h acc until [0x8003b648]
  cases hb : ((((0x8004fd62#64) ^^^ (BitVec.ofNat 64 ((pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 0 +
      (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).n 4 - 408))) &&& sign_extend (m := 64) (0x007#12)) != (0#64))
  · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfF.at_8003b648_8003b658_n _ hX hb)
    fat_run Lua.Vm.AtF.PushfF h acc until [0x80017694]
    exact ⟨_, acc, h⟩
  · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfF.at_8003b648_8003b658_t _ hX hb)
    fat_run Lua.Vm.AtF.PushfF h acc until [0x80017694]
    exact ⟨_, acc, h⟩

/-- `pushstr`'s frame at `luaS_newlstr`'s call (`"%f"`'s empty rest). -/
abbrev pffNlFr (sp L top : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 top, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440), BitVec.ofNat 64 (sp - 408),
    0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x0#64, 0x8004fd62#64, f.s11⟩

/-- **From `tostringbuff`'s return to `luaS_newlstr`'s** (`T`, `0x80011ec0`):
the string found or created (`PfStr`, against the memory `M2` after the cut),
`T`'s facts (`PfT`). -/
theorem pff_nl (hM : MallocR_Statement) (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame)
    (a3 a4 a5 a6 a7 : BitVec 64) (M2 : Mem) (o : Array String) (hP : PfIn M2 sp L g top r)
    (hS : PffS M2 sp L r x f) (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat)
    (H : HeapIx) (hT : NlTab M2 L g top (tsbU8 x) seed K X W cw size hash head d nuse H) (n : Nat)
    (hn : (tsbBytes x).length = n) :
    Triple (SegSt 0x800115c0#64 (Lua.Vm.AtF.PushfF.r6 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o))
        (ArmPay (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).m (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o).o))
      (fun c => ∃ ts M3 H', PfT M3 sp L g top ts r f ∧
        PfStr M2 M3 (PfFr sp) g (tsbU8 x) seed K X W size hash nuse head H ts H' ∧
        SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfF.r9 (pfX [sp, L, g, top, n, ts] r f x a3 a4 a5 a6 a7 (pfS8 sp) M3 o))
          (ArmPay M3 o) c) := by
  intro c h
  pf_in hP
  have hn1 := hS.len_lo
  have hn2 := hS.len_hi
  obtain ⟨c1, s1, h⟩ := pff_nl_reach sp L g top x r f a3 a4 a5 a6 a7 M2 o hP hS n hn c h
  generalize hM10 : Lua.Vm.AtF.PushfF.m10 (pffX2 sp L g top n r f x a3 a4 a5 a6 a7 M2 o) = M10 at h
  have k10 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) → bytesT1 M10 a = bytesT1 M2 a := by
    intro a ha
    rw [← hM10]
    simp only [Lua.Vm.AtF.PushfF.m10, pffX2, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4]
  have low10 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M10 a = bytesT1 M2 a := fun a ha => k10 a (by omega)
  have hl : (tsbU8 x).length = n := by rw [tsbU8_length, hn]
  fcx_unfold at h
  obtain ⟨c2, s2, ts, M3, H', hPT, hstr, hret⟩ := pf_newlstr hM sp L g top r f (pffNlFr sp L top f) M2 M10 o hP
    (hS.slots.congr (by omega) fun a ha => k10 a (by omega)) low10 (tsbU8 x) (by omega) (by omega)
    (fun j hj => by
      rw [k10 _ (by omega), bytesAt_get hS.bytes (by rw [← tsbU8_length]; exact hj), ← tsbU8_map]
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj])
    seed K X W cw size hash head d nuse H hT _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
      rw [hl]
      exact h.repin (by pins_of h))
  simp only [wrRet] at hret
  exact ⟨c2, s1.trans s2, ts, M3, H', hPT, hstr, by fcx_unfold; exact hret.repin (by pins_of hret)⟩

/-- **From `luaS_newlstr`'s return to `lua_pushfstring`'s** (`"%f"`):
`pf_tail` on this module's rows. -/
theorem pff_ret (sp L g top n ts : Nat) (i r : BitVec 64) (f : AbiFrame) (a3 a4 a5 a6 a7 : BitVec 64)
    (m M3 : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hT : PfT M3 sp L g top ts r f)
    (hgc : bytesT1 M3 (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfF.r9 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o))
        (ArmPay M3 o))
      (fun c => ∃ M, PfPost M3 M sp L g top ts ∧ wrRet r sp (ts + 24) f M o c) := by
  pf_tail Lua.Vm.AtF.PushfF r9 r14 m11 m12

/-! ## The two halves -/

/-- **`lua_pushfstring(L, "%f", n)` to `tostringbuff`'s return** (lane
F1-25): a bignum computation (`BigRun`, off `lua_pushfstring`'s callees'
frames `PffFr`) that leaves `tostringbuff`'s bytes in the buffer (`PffS`). -/
theorem pushfF_pre (hF : FloatToStr_Statement) (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (H : HeapIx) (B : Nat → Prop) (hP : PfIn m sp L g top r) (hI : PffIn m H B) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd60#64⟩,
        ⟨Register.x12, x⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M H' B' a3 a4 a5 a6 a7, PffS M sp L r x f ∧ BigRun (PffFr sp) m M H H' B B' dtoaRoom ∧
        SegSt 0x800115c0#64
          (Lua.Vm.AtF.PushfF.r6 (pffX2 sp L g top (tsbBytes x).length r f x a3 a4 a5 a6 a7 M o)) (ArmPay M o) c) := by
  intro c h
  pf_in hP
  obtain ⟨c1, s1, a3, a4, a5, a6, a7, h1⟩ := pff_cut sp L g top x r f m o hP c h
  obtain ⟨c2, s2, M, H', B', hS, hR, h2⟩ := pff_tsb hF sp L g top x r f a3 a4 a5 a6 a7 m _ o H B hP hI
    (pfC_of (by omega)) c1 h1
  exact ⟨c2, s1.trans s2, M, H', B', a3, a4, a5, a6, a7, hS, hR, h2⟩

/-- **From `tostringbuff`'s return to `lua_pushfstring`'s** (lane F1-25):
the bytes interned (found or created, `PfStr`, against the memory `M2` after
the cut) and pushed at `L->top` (`PfPost`), `getstr` of the string returned. -/
theorem pushfF_post (hM : MallocR_Statement) (sp L g top : Nat) (x r : BitVec 64) (f : AbiFrame)
    (a3 a4 a5 a6 a7 : BitVec 64) (M2 : Mem) (o : Array String) (hP : PfIn M2 sp L g top r)
    (hS : PffS M2 sp L r x f) (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat)
    (H : HeapIx) (hT : NlTab M2 L g top (tsbU8 x) seed K X W cw size hash head d nuse H)
    (hgc : bytesT1 M2 (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x800115c0#64
        (Lua.Vm.AtF.PushfF.r6 (pffX2 sp L g top (tsbBytes x).length r f x a3 a4 a5 a6 a7 M2 o)) (ArmPay M2 o))
      (fun c => ∃ ts M3 M H', PfStr M2 M3 (PfFr sp) g (tsbU8 x) seed K X W size hash nuse head H ts H' ∧
        PfPost M3 M sp L g top ts ∧ PfTs M ts (tsbU8 x).length ∧ wrRet r sp (ts + 24) f M o c) := by
  intro c h
  pf_in hP
  have hn1 := hS.len_lo
  have hn2 := hS.len_hi
  obtain ⟨c3, s3, ts, M3, H', hPT, hstr, h3⟩ :=
    pff_nl hM sp L g top x r f a3 a4 a5 a6 a7 M2 o hP hS seed K X W cw size hash head d nuse H hT _ rfl c h
  have hgc3 : bytesT1 M3 (g + gGcstpOff) = 0x1#8 :=
    (hstr.gw (a := g + gGcstpOff) (F := PfFr sp) hT (by omega) (fun a ha => by simp only [PfFr] at ha; omega)
      (by simp only [gGcstpOff]; omega) (by simp only [gGcstpOff]; omega)
      (by simp only [Rng, gGcstpOff]; omega)).trans hgc
  obtain ⟨c4, s4, M, hpost, hret⟩ := pff_ret sp L g top _ ts x r f a3 a4 a5 a6 a7 M2 M3 o hP hPT hgc3 hgal c3 h3
  exact ⟨c4, s3.trans s4, ts, M3, M, H', hstr, hpost,
    pfTs_of hT (by rw [tsbU8_length]; omega) (by omega) (by omega) (by omega) (by omega) hPT hstr hpost, hret⟩

end Lua.Vm.Sim.Kit
