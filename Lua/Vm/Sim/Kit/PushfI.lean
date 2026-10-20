import Lua.Vm.Sim.Kit.Newlstr
import Lua.Vm.Sim.Kit.PushLit
import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.DecDigits
import Lua.Vm.Sim.Kit.FltValLt
import Lua.Vm.AtF.PushfI

/-!
# `lua_pushfstring(L, "%I", i)` (lane F1-20)

`luaO_pushvfstring` on `"%I"`: `strchr`, `addstr2buff` of the empty prefix,
`addnum2buff` → `tostringbuff` → `snprintf(buf, 44, "%lld", i)` (a call node:
`IntegerToStr_Statement`), `clearbuff` → `pushstr` → `luaS_newlstr` of the
digits in the buffer (a call node: `newlstr_any_sum`), the push at `L->top`;
then `luaC_checkGC` (`luaC_step` with the collector stopped, `luaC_step_sum`,
when the debt is positive). Its at-lemmas are generated
(`Lua/Vm/AtF/PushfI.lean`): the entry, the cut after `strchr` (`C`), the
returns from `snprintf` (`S`), `luaS_newlstr` (`T`) and `luaC_step`. A root's
context is re-bound at each, its stack words read through what the callee
kept (`PfSlots`, one transport per callee).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- `lua_pushfstring`'s contexts: `sp` (the entry's), `L`, `g`, `L->top`, the
digits' count, the string; `ra`, the caller's `s0`–`s11`, `i`, the vararg
registers `a3`–`a7`, `s8` at the cut. -/
@[at_row] abbrev pfX (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (i a3 a4 a5 a6 a7 s8 : BitVec 64) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, i, a3, a4, a5, a6,
    a7, 0#64, s8] m o

/-- A 4-byte `.rodata` read. -/
theorem rod4 {m : Mem} (h : RodataRead m) (o : Nat) (ho : o + 4 ≤ Image.rodataSize) :
    bytesT4 m (Image.rodataBase + o) =
      (((Image.rodataByte (o + 3)).append (Image.rodataByte (o + 2))).append
        (Image.rodataByte (o + 1))).append (Image.rodataByte o) := by
  have hb := fun i (hi : i < 4) => h (o + i) (by omega)
  simp only [bytesT1, ← Nat.add_assoc] at hb
  have h0 := hb 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]

/-- **The `.rodata` words `lua_pushfstring` reads**: the format `"%I"` (its
word, bytes, terminator), `luaO_pushvfstring`'s conversion table entry for
`'I'`, `"%lld"`. -/
structure PfRod (m : Mem) : Prop where
  fmt8 : bytesT8 m 0x8004fd58 = 0x4925#64
  fmt0 : bytesT1 m 0x8004fd58 = 0x25#8
  fmt1 : bytesT1 m 0x8004fd59 = 0x49#8
  fmt2 : bytesT1 m 0x8004fd5a = 0x0#8
  jt : bytesT4 m 0x80052c1c = 0xfffbf3a4#32
  lld : bytesAt m 0x8004f3f0 5 = [0x25#8, 0x6c#8, 0x6c#8, 0x64#8, 0#8]

theorem pfRod_of {m : Mem} (h : RodataRead m) : PfRod m := by
  have e : ∀ a, Image.rodataBase ≤ a → a < Image.rodataBase + Image.rodataSize →
      bytesT1 m a = Image.rodataByte (a - Image.rodataBase) := fun a h1 h2 => by
    have := h (a - Image.rodataBase) (by omega)
    rwa [show Image.rodataBase + (a - Image.rodataBase) = a by omega] at this
  have hb : Image.rodataBase = 0x8004ecc8 := rfl
  have hs : Image.rodataSize = 55776 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0x8004fd58 : Nat) = Image.rodataBase + 0x1090 by decide, At.rod8 h _ (by decide)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [e _ (by omega) (by omega)]; decide
  · rw [show (0x80052c1c : Nat) = Image.rodataBase + 0x3f54 by decide, rod4 h _ (by decide)]; decide
  · simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.map_append]
    rw [e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega),
      e _ (by omega) (by omega), e _ (by omega) (by omega)]
    decide

/-- **`lua_pushfstring`'s inputs**: the C frame (room for `luaO_pushvfstring`'s
buffer and the callees' frames below it), `L`, `g`, `L->top` apart, `G(L)`
and `L->top` as `L`'s words, `.rodata`. -/
structure PfIn (m : Mem) (sp L g top : Nat) (r : BitVec 64) : Prop where
  sp_lo : 0x87800000 + 16384 + 8192 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_al : L % 8 = 0
  L_he : L + 200 ≤ 0x87800000
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  t_lo : 0x8005c6d0 ≤ top
  t_hi : top + 32 ≤ 0x87800000
  t_al : top % 8 = 0
  tL : top + 16 ≤ L ∨ L + 200 ≤ top
  tg : top + 16 ≤ g ∨ g + 1400 ≤ top
  Lg : L + 200 ≤ g ∨ g + 1400 ≤ L
  Lg_w : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  rod : RodataRead m

set_option hygiene false in
/-- `PfIn`'s facts in context. -/
local macro "pf_in" hP:ident : tactic => `(tactic| (
  have := ($hP).sp_lo; have := ($hP).sp_hi; have := ($hP).sp_al; have := ($hP).ra; have := ($hP).L_lo
  have := ($hP).L_al; have := ($hP).L_he; have := ($hP).g_lo; have := ($hP).g_hi; have := ($hP).t_lo
  have := ($hP).t_hi; have := ($hP).t_al; have := ($hP).tL; have := ($hP).tg; have := ($hP).Lg))

/-- **`fat_pin h v n R`**: register `R` (GPR `n`) pinned at the value `v` it
holds. -/
macro "fat_pin " h:ident v:ident n:num R:ident : tactic => `(tactic| (
  obtain ⟨$v, hv⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk $h) $n (by decide) (by decide))
  have $h := Vsa.Sim.SegSt.repin (L' := ⟨$R, $v⟩ :: _) $h ⟨hv, Vsa.Sim.SegSt.pins $h⟩))

/-- The memory at the cut: the entry's with `lua_pushfstring`'s and
`luaO_pushvfstring`'s frames stored. -/
abbrev pfM1 (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (i a3 a4 a5 a6 a7 : BitVec 64) (m : Mem)
    (o : Array String) : Mem :=
  Lua.Vm.AtF.PushfI.m1 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 0#64 m o)

/-- `s8` at the cut (`luaO_pushvfstring`'s `addiw s8, a5, -230`). -/
abbrev pfS8 (sp : Nat) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb ((((BitVec.ofNat 64 (sp - 96)) + sign_extend (m := 64) (0xe90#12)) +
    sign_extend (m := 64) (0x100#12)) + sign_extend (m := 64) (0xf1a#12)) 31 0)

theorem uge_self (x : BitVec 64) : zopz0zKzJ_u x x = true := by
  simp [zopz0zKzJ_u]

/-- **From the entry to the cut** (`0x80011df8`, after `strchr`): the vararg
registers at whatever they hold. -/
theorem pf_cut (sp L g top : Nat) (i r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hP : PfIn m sp L g top r) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd58#64⟩,
        ⟨Register.x12, i⟩] sp r f) (ArmPay m o))
      (fun c => ∃ a3 a4 a5 a6 a7, SegSt 0x80011df8#64
        (Lua.Vm.AtF.PushfI.r3 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) (pfM1 sp L g top r f i a3 a4 a5 a6 a7 m o) o))
        (ArmPay (pfM1 sp L g top r f i a3 a4 a5 a6 a7 m o) o) c) := by
  intro c h
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  fat_pin h a3 13 Register.x13
  fat_pin h a4 14 Register.x14
  fat_pin h a5 15 Register.x15
  fat_pin h a6 16 Register.x16
  fat_pin h a7 17 Register.x17
  simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800030a4#64 (Lua.Vm.AtF.PushfI.r0 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 0#64 m o))
      (ArmPay (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 0#64 m o).m
        (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 0#64 m o).o) c := by
    fcx_unfold; exact h.repin (by pins_of h)
  have hX : Lua.Vm.AtF.PushfI.Ok (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 0#64 m o) := by fcx_ok
  have R := pfRod_of hP.rod
  have hc0 : bytesT8 m 0x8004fd58 = 0x4925#64 := R.fmt8
  have hc1 : bytesT1 m 0x8004fd58 = 0x25#8 := R.fmt0
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfI h acc until [0x80011df8]
  exact ⟨_, acc, a3, a4, a5, a6, a7, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-- The digits' count: one to twenty bytes. -/
theorem intBytes_len (i : BitVec 64) : 1 ≤ (intBytes i).length ∧ (intBytes i).length ≤ 20 := by
  rw [intBytes_eq]
  have hpos : 0 < (decBytes (magOf i)).length := List.length_pos_iff.mpr (decBytes_ne_nil _)
  have hc := BitVec.toInt_eq_toNat_cond i
  have hi := i.isLt
  by_cases hn : i.toInt < 0
  · have hm : magOf i < 10 ^ (18 + 1) := by
      simp only [magOf, if_pos hn, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
      split at hc <;> omega
    have := decBytes_length_le 18 _ hm
    simp only [hn, if_true, List.length_append, List.length_cons, List.length_nil]
    omega
  · have hm : magOf i < 2 ^ 64 := by simp only [magOf, if_neg hn]; exact hi
    have := decBytes_length_64 hm
    simp only [hn, if_false, List.nil_append]
    omega

/-- **The stack words `lua_pushfstring`'s later roots read** (lane F1-20):
`buff.L`, `buff.pushed`, `luaO_pushvfstring`'s return address, `L` and the
caller's `s1`–`s11` in its frame, `lua_pushfstring`'s `ra` and `s0`. -/
structure PfSlots (M : Mem) (sp L : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  buffL : bytesT8 M (sp - 424) = BitVec.ofNat 64 L
  pushed : bytesT4 M (sp - 416) = 0x0#32
  ra2 : bytesT8 M (sp - 104) = 0x800030dc#64
  L112 : bytesT8 M (sp - 112) = BitVec.ofNat 64 L
  s1 : bytesT8 M (sp - 120) = f.s1
  s2 : bytesT8 M (sp - 128) = f.s2
  s3 : bytesT8 M (sp - 136) = f.s3
  s4 : bytesT8 M (sp - 144) = f.s4
  s5 : bytesT8 M (sp - 152) = f.s5
  s6 : bytesT8 M (sp - 160) = f.s6
  s7 : bytesT8 M (sp - 168) = f.s7
  s8 : bytesT8 M (sp - 176) = f.s8
  s9 : bytesT8 M (sp - 184) = f.s9
  s10 : bytesT8 M (sp - 192) = f.s10
  s11 : bytesT8 M (sp - 200) = f.s11
  ra : bytesT8 M (sp - 56) = r
  s0 : bytesT8 M (sp - 64) = f.s0

/-- The slots again at a memory agreeing on `[sp - 424, sp - 412)` and
`[sp - 200, sp - 48)` (not the buffer's length, nor its bytes). -/
theorem PfSlots.congr {M M' : Mem} {sp L : Nat} {r : BitVec 64} {f : AbiFrame} (h : PfSlots M sp L r f)
    (hsp : 424 ≤ sp)
    (hk : ∀ a, (sp - 424 ≤ a ∧ a < sp - 412) ∨ (sp - 200 ≤ a ∧ a < sp - 48) → bytesT1 M' a = bytesT1 M a) :
    PfSlots M' sp L r f where
  buffL := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.buffL
  pushed := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.pushed
  ra2 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.ra2
  L112 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.L112
  s1 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s1
  s2 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s2
  s3 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s3
  s4 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s4
  s5 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s5
  s6 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s6
  s7 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s7
  s8 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s8
  s9 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s9
  s10 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s10
  s11 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s11
  ra := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.ra
  s0 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.s0

/-- A slot of the cut's memory, read through its stores. -/
macro "pf_m1" : tactic => `(tactic| (
  simp only [pfM1, Lua.Vm.AtF.PushfI.m1, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw8_same, fw8_wm8, fw4_wm8, fw4_in8_zero]))

/-- **The cut's memory**: the entry's below the frames. -/
theorem pfM1_low {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {i a3 a4 a5 a6 a7 : BitVec 64} {m : Mem}
    {o : Array String} (hsp : 424 ≤ sp) :
    ∀ a, (a + 424 < sp ∨ sp ≤ a) → bytesT1 (pfM1 sp L g top r f i a3 a4 a5 a6 a7 m o) a = bytesT1 m a := by
  intro a ha
  simp only [pfM1, Lua.Vm.AtF.PushfI.m1, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw1_wm8]

/-- **The cut's memory**: the slots stored. -/
theorem pfM1_slots {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {i a3 a4 a5 a6 a7 : BitVec 64} {m : Mem}
    {o : Array String} (hsp : 424 ≤ sp) : PfSlots (pfM1 sp L g top r f i a3 a4 a5 a6 a7 m o) sp L r f where
  buffL := by pf_m1
  pushed := by pf_m1
  ra2 := by pf_m1
  L112 := by pf_m1
  s1 := by pf_m1
  s2 := by pf_m1
  s3 := by pf_m1
  s4 := by pf_m1
  s5 := by pf_m1
  s6 := by pf_m1
  s7 := by pf_m1
  s8 := by pf_m1
  s9 := by pf_m1
  s10 := by pf_m1
  s11 := by pf_m1
  ra := by pf_m1
  s0 := by pf_m1

/-- `snprintf`'s static words at another memory agreeing below the stack. -/
theorem FmtStatic.congr {m M : Mem} (h : FmtStatic m) (hk : ∀ a, a < 0x8005e720 → bytesT1 M a = bytesT1 m a) :
    FmtStatic M where
  impure := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.impure
  decpt := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.decpt
  dotw := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.dotw
  dot0 := (hk _ (by omega)).trans h.dot0
  dot1 := (hk _ (by omega)).trans h.dot1
  mbtowc := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.mbtowc
  mbmax := (hk _ (by omega)).trans h.mbmax
  jt_l := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.jt_l
  jt_d := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.jt_d

/-- **The memory at the cut** (`C`'s root memory), against the entry's: the
slots, the buffer's length `0`, `i` in `lua_pushfstring`'s vararg area, the
entry's memory off the frames. -/
structure PfC (M m : Mem) (sp L : Nat) (r i : BitVec 64) (f : AbiFrame) : Prop where
  slots : PfSlots M sp L r f
  blen : bytesT4 M (sp - 412) = 0x0#32
  argi : bytesT8 M (sp - 48) = i
  low : ∀ a, (a + 424 < sp ∨ sp ≤ a) → bytesT1 M a = bytesT1 m a

theorem pfC_of {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {i a3 a4 a5 a6 a7 : BitVec 64} {m : Mem}
    {o : Array String} (hsp : 424 ≤ sp) : PfC (pfM1 sp L g top r f i a3 a4 a5 a6 a7 m o) m sp L r i f where
  slots := pfM1_slots hsp
  blen := by pf_m1
  argi := by pf_m1
  low := pfM1_low hsp

/-- `addnum2buff`'s frame at `snprintf`'s call. -/
abbrev pfSnFr (sp L : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 (sp - 424), 0x80052c1c#64, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440),
    BitVec.ofNat 64 (sp - 408), 0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x8004fd58#64, 0x8004fd58#64, f.s11⟩

/-- **The memory after `snprintf`** (`S`'s root memory): the slots, the
buffer's length still `0`, `addnum2buff`'s return address and buffer, the
digits and their terminator at `sp - 408`, the entry's memory below the
frames. -/
structure PfS (M m : Mem) (sp L : Nat) (r i : BitVec 64) (f : AbiFrame) : Prop where
  slots : PfSlots M sp L r f
  blen : bytesT4 M (sp - 412) = 0x0#32
  ra3 : bytesT8 M (sp - 472) = 0x80011fe0#64
  bufp : bytesT8 M (sp - 480) = BitVec.ofNat 64 (sp - 40)
  digits : bytesAt M (sp - 408) ((intBytes i).length + 1) = intBytes i ++ [0#8]
  low : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M a = bytesT1 m a

set_option hygiene false in
/-- A word of `snprintf`'s call memory (the generated `m6`) at a literal
offset. -/
local macro "pf_m6" : tactic => `(tactic| (
  simp only [Lua.Vm.AtF.PushfI.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw8_same, fw8_wm8, fw8_wm4, fw8_ins, fw4_same, fw4_wm8, fw4_ins, fw1_wm8,
    fw1_wm4, fw1_ins]))

/-- **From the cut to `snprintf`'s return** (`S`, `0x800115f4`). -/
theorem pf_snp (hS : IntegerToStr_Statement) (sp L g top : Nat) (i r : BitVec 64) (f : AbiFrame)
    (a3 a4 a5 a6 a7 : BitVec 64) (m M1 : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hst : FmtStatic m)
    (hC : PfC M1 m sp L r i f) :
    Triple (SegSt 0x80011df8#64 (Lua.Vm.AtF.PushfI.r3 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o))
        (ArmPay (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m
          (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).o))
      (fun c => ∃ M, PfS M m sp L r i f ∧ SegSt 0x800115f4#64
        (Lua.Vm.AtF.PushfI.r6 (pfX [sp, L, g, top, (intBytes i).length] r f i a3 a4 a5 a6 a7 (pfS8 sp) M o))
        (ArmPay M o) c) := by
  intro c h
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have R := pfRod_of hP.rod
  have k1 := hC.low
  have hX : Lua.Vm.AtF.PushfI.Ok_C (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o) := by fcx_ok
  have hc2 : bytesT4 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m
      ((pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 412) = 0x0#32 := hC.blen
  have hc3 : bytesT1 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m 0x8004fd59 = 0x49#8 :=
    (k1 _ (.inl (by omega))).trans R.fmt1
  have hc4 : bytesT4 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m 0x80052c1c = 0xfffbf3a4#32 :=
    (bytesT4_congrT fun j _ => k1 _ (.inl (by omega))).trans R.jt
  have hc5 : bytesT8 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).m
      ((pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 48) =
      (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).b 13 := hC.argi
  -- `memcpy` of the empty prefix: the pointers aligned alike
  have hg_4 : ((((0x8004fd58#64) ^^^ (BitVec.ofNat 64
      ((pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = false :=
    xor_al _ _ (by decide) (by simp only [pfX, FCx.mk', List.getD_cons_zero]; omega)
  have hg_2 : zopz0zKzJ_u (BitVec.ofNat 64 ((pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408))
      (BitVec.ofNat 64 ((pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o).n 0 - 408)) = true := uge_self _
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfI h acc until [0x8003b648]
  -- `memcpy`'s alignment test (its other outcome's guard sends `fat_hyp` past the recursion limit)
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.PushfI.at_8003b648_8003b658_n_1 _ hX hg_4)
  fat_run Lua.Vm.AtF.PushfI h acc until [0x80034de0]
  generalize hM6 : Lua.Vm.AtF.PushfI.m6 (pfX [sp, L, g, top] r f i a3 a4 a5 a6 a7 (pfS8 sp) M1 o) = M6 at h
  have k6 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) →
      bytesT1 M6 a = bytesT1 M1 a := by
    intro a ha
    rw [← hM6]
    simp only [Lua.Vm.AtF.PushfI.m6, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins]
  have low6 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M6 a = bytesT1 m a := fun a ha =>
    (k6 a (by omega)).trans (k1 a (by omega))
  have hIn : IntFmtIn M6 (sp - 496) (sp - 408) 0x8004f3f0 0x800115f4#64 := {
    fmtb := (bytesAt_congr fun j hj => low6 _ (.inl (by omega))).trans R.lld
    f_lo := by decide, f_hi := by decide, ra := by decide
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, b_lo := by omega, b_ap := .inr (by omega)
    b_hi := by omega
    stat := hst.congr fun a ha => low6 a (.inl (by omega)) }
  fcx_unfold at h
  obtain ⟨c2, s2, M2, hret, hdig, hkeep⟩ := hS (sp - 496) (sp - 408) 0x8004f3f0 i 0x800115f4#64
    (pfSnFr sp L f) M6 o hIn _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s2
  have kS : ∀ a, sp - 496 ≤ a → (a < sp - 408 ∨ sp - 408 + 44 ≤ a) → bytesT1 M2 a = bytesT1 M6 a :=
    fun a h1 h2 => hkeep a (.inr h1) h2
  have P : PfS M2 m sp L r i f := {
    slots := hC.slots.congr (by omega) fun a ha => (kS a (by omega) (by omega)).trans (k6 a (by omega))
    blen := (bytesT4_congrT fun j _ => kS _ (by omega) (by omega)).trans (by rw [← hM6]; pf_m6; decide)
    ra3 := (bytesT8_congrT fun j _ => kS _ (by omega) (by omega)).trans (by rw [← hM6]; pf_m6)
    bufp := (bytesT8_congrT fun j _ => kS _ (by omega) (by omega)).trans (by rw [← hM6]; pf_m6)
    digits := hdig
    low := fun a ha => (hkeep a (by omega) (by omega)).trans (low6 a ha) }
  simp only [wrRet] at hret
  exact ⟨c2, acc, M2, P, by fcx_unfold; exact hret.repin (by pins_of hret)⟩

/-- **The new string's facts against another memory** agreeing off `G`
(where `g`'s white and `g->allgc` lie outside it). -/
theorem IaNewPost.trans {M0 M m' : Mem} {F G : Nat → Prop} {g bkt nuse head p : Nat} {b : List UInt8}
    {hh : BitVec 64} {H H' : HeapIx} (h : IaNewPost M m' F g bkt nuse head b hh H p H')
    (hk : ∀ a, ¬ G a → bytesT1 M a = bytesT1 M0 a) (h100 : ¬ G (g + 100)) (h112 : ∀ i, i < 8 → ¬ G (g + 112 + i)) :
    IaNewPost M0 m' (fun a => F a ∨ G a) g bkt nuse head b hh H p H' := by
  refine ⟨h.heap, h.brk, h.kept, h.obj_in, h.fresh, h.lo, h.hi, h.al, h.tt, ?_, h.extra, h.len, h.hash, h.hnext,
    ?_, h.bytes, h.nul, h.bucket, h.nuse, h.allgc, fun a ha => ?_⟩
  · rw [h.mark, hk _ h100]
  · rw [h.next]; exact bytesT8_congrT fun i hi => hk _ (h112 i hi)
  · refine (h.keep a fun hc => ha ?_).trans (hk a fun hG => ha (.inr (.inr (.inr (.inr (.inr (.inr (.inr hG))))))))
    rcases hc with hc | hc | hc | hc | hc | hc | hc
    · exact .inl hc
    · exact .inr (.inl hc)
    · exact .inr (.inr (.inl hc))
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr (.inl hc))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hc)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl hc))))))

/-- The digits as bytes. -/
def intU8 (i : BitVec 64) : List UInt8 := (intBytes i).map UInt8.ofBitVec

theorem intU8_length (i : BitVec 64) : (intU8 i).length = (intBytes i).length := by simp [intU8]

theorem intU8_get (i : BitVec 64) (j : Nat) (hj : j < (intBytes i).length) :
    BitVec.ofNat 8 ((intU8 i).getD j 0).toNat = (intBytes i)[j] := by
  simp only [intU8, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
    Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp

/-- **`luaS_newlstr`'s table at `lua_pushfstring`'s entry** (lane F1-20): the
seed, the table as `internshrstr` reads it at any memory agreeing below the
stack (its chains' nodes in `K`, in the arena, apart from `L->top`'s slot),
the creation path's inputs, `L->top`'s slot in a chunk in use. -/
structure NlTab (m : Mem) (L g top : Nat) (b : List UInt8) (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8)
    (size hash head d nuse : Nat) (H : HeapIx) : Prop where
  seed_w : bytesT4 m (g + 96) = seed.toBitVec
  hK : ∀ a, K a → 0x8006ecd0 ≤ a ∧ a < 0x87800000
  kt : ∀ a, K a → ¬ Rng top 16 a
  tab : ∀ M : Mem, (∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a) →
    bytesT1 M (g + 100) = cw ∧ IaTab M g (luaHash seed b) b cw (IaNode M K X W) size hash head d
  new : IaNewIn m L g (hash + 8 * ((luaHash seed b).toNat % size)) size nuse head b H
  top_in : ∀ a, Rng top 16 a → InUse H.chunks a
  Lk : hash + 8 * ((luaHash seed b).toNat % size) + 8 ≤ L ∨ L + 200 ≤ hash + 8 * ((luaHash seed b).toNat % size)

/-- **A string found**, against the entry's memory `m`: the node's facts,
its length and contents; every byte off `F` (the frames) kept. -/
structure PfHit (m M : Mem) (F K X W : Nat → Prop) (ts : Nat) (b : List UInt8) : Prop where
  node : IaNode m K X W ts
  len : bytesT1 m (ts + 11) = BitVec.ofNat 8 b.length
  bytes : ∀ i, i < b.length → bytesT1 m (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  keep : ∀ a, ¬ F a → bytesT1 M a = bytesT1 m a

/-- `lua_pushfstring`'s frames: `[sp - 8192, sp)`. -/
def PfFr (sp a : Nat) : Prop := sp - 8192 ≤ a ∧ a < sp

/-- **`luaS_newlstr`'s outcome for `lua_pushfstring`**: found (the heap as
it was) or created (`IaNewPost` off the frames). -/
def PfStr (m M : Mem) (sp g : Nat) (b : List UInt8) (seed : UInt32) (K X W : Nat → Prop) (size hash nuse head : Nat)
    (H : HeapIx) (ts : Nat) (H' : HeapIx) : Prop :=
  (PfHit m M (PfFr sp) K X W ts b ∧ H' = H) ∨
    IaNewPost m M (PfFr sp) g (hash + 8 * ((luaHash seed b).toNat % size)) nuse head b (hw (luaHash seed b)) H ts H'

/-- **The memory at `luaS_newlstr`'s return** (`T`'s root memory): the
slots, `L->top` and `G(L)`, the string's tag, where it lies. -/
structure PfT (M : Mem) (sp L g top ts : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  slots : PfSlots M sp L r f
  top_w : bytesT8 M (L + 16) = BitVec.ofNat 64 top
  Lg_w : bytesT8 M (L + 24) = BitVec.ofNat 64 g
  tt : bytesT1 M (ts + 8) = 0x4#8
  ts_lo : 0x8005c6d0 ≤ ts
  ts_hi : ts + 24 ≤ 0x87800000
  tts : top + 16 ≤ ts ∨ ts + 16 ≤ top

theorem ofNat_sub_le {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A byte of a list read by `bytesAt`. -/
theorem bytesAt_get {M : Mem} {a n : Nat} {l : List (BitVec 8)} (h : bytesAt M a n = l) {j : Nat} (hj : j < n) :
    bytesT1 M (a + j) = l.getD j 0 := by
  subst h
  simp [bytesAt, List.getD_eq_getElem?_getD, hj]

/-- A new string's facts with more of the frames excluded. -/
theorem IaNewPost.mono {M m' : Mem} {F F' : Nat → Prop} {g bkt nuse head p : Nat} {b : List UInt8}
    {hh : BitVec 64} {H H' : HeapIx} (h : IaNewPost M m' F g bkt nuse head b hh H p H') (hF : ∀ a, F a → F' a) :
    IaNewPost M m' F' g bkt nuse head b hh H p H' := by
  refine ⟨h.heap, h.brk, h.kept, h.obj_in, h.fresh, h.lo, h.hi, h.al, h.tt, h.mark, h.extra, h.len, h.hash, h.hnext,
    h.next, h.bytes, h.nul, h.bucket, h.nuse, h.allgc, fun a ha => h.keep a fun hc => ha ?_⟩
  rcases hc with hc | hc | hc | hc | hc | hc | hc
  · exact .inl hc
  · exact .inr (.inl hc)
  · exact .inr (.inr (.inl hc))
  · exact .inr (.inr (.inr (.inl hc)))
  · exact .inr (.inr (.inr (.inr (.inl hc))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl hc)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (hF a hc))))))

/-- `S`'s context. -/
@[at_row] abbrev pfX2 (sp L g top n : Nat) (r : BitVec 64) (f : AbiFrame) (i a3 a4 a5 a6 a7 : BitVec 64) (M : Mem)
    (o : Array String) : FCx :=
  pfX [sp, L, g, top, n] r f i a3 a4 a5 a6 a7 (pfS8 sp) M o

/-- **From `snprintf`'s return to `luaS_newlstr`'s call**: `addsize`, the
second `strchr` (none), `addstr2buff` of the empty suffix (`memcpy` of no
bytes, its alignment test either way), `clearbuff`. -/
theorem pf_nl_reach (sp L g top : Nat) (i r : BitVec 64) (f : AbiFrame) (a3 a4 a5 a6 a7 : BitVec 64)
    (m M2 : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hS : PfS M2 m sp L r i f) (n : Nat)
    (hn : (intBytes i).length = n) (c : Config)
    (h : SegSt 0x800115f4#64 (Lua.Vm.AtF.PushfI.r6 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o))
      (ArmPay (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80017694#64 (Lua.Vm.AtF.PushfI.r8 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o))
      (ArmPay (Lua.Vm.AtF.PushfI.m10 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o)) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have R := pfRod_of hP.rod
  have hn1 := (intBytes_len i).1
  have hn2 := (intBytes_len i).2
  rw [hn] at hn1 hn2
  have hX : Lua.Vm.AtF.PushfI.Ok_S (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o) := by fcx_ok
  have hc2 : bytesT4 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m
      ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 - 412) = 0x0#32 := hS.blen
  have hc6 : bytesT8 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m
      ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 - 472) = 0x80011fe0#64 := hS.ra3
  have hc7 : bytesT8 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m
      ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 - 480) =
      BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 - 40) := hS.bufp
  have hc8 : bytesT1 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m 0x8004fd5a = 0x0#8 :=
    (hS.low _ (.inl (by omega))).trans R.fmt2
  have hc9 : bytesT8 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m
      ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 - 424) =
      BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 1) := hS.slots.buffL
  have hc10 : bytesT8 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m
      ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 1 + 16) =
      BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 3) :=
    show bytesT8 M2 (L + 16) = BitVec.ofNat 64 top from
      (bytesT8_congrT fun j _ => hS.low _ (.inl (by omega))).trans hP.top_w
  have hg_4 : zopz0zI_s ((BitVec.ofNat 64 (199) - BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 4)))
      (0x0#64) = false := by
    simp only [pfX2, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [ofNat_sub_le (by omega) (by omega)]
    fmt_scmp
  have hg_2 : zopz0zKzJ_u (BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 +
      (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 4 - 408))
      (BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 +
      (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 4 - 408)) = true := uge_self _
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfI h acc until [0x8003b648]
  -- `memcpy`'s alignment test, either way
  cases hb : ((((0x8004fd5a#64) ^^^ (BitVec.ofNat 64 ((pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 0 +
      (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).n 4 - 408))) &&& sign_extend (m := 64) (0x007#12)) != (0#64))
  · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_8003b648_8003b658_n _ hX hb)
    fat_run Lua.Vm.AtF.PushfI h acc until [0x80017694]
    exact ⟨_, acc, h⟩
  · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_8003b648_8003b658_t _ hX hb)
    fat_run Lua.Vm.AtF.PushfI h acc until [0x80017694]
    exact ⟨_, acc, h⟩

/-- `pushstr`'s frame at `luaS_newlstr`'s call. -/
abbrev pfNlFr (sp L top : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 top, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440), BitVec.ofNat 64 (sp - 408),
    0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x0#64, 0x8004fd5a#64, f.s11⟩

/-- Two objects apart: one's bytes in `K`, the other's off it. -/
theorem apart_of_K {K : Nat → Prop} {ts top : Nat} (hK : ∀ a, ts ≤ a → a < ts + 24 → K a)
    (kt : ∀ a, K a → ¬ Rng top 16 a) : top + 16 ≤ ts ∨ ts + 16 ≤ top := by
  by_cases h1 : top ≤ ts
  · by_cases h2 : ts < top + 16
    · exact absurd ⟨h1, h2⟩ (kt ts (hK ts (Nat.le_refl _) (by omega)))
    · exact .inl (by omega)
  · by_cases h2 : top < ts + 16
    · exact absurd ⟨Nat.le_refl _, by omega⟩ (kt top (hK top (by omega) (by omega)))
    · exact .inr (by omega)

/-- **The `T` root's facts when the string is found.** -/
theorem pfT_hit {m M2 M10 M3 : Mem} {sp L g top ts : Nat} {i r : BitVec 64} {f : AbiFrame} {K X W : Nat → Prop}
    (hP : PfIn m sp L g top r) (hS : PfS M2 m sp L r i f)
    (k10 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) → bytesT1 M10 a = bytesT1 M2 a)
    (low10 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M10 a = bytesT1 m a)
    (hK : ∀ a, K a → 0x8006ecd0 ≤ a ∧ a < 0x87800000) (kt : ∀ a, K a → ¬ Rng top 16 a)
    (hh : NlHit M10 M3 K X W (sp - 464) ts (intU8 i)) : PfT M3 sp L g top ts r f := by
  pf_in hP
  have k3 : ∀ a, (a + 600 < sp ∨ sp - 464 ≤ a) → bytesT1 M3 a = bytesT1 M10 a := fun a ha =>
    hh.keep a (by simp only [Below]; omega)
  have o0 := hh.node.obj ts (Nat.le_refl _) (by omega)
  have o23 := hh.node.obj (ts + 23) (by omega) (by omega)
  have := (hK _ o0.1).1; have := (hK _ o23.1).2
  exact {
    slots := hS.slots.congr (by omega) fun a ha => (k3 a (by omega)).trans (k10 a (by omega))
    top_w := (bytesT8_congrT fun j _ => (k3 _ (by omega)).trans (low10 _ (by omega))).trans hP.top_w
    Lg_w := (bytesT8_congrT fun j _ => (k3 _ (by omega)).trans (low10 _ (by omega))).trans hP.Lg_w
    tt := (k3 _ (by omega)).trans hh.node.tt
    ts_lo := by omega
    ts_hi := by omega
    tts := apart_of_K (fun a h1 h2 => (hh.node.obj a h1 (by omega)).1) kt }

/-- **The string found, against `lua_pushfstring`'s entry memory.** -/
theorem pfHit_of {m M10 M3 : Mem} {sp ts : Nat} {b : List UInt8} {K X W : Nat → Prop}
    (low10 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M10 a = bytesT1 m a) (hsp : 0x87800000 + 8192 ≤ sp)
    (hK : ∀ a, K a → 0x8006ecd0 ≤ a ∧ a < 0x87800000) (hb : b.length ≤ 40)
    (hh : NlHit M10 M3 K X W (sp - 464) ts b) : PfHit m M3 (PfFr sp) K X W ts b := by
  have kK : ∀ a, K a → bytesT1 M10 a = bytesT1 m a := fun a ha => low10 a (.inl (by have := (hK a ha).2; omega))
  have o0 := hh.node.obj ts (Nat.le_refl _) (by omega)
  have o11 := hh.node.obj (ts + 11) (by omega) (by omega)
  have e11 : bytesT1 M10 (ts + 11) = bytesT1 m (ts + 11) := kK _ o11.1
  refine ⟨⟨(kK _ (hh.node.obj (ts + 8) (by omega) (by omega)).1).symm.trans hh.node.tt, fun a h1 h2 => ?_,
    hh.node.mark⟩, e11 ▸ hh.len, fun j hj => ?_, fun a ha => ?_⟩
  · rw [← e11] at h2; exact hh.node.obj a h1 h2
  · have hl : (bytesT1 M10 (ts + 11)).toNat = b.length := by rw [hh.len, BitVec.toNat_ofNat]; omega
    rw [← kK _ (hh.node.obj _ (by omega) (by rw [hl]; omega)).1]; exact hh.bytes j hj
  · exact (hh.keep a (by simp only [Below, PfFr] at ha ⊢; omega)).trans (low10 a (by simp only [PfFr] at ha; omega))

/-- **The `T` root's facts when the string is created.** -/
theorem pfT_new {m M2 M10 M3 : Mem} {sp L g top bkt nuse head p : Nat} {i r : BitVec 64} {f : AbiFrame}
    {size : Nat} {b : List UInt8} {hh : BitVec 64} {H H' : HeapIx}
    (hP : PfIn m sp L g top r) (hS : PfS M2 m sp L r i f)
    (k10 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) → bytesT1 M10 a = bytesT1 M2 a)
    (low10 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M10 a = bytesT1 m a)
    (hN : IaNewIn m L g bkt size nuse head b H) (Lk : bkt + 8 ≤ L ∨ L + 200 ≤ bkt)
    (top_in : ∀ a, Rng top 16 a → InUse H.chunks a) (hb : b.length ≤ 40)
    (hp : IaNewPost M10 M3 (Below (sp - 464) 2048) g bkt nuse head b hh H p H') : PfT M3 sp L g top p r f := by
  pf_in hP
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have := hN.bkt_he; have := hN.bkt_lo; have hp1 := hp.lo; have hp2 := hp.hi
  have inLo : ∀ a, InUse H.chunks a → heapStart + 16 ≤ a := fun a hu =>
    Nat.le_of_not_lt fun hc => ChunkWalk.notInUse_lo hN.heap.walk a hc hu
  have kS : ∀ a, sp - 464 ≤ a → a < 2 ^ 32 → bytesT1 M3 a = bytesT1 M10 a := fun a h1 h2 =>
    hp.keep a fun hc => by
      rcases hc with hc | hc | hc | hc | hc | hc | hc
      · rcases hc with hc | hc
        · exact absurd hc.lo (by omega)
        · omega
      all_goals simp only [Rng, Below] at hc; omega
  have kL : ∀ a, L ≤ a → a < L + 200 → bytesT1 M3 a = bytesT1 M10 a := fun a h1 h2 =>
    have hu := hN.L_in a h1 h2
    have := inLo a hu
    hp.keep a fun hc => by
      rcases hc with hc | hc | hc | hc | hc | hc | hc
      · rcases hc with hc | hc
        · exact absurd hc.lo (by omega)
        · exact hc.2.2 hu
      · exact hp.fresh a hc.1 hc.2 hu
      all_goals simp only [Rng, Below] at hc; omega
  exact {
    slots := hS.slots.congr (by omega) fun a ha => (kS a (by omega) (by omega)).trans (k10 a (by omega))
    top_w := (bytesT8_congrT fun j _ => (kL _ (by omega) (by omega)).trans (low10 _ (by omega))).trans hP.top_w
    Lg_w := (bytesT8_congrT fun j _ => (kL _ (by omega) (by omega)).trans (low10 _ (by omega))).trans hP.Lg_w
    tt := hp.tt
    ts_lo := by omega
    ts_hi := by omega
    tts := (apart_of_use (x := top) (n := 16) (p := p) (k := b.length + 25) (fun a h1 h2 => top_in a ⟨h1, h2⟩)
      (fun a h1 h2 => hp.fresh a h1 (by omega)) (by omega) (by omega)).imp (fun h => by omega) (fun h => by omega) }

/-- **From `snprintf`'s return to `luaS_newlstr`'s** (`T`, `0x80011ec0`): the
string found or created (`PfStr`), `T`'s facts (`PfT`). -/
theorem pf_nl (hM : MallocR_Statement) (sp L g top : Nat) (i r : BitVec 64) (f : AbiFrame)
    (a3 a4 a5 a6 a7 : BitVec 64) (m M2 : Mem) (o : Array String) (hP : PfIn m sp L g top r)
    (hS : PfS M2 m sp L r i f) (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat)
    (H : HeapIx) (hT : NlTab m L g top (intU8 i) seed K X W cw size hash head d nuse H) (n : Nat)
    (hn : (intBytes i).length = n) :
    Triple (SegSt 0x800115f4#64 (Lua.Vm.AtF.PushfI.r6 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o))
        (ArmPay (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).m (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o).o))
      (fun c => ∃ ts M3 H', PfT M3 sp L g top ts r f ∧
        PfStr m M3 sp g (intU8 i) seed K X W size hash nuse head H ts H' ∧
        SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfI.r9 (pfX [sp, L, g, top, n, ts] r f i a3 a4 a5 a6 a7 (pfS8 sp) M3 o))
          (ArmPay M3 o) c) := by
  intro c h
  pf_in hP
  have hn1 := (intBytes_len i).1
  have hn2 := (intBytes_len i).2
  obtain ⟨c1, s1, h⟩ := pf_nl_reach sp L g top i r f a3 a4 a5 a6 a7 m M2 o hP hS n hn c h
  generalize hM10 : Lua.Vm.AtF.PushfI.m10 (pfX2 sp L g top n r f i a3 a4 a5 a6 a7 M2 o) = M10 at h
  have k10 : ∀ a, (a + 600 < sp ∨ (sp - 424 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) → bytesT1 M10 a = bytesT1 M2 a := by
    intro a ha
    rw [← hM10]
    simp only [Lua.Vm.AtF.PushfI.m10, pfX2, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4]
  have low10 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M10 a = bytesT1 m a := fun a ha =>
    (k10 a (by omega)).trans (hS.low a ha)
  have hb40 : (intU8 i).length ≤ 40 := by rw [intU8_length]; omega
  have hIa : IaIn M10 (sp - 464) L (sp - 408) g (intU8 i) seed 0x80011ec0#64 := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega
    L_he := by omega, L_al := by omega, s_ge := by omega, s_hi := by rw [intU8_length]; omega
    s_al := by omega, l_lo := by rw [intU8_length]; omega, l_hi := hb40, g_lo := by omega, g_hi := by omega
    Lg := (bytesT8_congrT fun j _ => low10 _ (by omega)).trans hP.Lg_w
    bytes := fun j hj => by
      rw [intU8_length] at hj
      rw [k10 _ (by omega), bytesAt_get hS.digits (by omega), intU8_get i j hj]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
    seed_w := (bytesT4_congrT fun j _ => low10 _ (by omega)).trans hT.seed_w }
  fcx_unfold at h
  obtain ⟨c2, s2, hq⟩ := newlstr_any_sum hM (sp - 464) L (sp - 408) g size hash head d nuse (intU8 i) seed
    0x80011ec0#64 (pfNlFr sp L top f) M10 o hIa K X W cw (fun a ha => (hT.hK a ha).2)
    (fun M hM => hT.tab M fun a ha => (hM a ha).trans (low10 a (.inl (by omega)))) H
    (hT.new.congr fun a ha => low10 a (.inl (by omega))) _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
      rw [intU8_length, hn]
      exact h.repin (by pins_of h))
  rcases hq with ⟨ts, M3, hret, hh⟩ | ⟨M3, p, H', hret, hp⟩
  · simp only [wrRet] at hret
    exact ⟨c2, s1.trans s2, ts, M3, H, pfT_hit hP hS k10 low10 hT.hK hT.kt hh,
      .inl ⟨pfHit_of low10 (by omega) hT.hK hb40 hh, rfl⟩, by fcx_unfold; exact hret.repin (by pins_of hret)⟩
  · simp only [wrRet] at hret
    refine ⟨c2, s1.trans s2, p, M3, H', pfT_new hP hS k10 low10 hT.new hT.Lk hT.top_in hb40 hp, .inr ?_,
      by fcx_unfold; exact hret.repin (by pins_of hret)⟩
    refine (hp.trans (G := PfFr sp) (fun a ha => low10 a (by simp only [PfFr] at ha; omega))
      (by simp only [PfFr]; omega) (fun j _ => by simp only [PfFr]; omega)).mono fun a ha => ?_
    rcases ha with ha | ha
    · simp only [Below] at ha; exact ⟨by omega, by omega⟩
    · exact ha

/-- **What `lua_pushfstring` leaves after `luaS_newlstr`'s return** (`M3`,
`T`'s root memory): the string pushed at `L->top` (`setsvalue2s`, the tag
`LUA_VSHRSTR | BIT_ISCOLLECTABLE`), `L->top` advanced; every byte off the
slot, `L->top`, `g->totalbytes` and `g->GCdebt` (`luaC_step`) and the frames
kept. -/
structure PfPost (M3 M : Mem) (sp L g top ts : Nat) : Prop where
  val : bytesT8 M top = BitVec.ofNat 64 ts
  tag : bytesT1 M (top + 8) = 0x44#8
  top_w : bytesT8 M (L + 16) = BitVec.ofNat 64 (top + 16)
  keep : ∀ a, ¬ (Rng top 9 a ∨ Rng (L + 16) 8 a ∨ Rng (g + gTotalbytesOff) 8 a ∨ Rng (g + gGCdebtOff) 8 a ∨
    PfFr sp a) → bytesT1 M a = bytesT1 M3 a

/-- `T`'s context. -/
@[at_row] abbrev pfX3 (sp L g top n ts : Nat) (r : BitVec 64) (f : AbiFrame) (i a3 a4 a5 a6 a7 : BitVec 64) (M : Mem)
    (o : Array String) : FCx :=
  pfX [sp, L, g, top, n, ts] r f i a3 a4 a5 a6 a7 (pfS8 sp) M o

/-- The push's stores (the generated `m11`) at the slot, its tag, `L->top`. -/
theorem pf_m11 {sp L g top n ts : Nat} {r : BitVec 64} {f : AbiFrame} {i a3 a4 a5 a6 a7 : BitVec 64} {M : Mem}
    {o : Array String} (htL : top + 16 ≤ L ∨ L + 200 ≤ top) :
    bytesT8 (Lua.Vm.AtF.PushfI.m11 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) top = BitVec.ofNat 64 ts ∧
    bytesT1 (Lua.Vm.AtF.PushfI.m11 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) (top + 8) = 0x44#8 ∧
    bytesT8 (Lua.Vm.AtF.PushfI.m11 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) (L + 16) =
      BitVec.ofNat 64 (top + 16) ∧
    ∀ a, ¬ (Rng top 9 a ∨ Rng (L + 16) 8 a) →
      bytesT1 (Lua.Vm.AtF.PushfI.m11 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) a = bytesT1 M a := by
  simp only [Lua.Vm.AtF.PushfI.m11, pfX3, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
  · simp (disch := omega) only [fw8_wm8, fw8_ins, fw8_same]
  · simp (disch := omega) only [fw1_wm8, fw1_same]; decide
  · simp (disch := omega) only [fw8_same]
  · simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    simp (disch := omega) only [fw1_wm8, fw1_ins]

/-- The push's stores and the return value's slot (the generated `m12`). -/
theorem pf_m12 {sp L g top n ts : Nat} {r : BitVec 64} {f : AbiFrame} {i a3 a4 a5 a6 a7 : BitVec 64} {M : Mem}
    {o : Array String} (htL : top + 16 ≤ L ∨ L + 200 ≤ top) (hts : top + 16 ≤ sp - 88) (hL : L + 200 ≤ sp - 88) :
    bytesT8 (Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) top = BitVec.ofNat 64 ts ∧
    bytesT1 (Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) (top + 8) = 0x44#8 ∧
    bytesT8 (Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) (L + 16) =
      BitVec.ofNat 64 (top + 16) ∧
    bytesT8 (Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) (sp - 88) =
      BitVec.ofNat 64 (ts + 24) ∧
    ∀ a, ¬ (Rng top 9 a ∨ Rng (L + 16) 8 a ∨ Rng (sp - 88) 8 a) →
      bytesT1 (Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M o)) a = bytesT1 M a := by
  simp only [Lua.Vm.AtF.PushfI.m12, pfX3, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · simp (disch := omega) only [fw8_wm8, fw8_ins, fw8_same]
  · simp (disch := omega) only [fw1_wm8, fw1_same]; decide
  · simp (disch := omega) only [fw8_wm8, fw8_same]
  · simp (disch := omega) only [fw8_same]
  · simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    simp (disch := omega) only [fw1_wm8, fw1_ins]

/-- **From `luaS_newlstr`'s return to `lua_pushfstring`'s**: the push,
`luaO_pushvfstring`'s epilogue, `luaC_checkGC` (a positive debt: `luaC_step`
with the collector stopped). -/
theorem pf_ret (sp L g top n ts : Nat) (i r : BitVec 64) (f : AbiFrame) (a3 a4 a5 a6 a7 : BitVec 64)
    (m M3 : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hT : PfT M3 sp L g top ts r f)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 20) (hgc : bytesT1 M3 (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfI.r9 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o))
        (ArmPay M3 o))
      (fun c => ∃ M, PfPost M3 M sp L g top ts ∧ wrRet r sp (ts + 24) f M o c) := by
  intro c h
  pf_in hP
  have := hT.ts_lo; have := hT.ts_hi; have := hT.tts
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.PushfI.Ok_T (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o) := by fcx_ok
  have h : SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfI.r9 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o))
      (ArmPay (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o).m (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o).o)
      c := h
  have S := hT.slots
  have acc := Steps.refl c
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.PushfI.at_80011ec0_80011ee4_n _ hX hT.tt hT.top_w S.pushed)
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.PushfI.at_80011ee4_80011f2c _ hX S.ra2 S.L112 S.s1 S.s2 S.s3 S.s4 S.s5 S.s6 S.s7 S.s8 S.s9 S.s10 S.s11)
  obtain ⟨hv, htg, htw, hk11⟩ := pf_m11 (sp := sp) (n := n) (r := r) (f := f) (i := i) (a3 := a3) (a4 := a4)
    (a5 := a5) (a6 := a6) (a7 := a7) (M := M3) (o := o) (g := g) (ts := ts) (by omega)
  cases hb : zopz0zKzJ_s (0x0#64) (bytesT8 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o).m
      ((pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o).n 2 + 24))
  · -- a positive debt: `luaC_step` with the collector stopped
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030dc_800030ec_n _ hX hT.Lg_w hb)
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030ec_800030f8 _ hX)
    obtain ⟨hv2, htg2, htw2, h88, hk12⟩ := pf_m12 (sp := sp) (n := n) (r := r) (f := f) (i := i) (a3 := a3)
      (a4 := a4) (a5 := a5) (a6 := a6) (a7 := a7) (M := M3) (o := o) (g := g) (ts := ts) (by omega) (by omega)
      (by omega)
    generalize hM12 : Lua.Vm.AtF.PushfI.m12 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o) = M12 at h hv2 htg2 htw2 h88 hk12
    have hG12 : bytesT8 M12 (L + 24) = BitVec.ofNat 64 g :=
      (bytesT8_congrT fun j _ => hk12 _ (by simp only [Rng]; omega)).trans hT.Lg_w
    have hS12 : bytesT1 M12 (g + gGcstpOff) = 0x1#8 :=
      (hk12 _ (by simp only [Rng, gGcstpOff]; omega)).trans hgc
    fcx_unfold at h
    obtain ⟨c4, s4, M4, hret, hst⟩ := luaC_step_sum (sp - 96) L g 0x800030f8#64
      ⟨BitVec.ofNat 64 L, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M12 o
      ⟨by omega, by omega, by omega, by decide, by omega, by omega, by omega, by omega, by omega, hgal⟩ hG12 hS12 _
      (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
    have acc := acc.trans s4
    have k4 : ∀ a, ¬ (Rng (g + gTotalbytesOff) 8 a ∨ Rng (g + gGCdebtOff) 8 a ∨ PfFr sp a) →
        bytesT1 M4 a = bytesT1 M12 a := fun a ha => hst.keep a fun hc => ha (by
      rcases hc with hc | hc | hc
      · exact .inl hc
      · exact .inr (.inl hc)
      · simp only [Below, PfFr] at hc ⊢; exact .inr (.inr ⟨by omega, by omega⟩))
    have nG : ∀ a, (a + 1400 ≤ g ∨ g + 1400 ≤ a) → ¬ (Rng (g + gTotalbytesOff) 8 a ∨ Rng (g + gGCdebtOff) 8 a) := by
      intro a ha; simp only [Rng, gTotalbytesOff, gGCdebtOff]; omega
    have hX4 : Lua.Vm.AtF.PushfI.Ok_T (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M4 o) := by fcx_ok
    have h29 : bytesT8 M4 (sp - 88) = BitVec.ofNat 64 (ts + 24) :=
      (bytesT8_congrT fun j _ => hst.keep _ (by simp only [Rng, Below, gTotalbytesOff, gGCdebtOff]; omega)).trans h88
    have h27 : bytesT8 M4 (sp - 56) = r :=
      (bytesT8_congrT fun j _ => (hst.keep _ (by simp only [Rng, Below, gTotalbytesOff, gGCdebtOff]; omega)).trans
        (hk12 _ (by simp only [Rng]; omega))).trans S.ra
    have h28 : bytesT8 M4 (sp - 64) = f.s0 :=
      (bytesT8_congrT fun j _ => (hst.keep _ (by simp only [Rng, Below, gTotalbytesOff, gGCdebtOff]; omega)).trans
        (hk12 _ (by simp only [Rng]; omega))).trans S.s0
    simp only [wrRet] at hret
    have h : SegSt 0x800030f8#64 (Lua.Vm.AtF.PushfI.r14 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M4 o))
        (ArmPay (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M4 o).m (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M4 o).o)
        c4 := by fcx_unfold; exact hret.repin (by pins_of hret)
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030f8_800030fc _ hX4 h29)
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030fc_80003110_1 _ hX4 h27 h28)
    refine ⟨_, acc, M4, ⟨?_, ?_, ?_, fun a ha => ?_⟩, ?_⟩
    · exact (bytesT8_congrT fun j _ => k4 _ (by simp only [Rng, gTotalbytesOff, gGCdebtOff, PfFr]; omega)).trans hv2
    · exact (k4 _ (by simp only [Rng, gTotalbytesOff, gGCdebtOff, PfFr]; omega)).trans htg2
    · exact (bytesT8_congrT fun j _ => k4 _ (by simp only [Rng, gTotalbytesOff, gGCdebtOff, PfFr]; omega)).trans htw2
    · simp only [not_or] at ha
      obtain ⟨h1, h2, h3, h4, h5⟩ := ha
      rw [k4 a (by simp only [not_or]; exact ⟨h3, h4, h5⟩), hk12 a (by
        simp only [PfFr, Rng] at h1 h2 h5 ⊢; omega)]
    · simp only [wrRet]
      fcx_unfold at h
      exact h.repin (by pins_of h)
  · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030dc_800030ec_t _ hX hT.Lg_w hb)
    obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
      (Lua.Vm.AtF.PushfI.at_800030fc_80003110 _ hX S.ra S.s0)
    refine ⟨_, acc, _, ⟨hv, htg, htw, fun a ha => hk11 a fun hc => ha ?_⟩, ?_⟩
    · rcases hc with hc | hc
      · exact .inl hc
      · exact .inr (.inl hc)
    · simp only [wrRet]
      fcx_unfold at h
      exact h.repin (by pins_of h)

/-- A word of `g`'s object `luaS_newlstr` does not write (not `GCdebt`,
`nuse`, `g->allgc`), as it was. -/
theorem PfStr.gw {m M3 : Mem} {sp L g top : Nat} {b : List UInt8} {seed : UInt32} {K X W : Nat → Prop}
    {cw : BitVec 8} {size hash head d nuse ts : Nat} {H H' : HeapIx}
    (hT : NlTab m L g top b seed K X W cw size hash head d nuse H) (hsp : 0x87800000 + 8192 ≤ sp)
    (hg : g + 1400 ≤ 0x87800000) (hs : PfStr m M3 sp g b seed K X W size hash nuse head H ts H') {a : Nat} (h1 : g ≤ a) (h2 : a < g + 1400)
    (hw : ¬ (Rng (g + 24) 8 a ∨ Rng (g + 56) 4 a ∨ Rng (g + 112) 8 a)) : bytesT1 M3 a = bytesT1 m a := by
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have hu := hT.new.g_in a h1 h2
  have hlo : heapStart + 16 ≤ a := Nat.le_of_not_lt fun hc => ChunkWalk.notInUse_lo hT.new.heap.walk a hc hu
  have hhi : a < heapEnd + 8 := Nat.lt_of_not_le fun hc =>
    ChunkWalk.notInUse_hi hT.new.heap.walk a (by have := hT.new.heap.top_le; have := hT.new.heap.brk_le; omega) hu
  have := hT.new.kg
  rcases hs with ⟨hh, -⟩ | hp
  · exact hh.keep a (by simp only [PfFr]; omega)
  · refine hp.keep a fun hc => ?_
    simp only [Rng] at hw
    rcases hc with hc | hc | hc | hc | hc | hc | hc
    · rcases hc with hc | hc
      · exact absurd hc.lo (by omega)
      · exact hc.2.2 hu
    · exact hp.fresh a hc.1 hc.2 hu
    all_goals simp only [Rng, PfFr] at hc; omega

/-- **`lua_pushfstring(L, "%I", i)`** (lane F1-20): the digits of `i`
interned (found or created, `PfStr`) and pushed at `L->top` (`PfPost`),
`getstr` of the string returned. -/
theorem pushfI_sum (hM : MallocR_Statement) (hI2S : IntegerToStr_Statement) (sp L g top : Nat) (i r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hst : FmtStatic m) (seed : UInt32)
    (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat) (H : HeapIx)
    (hT : NlTab m L g top (intU8 i) seed K X W cw size hash head d nuse H)
    (hgc : bytesT1 m (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd58#64⟩,
        ⟨Register.x12, i⟩] sp r f) (ArmPay m o))
      (fun c => ∃ ts M3 M H', PfStr m M3 sp g (intU8 i) seed K X W size hash nuse head H ts H' ∧
        PfPost M3 M sp L g top ts ∧ wrRet r sp (ts + 24) f M o c) := by
  intro c h
  pf_in hP
  have hn1 := (intBytes_len i).1
  have hn2 := (intBytes_len i).2
  obtain ⟨c1, s1, a3, a4, a5, a6, a7, h1⟩ := pf_cut sp L g top i r f m o hP c h
  obtain ⟨c2, s2, M2, hS, h2⟩ := pf_snp hI2S sp L g top i r f a3 a4 a5 a6 a7 m _ o hP hst (pfC_of (by omega)) c1 h1
  obtain ⟨c3, s3, ts, M3, H', hPT, hstr, h3⟩ :=
    pf_nl hM sp L g top i r f a3 a4 a5 a6 a7 m M2 o hP hS seed K X W cw size hash head d nuse H hT _ rfl c2 h2
  have hgc3 : bytesT1 M3 (g + gGcstpOff) = 0x1#8 :=
    (hstr.gw hT (by omega) (by omega) (by simp only [gGcstpOff]; omega) (by simp only [gGcstpOff]; omega)
      (by simp only [Rng, gGcstpOff]; omega)).trans hgc
  obtain ⟨c4, s4, M, hpost, hret⟩ := pf_ret sp L g top _ ts i r f a3 a4 a5 a6 a7 m M3 o hP hPT hn1 hn2 hgc3 hgal c3 h3
  exact ⟨c4, ((s1.trans s2).trans s3).trans s4, ts, M3, M, H', hstr, hpost, hret⟩

end Lua.Vm.Sim.Kit
