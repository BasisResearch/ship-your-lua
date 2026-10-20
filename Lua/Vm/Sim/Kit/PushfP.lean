import Lua.Vm.Sim.Kit.PushfI
import Lua.Vm.Sim.Kit.PtrFmt
import Lua.Vm.Sim.Kit.AtAlign
import Lua.Vm.AtF.PushfP

/-!
# `lua_pushfstring(L, "%s: %p", "function", print)` (lane F1-24)

`luaL_tolstring`'s default case on F1's light C function: `luaO_pushvfstring`
on `"%s: %p"` (`.rodata`): `strchr`, `addstr2buff` of the empty prefix; `'s'`:
`strlen` of the type name `"function"` and `addstr2buff` (`memcpy`'s word
path); `strchr` past it and `addstr2buff` of `": "` (`memcpy`'s byte path);
`'p'`: `snprintf(buf + 10, 32, "%p", print)` (a call node: `snprintfP_sum`);
the empty rest; `luaS_newlstr` of the twenty bytes `"function: 0x80022f18"`
(a call node: `newlstr_any_sum`, found or created), the push, `luaC_checkGC`
(the tail shared with `"%I"`, `pf_tail`). Its at-lemmas are generated
(`Lua/Vm/AtF/PushfP.lean`): the entry, the cuts after `strchr` (`C`) and at the
conversions (`K`, `J`, `P`), the returns from `snprintf` (`S`), `luaS_newlstr`
(`T`) and `luaC_step`. Every root's context is `pfpX` (`PushfI`'s layout, the
format's arguments literals), the cut's memory `PushfI`'s (`pfM1`, the same
prologue's stores).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The string -/

/-- `"function: 0x80022f18"`: what `luaL_tolstring` makes of `print`. -/
def fnU8 : List UInt8 :=
  [0x66, 0x75, 0x6e, 0x63, 0x74, 0x69, 0x6f, 0x6e, 0x3a, 0x20, 0x30, 0x78, 0x38, 0x30, 0x30, 0x32, 0x32, 0x66,
   0x31, 0x38]

theorem fnU8_length : fnU8.length = 20 := rfl

/-- The bytes `print` prints for a function (`binaryHost`'s `showBuiltin`). -/
theorem argBytes_fn : argBytes (.builtin .print) = fnU8.map fun c => BitVec.ofNat 8 c.toNat := by decide

/-! ## Contexts and `.rodata` -/

/-- Every root's context: `PushfI`'s layout (`pfX`), the format's arguments
(the type name, the pointer) literals, `s8` at the cut. -/
@[at_row] abbrev pfpX (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (M : Mem)
    (o : Array String) : FCx :=
  pfX [sp, L, g, top] r f 0#64 0#64 a4 a5 a6 a7 (pfS8 sp) M o

/-- **The `.rodata` words `lua_pushfstring(L, "%s: %p", …)` reads**: the
format `"%s: %p"` (its word, its bytes), `luaO_pushvfstring`'s conversion
table entries for `'s'` and `'p'`, the type name `"function"` (its words and
terminator), `"%p"`. -/
structure PfpRod (m : Mem) : Prop where
  fmt8 : bytesT8 m 0x8004fd68 = 0x7025203a7325#64
  f0 : bytesT1 m 0x8004fd68 = 0x25#8
  f1 : bytesT1 m 0x8004fd69 = 0x73#8
  f2 : bytesT1 m 0x8004fd6a = 0x3a#8
  f3 : bytesT1 m 0x8004fd6b = 0x20#8
  f4 : bytesT1 m 0x8004fd6c = 0x25#8
  f5 : bytesT1 m 0x8004fd6d = 0x70#8
  f6 : bytesT1 m 0x8004fd6e = 0x0#8
  jt_s : bytesT4 m 0x80052cc4 = 0xfffbf238#32
  jt_p : bytesT4 m 0x80052cb8 = 0xfffbf310#32
  kind8 : bytesT8 m 0x8004f290 = 0x6e6f6974636e7566#64
  kind8z : bytesT8 m 0x8004f298 = 0x0#64
  kindz : bytesT1 m 0x8004f298 = 0x0#8
  pfmt : bytesAt m 0x8004f408 3 = [0x25#8, 0x70#8, 0#8]

theorem pfpRod_of {m : Mem} (h : RodataRead m) : PfpRod m := by
  have e : ∀ a, Image.rodataBase ≤ a → a < Image.rodataBase + Image.rodataSize →
      bytesT1 m a = Image.rodataByte (a - Image.rodataBase) := fun a h1 h2 => by
    have := h (a - Image.rodataBase) (by omega)
    rwa [show Image.rodataBase + (a - Image.rodataBase) = a by omega] at this
  have hb : Image.rodataBase = 0x8004ecc8 := rfl
  have hs : Image.rodataSize = 55776 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0x8004fd68 : Nat) = Image.rodataBase + 0x10a0 by decide, At.rod8 h _ (by decide)]; decide
  any_goals (rw [e _ (by omega) (by omega)]; decide)
  · rw [show (0x80052cc4 : Nat) = Image.rodataBase + 0x3ffc by decide, rod4 h _ (by decide)]; decide
  · rw [show (0x80052cb8 : Nat) = Image.rodataBase + 0x3ff0 by decide, rod4 h _ (by decide)]; decide
  · rw [show (0x8004f290 : Nat) = Image.rodataBase + 0x5c8 by decide, At.rod8 h _ (by decide)]; decide
  · rw [show (0x8004f298 : Nat) = Image.rodataBase + 0x5d0 by decide, At.rod8 h _ (by decide)]; decide
  · simp only [bytesAt, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.map_append]
    rw [e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega)]
    decide

/-- `PfpRod` at a memory agreeing below the stack. -/
theorem PfpRod.congr {m M : Mem} (h : PfpRod m) (hk : ∀ a, a < 0x8005e720 → bytesT1 M a = bytesT1 m a) :
    PfpRod M where
  fmt8 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.fmt8
  f0 := (hk _ (by omega)).trans h.f0
  f1 := (hk _ (by omega)).trans h.f1
  f2 := (hk _ (by omega)).trans h.f2
  f3 := (hk _ (by omega)).trans h.f3
  f4 := (hk _ (by omega)).trans h.f4
  f5 := (hk _ (by omega)).trans h.f5
  f6 := (hk _ (by omega)).trans h.f6
  jt_s := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.jt_s
  jt_p := (bytesT4_congrT fun i _ => hk _ (by omega)).trans h.jt_p
  kind8 := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.kind8
  kind8z := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.kind8z
  kindz := (hk _ (by omega)).trans h.kindz
  pfmt := (bytesAt_congr fun j hj => hk _ (by omega)).trans h.pfmt

/-! ## From the entry to the cut after `strchr` -/

/-- The memory at the cut: the entry's with `lua_pushfstring`'s and
`luaO_pushvfstring`'s frames stored. -/
abbrev pfpM1 (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m : Mem)
    (o : Array String) : Mem :=
  pfM1 sp L g top r f 0x8004f290#64 0x80022f18#64 a4 a5 a6 a7 m o

/-- **From the entry to the cut** (`0x80011df8`, after `strchr`). -/
theorem pfp_cut (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hP : PfIn m sp L g top r) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd68#64⟩,
        ⟨Register.x12, 0x8004f290#64⟩, ⟨Register.x13, 0x80022f18#64⟩] sp r f) (ArmPay m o))
      (fun c => ∃ a4 a5 a6 a7, SegSt 0x80011df8#64
        (Lua.Vm.AtF.PushfP.r3 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM1 sp L g top r f a4 a5 a6 a7 m o) o))
        (ArmPay (pfpM1 sp L g top r f a4 a5 a6 a7 m o) o) c) := by
  intro c h
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  fat_pin h a4 14 Register.x14
  fat_pin h a5 15 Register.x15
  fat_pin h a6 16 Register.x16
  fat_pin h a7 17 Register.x17
  simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append] at h
  have h : SegSt 0x800030a4#64 (Lua.Vm.AtF.PushfP.r0 (pfX [sp, L, g, top] r f 0#64 0#64 a4 a5 a6 a7 0#64 m o))
      (ArmPay (pfX [sp, L, g, top] r f 0#64 0#64 a4 a5 a6 a7 0#64 m o).m
        (pfX [sp, L, g, top] r f 0#64 0#64 a4 a5 a6 a7 0#64 m o).o) c := by
    fcx_unfold; exact h.repin (by pins_of h)
  have hX : Lua.Vm.AtF.PushfP.Ok (pfX [sp, L, g, top] r f 0#64 0#64 a4 a5 a6 a7 0#64 m o) := by fcx_ok
  have R := pfpRod_of hP.rod
  have hc0 : bytesT8 m 0x8004fd68 = 0x7025203a7325#64 := R.fmt8
  have hc1 : bytesT1 m 0x8004fd68 = 0x25#8 := R.f0
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80011df8]
  exact ⟨_, acc, a4, a5, a6, a7, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-! ## The conversions: `'s'` and `'p'` (the cuts `C`, `K`, `J`, `P`) -/

section Stages

variable (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (o : Array String)

/-- The memory at the `'s'` conversion (`K`): the cut's, `addstr2buff`'s frame
of the empty prefix and the buffer's length `0` stored. -/
abbrev pfpM4 (M1 : Mem) : Mem := Lua.Vm.AtF.PushfP.m4 (pfpX sp L g top r f a4 a5 a6 a7 M1 o)
/-- The memory after `"function"` (`J`): its word at `sp - 408`, length `8`. -/
abbrev pfpM8 (M1 : Mem) : Mem :=
  Lua.Vm.AtF.PushfP.m8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o)
/-- The memory at the `'p'` conversion (`P`): `": "` at `sp - 400`, length `10`. -/
abbrev pfpM13 (M1 : Mem) : Mem :=
  Lua.Vm.AtF.PushfP.m13 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o)

end Stages

/-- A store chain of the stage memories read off its stores. -/
macro "pfp_keep" : tactic => `(tactic| (
  simp only [pfpM4, pfpM8, pfpM13, Lua.Vm.AtF.PushfP.m4, Lua.Vm.AtF.PushfP.m8, Lua.Vm.AtF.PushfP.m13,
    Lua.Vm.AtF.PushfP.m14, Lua.Vm.AtF.PushfP.m17, pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins]))

/-- **`K`'s memory off its stores** (`addstr2buff`'s frame `[sp - 520, sp - 464)`, the length). -/
theorem pfpM4_keep {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {a4 a5 a6 a7 : BitVec 64} {o : Array String}
    {M1 : Mem} (hsp : 1000 ≤ sp) :
    ∀ a, (a + 520 < sp ∨ (sp ≤ a + 464 ∧ a + 412 < sp) ∨ sp ≤ a + 408) →
      bytesT1 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) a = bytesT1 M1 a := by
  intro a ha; pfp_keep

/-- **`J`'s memory off its stores** (the frame, the length, `"function"`). -/
theorem pfpM8_keep {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {a4 a5 a6 a7 : BitVec 64} {o : Array String}
    {M1 : Mem} (hsp : 1000 ≤ sp) :
    ∀ a, (a + 520 < sp ∨ (sp ≤ a + 464 ∧ a + 412 < sp) ∨ sp ≤ a + 400) →
      bytesT1 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) a = bytesT1 M1 a := by
  intro a ha
  have e : bytesT1 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) a = bytesT1 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) a := by
    simp only [pfpM8, Lua.Vm.AtF.PushfP.m8, pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins]
  exact e.trans (pfpM4_keep hsp a (by omega))

/-- **`P`'s memory off its stores** (the frame, the length, `"function: "`). -/
theorem pfpM13_keep {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {a4 a5 a6 a7 : BitVec 64} {o : Array String}
    {M1 : Mem} (hsp : 1000 ≤ sp) :
    ∀ a, (a + 520 < sp ∨ (sp ≤ a + 464 ∧ a + 412 < sp) ∨ sp ≤ a + 398) →
      bytesT1 (pfpM13 sp L g top r f a4 a5 a6 a7 o M1) a = bytesT1 M1 a := by
  intro a ha
  have e : bytesT1 (pfpM13 sp L g top r f a4 a5 a6 a7 o M1) a = bytesT1 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) a := by
    simp only [pfpM13, Lua.Vm.AtF.PushfP.m13, pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins]
  exact e.trans (pfpM8_keep hsp a (by omega))

/-- A byte of a doubleword store, by its lane. -/
theorem fw1_wm8_lane {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (j : Nat) (hj : j < 8) (hx : x = a + j) :
    bytesT1 (writeMap8 m a d) x = d.extractLsb' (8 * j) 8 := by
  subst hx; simp only [bytesT1, getElem_writeMap8 m a d j hj, Option.getD_some]

/-- **The buffer at `P`**: `"function: "`. -/
theorem pfpM13_buf {sp L g top : Nat} {r : BitVec 64} {f : AbiFrame} {a4 a5 a6 a7 : BitVec 64} {o : Array String}
    {M1 : Mem} (hsp : 1000 ≤ sp) :
    ∀ j, j < 10 → bytesT1 (pfpM13 sp L g top r f a4 a5 a6 a7 o M1) (sp - 408 + j) =
      BitVec.ofNat 8 (fnU8.getD j 0).toNat := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  simp only [pfpM4, pfpM8, pfpM13, Lua.Vm.AtF.PushfP.m4, Lua.Vm.AtF.PushfP.m8, Lua.Vm.AtF.PushfP.m13,
    pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp (disch := omega) only [fw1_wm8, fw1_wm4, fw1_ins, fw1_same]
     first
     | decide
     | (rw [fw1_wm8_lane _ (by decide) (by omega)]; decide))


/-! ### The runs between the cuts -/

/-- **From the cut after `strchr` to the `'s'` conversion** (`K`): the empty
prefix's `addstr2buff` (`memcpy` of no bytes, both 8-aligned). -/
theorem pfp_toK (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m M1 : Mem)
    (o : Array String) (hP : PfIn m sp L g top r) (hC : PfC M1 m sp L r 0x8004f290#64 f) (c : Config)
    (h : SegSt 0x80011df8#64 (Lua.Vm.AtF.PushfP.r3 (pfpX sp L g top r f a4 a5 a6 a7 M1 o)) (ArmPay M1 o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80011e54#64
      (Lua.Vm.AtF.PushfP.r5 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have R := (pfpRod_of hP.rod).congr fun a ha => hC.low a (.inl (by omega))
  have hX : Lua.Vm.AtF.PushfP.Ok_C (pfpX sp L g top r f a4 a5 a6 a7 M1 o) := by fcx_ok
  have hc2 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 M1 o).m ((pfpX sp L g top r f a4 a5 a6 a7 M1 o).n 0 - 412) =
      0x0#32 := hC.blen
  have hc3 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 M1 o).m 0x8004fd69 = 0x73#8 := R.f1
  have hc4 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 M1 o).m 0x80052cc4 = 0xfffbf238#32 := R.jt_s
  have hg_4 : ((((0x8004fd68#64) ^^^ (BitVec.ofNat 64 ((pfpX sp L g top r f a4 a5 a6 a7 M1 o).n 0 - 408))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = false :=
    xor_al _ _ (by decide) (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
  have h : SegSt 0x80011df8#64 (Lua.Vm.AtF.PushfP.r3 (pfpX sp L g top r f a4 a5 a6 a7 M1 o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 M1 o).m (pfpX sp L g top r f a4 a5 a6 a7 M1 o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80011e54]
  exact ⟨_, acc, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-- **From the `'s'` conversion to the format's next piece** (`J`): `strlen`
of `"function"`, its `addstr2buff` (`memcpy`'s word path). -/
theorem pfp_toJ (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m M1 : Mem)
    (o : Array String) (hP : PfIn m sp L g top r) (hC : PfC M1 m sp L r 0x8004f290#64 f) (c : Config)
    (h : SegSt 0x80011e54#64
      (Lua.Vm.AtF.PushfP.r5 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r7 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have k4 := pfpM4_keep (sp := sp) (L := L) (g := g) (top := top) (r := r) (f := f) (a4 := a4) (a5 := a5)
    (a6 := a6) (a7 := a7) (o := o) (M1 := M1) (by omega)
  have R := (pfpRod_of hP.rod).congr fun a ha => (k4 a (.inl (by omega))).trans (hC.low a (.inl (by omega)))
  have hX : Lua.Vm.AtF.PushfP.Ok_K (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o) := by
    fcx_ok
  have hc5 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).n 0 - 48) = 0x8004f290#64 :=
    show bytesT8 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) (sp - 48) = 0x8004f290#64 from
      (bytesT8_congrT fun j _ => k4 _ (.inr (.inr (by omega)))).trans hC.argi
  have hc2 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).n 0 - 412) = 0x0#32 := by
    simp only [pfpM4, Lua.Vm.AtF.PushfP.m4, pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [fw4_same rfl]; decide
  have hc6 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004f290 =
      0x6e6f6974636e7566#64 := R.kind8
  have hc7 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004f298 =
      0x0#64 := R.kind8z
  have hc8 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004f298 =
      0x0#8 := R.kindz
  have hg_4 : ((((0x8004f290#64) ^^^ (BitVec.ofNat 64
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).n 0 - 408))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = false :=
    xor_al _ _ (by decide) (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
  have h : SegSt 0x80011e54#64
      (Lua.Vm.AtF.PushfP.r5 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).m
        (pfpX sp L g top r f a4 a5 a6 a7 (pfpM4 sp L g top r f a4 a5 a6 a7 o M1) o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80011e7c]
  exact ⟨_, acc, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-- **From the format's next piece to the `'p'` conversion** (`P`): `strchr`
past `": "`, its `addstr2buff` (`memcpy`'s byte path). -/
theorem pfp_toP (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m M1 : Mem)
    (o : Array String) (hP : PfIn m sp L g top r) (hC : PfC M1 m sp L r 0x8004f290#64 f) (c : Config)
    (h : SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r7 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80011f2c#64
      (Lua.Vm.AtF.PushfP.r9 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM13 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpM13 sp L g top r f a4 a5 a6 a7 o M1) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have k8 := pfpM8_keep (sp := sp) (L := L) (g := g) (top := top) (r := r) (f := f) (a4 := a4) (a5 := a5)
    (a6 := a6) (a7 := a7) (o := o) (M1 := M1) (by omega)
  have R := (pfpRod_of hP.rod).congr fun a ha => (k8 a (.inl (by omega))).trans (hC.low a (.inl (by omega)))
  have hX : Lua.Vm.AtF.PushfP.Ok_J (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o) := by
    fcx_ok
  have hc12 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).n 0 - 412) = 0x8#32 := by
    simp only [pfpM8, Lua.Vm.AtF.PushfP.m8, pfpX, pfX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    rw [fw4_same rfl]; decide
  have hc9 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004fd6a =
      0x3a#8 := R.f2
  have hc10 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004fd6b =
      0x20#8 := R.f3
  have hc11 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004fd6c =
      0x25#8 := R.f4
  have hc13 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x8004fd6d =
      0x70#8 := R.f5
  have hc14 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m 0x80052cb8 =
      0xfffbf310#32 := R.jt_p
  have hg_4 : ((((0x8004fd6a#64) ^^^ (BitVec.ofNat 64
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).n 0 - 400))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = true :=
    xor_mis _ _ (by decide) (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
      (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
  have h : SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r7 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).m
        (pfpX sp L g top r f a4 a5 a6 a7 (pfpM8 sp L g top r f a4 a5 a6 a7 o M1) o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80011f2c]
  exact ⟨_, acc, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-! ### `snprintf`, the empty rest, `luaS_newlstr` -/

/-- `luaO_pushvfstring`'s frame at `snprintf`'s call (`'p'`). -/
abbrev pfpSnFr (sp L : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 (sp - 40), 0x80052c1c#64, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440),
    BitVec.ofNat 64 (sp - 408), 0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x8004fd6c#64, 0x8004fd6a#64, f.s11⟩

/-- **From the `'p'` conversion to `snprintf`'s return** (`S`, `0x80011f50`):
`snprintf(buf + 10, 32, "%p", print)` (`snprintfP_sum`), the pointer's ten
characters and terminator at `sp - 398`. -/
theorem pfp_snp (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m M13 : Mem)
    (o : Array String) (hP : PfIn m sp L g top r) (hst : FmtStatic m)
    (low : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M13 a = bytesT1 m a)
    (hblen : bytesT4 M13 (sp - 412) = 0xa#32) (ha3 : bytesT8 M13 (sp - 40) = 0x80022f18#64) (c : Config)
    (h : SegSt 0x80011f2c#64 (Lua.Vm.AtF.PushfP.r9 (pfpX sp L g top r f a4 a5 a6 a7 M13 o)) (ArmPay M13 o) c) :
    ∃ c' M2, Steps c c' ∧ bytesAt M2 (sp - 398) 11 = ptrBytes ++ [0#8] ∧
      (∀ a, (a + 4560 ≤ sp ∨ sp ≤ a + 464) → (a < sp - 398 ∨ sp - 354 ≤ a) → bytesT1 M2 a = bytesT1 M13 a) ∧
      SegSt 0x80011f50#64 (Lua.Vm.AtF.PushfP.r12 (pfpX sp L g top r f a4 a5 a6 a7 M2 o)) (ArmPay M2 o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.PushfP.Ok_P (pfpX sp L g top r f a4 a5 a6 a7 M13 o) := by fcx_ok
  have hc15 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 M13 o).m ((pfpX sp L g top r f a4 a5 a6 a7 M13 o).n 0 - 412) =
      0xa#32 := hblen
  have hc16 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 M13 o).m ((pfpX sp L g top r f a4 a5 a6 a7 M13 o).n 0 - 40) =
      0x80022f18#64 := ha3
  have h : SegSt 0x80011f2c#64 (Lua.Vm.AtF.PushfP.r9 (pfpX sp L g top r f a4 a5 a6 a7 M13 o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 M13 o).m (pfpX sp L g top r f a4 a5 a6 a7 M13 o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80034de0]
  have lowR : ∀ a, a < 0x8005e720 → bytesT1 M13 a = bytesT1 m a := fun a ha => low a (.inl (by omega))
  have hIn : PtrFmtIn M13 (sp - 464) (sp - 398) 0x8004f408 0x80011f50#64 := {
    fmtb := (bytesAt_congr fun j hj => lowR _ (by omega)).trans (pfpRod_of hP.rod).pfmt
    f_lo := by decide, f_hi := by decide, ra := by decide
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, b_lo := by omega, b_ap := .inr (by omega)
    b_hi := by omega
    stat := hst.congr lowR
    rod := (ptrRod_of hP.rod).congr lowR }
  fcx_unfold at h
  obtain ⟨c2, s2, M2, hret, hbytes, hkeep⟩ := snprintfP_sum (sp - 464) (sp - 398) 0x8004f408 0x80011f50#64
    (pfpSnFr sp L f) M13 o hIn _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  simp only [wrRet] at hret
  exact ⟨c2, M2, acc.trans s2, hbytes, fun a h1 h2 => hkeep a (by omega) (by omega),
    by fcx_unfold; exact hret.repin (by pins_of hret)⟩

/-- The memory at the empty rest (`J2`): the buffer's length `20` stored. -/
abbrev pfpM14 (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (o : Array String)
    (M2 : Mem) : Mem :=
  Lua.Vm.AtF.PushfP.m14 (pfpX sp L g top r f a4 a5 a6 a7 M2 o)

/-- **From `snprintf`'s return to the empty rest** (`J2`): `addsize`. -/
theorem pfp_toJ2 (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame) (a4 a5 a6 a7 : BitVec 64) (m M2 : Mem)
    (o : Array String) (hP : PfIn m sp L g top r) (hblen : bytesT4 M2 (sp - 412) = 0xa#32) (c : Config)
    (h : SegSt 0x80011f50#64 (Lua.Vm.AtF.PushfP.r12 (pfpX sp L g top r f a4 a5 a6 a7 M2 o)) (ArmPay M2 o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r13 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o))
      (ArmPay (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.PushfP.Ok_S (pfpX sp L g top r f a4 a5 a6 a7 M2 o) := by fcx_ok
  have hc15 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 M2 o).m ((pfpX sp L g top r f a4 a5 a6 a7 M2 o).n 0 - 412) =
      0xa#32 := hblen
  have h : SegSt 0x80011f50#64 (Lua.Vm.AtF.PushfP.r12 (pfpX sp L g top r f a4 a5 a6 a7 M2 o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 M2 o).m (pfpX sp L g top r f a4 a5 a6 a7 M2 o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80011e7c]
  exact ⟨_, acc, by fcx_unfold at h ⊢; exact h.repin (by pins_of h)⟩

/-- `pushstr`'s frame at `luaS_newlstr`'s call (`"%s: %p"`'s empty rest). -/
abbrev pfpNlFr (sp L top : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 top, 0x25#64, 0x2a#64, BitVec.ofNat 64 (sp - 440), BitVec.ofNat 64 (sp - 408),
    0xc6#64, BitVec.ofNat 64 L, pfS8 sp, 0x0#64, 0x8004fd6e#64, f.s11⟩

/-- **The buffer's twenty bytes** from `"function: "` and `snprintf`'s ten. -/
theorem pfp_bytes {M : Mem} {sp : Nat} (hsp : 408 ≤ sp)
    (h1 : ∀ j, j < 10 → bytesT1 M (sp - 408 + j) = BitVec.ofNat 8 (fnU8.getD j 0).toNat)
    (h2 : bytesAt M (sp - 398) 11 = ptrBytes ++ [0#8]) :
    ∀ j, j < fnU8.length → bytesT1 M (sp - 408 + j) = BitVec.ofNat 8 (fnU8.getD j 0).toNat := by
  intro j hj
  rw [fnU8_length] at hj
  by_cases hj10 : j < 10
  · exact h1 j hj10
  · have e := bytesAt_get h2 (j := j - 10) (by omega)
    rw [show sp - 398 + (j - 10) = sp - 408 + j by omega] at e
    rw [e]
    have : j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **From the empty rest to `luaS_newlstr`'s return** (`T`, `0x80011ec0`):
`addstr2buff` of nothing (`memcpy`'s byte path), `clearbuff`'s
`luaS_newlstr` of the twenty bytes (`pf_newlstr`). -/
theorem pfp_nl (hM : MallocR_Statement) (sp L g top : Nat) (r : BitVec 64) (f : AbiFrame)
    (a4 a5 a6 a7 : BitVec 64) (m M2 : Mem) (o : Array String) (hP : PfIn m sp L g top r)
    (hS : PfSlots M2 sp L r f) (low2 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M2 a = bytesT1 m a)
    (hb : ∀ j, j < fnU8.length → bytesT1 M2 (sp - 408 + j) = BitVec.ofNat 8 (fnU8.getD j 0).toNat)
    (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat)
    (H : HeapIx) (hT : NlTab m L g top fnU8 seed K X W cw size hash head d nuse H) (n : Nat) (i a3 : BitVec 64)
    (c : Config)
    (h : SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r13 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o))
      (ArmPay (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o) c) :
    ∃ c' ts M3 H', Steps c c' ∧ PfT M3 sp L g top ts r f ∧
      PfStr m M3 (PfFr sp) g fnU8 seed K X W size hash nuse head H ts H' ∧
      SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfP.r16 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o)) (ArmPay M3 o) c' := by
  pf_in hP
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have k14 : ∀ a, (a + 1 ≤ sp - 412 ∨ sp - 408 ≤ a) →
      bytesT1 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) a = bytesT1 M2 a := by
    intro a ha
    simp only [pfpM14, Lua.Vm.AtF.PushfP.m14, pfpX, pfX, FCx.mk', List.getD_cons_zero]
    simp (disch := omega) only [fw1_wm4]
  have R := (pfpRod_of hP.rod).congr fun a ha => (k14 a (.inl (by omega))).trans (low2 a (.inl (by omega)))
  have hX : Lua.Vm.AtF.PushfP.Ok_J
      (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o) := by fcx_ok
  have hc17 : bytesT1 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).m 0x8004fd6e =
      0x0#8 := R.f6
  have hc18 : bytesT4 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 0 - 412) = 0x14#32 := by
    simp only [pfpM14, Lua.Vm.AtF.PushfP.m14, pfpX, pfX, FCx.mk', List.getD_cons_zero]
    rw [fw4_same rfl]; decide
  have hc19 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 0 - 424) =
      BitVec.ofNat 64 ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 1) :=
    show bytesT8 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) (sp - 424) = BitVec.ofNat 64 L from
      (bytesT8_congrT fun j _ => k14 _ (.inl (by omega))).trans hS.buffL
  have hc20 : bytesT8 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).m
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 1 + 16) =
      BitVec.ofNat 64 ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 3) :=
    show bytesT8 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) (L + 16) = BitVec.ofNat 64 top from
      (bytesT8_congrT fun j _ => (k14 _ (.inl (by omega))).trans (low2 _ (.inl (by omega)))).trans hP.top_w
  have hg_4 : ((((0x8004fd6e#64) ^^^ (BitVec.ofNat 64
      ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 0 - 388))) &&&
      sign_extend (m := 64) (0x007#12)) != (0#64)) = true :=
    xor_mis _ _ (by decide) (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
      (by simp only [pfpX, pfX, FCx.mk', List.getD_cons_zero]; omega)
  have hg_2 : zopz0zKzJ_u
      (BitVec.ofNat 64 ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 0 - 388))
      (BitVec.ofNat 64 ((pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).n 0 - 388)) =
      true := uge_self _
  have h : SegSt 0x80011e7c#64
      (Lua.Vm.AtF.PushfP.r13 (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o))
      (ArmPay (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).m
        (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.PushfP h acc until [0x80017694]
  generalize hM17 : Lua.Vm.AtF.PushfP.m17
    (pfpX sp L g top r f a4 a5 a6 a7 (pfpM14 sp L g top r f a4 a5 a6 a7 o M2) o) = M17 at h
  have k17 : ∀ a, (a + 520 < sp + 0 ∨ (sp - 464 ≤ a ∧ a < sp - 412) ∨ sp - 408 ≤ a) →
      bytesT1 M17 a = bytesT1 M2 a := by
    intro a ha
    rw [← hM17]
    simp only [pfpM14, Lua.Vm.AtF.PushfP.m14, Lua.Vm.AtF.PushfP.m17, pfpX, pfX, FCx.mk', List.getD_cons_zero]
    simp (disch := omega) only [fw1_wm8, fw1_wm4]
  have low17 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M17 a = bytesT1 m a := fun a ha =>
    (k17 a (by omega)).trans (low2 a ha)
  fcx_unfold at h
  obtain ⟨c2, s2, ts, M3, H', hPT, hstr, hret⟩ := pf_newlstr hM sp L g top r f (pfpNlFr sp L top f) m M17 o hP
    (hS.congr (by omega) fun a ha => k17 a (by omega)) low17 fnU8 (by rw [fnU8_length]; omega)
    (by rw [fnU8_length]; omega) (fun j hj => (k17 _ (by omega)).trans (hb j hj))
    seed K X W cw size hash head d nuse H hT _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append, fnU8_length]
      exact h.repin (by pins_of h))
  simp only [wrRet] at hret
  exact ⟨c2, ts, M3, H', acc.trans s2, hPT, hstr, by fcx_unfold; exact hret.repin (by pins_of hret)⟩

/-- **From `luaS_newlstr`'s return to `lua_pushfstring`'s** (`"%s: %p"`):
`pf_tail` on this module's rows. -/
theorem pfp_ret (sp L g top n ts : Nat) (i r : BitVec 64) (f : AbiFrame) (a3 a4 a5 a6 a7 : BitVec 64)
    (m M3 : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hT : PfT M3 sp L g top ts r f)
    (hgc : bytesT1 M3 (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x80011ec0#64 (Lua.Vm.AtF.PushfP.r16 (pfX3 sp L g top n ts r f i a3 a4 a5 a6 a7 M3 o))
        (ArmPay M3 o))
      (fun c => ∃ M, PfPost M3 M sp L g top ts ∧ wrRet r sp (ts + 24) f M o c) := by
  pf_tail Lua.Vm.AtF.PushfP r16 r21 m18 m19

/-- **`lua_pushfstring(L, "%s: %p", "function", print)`** (lane F1-24): the
twenty bytes `"function: 0x80022f18"` interned (found or created, `PfStr`)
and pushed at `L->top` (`PfPost`), `getstr` of the string returned. -/
theorem pushfP_sum (hM : MallocR_Statement) (sp L g top : Nat) (r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (hP : PfIn m sp L g top r) (hst : FmtStatic m) (seed : UInt32)
    (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat) (H : HeapIx)
    (hT : NlTab m L g top fnU8 seed K X W cw size hash head d nuse H)
    (hgc : bytesT1 m (g + gGcstpOff) = 0x1#8) (hgal : g % 8 = 0) :
    Triple (SegSt 0x800030a4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd68#64⟩,
        ⟨Register.x12, 0x8004f290#64⟩, ⟨Register.x13, 0x80022f18#64⟩] sp r f) (ArmPay m o))
      (fun c => ∃ ts M3 M H', PfStr m M3 (PfFr sp) g fnU8 seed K X W size hash nuse head H ts H' ∧
        PfPost M3 M sp L g top ts ∧ PfTs M ts fnU8.length ∧ wrRet r sp (ts + 24) f M o c) := by
  intro c h
  pf_in hP
  obtain ⟨c1, s1, a4, a5, a6, a7, h1⟩ := pfp_cut sp L g top r f m o hP c h
  have hC : PfC (pfpM1 sp L g top r f a4 a5 a6 a7 m o) m sp L r 0x8004f290#64 f := pfC_of (by omega)
  have ha3 : bytesT8 (pfpM1 sp L g top r f a4 a5 a6 a7 m o) (sp - 40) = 0x80022f18#64 := by
    simp only [pfpM1]; pf_m1
  obtain ⟨c2, s2, h2⟩ := pfp_toK sp L g top r f a4 a5 a6 a7 m _ o hP hC c1 h1
  obtain ⟨c3, s3, h3⟩ := pfp_toJ sp L g top r f a4 a5 a6 a7 m _ o hP hC c2 h2
  obtain ⟨c4, s4, h4⟩ := pfp_toP sp L g top r f a4 a5 a6 a7 m _ o hP hC c3 h3
  have k13 := pfpM13_keep (sp := sp) (L := L) (g := g) (top := top) (r := r) (f := f) (a4 := a4) (a5 := a5)
    (a6 := a6) (a7 := a7) (o := o) (M1 := pfpM1 sp L g top r f a4 a5 a6 a7 m o) (by omega)
  have low13 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) →
      bytesT1 (pfpM13 sp L g top r f a4 a5 a6 a7 o (pfpM1 sp L g top r f a4 a5 a6 a7 m o)) a = bytesT1 m a :=
    fun a ha => (k13 a (by omega)).trans (hC.low a (by omega))
  have hb13 : bytesT4 (pfpM13 sp L g top r f a4 a5 a6 a7 o (pfpM1 sp L g top r f a4 a5 a6 a7 m o)) (sp - 412) =
      0xa#32 := by
    simp only [pfpM13, Lua.Vm.AtF.PushfP.m13, pfpX, pfX, FCx.mk', List.getD_cons_zero]
    rw [fw4_same rfl]; decide
  obtain ⟨c5, M2, s5, hptr, k2, h5⟩ := pfp_snp sp L g top r f a4 a5 a6 a7 m _ o hP hst low13 hb13
    ((bytesT8_congrT fun j _ => k13 _ (by omega)).trans ha3) c4 h4
  have hb2 : bytesT4 M2 (sp - 412) = 0xa#32 :=
    (bytesT4_congrT fun j _ => k2 _ (by omega) (by omega)).trans hb13
  obtain ⟨c6, s6, h6⟩ := pfp_toJ2 sp L g top r f a4 a5 a6 a7 m M2 o hP hb2 c5 h5
  have low2 : ∀ a, (a + 8192 ≤ sp ∨ sp ≤ a) → bytesT1 M2 a = bytesT1 m a := fun a ha =>
    (k2 a (by omega) (by omega)).trans (low13 a ha)
  have hS2 : PfSlots M2 sp L r f :=
    (hC.slots.congr (by omega) fun a ha => k13 a (by omega)).congr (by omega)
      fun a ha => k2 a (by omega) (by omega)
  have hbuf := pfpM13_buf (sp := sp) (L := L) (g := g) (top := top) (r := r) (f := f) (a4 := a4) (a5 := a5)
    (a6 := a6) (a7 := a7) (o := o) (M1 := pfpM1 sp L g top r f a4 a5 a6 a7 m o) (by omega)
  have hb : ∀ j, j < fnU8.length → bytesT1 M2 (sp - 408 + j) = BitVec.ofNat 8 (fnU8.getD j 0).toNat :=
    pfp_bytes (by omega) (fun j hj => (k2 _ (by omega) (by omega)).trans (hbuf j hj)) hptr
  obtain ⟨c7, ts, M3, H', s7, hPT, hstr, h7⟩ := pfp_nl hM sp L g top r f a4 a5 a6 a7 m M2 o hP hS2 low2 hb
    seed K X W cw size hash head d nuse H hT 20 0#64 0#64 c6 h6
  have hgc3 : bytesT1 M3 (g + gGcstpOff) = 0x1#8 :=
    (hstr.gw (a := g + gGcstpOff) (F := PfFr sp) hT (by omega) (fun a ha => by simp only [PfFr] at ha; omega)
      (by simp only [gGcstpOff]; omega) (by simp only [gGcstpOff]; omega)
      (by simp only [Rng, gGcstpOff]; omega)).trans hgc
  obtain ⟨c8, s8, M, hpost, hret⟩ := pfp_ret sp L g top 20 ts 0#64 r f 0#64 a4 a5 a6 a7 m M3 o hP hPT hgc3 hgal c7 h7
  exact ⟨c8, (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8), ts, M3, M, H', hstr,
    hpost, pfTs_of hT (by rw [fnU8_length]; omega) (by omega) (by omega) (by omega) (by omega) hPT hstr hpost, hret⟩

end Lua.Vm.Sim.Kit
