import Lua.Vm.Sim.Kit.Run
import Vsa.Sim.Muldi3Spec

/-!
# Whole-function summaries of loop-free helpers (lane float-m0, FLOAT-DESIGN.md §3 level 1)

`scripts/gen_lua_fn.py` folds a loop-free helper (`__floatsidf`, `__eqdf2`,
`__adddf3`, …) over its generated helper segments (`Lua.Vm.Arms.seg_*`,
`scripts/gen_lua_arms.py` `HELPERS`): one **node** per segment entry, its
lifted function `N_<pc>` (the node's result as a function of its live
registers: an `if` per branch, the successor's function applied to the
segment's post-state otherwise) and its node lemma `n_<pc>` (the segment,
then the successor's node lemma), proved in its own declaration. The fold is
linear in the segments, not in the paths (`__adddf3`: 497 paths, 210
segments). This file holds what every generated file uses:

* `memPatch m m' lo n`: `m` with the window `[lo, lo + n)` taken from `m'`.
  A helper with a stack frame (`addi sp, sp, -F`) writes only its frame
  `[sp - F, sp)`, on some paths and not others; its summary's memory is
  `memPatch m M (sp - F) F`, which is `m` outside the frame by construction
  (`getElem?_memPatch_out`), whatever the path (`memPatch_self`,
  `memPatch_wm8_in`);
* `SFrame`: the callee-saved registers but `sp` (a framed helper's summary
  states `sp` as `BitVec.ofNat 64 s`, so that its frame's addresses are
  `kit_disch` arithmetic over `s`), and `FnSp s F`, the stack facts a frame
  of `F` bytes below `s` needs;
* the epilogue's two facts: `sp` restored (`fn_sp_restore`) and the reloaded
  `ra` (`fn_tgt`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## The frame window -/

/-- **`m` with the window `[lo, lo + n)` taken from `m'`** (each byte present
or absent as in `m'`). -/
def memPatch (m m' : Mem) (lo : Nat) : Nat → Mem
  | 0 => m
  | n + 1 =>
    match m'[lo + n]? with
    | some b => (memPatch m m' lo n).insert (lo + n) b
    | none => (memPatch m m' lo n).erase (lo + n)

theorem getElem?_memPatch (m m' : Mem) (lo x : Nat) :
    ∀ n, (memPatch m m' lo n)[x]? = if lo ≤ x ∧ x < lo + n then m'[x]? else m[x]?
  | 0 => by rw [if_neg (by omega)]; rfl
  | n + 1 => by
    have ih := getElem?_memPatch m m' lo x n
    simp only [memPatch]
    split
    · rename_i b hb
      rw [Std.ExtHashMap.getElem?_insert]
      by_cases e : lo + n = x
      · subst e; simp [hb]
      · rw [if_neg (by simpa using e), ih]
        by_cases h1 : lo ≤ x ∧ x < lo + n
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · rename_i hb
      rw [Std.ExtHashMap.getElem?_erase]
      by_cases e : lo + n = x
      · subst e; simp [hb]
      · rw [if_neg (by simpa using e), ih]
        by_cases h1 : lo ≤ x ∧ x < lo + n
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]

/-- Outside the window, the base memory. -/
theorem getElem?_memPatch_out {m m' : Mem} {lo n x : Nat} (h : x < lo ∨ lo + n ≤ x) :
    (memPatch m m' lo n)[x]? = m[x]? := by
  rw [getElem?_memPatch, if_neg (by omega)]

/-- Patching a memory with itself. -/
theorem memPatch_self (m : Mem) (lo n : Nat) : memPatch m m lo n = m :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch]; split <;> rfl

/-- A store inside the window is overwritten by the patch. -/
theorem memPatch_wm8_in {m M : Mem} {lo n a : Nat} {d : BitVec (8 * 8)} (h1 : lo ≤ a)
    (h2 : a + 8 ≤ lo + n) : memPatch (writeMap8 m a d) M lo n = memPatch m M lo n :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch, getElem?_memPatch]
    split
    · rfl
    · exact getElem?_writeMap8_out m a d x (by omega)

/-- An 8-byte read outside the window. -/
theorem bytesT8_memPatch_out {m m' : Mem} {lo n x : Nat} (h : x + 8 ≤ lo ∨ lo + n ≤ x) :
    bytesT8 (memPatch m m' lo n) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_memPatch_out (by omega)

/-- A byte read outside the window. -/
theorem bytesT1_memPatch_out {m m' : Mem} {lo n x : Nat} (h : x < lo ∨ lo + n ≤ x) :
    bytesT1 (memPatch m m' lo n) x = bytesT1 m x := by
  simp only [bytesT1, getElem?_memPatch_out h]

/-- Congruence of a patch. -/
theorem memPatch_congr {m₁ m₂ M₁ M₂ : Mem} {lo₁ lo₂ n : Nat} (hm : m₁ = m₂) (hM : M₁ = M₂)
    (hl : lo₁ = lo₂) : memPatch m₁ M₁ lo₁ n = memPatch m₂ M₂ lo₂ n := by subst hm hM hl; rfl

/-! ## Frames -/

/-- **The callee-saved registers but `sp`**: `gp`, `s0 … s11`. -/
structure SFrame where
  (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64)

/-- A frame to be read off a call site's pins (`pins_of`). -/
macro "sframe?" : term => `(SFrame.mk _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- **A stack pointer with room for an `F`-byte frame below it**: the frame
is RAM above the HTIF mailbox (the stores' `hlo`/`hwin`/`hht` side
conditions), below `2^32` (`hhi`), 8-aligned (`hal`). -/
structure FnSp (s F : Nat) : Prop where
  lo : tohostAddr + 16 + F ≤ s
  hi : s ≤ 0x100000000
  al : s % 8 = 0

/-- The epilogue's `addi sp, sp, F` undoes the prologue's `addi sp, sp, -F`. -/
theorem fn_sp_restore (s : Nat) (a b : BitVec 12)
    (h : sign_extend (m := 64) a + sign_extend (m := 64) b = 0#64) :
    (BitVec.ofNat 64 s + sign_extend (m := 64) a) + sign_extend (m := 64) b = BitVec.ofNat 64 s := by
  rw [BitVec.add_assoc, h, BitVec.add_zero]

/-- `ret` through the reloaded `ra` (`ld ra, K(sp)`): the saved return
address `r`, 4-aligned. -/
theorem fn_tgt {m : Mem} {a : Nat} {r : BitVec 64} (hra : bytesT8 m a = r) (hr : r.toNat % 4 = 0) :
    Sail.BitVec.update ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8))) +
      sign_extend (m := 64) (0x000#12)) 0 0#1 = r := by
  rw [sext64_id, hra]; exact Vsa.Sim.ret_tgt r hr

/-- `ret` through the caller's `ra`. -/
theorem fn_tgt0 {r : BitVec 64} (hr : r.toNat % 4 = 0) :
    Sail.BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1 = r := Vsa.Sim.ret_tgt r hr

/-- The read-back of the saved `ra` through the prologue's later stores. -/
theorem bytesT8_wm8_same {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x = a) :
    bytesT8 (writeMap8 m a d) x = d := by subst h; exact bytesT8_writeMap8 m x d

theorem bytesT8_wm8_far {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_writeMap8_out m a d (x + i) (by omega)

/-- `.rodata` survives a store above the HTIF mailbox. -/
theorem RodataRead.wm8 {m : Mem} (h : RodataRead m) {a : Nat} {d : BitVec (8 * 8)}
    (ha : tohostAddr ≤ a) : RodataRead (writeMap8 m a d) := fun o ho => by
  have := Lua.Vm.Sim.rodata_below_tohost
  rw [bytesT1_writeMap8_out m a d (by omega)]
  exact h o ho

/-- `.rodata` read through a patch above the HTIF mailbox. -/
theorem RodataRead.patch {m M : Mem} (h : RodataRead m) {lo n : Nat} (hl : tohostAddr ≤ lo) :
    RodataRead (memPatch m M lo n) := fun o ho => by
  have := Lua.Vm.Sim.rodata_below_tohost
  rw [bytesT1_memPatch_out (by omega)]
  exact h o ho

set_option hygiene false in
/-- The stack facts of `hs : FnSp s F` for `kit_disch`. -/
macro "fn_sp_facts" : tactic => `(tactic| (
  have := hs.lo; have := hs.hi; have := hs.al
  have hTH : tohostAddr = 0x8005c6c0 := rfl))

/-- The saved `ra` read back through the prologue's stores. -/
macro "fn_ra" : tactic => `(tactic| first
  | assumption
  | (rw [bytesT8_wm8_same (by kit_disch), sdData_id])
  | (simp (disch := kit_disch) only [bytesT8_wm8_far]
     first
     | assumption
     | (rw [bytesT8_wm8_same (by kit_disch), sdData_id])))

/-- `.rodata` through the prologue's stores. -/
macro "fn_rod" : tactic => `(tactic| (
  repeat (first | assumption | (refine RodataRead.wm8 ?_ (by kit_disch)))))

/-- A not-taken guard from the case split's negation. -/
theorem fn_false {b : Bool} (h : ¬ b = true) : b = false := by simpa using h

end Lua.Vm.Sim
