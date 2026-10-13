import Lua.Vm.Sim.Kit.Fn

/-!
# Call nodes to framed callees (lane float-sf3)

`scripts/gen_lua_fn.py` lifts a routine whose callees are routines with
proved summaries (`floor` calls `__adddf3` and `__gedf2`): a call node runs
the callee's summary (`Lua.Vm.Fn.<R>.sum`) and the lifted function applies
the callee's lifted function (`<R>.F`, its value; `<R>.Fm`, a framed
callee's frame). This file holds what such a fold uses beyond `Kit/Fn.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## Framed callees (lane float-sf3: call nodes to proved summaries)

A framed routine (`floor`, `__muldf3`, …) that calls a framed routine
(`__adddf3`) passes it `sp - F` as its `s`: the callee's window
`[s - F - F', s - F)` lies inside the caller's (`FnSp s W`, `F + F' ≤ W`),
so the caller's summary patches `W` bytes and the callee's patch is absorbed
(`memPatch_patch_in`). -/

/-- The callee's stack facts inside the caller's window. -/
theorem fn_sp_in {s W F F' : Nat} (hs : FnSp s W) (h : F + F' ≤ W) (hF : F % 8 = 0) :
    FnSp (s - F) F' :=
  ⟨by have := hs.lo; omega, by have := hs.hi; omega, by have := hs.al; omega⟩

/-- The caller's `sp` inside its frame, `s + sext (-F)`, as the `Nat` `s - F`. -/
theorem fn_sp_nat (s : Nat) (a : BitVec 12) (k : Nat)
    (ha : sign_extend (m := 64) a = BitVec.ofNat 64 (2 ^ 64 - k)) (hk : k ≤ s) (hk2 : k ≤ 2 ^ 64)
    (hs : s < 2 ^ 64) :
    BitVec.ofNat 64 s + sign_extend (m := 64) a = BitVec.ofNat 64 (s - k) := by
  rw [ha, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- **A pin put in front** (found first by `pins_of`): the caller's `sp` as
the callee's `BitVec.ofNat 64 (s - F)` at a framed call, and back after it. -/
theorem _root_.Vsa.Sim.SegSt.pin_sp {pc : BitVec 64} {L : List Pin} {P : MState → Prop}
    {c : Config} (h : SegSt pc L P c) {v : BitVec 64}
    (hv : c.σ.regs.get? Register.x2 = some v) : SegSt pc (⟨Register.x2, v⟩ :: L) P c :=
  ⟨h.good, h.pcAt, ⟨hv, h.pins⟩, h.minstret, h.tick, h.extra⟩

/-- A framed callee's patch inside the caller's window is overwritten by it. -/
theorem memPatch_patch_in {m M M' : Mem} {lo n lo' n' : Nat} (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    memPatch (memPatch m M' lo' n') M lo n = memPatch m M lo n :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch (memPatch m M' lo' n') M lo x n, getElem?_memPatch m M lo x n]
    split
    · rfl
    · exact getElem?_memPatch_out (by omega)

open Lean Elab Tactic Meta in
/-- `assumption` by syntactic equality (never a definitional unfolding of the
memory's stores, nor of the reads' addresses). -/
elab "fn_assumption" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type) == t then
      closeMainGoal `fn_assumption (mkFVar d.fvarId)
      return
  throwError "fn_assumption: no hypothesis is the goal"

open Lean Elab Tactic Meta in
/-- The head of a `RodataRead`/`bytesT8` goal's memory: `0` a store, `1` a
framed callee's patch, `2` anything else. -/
def fnMemHead (t : Expr) : MetaM Nat := do
  let t ← instantiateMVars t
  let m? : Option Expr :=
    if t.isAppOfArity ``Lua.Vm.Sim.RodataRead 1 then some t.appArg!
    else match t.eq? with
      | some (_, l, _) => if l.isAppOfArity ``Vsa.Sim.bytesT8 2 then some (l.getArg! 0) else none
      | none => none
  match m? with
  | some m =>
    if m.isAppOfArity ``Vsa.Sim.writeMap8 3 then return 0
    if m.isAppOfArity ``Lua.Vm.Sim.memPatch 4 then return 1
    return 2
  | none => return 2

open Lean Elab Tactic Meta in
/-- `.rodata` through the stores and the framed callees' patches, stripped by
their head symbols, then the hypothesis that states it. -/
elab "fn_rod_patch" : tactic => withMainContext do
  let mut go := true
  while go do
    match ← fnMemHead (← getMainTarget) with
    | 0 => evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.wm8 ?_ (by kit_disch)))
    | 1 => evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.patch ?_ (by kit_disch)))
    | _ => go := false
  evalTactic (← `(tactic| fn_assumption))

open Lean Elab Tactic Meta in
/-- A frame slot (the saved `ra`, a forwarded spill) read back through the
stores and the framed callees' patches after it: the store that wrote it
(`bytesT8_wm8_same`), or the hypothesis that states it. -/
elab "fn_ra_patch" : tactic => withMainContext do
  let mut go := true
  while go do
    if (← getUnsolvedGoals).isEmpty then return
    match ← fnMemHead (← getMainTarget) with
    | 0 => evalTactic (← `(tactic| simp (disch := kit_disch) only [Lua.Vm.Sim.bytesT8_wm8_same,
        Lua.Vm.Sim.bytesT8_wm8_far, Lua.Vm.Sim.sdData_id]))
    | 1 => evalTactic (← `(tactic| simp (disch := kit_disch) only [Lua.Vm.Sim.bytesT8_memPatch_out]))
    | _ =>
      evalTactic (← `(tactic| fn_assumption))
      go := false

/-! ## Jump tables (lane float-sf4)

A class switch compiles to `jr` through a table of 32-bit offsets in
`.rodata` (`__divdf3`'s two). `gen_lua_fn.py` (`JUMPS`) makes the `jr` node
case on the index the node facts bound: the predecessor's not-taken bound
check gives `hjt : idx.toNat < n` (`fn_jt_bound`), `fn_jt_split`/`fn_jt_zero`
enumerate the index, and `fn_jt_tgt` reads entry `k`'s target. -/

/-- Byte `i` of the `.rodata` word at absolute address `a`. -/
def rodB (a i : Nat) : BitVec 8 := Image.rodataByte (a - Image.rodataBase + i)

/-- The `.rodata` word at absolute address `a`, as `lw` reads it. -/
def rodWord (a : Nat) : BitVec 32 :=
  (((rodB a 3).append (rodB a 2)).append (rodB a 1)).append (rodB a 0)

theorem rodWord_eq {m : Mem} (h : RodataRead m) {a : Nat} (hlo : Image.rodataBase ≤ a)
    (hhi : a + 4 ≤ Image.rodataBase + Image.rodataSize) : bytesT4 m a = rodWord a := by
  have hb : ∀ i, i < 4 → (m[a + i]?).getD 0 = rodB a i := by
    intro i hi
    have := h (a - Image.rodataBase + i) (by omega)
    rw [show Image.rodataBase + (a - Image.rodataBase + i) = a + i by omega] at this
    exact this
  have h0 : (m[a]?).getD 0 = rodB a 0 := hb 0 (by omega)
  unfold bytesT4 rodWord
  rw [h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]

/-- **A jump-table `jr`'s target**: the entry at `a` (`A`, the indexed
address, evaluated) plus the table base. -/
theorem fn_jt_tgt {m : Mem} (hrod : RodataRead m) {A tbE t : BitVec 64} {a : Nat}
    (ha : A.toNat = a) (hlo : Image.rodataBase ≤ a) (hhi : a + 4 ≤ Image.rodataBase + Image.rodataSize)
    (ht : BitVec.update ((sign_extend (m := 64) (rodWord a) + tbE) + sign_extend (m := 64) (0x000#12)) 0 0#1 = t) :
    BitVec.update ((sign_extend (m := 64) (bytesT4 m A.toNat : BitVec (8 * 4)) + tbE) +
      sign_extend (m := 64) (0x000#12)) 0 0#1 = t := by
  rw [ha, rodWord_eq hrod hlo hhi]; exact ht

/-- The bound check before a table (`bltu a, idx` not taken). -/
theorem fn_jt_bound {a x : BitVec 64} {n : Nat} (h : zopz0zI_u a x = false) (ha : a.toNat + 1 = n) :
    x.toNat < n := by
  unfold zopz0zI_u at h; simp [BitVec.toNatInt] at h; omega

/-- The index enumerated from the top. -/
theorem fn_jt_split {x : BitVec 64} {n : Nat} (h : x.toNat < n + 1) :
    x = BitVec.ofNat 64 n ∨ x.toNat < n := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
  · exact Or.inr h
  · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [h]; simp; omega))

theorem fn_jt_zero {x : BitVec 64} (h : x.toNat < 1) : x = BitVec.ofNat 64 0 :=
  BitVec.eq_of_toNat_eq (by simp; omega)

theorem fn_jt_idx {x : BitVec 64} {k : Nat} (h : x = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) : x.toNat = k := by
  rw [h]; simp; omega

/-! ## Callee-saved registers spilled mid-body (lane float-sf4)

A routine that saves `s0`… to their slots and reuses them (`__divdf3`'s
`udiv_qrnnd`) restores them before it returns: the node lemmas carry the
save slot's fact `hsv<off> : bytesT8 m slot = g.<s>` (as `hra` for `ra`), and
the restore's load is the caller's value. -/

theorem fn_sv_ld {m : Mem} {a : Nat} {v : BitVec 64} (h : bytesT8 m a = v) :
    sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)) = v := by
  rw [sext64_id, h]

end Lua.Vm.Sim
