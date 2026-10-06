import Lua.Vm.Sim.Kit.Close

/-!
# The kit's multi-slot close (lane KIT-2)

Two generalisations of `Core.bleach` (M3) that the control arms need:

* **C-frame writes** (`Core.bleachF`): `FORPREP` spills `ra` (`sd a5,16(sp)`)
  and passes `&limit` (`sp+40`) to `luaV_tointeger`, both in
  `luaV_execute`'s own frame `[sp, sp + 176)`, which is in the window `Win`
  (no head invariant) but for `0(sp)`, which holds `k` (`Core.kptr`), `8(sp)`,
  which holds the closure (`Core.clptr`), and the saved registers
  `72…175(sp)` (`Core.saved`). The close asks agreement outside slots,
  `Scratch` and the locals `[sp + 16, sp + 72)` (every store of an F1 arm to
  `luaV_execute`'s frame is in `[16(sp), 64(sp))`; only the prologue and the
  `OP_CALL`/`OP_RETURN` re-entries write `8(sp)`).
* **Several registers written** (`Core.stack_of`): the defined registers of
  the successor are represented if every written register `j` (`D j`) is
  represented in the new memory, every other register is the old one, and
  the slots of the unwritten registers are unchanged.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- `luaV_execute`'s locals: its C frame above the `k` word `0(sp)` and the
closure word `8(sp)` (`Core.clptr`), and below the saved registers
`72…175(sp)` (`SavedAt`). -/
def CFrame (w : RelPtrs) (x : Nat) : Prop := w.sp + 16 ≤ x ∧ x < w.sp + 72

/-- **The close with C-frame writes**: as `Core.bleach`, with the final
memory free in `CFrame` too. -/
theorem Core.bleachF (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    {regs' : Nat → Option Value} {out' : String} (hout : out' = s.out) (hpins : Pins c'.σ w pc')
    (hfr : ∀ x, ¬ Slots p w x → ¬ Scratch w x → ¬ CFrame w x → m[x]? = c.σ.mem[x]?)
    (hst : ∀ j v, j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v) :
    Core p c' ⟨pc', regs', out'⟩ w := by
  subst hout
  have hm := hseg.armMem
  subst hm
  have hr := hc.ranges
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hseg.armText, fun x hx => ?_, ?_, ?_, hst, hc.comp, hr,
    hc.saved.congr fun x h1 _ => hfr x
      (fun hs => by have := hr.frame_sep; simp only [Slots] at hs; omega)
      (fun hs => by have := (hr.scratch_out _ hs).2; omega)
      (fun hs => by simp only [CFrame] at hs; omega)⟩
  · simp only [bytesT1, hfr x (Win.of_slots hx) (fun h => hx (.inr (.inr h)))
      (fun h => hx (.inr (.inl ⟨by simp only [CFrame] at h; omega,
        by simp only [CFrame] at h; simp only [execFrame]; omega⟩)))]
    exact hc.frame x hx
  · refine (bytesT8_congr fun i hi => hfr _ (fun hs => ?_) (fun hs => ?_) (fun hs => ?_)).trans hc.kptr
    · have := hr.frame_sep; simp only [Slots] at hs; omega
    · have := (hr.scratch_out _ hs).2; omega
    · simp only [CFrame] at hs; omega
  · refine (bytesT8_congr fun i hi => hfr _ (fun hs => ?_) (fun hs => ?_) (fun hs => ?_)).trans hc.clptr
    · have := hr.frame_sep; simp only [Slots] at hs; omega
    · have := (hr.scratch_out _ hs).2; omega
    · simp only [CFrame] at hs; omega

/-- **Several registers written**: `D` the written registers. -/
theorem Core.stack_of (hc : Core p c s w) {m : Mem} {regs' : Nat → Option Value}
    (D : Nat → Prop) (hold : ∀ j, ¬ D j → regs' j = s.regs j)
    (hfr : ∀ x, Slots p w x → (∀ j, D j → x < w.slot j ∨ w.slot j + 16 ≤ x) → m[x]? = c.σ.mem[x]?)
    (hnew : ∀ j v, D j → j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v) :
    ∀ j v, j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v := by
  intro j v hj hv
  by_cases hD : D j
  · exact hnew j v hD hj hv
  rw [hold j hD] at hv
  obtain ⟨ht, hv2⟩ := slot_congr (m := m) (m' := c.σ.mem) (a := w.slot j) fun i hi => by
    refine hfr _ ?_ fun k hk => ?_
    · simp only [Slots, RelPtrs.slot, stackValueSize]; omega
    · have hne : j ≠ k := fun e => hD (e ▸ hk)
      simp only [RelPtrs.slot, stackValueSize]
      rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
  rw [ht, hv2]
  exact hc.stack j v hj hv

end

/-! ## Reads through a tag store (`sb`) -/

theorem slotTag_ins {m : Mem} {a n : Nat} {b : BitVec 8} (h : a ≠ n + 8) :
    slotTag (m.insert a b) n = slotTag m n := by
  simp only [slotTag, tvalueTagOff, bytesT1, getElem?_insert_out (Ne.symm h)]

theorem slotVal_ins {m : Mem} {a n : Nat} {b : BitVec 8} (h : a < n ∨ n + 8 ≤ a) :
    slotVal (m.insert a b) n = slotVal m n := by
  simp only [slotVal, tvalueValOff, Nat.add_zero]
  exact bytesT8_congr fun i _ => getElem?_insert_out (by omega)

theorem bytesT8_ins {m : Mem} {a x : Nat} {b : BitVec 8} (h : a < x ∨ x + 8 ≤ a) :
    bytesT8 (m.insert a b) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_insert_out (by omega)

theorem slotTag_ins_same {m : Mem} {a n : Nat} {b : BitVec 8} (h : a = n + 8) :
    slotTag (m.insert a b) n = b := by
  subst h; simp [slotTag, tvalueTagOff, bytesT1]

theorem slotVal_wm8_same {m : Mem} {a n : Nat} {d : BitVec (8 * 8)} (h : a = n) :
    slotVal (writeMap8 m a d) n = d := by
  subst h; simpa [slotVal, tvalueValOff] using bytesT8_writeMap8 m a d

/-- A temporary register's pin (every GPR holds a value, `RegsOk`): `t0`
for a callee that saves it (`__udivdi3`'s carried `t0`). -/
theorem _root_.Vsa.Sim.SegSt.pin5 {pc : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    {c : Config} (h : SegSt pc L (ArmPay m o) c) :
    ∃ t, SegSt pc (⟨Register.x5, t⟩ :: L) (ArmPay m o) c := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h.armOk.gpr 5 (by decide) (by decide))
  exact ⟨t, h.repin ⟨ht, h.pins⟩⟩

/-- A doubleword load of the doubleword just stored (the address given in
another form, discharged by `kit_disch`). -/
theorem bytesT8_wm8_same {m : Mem} {a b : Nat} {d : BitVec (8 * 8)} (h : b = a) :
    bytesT8 (writeMap8 m a d) b = d := by
  subst h; exact bytesT8_writeMap8 m b d

/-- A segment state's memory restated (an address in another form). -/
theorem _root_.Vsa.Sim.SegSt.mem_eq {pc : BitVec 64} {L : List Pin} {m m' : Mem} {o : Array String}
    {c : Config} (h : SegSt pc L (ArmPay m o) c) (e : m = m') : SegSt pc L (ArmPay m' o) c :=
  e ▸ h

/-- A pin whose value is an address in another form (`ofNat a + imm` against
`ofNat b`): `slot_arith` on the numbers. -/
macro_rules
  | `(tactic| kit_val) => `(tactic| (
      try simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      apply BitVec.eq_of_toNat_eq; slot_arith))

/-- `setNils`' register file: `writeDefs` over a range of one value. -/
theorem writeDefs_range {V : Type} (v : V) (ρ : Nat → Option V) :
    ∀ (n a j : Nat), writeDefs (List.range' a n) (List.replicate n v) ρ j =
      if a ≤ j ∧ j < a + n then some v else ρ j
  | 0, a, j => by simp [writeDefs]; omega
  | n + 1, a, j => by
    simp only [List.range'_succ, List.replicate_succ, writeDefs, List.head?_cons, List.tail_cons]
    rw [writeDefs_range v ρ n (a + 1) j]
    by_cases h : j = a
    · simp [h]
    · simp only [h, ite_false]
      congr 1; apply propext; omega

theorem writeDefs_range' {V : Type} (v : V) (ρ : Nat → Option V) (n a : Nat) :
    writeDefs (List.range' a n) (List.replicate n v) ρ =
      fun j => if a ≤ j ∧ j < a + n then some v else ρ j :=
  funext (writeDefs_range v ρ n a)

/-- `regTop` of a range of ports. -/
theorem foldr_range_top : ∀ (n a : Nat),
    List.foldr (fun r m => max (r + 1) m) 0 (List.range' a (n + 1)) = a + n + 1
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range'_succ, List.foldr_cons, foldr_range_top n (a + 1)]; omega

end Lua.Vm.Sim
