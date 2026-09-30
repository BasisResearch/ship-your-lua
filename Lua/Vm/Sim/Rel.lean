import Lua.Vm.Runtime
import Lua.Vm.Host
import Lua.Vm.RegsOk
import Lua.Vm.Sim.Mem
import Lua.Vm.Sim.Step
import Vsa.Sim.SegState

/-!
# `VmRel`: the machine at `luaV_execute`'s fetch head represents a `BcSem` state (A1)

`VmRel p c s` relates a machine configuration `c` to a bytecode state `s` of
the main chunk `p` when `c` sits at the fetch head of `luaV_execute`
(`Lua.Vm.Arms.headPc`, the `bnez s5` before `lw s4,0(s11)`) about to execute
instruction `s.pc`. It is `∃ w, VmRelAt p c s w` over the pointers `w`
(`RelPtrs`), and every part is a named field:

* **Registers** (`Pins`). `luaV_execute` keeps its state in callee-saved
  registers at the head: s0 = `L`, s7 = `ci`, s8 = the jump table, s1 = 81
  (the last opcode in the table), s2 = 3 (`LUA_VNUMINT`), s5 = `trap` (0: no
  hooks), s9 = `base`, s11 = the cached `pc` (`code + 4·s.pc`; the
  `ci->u.l.savedpc` in memory is only written back by `savepc` before calls,
  so the relation pins the register, not the memory word), plus `sp` and `gp`.
* **Registers of the chunk** (`Core.stack`). Every register `j <
  maxstacksize` that holds a value (`s.regs j = some v`) is represented by
  the stack slot `base + 16·j` (`ValRepr` of its tag byte and payload). The
  kernel semantics already marks the registers the definite-initialisation
  analysis cannot see as ⊥ (`none`: stale, kill ports), so this is the
  `FrameRepr` of the defined registers: at a reachable state it covers
  `defMask p s.pc` (`Lua/FragmentSound.lean`), and it holds of the entry
  state (all ⊥) for any stack contents.
* **Output** (`Core.out`): the HTIF console so far is `s.out`.
* **Registers present, mailbox idle** (`Core.ok`, `RegsOk`): every GPR holds a
  value and no `tohost` word is half-written (ship-your-interpreter's `VsaOk`
  register half), established by `MachineAt.regs` and threaded by every
  segment (`gen_segment.py`'s `"ok"` option).
* **Frame** (`Core.frame`, `Complement`). Outside the window `Win` (the
  register slots and `luaV_execute`'s own C frame) the memory reads TOTALLY
  (`bytesT1`, the model's `getD 0`) as a fixed complement `w.mo`: presence is
  never demanded, since the densification (`Vsa.Densify`) already gives it.
  The one presence the relation carries is `.text` (`Core.text`), which the
  segments' instruction fetches demand (`SegSt`'s `TextLoaded`). Of `w.mo`,
  `Complement` states the image (`.text`, `.rodata`), the prototype (`ProtoRepr`, and its code words as `lw` reads
  them), `ci->func` and `ci->u.l.trap`, and the Lua state and heap of
  `luaLayout` (`LuaStateAt`, `DlHeap.HeapAt`, `ErrorJmpAt`).

**Relocation.** Registers are decoded relative to `ci->func` as the complement
holds it (`w.func`, `base = func + 16`), not to a fixed address. `OP_VARARGPREP`
moves `ci->func` inside the main activation (`luaT_adjustvarargs`), and
`CALL print` can reallocate the Lua stack (`luaD_precall` → `checkstackGCp`,
`correctstack` rewrites `ci->func`); after either, `luaV_execute` reloads
`base` from `ci->func` (`updatebase`) and the relation holds again with a new
`func` and the moved slots. The pilot arms (`MOVE`, `LOADI`, `JMP`) keep `w`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config)

/-- **A register's value from its slot's tag byte `t` and payload `x`.**
The `TValueRepr` of `Lua/Vm/Repr.lean` in the form the arms read it (`lbu`
of the tag, `ld` of the payload); a string's bytes live in the complement
memory `mo`. -/
inductive ValRepr (mo : Mem) : BitVec 8 → BitVec 64 → Value → Prop where
  | nil {t x} : t.toNat % 16 = 0 → ValRepr mo t x .nil
  | false_ {x} : ValRepr mo (BitVec.ofNat 8 vFalse) x (.bool false)
  | true_ {x} : ValRepr mo (BitVec.ofNat 8 vTrue) x (.bool true)
  | int {i} : ValRepr mo (BitVec.ofNat 8 vNumInt) i (.int i)
  | str {t x s} : (t.toNat = vShrStr ∨ t.toNat = vLngStr) → TStringRepr mo x.toNat s →
      ValRepr mo t x (.str s)
  | print {x} : x = BitVec.ofNat 64 symLuaBPrint → ValRepr mo (BitVec.ofNat 8 vLcf) x (.builtin .print)

/-- `luaV_execute`'s own C frame (`addi sp,sp,-176` in its prologue). -/
def execFrame : Nat := 176

/-- The pointers of the relation. -/
structure RelPtrs where
  /-- `lua_State *L` (s0) -/
  L : Nat
  /-- `CallInfo *ci` (s7) -/
  ci : Nat
  /-- `ci->func` as the complement holds it; `base = func + 16` -/
  func : Nat
  /-- the `Proto`, its `code` array and its constant array `k` -/
  pa : Nat
  code : Nat
  k : Nat
  /-- `sp` inside `luaV_execute` -/
  sp : Nat
  /-- the memory outside the window -/
  mo : Mem

namespace RelPtrs

/-- `base = ci->func + 1` (s9). -/
def base (w : RelPtrs) : Nat := w.func + stackValueSize

/-- The stack slot of register `j`. -/
def slot (w : RelPtrs) (j : Nat) : Nat := w.base + stackValueSize * j

end RelPtrs

/-- The register slots `[base, base + 16·maxstacksize)`. -/
def Slots (p : Proto) (w : RelPtrs) (a : Nat) : Prop :=
  w.base ≤ a ∧ a < w.base + stackValueSize * p.maxstacksize

/-- **The window**: the register slots and `luaV_execute`'s C frame
`[sp, sp + 176)`. -/
def Win (p : Proto) (w : RelPtrs) (a : Nat) : Prop :=
  Slots p w a ∨ (w.sp ≤ a ∧ a < w.sp + execFrame)

/-- The parts of `luaRuntimeReady` that live in memory and that the F1 arms
keep: the Lua state (with `ci->func = func`), the heap and the error
handler. (`StdioBoot`/`MemfsBoot` describe the state before the first
`print` and belong to the `CALL` arm.) -/
structure RuntimeMem (m : Mem) (L ci func : Nat) (rt : RtPtrs) : Prop where
  func : rt.func = func
  lua : LuaStateAt m L ci rt
  heap : DlHeap.HeapAt m rt.top rt.brkv rt.chunks (fun i => rt.bins.getD i [])
  error_jmp : ErrorJmpAt m L

/-- **The complement**: what the relation knows about `w.mo`. -/
structure Complement (p : Proto) (w : RelPtrs) : Prop where
  text : Arms.TextLoaded w.mo
  rodata : RodataLoaded w.mo
  /-- `VmEntryData.proto`/`proto_code`: the prototype is loaded -/
  proto : ProtoRepr w.mo w.pa p
  proto_code : rd64 w.mo (w.pa + protoCodeOff) = some w.code
  /-- `proto`'s code words, as `lw` reads them (the total-read form) -/
  code_word : ∀ i ins, p.fetch i = some ins → bytesT4 w.mo (w.code + 4 * i) = ins
  /-- `ci->func`, as `updatebase` reads it -/
  func_word : bytesT8 w.mo (w.ci + ciFuncOff) = BitVec.ofNat 64 w.func
  /-- `ci->u.l.trap = 0` (no hooks), as `updatetrap` reads it -/
  trap_word : bytesT4 w.mo (w.ci + ciTrapOff) = 0
  runtime : ∃ rt, RuntimeMem w.mo w.L w.ci w.func rt
  /-- the constants (`kval`), as the `K` arms read `k[i]` -/
  kconst : ∀ i v, kval p i = some v →
    ValRepr w.mo (slotTag w.mo (w.k + stackValueSize * i)) (slotVal w.mo (w.k + stackValueSize * i)) v

/-- **Where things are**: the address ranges the arms' side conditions need,
and the window's separation from the code array and the `CallInfo`. -/
structure Ranges (p : Proto) (w : RelPtrs) : Prop where
  sp_eq : w.sp + execFrame = RuntimeData.spEntry
  base_lo : tohostAddr + 16 ≤ w.base
  base_hi : w.base + stackValueSize * p.maxstacksize ≤ 0x100000000
  base_al : w.base % 8 = 0
  code_lo : tohostAddr + 16 ≤ w.code
  code_hi : w.code + 4 * p.code.length ≤ 0x100000000
  ci_lo : tohostAddr + 16 ≤ w.ci
  ci_hi : w.ci + ciSize ≤ 0x100000000
  code_out : ∀ a, w.code ≤ a → a < w.code + 4 * p.code.length → ¬ Win p w a
  ci_out : ∀ a, w.ci ≤ a → a < w.ci + ciSize → ¬ Win p w a
  k_lo : tohostAddr + 16 ≤ w.k
  k_hi : w.k + stackValueSize * p.k.length ≤ 0x100000000
  k_al : w.k % 8 = 0
  k_out : ∀ a, w.k ≤ a → a < w.k + stackValueSize * p.k.length → ¬ Win p w a
  /-- the register slots lie below the C frame -/
  frame_sep : w.base + stackValueSize * p.maxstacksize ≤ w.sp
  /-- the constant array lies apart from the register slots -/
  k_sep : w.k + stackValueSize * p.k.length ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ w.k

/-- **The fetch-head registers** for pointers `w` and bytecode pc `pc`. -/
structure Pins (σ : MState) (w : RelPtrs) (pc : Nat) : Prop where
  sp : σ.regs.get? Register.x2 = some (BitVec.ofNat 64 w.sp)
  gp : σ.regs.get? Register.x3 = some (BitVec.ofNat 64 symGlobalPointer)
  L : σ.regs.get? Register.x8 = some (BitVec.ofNat 64 w.L)
  opMax : σ.regs.get? Register.x9 = some (BitVec.ofNat 64 (Arms.jtEntries - 1))
  intTag : σ.regs.get? Register.x18 = some (BitVec.ofNat 64 vNumInt)
  trap : σ.regs.get? Register.x21 = some (0#64)
  ci : σ.regs.get? Register.x23 = some (BitVec.ofNat 64 w.ci)
  jt : σ.regs.get? Register.x24 = some (BitVec.ofNat 64 Arms.jtBase)
  base : σ.regs.get? Register.x25 = some (BitVec.ofNat 64 w.base)
  pc : σ.regs.get? Register.x27 = some (BitVec.ofNat 64 (w.code + 4 * pc))

/-- Everything but the machine pc: shared by the head (`VmRelAt`) and the arm
entry after dispatch (`ArmAt`). -/
structure Core (p : Proto) (c : Config) (s : State) (w : RelPtrs) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  pins : Pins c.σ w s.pc
  out : Vsa.Machine.output c.σ = s.out
  /-- every GPR present, the HTIF mailbox idle -/
  ok : RegsOk c.σ
  /-- `.text` is present: the segments' fetches (`SegSt`'s `TextLoaded`) demand it -/
  text : Arms.TextLoaded c.σ.mem
  /-- outside the window, every TOTAL read (`bytesT1`, the model's `getD 0`) is the
  complement's: presence is not demanded, the densification gives it -/
  frame : ∀ a, ¬ Win p w a → bytesT1 c.σ.mem a = bytesT1 w.mo a
  /-- `0(sp)` holds `k` (the prologue's `sd`; the `K` arms' `ld a4,0(sp)`) -/
  kptr : bytesT8 c.σ.mem w.sp = BitVec.ofNat 64 w.k
  stack : ∀ j v, j < p.maxstacksize → s.regs j = some v →
    ValRepr w.mo (slotTag c.σ.mem (w.slot j)) (slotVal c.σ.mem (w.slot j)) v
  comp : Complement p w
  ranges : Ranges p w

/-- **The payload of an arm's segments** (`gen_lua_arms.py`, `sim` segments):
`.text` present, the memory `m`, the console `o`, `RegsOk`. -/
abbrev ArmPay (m : Mem) (o : Array String) : MState → Prop :=
  fun σ => Arms.TextLoaded σ.mem ∧ σ.mem = m ∧ σ.sailOutput = o ∧ RegsOk σ

section
variable {pcv : BitVec 64} {L : List Pin} {m : Mem} {o : Array String} {c : Config}

/-- The payload's fields (its one destructuring point). -/
theorem _root_.Vsa.Sim.SegSt.armText (h : SegSt pcv L (ArmPay m o) c) : Arms.TextLoaded c.σ.mem := h.extra.1
theorem _root_.Vsa.Sim.SegSt.armMem (h : SegSt pcv L (ArmPay m o) c) : c.σ.mem = m := h.extra.2.1
theorem _root_.Vsa.Sim.SegSt.armOut (h : SegSt pcv L (ArmPay m o) c) : c.σ.sailOutput = o := h.extra.2.2.1
theorem _root_.Vsa.Sim.SegSt.armOk (h : SegSt pcv L (ArmPay m o) c) : RegsOk c.σ := h.extra.2.2.2

end

/-- **The relation at the fetch head**, for pointers `w`. -/
structure VmRelAt (p : Proto) (c : Config) (s : State) (w : RelPtrs) : Prop where
  core : Core p c s w
  pcAt : c.σ.regs.get? Register.PC = some Arms.headPc

/-- **`VmRel p c s`**: `c` is at `luaV_execute`'s fetch head about to run
instruction `s.pc` of `p`, representing `s`. -/
def VmRel (p : Proto) (c : Config) (s : State) : Prop := ∃ w, VmRelAt p c s w

/-- **Open (A1): the entry lemma.** From `luaV_execute`'s entry, the prologue
runs to the fetch head in the relation with the initial state. -/
def vmRel_entry_Statement : Prop :=
  ∀ p c, Supported p → VmLoaded luaLayout p c →
    ∃ c', Vsa.Machine.Steps c c' ∧ VmRel p c' State.init

/-- **After dispatch**: at the arm of `ins`'s opcode, with s3 = `pc + 1` and
s4 = the instruction (sign-extended by `lw`). -/
structure ArmAt (p : Proto) (c : Config) (s : State) (w : RelPtrs) (ins : Word) : Prop where
  core : Core p c s w
  pcAt : c.σ.regs.get? Register.PC = some (armTarget ins.opNum)
  s3 : c.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1)))
  s4 : c.σ.regs.get? Register.x20 = some (sign_extend (m := 64) ins)

/-! ## Reading the machine through the relation -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

theorem Win.above (hr : Ranges p w) {a : Nat} (h : Win p w a) : tohostAddr + 16 ≤ a := by
  have := hr.sp_eq
  have := hr.base_lo
  simp only [Win, Slots, execFrame, RuntimeData.spEntry, tohostAddr] at *
  omega

theorem Win.of_slots {a : Nat} (h : ¬ Win p w a) : ¬ Slots p w a := fun hs => h (.inl hs)

/-- The machine's `.rodata`, read totally, is the image's. -/
theorem Core.rodata (hc : Core p c s w) : RodataRead c.σ.mem := fun o ho => by
  have := rodata_below_tohost
  refine (hc.frame _ fun hw => ?_).trans ?_
  · have := Win.above hc.ranges hw; omega
  · simp only [bytesT1, hc.comp.rodata o ho, Option.getD_some]

/-- The instruction at `pc`, as `lw s4,0(s11)` reads it. -/
theorem Core.fetch (hc : Core p c s w) {pc : Nat} {ins : Word} (hf : p.fetch pc = some ins) :
    bytesT4 c.σ.mem (w.code + 4 * pc) = ins := by
  have hlt := fetch_lt hf
  refine (bytesT4_congrT fun i hi => ?_).trans (hc.comp.code_word pc ins hf)
  exact hc.frame _ (hc.ranges.code_out _ (by omega) (by omega))

/-- `ci->u.l.trap`, as `updatetrap` reads it. -/
theorem Core.trap (hc : Core p c s w) : bytesT4 c.σ.mem (w.ci + ciTrapOff) = 0 := by
  refine (bytesT4_congrT fun i hi => ?_).trans hc.comp.trap_word
  exact hc.frame _ (hc.ranges.ci_out _ (by omega) (by simp only [ciTrapOff, ciSize]; omega))

theorem kval_lt {p : Proto} {i : Nat} {v : Value} (h : kval p i = some v) : i < p.k.length := by
  simp only [kval, Proto.const, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, -⟩ := h
  exact (List.getElem?_eq_some_iff.1 hc).1

/-- The constant `k[i]`, as a `K` arm reads it (`ld a4,0(sp)`, then the slot). -/
theorem Core.kconst (hc : Core p c s w) {i : Nat} {v : Value} (hk : kval p i = some v) :
    ValRepr w.mo (slotTag c.σ.mem (w.k + stackValueSize * i))
      (slotVal c.σ.mem (w.k + stackValueSize * i)) v := by
  have hi := kval_lt hk
  obtain ⟨ht, hv⟩ := slot_congrT (m := c.σ.mem) (m' := w.mo) (a := w.k + stackValueSize * i)
    fun j hj => hc.frame _ (hc.ranges.k_out _ (by omega) (by simp only [stackValueSize] at *; omega))
  rw [ht, hv]
  exact hc.comp.kconst i v hk

/-! ## Re-establishing the relation after an arm -/

/-- `.text` survives any memory change that is exact outside the register slots. -/
theorem Core.text_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    Arms.TextLoaded m :=
  Vsa.Sim.Code.FixedBytesLoaded.transport hc.text fun a _ h2 => h a fun hw => by
    have := Win.above hc.ranges (.inl hw); have := Arms.text_below_tohost; omega

/-- The frame survives any memory change that is exact outside the register slots. -/
theorem Core.frame_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    ∀ x, ¬ Win p w x → bytesT1 m x = bytesT1 w.mo x := fun x hx => by
  simp only [bytesT1, h x (Win.of_slots hx)]; exact hc.frame x hx

/-- `0(sp)` survives any memory change that is exact outside the register slots. -/
theorem Core.kptr_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    bytesT8 m w.sp = BitVec.ofNat 64 w.k :=
  (bytesT8_congr fun i _ => h _ fun hs => by
    have := hc.ranges.frame_sep; simp only [Slots] at hs; omega).trans hc.kptr

theorem output_congr {σ σ' : MState} (h : σ'.sailOutput = σ.sailOutput) :
    Vsa.Machine.output σ' = Vsa.Machine.output σ := by
  simp only [Vsa.Machine.output, h]

/-- **An arm that writes `R[a]`**: the machine stored the slot of `a` (and
nothing else), with a tag and payload that represent `v`. -/
theorem Core.write (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' a : Nat} {v : Value}
    {tag : BitVec 8} {val : BitVec 64} (ha : a < p.maxstacksize) (hpins : Pins c'.σ w pc')
    (hst : SlotStore c.σ.mem c'.σ.mem (w.slot a) tag val)
    (hv : ValRepr w.mo tag val v) :
    Core p c' ⟨pc', fun j => if j = a then some v else s.regs j, s.out⟩ w := by
  have hwin : ∀ x, ¬ (x < w.slot a ∨ w.slot a + 9 ≤ x) → Slots p w x := fun x hx => by
    simp only [RelPtrs.slot, Slots, stackValueSize] at hx ⊢
    constructor <;> omega
  have hfr : ∀ x, ¬ Slots p w x → c'.σ.mem[x]? = c.σ.mem[x]? := fun x hx =>
    hst.frame x (Classical.byContradiction fun h => hx (hwin x h))
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hc.text_of hfr, hc.frame_of hfr, hc.kptr_of hfr, fun j v' hj hv' => ?_, hc.comp,
    hc.ranges⟩
  · simp only at hv'
    by_cases hja : j = a
    · subst hja
      simp only [if_true, Option.some.injEq] at hv'
      subst hv'
      simp only [slotTag, slotVal, tvalueTagOff, tvalueValOff, Nat.add_zero, hst.val, hst.tag]
      exact hv
    · simp only [hja, if_false] at hv'
      obtain ⟨ht, hv2⟩ := slot_congr (m := c'.σ.mem) (m' := c.σ.mem) (a := w.slot j) fun i hi =>
        hst.frame _ (by
          simp only [RelPtrs.slot, stackValueSize]
          rcases Nat.lt_or_gt_of_ne hja with h | h
          · left; omega
          · right; omega)
      rw [ht, hv2]
      exact hc.stack j v' hj hv'

/-- **An arm that writes no register** and no memory (a jump). -/
theorem Core.jump (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    (hpins : Pins c'.σ w pc') (hmem : c'.σ.mem = c.σ.mem) :
    Core p c' ⟨pc', s.regs, s.out⟩ w := by
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hmem ▸ hc.text, hmem ▸ hc.frame, hmem ▸ hc.kptr, fun j v hj hv => ?_, hc.comp,
    hc.ranges⟩
  rw [hmem]
  exact hc.stack j v hj hv

end

end Lua.Vm.Sim
