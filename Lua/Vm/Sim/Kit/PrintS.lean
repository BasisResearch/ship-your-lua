import Lua.Vm.Sim.Kit.PrintSum

/-!
# `luaB_print`'s Lua state, concrete (lane F1-12)

`print_sum` (lane F1-11) takes the Lua side as an abstract invariant `S k ph H
m` with its callees' contracts (`PrintLua`). Here `S` is concrete, for a call
from `luaD_precall`'s C path (`PrS`): the C function's API frame (`ApiAt`:
`L->ci` the C `CallInfo`, its `func`, `L->top` `k` values above it,
`L->tbclist` below it), every byte it reads (`F`) in a chunk in use of the heap
and apart from `stdout`'s buffer (`Kept`), and the arguments as any predicate
`A` of the memory that depends only on its own bytes (`Fa`, apart from
`L->top`). Then `lua_gettop` (`gettop_sum`), `lua_settop(L, -2)`
(`settop_pop_sum`) and the stability under a write (`PrintLua.stable`) are
proved (`printLua_of`); `luaL_tolstring` per argument stays the premise.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- **A byte a `print`'s Lua side keeps**: in a chunk in use of the heap, in
the arena, apart from `stdout`'s buffer. -/
structure Kept (H : HeapIx) (ph : StdoutPh) (a : Nat) : Prop where
  inuse : InUse H.chunks a
  lo : heapStart ≤ a
  hi : a < heapEnd
  nbuf : ¬ ph.Buf a

/-- **A kept byte is no write's** (`PrintW`), nor `luaB_print`'s frame. -/
theorem Kept.not_printW {H : HeapIx} {ph ph' : StdoutPh} {a sp : Nat} (h : Kept H ph a)
    (hsp : heapEnd + 4096 ≤ sp) (hbf : BufFrom ph ph' H) : ¬ (PrintW sp H ph' a ∨ Rng sp 64 a) := by
  have hl := h.lo; have hh := h.hi
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  rw [e2] at hl; rw [e3] at hh hsp
  intro hw
  pw_nums
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symFiles = 0x8005d760 := rfl
  rcases hw with (hw | hw | hw | hw | hw | hw) | hw
  · simp only [FsGlobal] at hw; omega
  · rcases hw with hw | ⟨_, _, hu⟩
    · simp only [MallocGlobal] at hw; omega
    · exact hu h.inuse
  · simp only [SinitW, Rng] at hw; omega
  · simp only [Rng] at hw; omega
  · rcases hbf a hw with hb | ⟨_, _, hu⟩
    · exact h.nbuf hb
    · exact hu h.inuse
  · simp only [Below] at hw; omega
  · simp only [Rng] at hw; omega

/-- **Kept bytes stay kept** across a write that keeps the chunks in use and
takes a buffer of its own or a fresh one. -/
theorem Kept.mono {H H' : HeapIx} {ph ph' : StdoutPh} {a : Nat} (h : Kept H ph a)
    (hk : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) (hbf : BufFrom ph ph' H) : Kept H' ph' a :=
  ⟨by obtain ⟨c, hc, hu, h1, h2⟩ := h.inuse; exact ⟨c, hk c hc hu, hu, h1, h2⟩, h.lo, h.hi,
    fun hb => (hbf a hb).elim h.nbuf fun ⟨_, _, hu⟩ => hu h.inuse⟩

/-- A kept byte is not in `print`'s I/O footprint (`PrintFoot`). -/
theorem Kept.not_printFoot {H : HeapIx} {ph : StdoutPh} {a : Nat} (h : Kept H ph a) : ¬ PrintFoot ph H a := by
  have hl := h.lo
  have e2 : heapStart = 0x8006ecd0 := rfl
  rw [e2] at hl
  rintro (hg | hb | ⟨_, hu⟩ | hr)
  · simp only [StdioGlob] at hg; omega
  · exact h.nbuf hb
  · exact hu h.inuse
  · omega

/-- The bytes the API frame reads: `L->top`, `L->ci`, `L->tbclist`, the C
`CallInfo`'s `func`. -/
def ApiFoot (L nci : Nat) (a : Nat) : Prop :=
  Rng (L + 16) 8 a ∨ Rng (L + 32) 8 a ∨ Rng (L + 64) 8 a ∨ Rng nci 8 a

/-- The API frame depends only on its bytes. -/
theorem ApiAt.congrT {m m' : Mem} {L nci func k tbc : Nat} (h : ApiAt m L nci func k tbc)
    (hk : ∀ a, ApiFoot L nci a → bytesT1 m' a = bytesT1 m a) : ApiAt m' L nci func k tbc :=
  ⟨(bytesT8_congrT fun i _ => hk _ (.inr (.inl ⟨by omega, by omega⟩))).trans h.ci_w,
   (bytesT8_congrT fun i _ => hk _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))).trans h.func_w,
   (bytesT8_congrT fun i _ => hk _ (.inl ⟨by omega, by omega⟩)).trans h.top_w,
   (bytesT8_congrT fun i _ => hk _ (.inr (.inr (.inl ⟨by omega, by omega⟩)))).trans h.tbc_w, h.tbc_lt⟩

/-- **The arguments' predicate** of a `print` call: `A` depends only on the
bytes `Fa`, which miss `L->top` (`lua_settop`'s one store). -/
structure ArgPred (L : Nat) (A : Mem → Prop) (Fa : Nat → Prop) : Prop where
  congr : ∀ m m', A m → (∀ a, Fa a → bytesT1 m' a = bytesT1 m a) → A m'
  apart : ∀ a, Fa a → ¬ Rng (L + 16) 8 a

/-- **`luaB_print`'s Lua state** (`print_sum`'s `S k ph H m`) for a call from
`luaD_precall`'s C path: the API frame of `k` values, the bytes it and the
arguments read kept, the arguments' predicate. -/
structure PrS (L nci func tbc : Nat) (A : Mem → Prop) (Fa : Nat → Prop) (k : Nat) (ph : StdoutPh)
    (H : HeapIx) (m : Mem) : Prop where
  api : ApiAt m L nci func k tbc
  kept : ∀ a, ApiFoot L nci a ∨ Fa a → Kept H ph a
  args : A m

/-- **What `luaB_print`'s API calls need of the frame's numbers.** -/
structure PrNums (sp0 L nci func n : Nat) (r : BitVec 64) : Prop where
  ok : PrOk sp0 L r
  n_lt : n + 1 < 2 ^ 31
  nci_lo : 0x8005c6d0 ≤ nci
  nci_hi : nci + 256 ≤ 2 ^ 32
  f_lo : 0x8005c6d0 ≤ func
  f_hi : func + 16 * n + 48 ≤ 2 ^ 32
  sep : nci + 8 ≤ L + 16 ∨ L + 24 ≤ nci

/-- **`PrintLua` for the concrete state** (`PrS`): `lua_gettop`,
`lua_settop(L, -2)` and the stability are proved; `luaL_tolstring` of each
argument is the premise `htol`. -/
theorem printLua_of {sp0 L nci func tbc n : Nat} {A : Mem → Prop} {Fa : Nat → Prop}
    {bs : Nat → List (BitVec 8)} {r0 : BitVec 64} (hn : PrNums sp0 L nci func n r0) (hA : ArgPred L A Fa)
    (htol : ∀ (i : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64)
      (f : AbiFrame), 1 ≤ i → i ≤ n → PrS L nci func tbc A Fa n ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
      Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
          ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
        (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧
          TolPost sp0 n (PrS L nci func tbc A Fa) (bs i) ph m m' s H H')) :
    PrintLua L sp0 n (PrS L nci func tbc A Fa) bs where
  n_lt := hn.n_lt
  gettop := by
    intro ph H m o r f hS hr
    have q := hn.ok
    have := q.sp_hi; have := q.L_lo; have := q.L_hi; have := q.L_al
    have := hn.nci_lo; have := hn.nci_hi; have := hn.f_lo; have := hn.f_hi; have := hn.n_lt
    exact gettop_sum (sp0 - 64) L nci func n tbc r f m o hS.api (by omega) hr (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  tolstring := htol
  settop := by
    intro ph H m o r f hS hP hr c h
    have q := hn.ok
    have := q.sp_hi; have := q.L_lo; have := q.L_hi; have := q.L_al; have := q.sp_lo
    have := hn.nci_lo; have := hn.f_lo; have := hn.f_hi; have := hn.sep
    obtain ⟨c', s', m', hret, hapi, hag⟩ := settop_pop_sum (sp0 - 64) L nci func n tbc r f m o hS.api hr
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) c h
    have hk : ∀ a, ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a := fun a ha => AtF.bT1_congr (hag a ha)
    have hL : ∀ a, Rng (L + 16) 8 a → Kept H ph a := fun a ha => hS.kept a (.inl (.inl ha))
    refine ⟨c', s', m', hret, ⟨hapi, hS.kept, hA.congr m m' hS.args fun a ha => hk a (hA.apart a ha)⟩,
      hP.keep fun a ha => hk a fun hr' => (hL a hr').not_printFoot ha, fun a ha => hk a fun hr' => ?_⟩
    have := (hL a hr').hi
    simp only [Rng] at hr'; omega
  stable := by
    intro k ph ph' H H' m m' hS hk hbf hkept
    have q := hn.ok
    have hsp : heapEnd + 4096 ≤ sp0 - 64 := by
      have h1 := q.sp_lo; revert h1; generalize heapEnd = E; intro h1; omega
    have keepF : ∀ a, ApiFoot L nci a ∨ Fa a → bytesT1 m' a = bytesT1 m a := fun a ha =>
      hk a ((hS.kept a ha).not_printW hsp hbf)
    exact ⟨hS.api.congrT fun a ha => keepF a (.inl ha), fun a ha => (hS.kept a ha).mono hkept hbf,
      hA.congr m m' hS.args fun a ha => keepF a (.inr ha)⟩

end Lua.Vm.Sim.Kit
