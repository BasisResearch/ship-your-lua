import Lua.Vm.Sim.Kit.LuaApi
import Lua.Vm.AtF.Precall
import Lua.Vm.AtF.PrecallExt

/-!
# `luaD_precall` on a light C function (lane F1-12)

`luaD_precall(L, func, nresults)` (`0x8000aab4`) for `print` (`LUA_VLCF`,
`ldo.c` `precallC`), on the callee-context route (`Lua/Vm/AtF/Precall.lean`,
`Lua/Vm/AtF/PrecallExt.lean`, `gen_lua_at.py --fn luaD_precall`):

* the tag test (`LUA_VLCF` = 22), `checkstackGCp` with room (`L->stack_last -
  L->top > LUA_MINSTACK` slots: no `luaD_growstack`; the growth path is a stop
  of the generator, `0x8000abe4`);
* `next_ci`: `ci->next` reused (`precall_reuse`), or `luaE_extendCI` when it
  is NULL (`precall_ext`, its summary a hypothesis `PcExt`);
* the join (`precall_join`): the C `CallInfo`'s `func`, `top = L->top +
  LUA_MINSTACK`, `nresults`, `callstatus = CIST_C`, `L->ci` (no call hook),
  the C function through `jalr a7` (its summary a hypothesis `PcC`), then
  `luaD_poscall(L, ci, n)` (a hypothesis `PcPos`); `0` returned.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- The context of `luaD_precall`'s rows: `sp`, `L`, `func`, `nresults`,
`L->top`, `L->stack_last`, `L->ci`, the C `CallInfo`; `ra` and the frame. -/
@[at_row] abbrev pcX (sp L func nres top sl ci nci : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, L, func, nres, top, sl, ci, nci]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- The frame the C function and `luaD_poscall` see: `s0 = L`. -/
abbrev pcFr (L : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- **Where `luaD_precall`'s objects lie** on the C path: in the arena below
its frame, `L->top` with room below `L->stack_last`. -/
structure PcNum (sp L func nres top sl ci : Nat) (r : BitVec 64) : Prop where
  sp_lo : 0x8005e7d8 + 4096 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_al : L % 8 = 0
  f_lo : 0x8005c6d0 ≤ func
  f_al : func % 8 = 0
  nr_lt : nres < 2 ^ 15
  t_hi : top + 320 < sl
  s_hi : sl ≤ 2 ^ 32
  ci_lo : 0x8005c6d0 ≤ ci
  ci_al : ci % 8 = 0
  L_sp : L + 256 + 96 ≤ sp
  f_sp : func + 16 + 96 ≤ sp
  ci_sp : ci + 64 + 96 ≤ sp

/-- **What `luaD_precall` reads** on the C path: `L->top`, `L->stack_last`,
`L->ci`, the function's value (`luaB_print`) and tag (`LUA_VLCF`), no hook. -/
structure PcCells (m : Mem) (L func top sl ci : Nat) : Prop where
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  sl_w : bytesT8 m (L + 40) = BitVec.ofNat 64 sl
  ci_w : bytesT8 m (L + 32) = BitVec.ofNat 64 ci
  fn_w : bytesT8 m func = 0x80022f18#64
  tag_w : bytesT1 m (func + 8) = 0x16#8
  hook_w : bytesT4 m (L + 192) = 0#32

set_option hygiene false in
/-- The numbers of `PcNum`, `PcNci` in context. -/
macro "pc_nums " hx:ident hn:ident : tactic => `(tactic| (
  have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al; have := ($hx).ra; have := ($hx).L_lo
  have := ($hx).L_al; have := ($hx).f_lo; have := ($hx).f_al; have := ($hx).nr_lt; have := ($hx).t_hi
  have := ($hx).s_hi; have := ($hx).ci_lo; have := ($hx).ci_al; have := ($hx).L_sp; have := ($hx).f_sp
  have := ($hx).ci_sp; have := ($hn).lo; have := ($hn).al; have := ($hn).sp))

/-- The C `CallInfo` `nci`: in the arena, below the frame. -/
structure PcNci (sp nci : Nat) : Prop where
  lo : 0x8005c6d0 ≤ nci
  al : nci % 8 = 0
  sp : nci + 64 + 96 ≤ sp

/-- The memory at the join: the frame's saved `s0`, `ra`. -/
abbrev pcFrameMem (m : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : Mem :=
  writeMap8 (writeMap8 m (sp - 16) (sdData_val f.s0)) (sp - 8) (sdData_val r)

/-- The memory at the C call: the C `CallInfo`'s `top`, `func`, `nresults`,
`callstatus`, `L->ci`, and the `CallInfo` saved at `0(sp)`. -/
abbrev pcCallMem (M : Mem) (sp L func nres top nci : Nat) : Mem :=
  writeMap8 (writeMap8 (writeMap2 (writeMap2 (writeMap8 (writeMap8 M (nci + 8)
    (sdData_val (BitVec.ofNat 64 (top + 320)))) nci (sdData_val (BitVec.ofNat 64 func))) (nci + 60)
    (shData (BitVec.ofNat 64 nres))) (nci + 62) (shData (0x2#64))) (L + 32)
    (sdData_val (BitVec.ofNat 64 nci))) (sp - 96) (sdData_val (BitVec.ofNat 64 nci))

/-- **The C function's summary** at `precallC`'s `jalr a7`: from `L` and the
memory `M`, it returns `0` results to `0x8000ac8c` with the frame, keeping the
`CallInfo` saved at `0(sp)`, the post `Q`. -/
def PcC (sp L nci : Nat) (f : AbiFrame) (M : Mem) (o : Array String) (Q : Mem → Array String → Prop) :
    Prop :=
  Triple (SegSt 0x80022f18#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp - 96) 0x8000ac8c#64 (pcFr L f))
      (ArmPay M o))
    (fun c => ∃ m' o', wrRet 0x8000ac8c#64 (sp - 96) 0 (pcFr L f) m' o' c ∧
      bytesT8 m' (sp - 96) = BitVec.ofNat 64 nci ∧ Q m' o')

/-- **`luaD_poscall(L, nci, 0)`'s summary** after the C function (post `Q`):
back at `0x8000ac9c` with the frame, the frame's saved `ra`/`s0` kept, the
post `Q'`. -/
def PcPos (sp L nci : Nat) (r : BitVec 64) (f : AbiFrame) (Q Q' : Mem → Array String → Prop) : Prop :=
  ∀ m' o', Q m' o' →
    Triple (SegSt 0x8000a39c#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ :: ⟨Register.x11, BitVec.ofNat 64 nci⟩ ::
        ⟨Register.x12, 0x0#64⟩ :: ⟨Register.x1, 0x8000ac9c#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 96)⟩ ::
        ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: (pcFr L f).pins) (ArmPay m' o'))
      (fun c => ∃ m'', SegSt 0x8000ac9c#64 (⟨Register.x2, BitVec.ofNat 64 (sp - 96)⟩ ::
          ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: (pcFr L f).pins) (ArmPay m'' o') c ∧
        bytesT8 m'' (sp - 8) = r ∧ bytesT8 m'' (sp - 16) = f.s0 ∧ Q' m'' o')

/-- **The join** (`0x8000ac5c`): the C `CallInfo` set up, the C function,
`luaD_poscall`, `0` returned. -/
theorem precall_join {sp L func nres top sl ci nci : Nat} {r : BitVec 64} {f : AbiFrame} {MJ : Mem}
    {o : Array String} {Q Q' : Mem → Array String → Prop} (hx : PcNum sp L func nres top sl ci r)
    (hk : bytesT4 MJ (L + 192) = 0#32) (hn : PcNci sp nci) (hC : PcC sp L nci f (pcCallMem MJ sp L func nres top nci) o Q)
    (hP : PcPos sp L nci r f Q Q') :
    Triple (SegSt 0x8000ac5c#64 (Lua.Vm.AtF.Precall.r4 (pcX sp L func nres top sl ci nci r f MJ o))
        (ArmPay MJ o))
      (fun c => ∃ m'' o', wrRet r sp 0 f m'' o' c ∧ Q' m'' o') := by
  intro c h
  pc_nums hx hn
  have hX : Lua.Vm.AtF.Precall.Ok_J (pcX sp L func nres top sl ci nci r f MJ o) := by fcx_ok
  have hc6 := hk
  have h : SegSt 0x8000ac5c#64 (Lua.Vm.AtF.Precall.r4 (pcX sp L func nres top sl ci nci r f MJ o))
      (ArmPay (pcX sp L func nres top sl ci nci r f MJ o).m (pcX sp L func nres top sl ci nci r f MJ o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Precall h acc until [0x80022f18]
  fcx_unfold at h
  obtain ⟨c1, s1, m', o', hret, hk, hQ⟩ := hC _ (by
    simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s1
  simp only [wrRet] at hret
  have hY : Lua.Vm.AtF.Precall.Ok_J (pcX sp L func nres top sl ci nci r f m' o') := by fcx_ok
  have h : SegSt 0x8000ac8c#64 (Lua.Vm.AtF.Precall.r7 (pcX sp L func nres top sl ci nci r f m' o'))
      (ArmPay (pcX sp L func nres top sl ci nci r f m' o').m (pcX sp L func nres top sl ci nci r f m' o').o) c1 :=
    hret.repin (by pins_of hret)
  fat_run Lua.Vm.AtF.Precall h acc until [0x8000a39c]
  fcx_unfold at h
  obtain ⟨c2, s2, m'', h2, hra, hs0, hQ'⟩ := hP m' o' hQ _ (h.repin (by pins_of h))
  have acc := acc.trans s2
  have hZ : Lua.Vm.AtF.Precall.Ok_J (pcX sp L func nres top sl ci nci r f m'' o') := by fcx_ok
  have h : SegSt 0x8000ac9c#64 (Lua.Vm.AtF.Precall.r9 (pcX sp L func nres top sl ci nci r f m'' o'))
      (ArmPay (pcX sp L func nres top sl ci nci r f m'' o').m (pcX sp L func nres top sl ci nci r f m'' o').o) c2 :=
    h2.repin (by pins_of h2)
  fat_run Lua.Vm.AtF.Precall h acc
  fcx_unfold at h
  exact ⟨_, acc, m'', o', h.repin (by pins_of h), hQ'⟩

/-- **`luaD_precall` on `print` with `ci->next` reused** (`nci ≠ 0`). -/
theorem precall_reuse {sp L func nres top sl ci nci : Nat} {r : BitVec 64} {f : AbiFrame} {m : Mem}
    {o : Array String} {Q Q' : Mem → Array String → Prop} (hx : PcNum sp L func nres top sl ci r)
    (hm : PcCells m L func top sl ci) (hn : PcNci sp nci) (hnw : bytesT8 m (ci + 24) = BitVec.ofNat 64 nci)
    (hC : PcC sp L nci f (pcCallMem (pcFrameMem m sp r f) sp L func nres top nci) o Q)
    (hP : PcPos sp L nci r f Q Q') :
    Triple (SegSt 0x8000aab4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 func⟩,
        ⟨Register.x12, BitVec.ofNat 64 nres⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m'' o', wrRet r sp 0 f m'' o' c ∧ Q' m'' o') := by
  intro c h
  pc_nums hx hn
  have hX : Lua.Vm.AtF.Precall.Ok (pcX sp L func nres top sl ci nci r f m o) := by fcx_ok
  have hc0 := hm.tag_w; have hc1 := hm.top_w; have hc2 := hm.sl_w; have hc3 := hm.fn_w; have hc4 := hm.ci_w
  have hg_6 : zopz0zI_s (0x140#64) (BitVec.ofNat 64 sl - BitVec.ofNat 64 top) = true := by
    have e : BitVec.ofNat 64 sl - BitVec.ofNat 64 top = BitVec.ofNat 64 (sl - top) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have h1 : (BitVec.ofNat 64 (sl - top)).toInt = ((sl - top : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; omega
    have h2 : (0x140#64 : BitVec 64).toInt = 320 := by decide
    unfold zopz0zI_s; simp only [decide_eq_true_eq]
    rw [e, h1, h2]; omega
  have hg_4 : (BitVec.ofNat 64 nci == 0x0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8000aab4#64 (Lua.Vm.AtF.Precall.r0 (pcX sp L func nres top sl ci nci r f m o))
      (ArmPay (pcX sp L func nres top sl ci nci r f m o).m (pcX sp L func nres top sl ci nci r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc5 : bytesT8 (pcX sp L func nres top sl ci nci r f m o).m (ci + 24) = BitVec.ofNat 64 nci := hnw
  fat_run Lua.Vm.AtF.Precall h acc until [0x8000ac5c]
  fcx_unfold at h
  have hk : bytesT4 (pcFrameMem m sp r f) (L + 192) = 0#32 := by
    rw [fw4_wm8 (by omega), fw4_wm8 (by omega)]; exact hm.hook_w
  obtain ⟨c', s', hq⟩ := precall_join hx hk hn hC hP _ (h.repin (by pins_of h))
  exact ⟨c', acc.trans s', hq⟩

/-- **`luaE_extendCI(L)`'s summary** at `precallC`'s `next_ci` (`ci->next`
NULL): a new `CallInfo` `nci` returned to `0x8000acc8`, `luaD_precall`'s frame
`[sp - 96, sp)` and `L->hookmask` kept, the post `R`. -/
def PcExt (sp L : Nat) (f : AbiFrame) (M : Mem) (o : Array String) (R : Nat → Mem → Prop) : Prop :=
  Triple (SegSt 0x80016a5c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp - 96) 0x8000acc8#64 (pcFr L f))
      (ArmPay M o))
    (fun c => ∃ nci m', wrRet 0x8000acc8#64 (sp - 96) nci (pcFr L f) m' o c ∧ PcNci sp nci ∧
      (∀ a, sp - 96 ≤ a → a < sp → bytesT1 m' a = bytesT1 M a) ∧ bytesT4 m' (L + 192) = 0#32 ∧ R nci m')

/-- The memory at `luaE_extendCI`'s call: the frame's saved `s0`, `ra`, and
the four arguments saved across it. -/
abbrev pcExtMem (m : Mem) (sp func nres top : Nat) (r : BitVec 64) (f : AbiFrame) : Mem :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (pcFrameMem m sp r f) (sp - 72)
    (sdData_val (BitVec.ofNat 64 nres))) (sp - 80) (sdData_val (BitVec.ofNat 64 func))) (sp - 88)
    (sdData_val (BitVec.ofNat 64 (top + 320)))) (sp - 96) (sdData_val (0x80022f18#64))

/-- **`luaD_precall` on `print` with `ci->next` NULL**: `luaE_extendCI`
(`PcExt`), then the join with the new `CallInfo`. -/
theorem precall_ext {sp L func nres top sl ci : Nat} {r : BitVec 64} {f : AbiFrame} {m : Mem}
    {o : Array String} {R : Nat → Mem → Prop} {Q Q' : Nat → Mem → Array String → Prop}
    (hx : PcNum sp L func nres top sl ci r) (hm : PcCells m L func top sl ci)
    (hnw : bytesT8 m (ci + 24) = 0#64) (hE : PcExt sp L f (pcExtMem m sp func nres top r f) o R)
    (hC : ∀ nci m', R nci m' → PcC sp L nci f (pcCallMem m' sp L func nres top nci) o (Q nci))
    (hP : ∀ nci, PcPos sp L nci r f (Q nci) (Q' nci)) :
    Triple (SegSt 0x8000aab4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 func⟩,
        ⟨Register.x12, BitVec.ofNat 64 nres⟩] sp r f) (ArmPay m o))
      (fun c => ∃ nci m'' o', wrRet r sp 0 f m'' o' c ∧ Q' nci m'' o') := by
  intro c h
  have hn0 : PcNci sp 0x8005c6d0 := ⟨by omega, by omega, by have := hx.sp_lo; omega⟩
  pc_nums hx hn0
  have hX : Lua.Vm.AtF.PrecallExt.Ok (pcX sp L func nres top sl ci 0 r f m o) := by fcx_ok
  have hc0 := hm.tag_w; have hc1 := hm.top_w; have hc2 := hm.sl_w; have hc3 := hm.fn_w; have hc4 := hm.ci_w
  have hg_6 : zopz0zI_s (0x140#64) (BitVec.ofNat 64 sl - BitVec.ofNat 64 top) = true := by
    have e : BitVec.ofNat 64 sl - BitVec.ofNat 64 top = BitVec.ofNat 64 (sl - top) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have h1 : (BitVec.ofNat 64 (sl - top)).toInt = ((sl - top : Nat) : Int) := by
      rw [BitVec.toInt_eq_toNat_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]
      simp only [BitVec.toNat_ofNat]; omega
    have h2 : (0x140#64 : BitVec 64).toInt = 320 := by decide
    unfold zopz0zI_s; simp only [decide_eq_true_eq]
    rw [e, h1, h2]; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8000aab4#64 (Lua.Vm.AtF.PrecallExt.r0 (pcX sp L func nres top sl ci 0 r f m o))
      (ArmPay (pcX sp L func nres top sl ci 0 r f m o).m (pcX sp L func nres top sl ci 0 r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc5 : bytesT8 (pcX sp L func nres top sl ci 0 r f m o).m (ci + 24) = 0x0#64 := hnw
  fat_run Lua.Vm.AtF.PrecallExt h acc until [0x80016a5c]
  fcx_unfold at h
  obtain ⟨c1, s1, nci, m', hret, hn, hkeep, hk, hR⟩ := hE _ (by
    simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s1
  simp only [wrRet] at hret
  pc_nums hx hn
  have hY : Lua.Vm.AtF.PrecallExt.Ok (pcX sp L func nres top sl ci nci r f m' o) := by fcx_ok
  have h : SegSt 0x8000acc8#64 (Lua.Vm.AtF.PrecallExt.r3 (pcX sp L func nres top sl ci nci r f m' o))
      (ArmPay (pcX sp L func nres top sl ci nci r f m' o).m (pcX sp L func nres top sl ci nci r f m' o).o) c1 :=
    hret.repin (by pins_of hret)
  have rd : ∀ a, sp - 96 ≤ a → a + 8 ≤ sp → bytesT8 m' a = bytesT8 (pcExtMem m sp func nres top r f) a :=
    fun a h1 h2 => bytesT8_congrT fun i _ => hkeep _ (by omega) (by omega)
  have hc6 : bytesT8 m' (sp - 72) = BitVec.ofNat 64 nres := by
    rw [rd _ (by omega) (by omega)]; simp (disch := omega) only [fw8_same, fw8_wm8]
  have hc7 : bytesT8 m' (sp - 80) = BitVec.ofNat 64 func := by
    rw [rd _ (by omega) (by omega)]; simp (disch := omega) only [fw8_same, fw8_wm8]
  have hc8 : bytesT8 m' (sp - 88) = BitVec.ofNat 64 (top + 320) := by
    rw [rd _ (by omega) (by omega)]; simp (disch := omega) only [fw8_same, fw8_wm8]
  have hc9 : bytesT8 m' (sp - 96) = 0x80022f18#64 := by
    rw [rd _ (by omega) (by omega)]; simp (disch := omega) only [fw8_same]
  fat_run Lua.Vm.AtF.PrecallExt h acc until [0x8000ac5c]
  fcx_unfold at h
  obtain ⟨c', s', m'', o', hq, hQ⟩ := precall_join (MJ := m') hx hk hn (hC nci m' hR) (hP nci) _
    (h.repin (by pins_of h))
  exact ⟨c', acc.trans s', nci, m'', o', hq, hQ⟩

end Lua.Vm.Sim.Kit
