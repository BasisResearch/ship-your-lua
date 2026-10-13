import Lua.Vm.Sim.Kit.CallOpen
import Lua.Vm.Sim.Kit.AllocProof
import Lua.Vm.AtF.FcloseIn
import Lua.Vm.AtF.FcloseErr
import Lua.Vm.AtF.FcloseOut
import Lua.Vm.AtF.ExitHandler

/-!
# `exit(0)` once `stdout` is set up (lane F1-14)

After a `print`, `__sinit` has installed `__stdio_exit_handler =
stdio_exit_handler`, so `exit(0)` (after `__call_exitprocs` finds no
`atexit` handler) runs `_fwalk_sglue(_REENT, _fclose_r, &__sglue)` over
`__sf`'s three streams before `_exit(0)`:

* `stdin` and `stderr` as `std()` left them (`StdQuiet`): `_fclose_r` takes
  the lock, `__sflush_r`'s read path finds nothing read ahead, the `_close`
  hook `__sclose` → `_close_r` → htif.c's `_close` frees the descriptor,
  there is no buffer to free, `_flags` is cleared (`fclose_quiet`; the
  at-lemmas `Lua/Vm/AtF/{FcloseIn,FcloseErr}.lean`);
* `stdout` set up and flushed: `__sflush_r` (`sflush_sum`, nothing pending),
  the `_close` hook, `_free_r` of its buffer (`FreeR_Statement`, the one
  named premise), `_flags` cleared (`fclose_out`, `AtF/FcloseOut.lean`);
* `_fwalk_sglue`'s walk over `__sglue`'s one array of three
  (`exit_handler_sum`, `AtF/ExitHandler.lean`: a root after each call);
* `exit` itself: `__call_exitprocs`, the handler, `_exit`'s `tohost` store
  (`exit_run_up`).

What `exit` reads of the stdio globals is the `CALL` invariant's
(`StdoutIn.up`: `StdoutAt`, `StdioUp` with `stdout`'s tail and the standard
descriptors, `StdioRest`), so `ExitUp_Statement` follows from the invariant
(`exitUp_of_free`): `ExitOk`'s memory agrees with the complement off the C
stack and the `lua_State`, `CallInfo` and register slots, which lie in
chunks in use apart from `stdout`'s buffer.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- `bnez` on a nonzero word, sign-extended. -/
theorem sext_ne0 {x : BitVec 32} (h : x ≠ 0#32) : (sign_extend (m := 64) (x : BitVec (8 * 4)) != 0x0#64) = true := by
  simp only [bne_iff_ne, ne_eq]
  intro e; apply h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) e
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_zero] at this
  simpa [hi, show i < 64 by omega] using this

theorem beq0_false {x : BitVec 64} (h : x ≠ 0#64) : (x == 0x0#64) = false := by
  simpa only [beq_eq_false_iff_ne] using h

/-- **What a quiet `_fclose_r` writes**: the stream's `_flags`, its
descriptor's `kind`, `errno`, its stack. -/
def QuietW (sp fp fd a : Nat) : Prop :=
  Rng (fp + 16) 2 a ∨ Rng (symFds + 24 * fd) 4 a ∨ Rng errnoAddr 4 a ∨ Below sp 128 a

set_option hygiene false in
/-- The facts a quiet `_fclose_r`'s at-lemmas read, at their literal addresses. -/
macro "quiet_facts" hq:ident hk:ident hin:ident hrd:ident : tactic => `(tactic| (
  obtain ⟨hc2, hc1, hc6, hc5, hc4, hc8, hc3, hc9, hc0⟩ := $hq
  have hc7 := $hk
  have hg_2 := beq0_false $hin
  have hg_5 := sext_ne0 $hrd
  simp only [stdinFile, stderrFile, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hg_2 hg_5))

set_option hygiene false in
/-- The quiet `_fclose_r` run: its one root, then the keep. -/
macro "quiet_run" ns:ident ok:ident r0:ident : tactic => `(tactic| (
  intro c h
  let X := abiCx sp r f m o
  have hX : $ok X := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032580#64 ($r0 X) (ArmPay X.m X.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run $ns h acc
  fcx_unfold at h
  refine ⟨_, acc, _, h.repin (by pins_of h), fun a ha => ?_⟩
  fs_nums
  simp only [QuietW, Rng, Below, not_or, not_and, Nat.not_lt] at ha
  simp only [stdinFile, stderrFile, symSf, fileSize] at ha
  simp only [show X.n 0 = sp from rfl, show X.m = m from rfl]
  exact AtF.bT1_congr (by fs_off)))

/-- **`_fclose_r(_REENT, stdin)` at `exit`**: `0` returned, `QuietW` written. -/
theorem fclose_in (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : StdQuiet m stdinFile 0x4#16 0#16) (hk : bytesT4 m (symFds + 24 * 0) = 1#32)
    (hin : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64) (hrd : bytesT4 m symFsReady ≠ 0#32) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdinFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ QuietW sp stdinFile 0 a → bytesT1 m' a = bytesT1 m a) := by
  quiet_facts hq hk hin hrd
  quiet_run Lua.Vm.AtF.FcloseIn Lua.Vm.AtF.FcloseIn.Ok Lua.Vm.AtF.FcloseIn.r0

/-- **`_fclose_r(_REENT, stderr)` at `exit`**: `0` returned, `QuietW` written. -/
theorem fclose_err (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : StdQuiet m stderrFile 0x12#16 2#16) (hk : bytesT4 m (symFds + 24 * 2) = 3#32)
    (hin : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64) (hrd : bytesT4 m symFsReady ≠ 0#32) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stderrFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ QuietW sp stderrFile 2 a → bytesT1 m' a = bytesT1 m a) := by
  quiet_facts hq hk hin hrd
  quiet_run Lua.Vm.AtF.FcloseErr Lua.Vm.AtF.FcloseErr.Ok Lua.Vm.AtF.FcloseErr.r0

/-- **What `_fclose_r(stdout)` writes**: `stdout`, `fds[1]`, the allocator's
globals (with `errno`) and the arena (`_free_r`), its stack. -/
def OutW (sp a : Nat) : Prop :=
  Rng stdoutFile fileSize a ∨ Rng (symFds + 24) 4 a ∨ MallocGlobal a ∨ (heapStart ≤ a ∧ a < heapEnd) ∨
    Below sp 2048 a

/-- The frame `_fclose_r` hands its callees (`s0 = stdout`, `s1 = _REENT`, `s2`). -/
abbrev fcFr (s2 : BitVec 64) (f : AbiFrame) : AbiFrame :=
  ⟨0x8005e668#64, 0x8005d1b8#64, s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- **`_fclose_r(_REENT, stdout)` at `exit`** on the set-up, flushed
`stdout`: `__sflush_r` (`sflush_sum`), the `_close` hook, `_free_r` of the
buffer (`FreeR_Statement`); `0` returned, `OutW` written. -/
theorem fclose_out (hF : FreeR_Statement) (sp buf : Nat) (H : HeapIx) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32)
    (hal : sp % 16 = 0) (hs : StdoutAt m buf []) (hf2 : bytesT4 m (stdoutFile + fileFlags2Off) = 0#32)
    (ht : StdoutTail m) (hin : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64) (hb : BufOwned H buf)
    (hH : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ OutW sp a → bytesT1 m' a = bytesT1 m a) := by
  intro c h
  have hb0 := hs.buf_lo; have hbl := hb.lo; have hbh := hb.hi
  fs_nums
  stdio_nums
  have e1 : symFreeR = 0x8003be24 := rfl
  -- root 0: up to `__sflush_r`
  let X0 := abiCx sp r f m o
  have hX0 : Lua.Vm.AtF.FcloseOut.Ok X0 := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032580#64 (Lua.Vm.AtF.FcloseOut.r0 X0) (ArmPay X0.m X0.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT4 X0.m 0x8005e718 = 0x0#32 := hf2
  have hc1 : bytesT2 X0.m 0x8005e678 = 0x2889#16 := hs.flags
  have hc2 : bytesT8 X0.m 0x8005e6b8 = 0x80035004#64 := ht.close
  have hc3 : bytesT8 X0.m 0x8005e698 = 0x8005e668#64 := hs.cookie
  have hc4 : bytesT2 X0.m 0x8005e67a = 0x1#16 := hs.file
  have hc5 : bytesT4 X0.m 0x8005d478 = 0x2#32 := hs.stdout
  have hc6 : bytesT8 X0.m 0x8005e6c0 = 0x0#64 := ht.ub
  have hc7 : bytesT8 X0.m 0x8005e6e0 = 0x0#64 := ht.lb
  have hg_2 : (bytesT8 X0.m 0x8005d200 == 0x0#64) = false := beq0_false hin
  have hg_5 : (sign_extend (m := 64) (bytesT4 X0.m 0x8005d3c0 : BitVec (8 * 4)) != 0x0#64) = true :=
    sext_ne0 hs.ready
  fat_run Lua.Vm.AtF.FcloseOut h acc until [0x800326f8]
  have h1 : SegSt 0x800326f8#64 (sflPre 0x8005d1b8#64 (sp - 32) 0x800325d0#64 (fcFr f.s2 f))
      (ArmPay (Lua.Vm.AtF.FcloseOut.m1 X0) o) _ := h.repin (by pins_of h)
  have km1 : ∀ a, (a < sp - 32 ∨ sp ≤ a) → bytesT1 (Lua.Vm.AtF.FcloseOut.m1 X0) a = bytesT1 m a := fun a ha =>
    AtF.bT1_congr (by simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl, show X0.m = m from rfl]; fs_off)
  have hs1 : StdoutAt (Lua.Vm.AtF.FcloseOut.m1 X0) buf [] := hs.below fun a ha => by
    simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl, show X0.m = m from rfl]; fs_off
  obtain ⟨c2, s2, m2, hret, hout⟩ := sflush_sum 0x8005d1b8#64 (sp - 32) buf [] 0x800325d0#64 (fcFr f.s2 f) _ o
    ⟨by decide, by omega, by omega, by omega⟩ hs1 _ h1
  have acc := acc.trans s2
  -- root 1: the `_close` hook, up to `_free_r`
  have kF : ∀ a, stdoutFile + 18 ≤ a → a < stdoutFile + fileSize → bytesT1 m2 a = bytesT1 m a := fun a h1 h2 =>
    (hout.keep_file a h1 h2).trans (km1 a (by omega))
  have kL : ∀ a, a + 512 ≤ sp - 32 → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
      (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m2 a = bytesT1 m a := fun a h1 h2 h3 =>
    (hout.keep_lo a h1 h2 h3).trans (km1 a (by omega))
  let X1 := abiCx sp r f m2 o
  have hX1 : Lua.Vm.AtF.FcloseOut.Ok X1 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hret
  have h : SegSt 0x800325d0#64 (Lua.Vm.AtF.FcloseOut.r3 X1) (ArmPay X1.m X1.o) c2 := hret.repin (by pins_of hret)
  have hc0 : bytesT4 X1.m 0x8005e718 = 0x0#32 := (bytesT4_congrT fun i _ => kF _ (by omega) (by omega)).trans hf2
  have hc1 : bytesT2 X1.m 0x8005e678 = 0x2889#16 := hout.stdout.flags
  have hc2 : bytesT8 X1.m 0x8005e6b8 = 0x80035004#64 :=
    (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans ht.close
  have hc3 : bytesT8 X1.m 0x8005e698 = 0x8005e668#64 := hout.stdout.cookie
  have hc4 : bytesT2 X1.m 0x8005e67a = 0x1#16 := hout.stdout.file
  have hc5 : bytesT4 X1.m 0x8005d478 = 0x2#32 := hout.stdout.stdout
  have hc6 : bytesT8 X1.m 0x8005e6c0 = 0x0#64 := (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans ht.ub
  have hc7 : bytesT8 X1.m 0x8005e6e0 = 0x0#64 := (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans ht.lb
  have hg_5 : (sign_extend (m := 64) (bytesT4 X1.m 0x8005d3c0 : BitVec (8 * 4)) != 0x0#64) = true :=
    sext_ne0 hout.stdout.ready
  have fr : ∀ k, 1 ≤ k → k ≤ 4 → bytesT8 m2 (sp - 8 * k) = bytesT8 (Lua.Vm.AtF.FcloseOut.m1 X0) (sp - 8 * k) :=
    fun k h1 h2 => bytesT8_congrT fun i _ => hout.keep_hi _ (by omega)
  have hc8 : bytesT8 X1.m (X1.n 0 - 8) = X1.b 0 := (fr 1 (by omega) (by omega)).trans (by
    simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl]
    simp (disch := omega) only [fw8_same, fw8_wm8]; rfl)
  have hc9 : bytesT8 X1.m (X1.n 0 - 16) = X1.b 1 := (fr 2 (by omega) (by omega)).trans (by
    simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl]
    simp (disch := omega) only [fw8_same, fw8_wm8]; rfl)
  have hc10 : bytesT8 X1.m (X1.n 0 - 24) = X1.b 2 := (fr 3 (by omega) (by omega)).trans (by
    simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl]
    simp (disch := omega) only [fw8_same, fw8_wm8]; rfl)
  have hc11 : bytesT8 X1.m (X1.n 0 - 32) = X1.b 3 := (fr 4 (by omega) (by omega)).trans (by
    simp only [Lua.Vm.AtF.FcloseOut.m1, show X0.n 0 = sp from rfl]
    simp (disch := omega) only [fw8_same, fw8_wm8]; rfl)
  fat_run Lua.Vm.AtF.FcloseOut h acc until [0x8003be24]
  have hbase : bytesT8 X1.m 0x8005e680 = BitVec.ofNat 64 buf := hout.stdout.base
  simp only [Lua.Vm.AtF.FcloseOut.r5, hbase] at h
  have h3 : SegSt (BitVec.ofNat 64 symFreeR) (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 buf⟩] (sp - 32) 0x800326a4#64 (fcFr 0#64 f))
      (ArmPay (Lua.Vm.AtF.FcloseOut.m4 X1) o) _ := h.repin (by pins_of h)
  have km4 : ∀ a, (a < sp - 64 ∨ sp - 32 ≤ a) → (a < errnoAddr ∨ errnoAddr + 4 ≤ a) →
      (a < symFds + 24 ∨ symFds + 28 ≤ a) → bytesT1 (Lua.Vm.AtF.FcloseOut.m4 X1) a = bytesT1 m2 a :=
    fun a h1 h2 h3 => AtF.bT1_congr (by
      simp only [Lua.Vm.AtF.FcloseOut.m4, show X1.n 0 = sp from rfl, show X1.m = m2 from rfl]; fs_off)
  have hH4 : HeapAt (fillZeroMem (Lua.Vm.AtF.FcloseOut.m4 X1)) H.top H.brk H.chunks H.bins :=
    hH.ofTotal fun a hr _ => by
      have : a < heapEnd + 32 := by simp only [HeapReads] at hr; omega
      have : a < stdoutFile ∨ stdoutFile + fileSize ≤ a := by simp only [HeapReads] at hr; omega
      have : a < errnoAddr ∨ errnoAddr + 4 ≤ a := by simp only [HeapReads] at hr; omega
      have : a < symFds + 24 ∨ symFds + 28 ≤ a := by simp only [HeapReads] at hr; omega
      rw [km4 a (by omega) (by omega) (by omega), kL a (by omega) (by omega) (by omega), bytesT1_fill]
  obtain ⟨sz, hsz, _⟩ := hb.block
  obtain ⟨c4, s4, m3, hret3, hk3⟩ := hF (sp - 32) buf H.top H.brk H.chunks H.bins 0x800326a4#64 (fcFr 0#64 f)
    _ o hH4 (by decide) (by omega) (by omega) (by rw [show heapEnd = 0x87800000 from rfl]; omega) ⟨sz, hsz⟩ hbl _ h3
  have acc := acc.trans s4
  -- root 2: the unlocks, the return
  have k3 : ∀ a, (a < heapStart ∨ heapEnd ≤ a) → (a + 1024 ≤ sp - 32 ∨ sp - 32 ≤ a) → ¬ MallocGlobal a →
      bytesT1 m3 a = bytesT1 (Lua.Vm.AtF.FcloseOut.m4 X1) a := fun a h1 h2 h3 => AtF.bT1_congr (hk3 a h3 h1 h2)
  have nmg : ∀ a, stdoutFile ≤ a → ¬ MallocGlobal a := fun a ha hm => by
    simp only [MallocGlobal] at hm; omega
  let X2 := abiCx sp r f m3 o
  have hX2 : Lua.Vm.AtF.FcloseOut.Ok X2 := ⟨hlo, hhi, hal, hra⟩
  have h : SegSt 0x800326a4#64 (Lua.Vm.AtF.FcloseOut.r6 X2) (ArmPay X2.m X2.o) c4 := hret3.repin (by pins_of hret3)
  have kS : ∀ a, stdoutFile + 18 ≤ a → a < stdoutFile + fileSize → bytesT1 m3 a = bytesT1 m a := fun a h1 h2 =>
    (k3 a (by omega) (by omega) (nmg a (by omega))).trans ((km4 a (by omega) (by omega) (by omega)).trans
      (kF a h1 h2))
  have hc0 : bytesT4 X2.m 0x8005e718 = 0x0#32 := (bytesT4_congrT fun i _ => kS _ (by omega) (by omega)).trans hf2
  have hc6 : bytesT8 X2.m 0x8005e6c0 = 0x0#64 := (bytesT8_congrT fun i _ => kS _ (by omega) (by omega)).trans ht.ub
  have hc7 : bytesT8 X2.m 0x8005e6e0 = 0x0#64 := (bytesT8_congrT fun i _ => kS _ (by omega) (by omega)).trans ht.lb
  have fr2 : ∀ k, 1 ≤ k → k ≤ 4 → bytesT8 m3 (sp - 8 * k) = bytesT8 m2 (sp - 8 * k) := fun k h1 h2 =>
    bytesT8_congrT fun i _ => (k3 _ (by omega) (by omega) (nmg _ (by omega))).trans
      (km4 _ (by omega) (by omega) (by omega))
  have hc8 : bytesT8 X2.m (X2.n 0 - 8) = X2.b 0 := (fr2 1 (by omega) (by omega)).trans hc8
  have hc9 : bytesT8 X2.m (X2.n 0 - 16) = X2.b 1 := (fr2 2 (by omega) (by omega)).trans hc9
  have hc10 : bytesT8 X2.m (X2.n 0 - 24) = X2.b 2 := (fr2 3 (by omega) (by omega)).trans hc10
  have hc11 : bytesT8 X2.m (X2.n 0 - 32) = X2.b 3 := (fr2 4 (by omega) (by omega)).trans hc11
  fat_run Lua.Vm.AtF.FcloseOut h acc
  fcx_unfold at h
  refine ⟨_, acc, _, h.repin (by pins_of h), fun a ha => ?_⟩
  simp only [OutW, Rng, Below, not_or, not_and, Nat.not_lt] at ha
  obtain ⟨h1, h2, h3, h4, h5⟩ := ha
  have h4' : a < heapStart ∨ heapEnd ≤ a := by omega
  have hst : a < stdoutFile ∨ stdoutFile + fileSize ≤ a := by omega
  have herr : a < errnoAddr ∨ errnoAddr + 4 ≤ a := by simp only [MallocGlobal, not_or] at h3; omega
  rw [AtF.bT1_congr (getElem?_writeMap2_out _ _ _ _ (by omega)),
    k3 a h4' (by omega) h3, km4 a (by omega) herr (by omega)]
  by_cases hup : sp ≤ a
  · exact (hout.keep_hi a (by omega)).trans (km1 a (.inr hup))
  · exact kL a (by omega) hst herr

/-! ## `stdio_exit_handler` -/

/-- `stdout` across a change off its own words (its `FILE`, `fs_ready`,
`fds[1]`, its buffer). -/
theorem StdoutAtW.congrF {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} {wv : BitVec 32}
    (h : StdoutAtW m buf pend wv)
    (hk : ∀ a, Rng stdoutFile fileSize a ∨ Rng symFsReady 4 a ∨ Rng (symFds + 24) 4 a ∨ Rng buf 1024 a →
      bytesT1 m' a = bytesT1 m a) : StdoutAtW m' buf pend wv := by
  stdio_nums
  have hr := h.room
  have kF : ∀ a, stdoutFile ≤ a → a < stdoutFile + fileSize → bytesT1 m' a = bytesT1 m a := fun a h1 h2 =>
    hk a (.inl ⟨h1, h2⟩)
  refine ⟨(bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans h.p,
    (bytesT4_congrT fun i _ => kF _ (by omega) (by omega)).trans h.w,
    (bT2_congrT fun i _ => (kF _ (by omega) (by omega)).symm).symm.trans h.flags,
    (bT2_congrT fun i _ => (kF _ (by omega) (by omega)).symm).symm.trans h.file,
    (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans h.base,
    (bytesT4_congrT fun i _ => kF _ (by omega) (by omega)).trans h.size,
    (bytesT4_congrT fun i _ => kF _ (by omega) (by omega)).trans h.lbf,
    (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans h.cookie,
    (bytesT8_congrT fun i _ => kF _ (by omega) (by omega)).trans h.write, ?_, h.room, h.buf_lo, h.buf_hi, ?_,
    (bytesT4_congrT fun i _ => hk _ (.inr (.inr (.inl ⟨by omega, by omega⟩)))).trans h.stdout⟩
  · rw [bytesAt_congr fun i hi => hk _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))]; exact h.bytes
  · rw [bytesT4_congrT fun i _ => hk _ (.inr (.inl ⟨by omega, by omega⟩))]; exact h.ready

/-- **`_fwalk_sglue`'s saved registers** (`[sp - 72, sp)`: `ra`, `s0`–`s7`)
in a memory. -/
def HdSlots (M : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : Prop :=
  ∀ k, k < 9 → bytesT8 M (sp - 8 * (k + 1)) = [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7].getD k 0

theorem HdSlots.keep {M M' : Mem} {sp : Nat} {r : BitVec 64} {f : AbiFrame} (h : HdSlots M sp r f)
    (hk : ∀ a, sp - 72 ≤ a → a < sp → bytesT1 M' a = bytesT1 M a) (h72 : 72 ≤ sp) : HdSlots M' sp r f :=
  fun k hk' => (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans (h k hk')

set_option hygiene false in
/-- The saved registers as the at-lemmas state them, at the root `X`. -/
macro "hd_slots" hS:ident X:ident : tactic => `(tactic| (
  have hc9 : bytesT8 ($X).m (($X).n 0 - 8) = ($X).b 0 := $hS 0 (by decide)
  have hc10 : bytesT8 ($X).m (($X).n 0 - 16) = ($X).b 1 := $hS 1 (by decide)
  have hc11 : bytesT8 ($X).m (($X).n 0 - 24) = ($X).b 2 := $hS 2 (by decide)
  have hc12 : bytesT8 ($X).m (($X).n 0 - 32) = ($X).b 3 := $hS 3 (by decide)
  have hc13 : bytesT8 ($X).m (($X).n 0 - 40) = ($X).b 4 := $hS 4 (by decide)
  have hc14 : bytesT8 ($X).m (($X).n 0 - 48) = ($X).b 5 := $hS 5 (by decide)
  have hc15 : bytesT8 ($X).m (($X).n 0 - 56) = ($X).b 6 := $hS 6 (by decide)
  have hc17 : bytesT8 ($X).m (($X).n 0 - 64) = ($X).b 7 := $hS 7 (by decide)
  have hc16 : bytesT8 ($X).m (($X).n 0 - 72) = ($X).b 8 := $hS 8 (by decide)))

/-- The frame `_fwalk_sglue` hands `_fclose_r` (`s0` the stream). -/
abbrev fwFr (fp : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 fp, 0x8005e7d8#64, 0x8005cee0#64, 0xffffffffffffffff#64, 0x8005d1b8#64, 0x80032580#64,
    0#64, 1#64, f.s8, f.s9, f.s10, f.s11⟩

/-- **`stdio_exit_handler()`** (`exit`'s `__stdio_exit_handler`) on `stdout`
set up and flushed and the other streams quiet: `_fwalk_sglue` closes the
three streams (`fclose_in`, `fclose_out`, `fclose_err`) and returns. -/
theorem exit_handler_sum (hF : FreeR_Statement) (sp buf : Nat) (H : HeapIx) (r : BitVec 64) (f : AbiFrame)
    (M : Mem) (o : Array String) (hra : r.toNat % 4 = 0) (hlo' : 0x87800000 + 16384 ≤ sp) (hhi : sp ≤ 2 ^ 32)
    (hal : sp % 16 = 0) (hs : StdoutAt M buf []) (hu : StdioUp M) (hR : StdioRest M) (hb : BufOwned H buf)
    (hH : HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins) :
    Triple (SegSt 0x80032af8#64 (callPre [] sp r f) (ArmPay M o)) (fun c => ∃ M', voidRet r sp f M' o c) := by
  intro c h
  have hb0 := hs.buf_lo; have hbl := hb.lo; have hbh := hb.hi
  fs_nums
  stdio_nums
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : stdinFile = 0x8005e5b0 := rfl
  have : stderrFile = 0x8005e720 := rfl
  have hlo : 0x87800000 + 8192 ≤ sp := by omega
  -- root 0: up to `_fclose_r(stdin)`
  let X0 := abiCx sp r f M o
  have hX0 : Lua.Vm.AtF.ExitHandler.Ok X0 := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.nil_append] at h
  have h : SegSt 0x80032af8#64 (Lua.Vm.AtF.ExitHandler.r0 X0) (ArmPay X0.m X0.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT4 X0.m 0x8005cee8 = 0x3#32 := hR.glue_niobs
  have hc1 : bytesT8 X0.m 0x8005cef0 = 0x8005e5b0#64 := hR.glue_iobs
  have hc2 : bytesT2 X0.m 0x8005e5c0 = 0x4#16 := hR.stdin.flags
  have hc3 : bytesT2 X0.m 0x8005e5c2 = 0x0#16 := hR.stdin.file
  have hc4 : bytesT2 X0.m 0x8005e678 = 0x2889#16 := hs.flags
  have hc5 : bytesT2 X0.m 0x8005e67a = 0x1#16 := hs.file
  have hc6 : bytesT2 X0.m 0x8005e730 = 0x12#16 := hR.stderr.flags
  have hc7 : bytesT2 X0.m 0x8005e732 = 0x2#16 := hR.stderr.file
  have hc8 : bytesT8 X0.m 0x8005cee0 = 0x0#64 := hR.glue_next
  fat_run Lua.Vm.AtF.ExitHandler h acc until [0x80032580]
  have h1 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdinFile⟩] (sp - 80) 0x800340b4#64 (fwFr stdinFile f))
      (ArmPay (Lua.Vm.AtF.ExitHandler.m0 X0) o) _ := h.repin (by pins_of h)
  have k0 : ∀ a, (a < sp - 80 ∨ sp ≤ a) → bytesT1 (Lua.Vm.AtF.ExitHandler.m0 X0) a = bytesT1 M a := fun a ha =>
    AtF.bT1_congr (by
      simp only [Lua.Vm.AtF.ExitHandler.m0, show X0.n 0 = sp from rfl, show X0.m = M from rfl]; fs_off)
  have hS0 : HdSlots (Lua.Vm.AtF.ExitHandler.m0 X0) sp r f := fun k hk => by
    simp only [Lua.Vm.AtF.ExitHandler.m0, show X0.n 0 = sp from rfl]
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      simp (disch := omega) only [fw8_same, fw8_wm8] <;> rfl
  have lo : ∀ a, a < stdoutFile + 2 * fileSize → a < sp - 80 := fun a ha => by omega
  obtain ⟨c1, s1, m1, hr1, q1⟩ := fclose_in (sp - 80) 0x800340b4#64 (fwFr stdinFile f) _ o (by decide)
    (by omega) (by omega) (by omega)
    (hR.stdin.congrT fun a h1 h2 => k0 a (.inl (by omega)))
    ((bytesT4_congrT fun i _ => k0 _ (.inl (by omega))).trans hu.fds.fd0)
    (by rw [bytesT8_congrT fun i _ => k0 _ (.inl (by omega))]; exact hu.init)
    (by rw [bytesT4_congrT fun i _ => k0 _ (.inl (by omega))]; exact hs.ready) _ h1
  have acc := acc.trans s1
  -- the memory after `stdin`, against `M`
  have t1 : ∀ a, ¬ QuietW (sp - 80) stdinFile 0 a → (a < sp - 80 ∨ sp ≤ a) → bytesT1 m1 a = bytesT1 M a :=
    fun a h1 h2 => (q1 a h1).trans (k0 a h2)
  have hS1 : HdSlots m1 sp r f := hS0.keep (fun a h1 h2 => q1 a (by
    simp only [QuietW, Rng, Below, stdinFile, symSf]; omega)) (by omega)
  -- root 1: up to `_fclose_r(stdout)`
  let X1 := abiCx sp r f m1 o
  have hX1 : Lua.Vm.AtF.ExitHandler.Ok X1 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr1
  have h : SegSt 0x800340b4#64 (Lua.Vm.AtF.ExitHandler.r3 X1) (ArmPay X1.m X1.o) c1 := hr1.repin (by pins_of hr1)
  have u1 : ∀ a, (stdoutFile ≤ a ∧ a < stdoutFile + fileSize) ∨ (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨
      (symFsReady ≤ a ∧ a < symFsReady + 4) ∨ (symFds + 24 ≤ a ∧ a < symFds + 52) ∨
      (symSglue ≤ a ∧ a < symSglue + 24) ∨ (stderrFile ≤ a ∧ a < stderrFile + fileSize) ∨ heapStart ≤ a ∧ a < heapEnd + 32 ∨
      (0x8005c6d0 ≤ a ∧ a < 0x8005e5b0 ∧ (a < 0x8005d408 ∨ 0x8005d40c ≤ a) ∧ (a < 0x8005d460 ∨ 0x8005d464 ≤ a)) →
      bytesT1 m1 a = bytesT1 M a := fun a ha => t1 a (by
        simp only [QuietW, Rng, Below, stdinFile, stderrFile, symSf, not_or, not_and, Nat.not_lt]; omega) (by omega)
  have hsA : StdoutAt m1 buf [] := hs.congrF fun a ha => u1 a (by simp only [Rng] at ha; omega)
  hd_slots hS1 X1
  have hc4 : bytesT2 X1.m 0x8005e678 = 0x2889#16 := hsA.flags
  have hc5 : bytesT2 X1.m 0x8005e67a = 0x1#16 := hsA.file
  have hc6 : bytesT2 X1.m 0x8005e730 = 0x12#16 :=
    (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hR.stderr.flags
  have hc7 : bytesT2 X1.m 0x8005e732 = 0x2#16 :=
    (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hR.stderr.file
  have hc8 : bytesT8 X1.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => u1 _ (by omega)).trans hR.glue_next
  fat_run Lua.Vm.AtF.ExitHandler h acc until [0x80032580]
  have h2 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (sp - 80) 0x800340b4#64 (fwFr stdoutFile f))
      (ArmPay m1 o) _ := h.repin (by pins_of h)
  have hH1 : HeapAt (fillZeroMem m1) H.top H.brk H.chunks H.bins :=
    hH.ofTotal fun a hr _ => by
      rw [u1 a (by simp only [HeapReads, MallocGlobal] at hr; omega), bytesT1_fill]
  obtain ⟨c2, s2, m2, hr2, q2⟩ := fclose_out hF (sp - 80) buf H 0x800340b4#64 (fwFr stdoutFile f) m1 o
    (by decide) (by omega) (by omega) (by omega) hsA
    ((bytesT4_congrT fun i _ => u1 _ (by omega)).trans hu.flags2)
    (hu.tail.congrT fun a h1 h2 => u1 a (by omega))
    (by rw [bytesT8_congrT fun i _ => u1 _ (by omega)]; exact hu.init) hb hH1 _ h2
  have acc := acc.trans s2
  -- root 2: up to `_fclose_r(stderr)`
  have u2 : ∀ a, (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨ (symFsReady ≤ a ∧ a < symFsReady + 4) ∨
      (symFds + 48 ≤ a ∧ a < symFds + 52) ∨ (symSglue ≤ a ∧ a < symSglue + 24) ∨
      (stderrFile ≤ a ∧ a < stderrFile + fileSize) → bytesT1 m2 a = bytesT1 M a := fun a ha =>
    (q2 a (by simp only [OutW, MallocGlobal, Rng, Below, not_or, not_and, Nat.not_lt]; omega)).trans
      (u1 a (by omega))
  have hS2 : HdSlots m2 sp r f := hS1.keep (fun a h1 h2 => q2 a (by
    simp only [OutW, MallocGlobal, Rng, Below, not_or, not_and, Nat.not_lt]; omega)) (by omega)
  let X2 := abiCx sp r f m2 o
  have hX2 : Lua.Vm.AtF.ExitHandler.Ok X2 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr2
  have h : SegSt 0x800340b4#64 (Lua.Vm.AtF.ExitHandler.r6 X2) (ArmPay X2.m X2.o) c2 := hr2.repin (by pins_of hr2)
  hd_slots hS2 X2
  have hc6 : bytesT2 X2.m 0x8005e730 = 0x12#16 :=
    (bT2_congrT fun i _ => (u2 _ (by omega)).symm).symm.trans hR.stderr.flags
  have hc7 : bytesT2 X2.m 0x8005e732 = 0x2#16 :=
    (bT2_congrT fun i _ => (u2 _ (by omega)).symm).symm.trans hR.stderr.file
  have hc8 : bytesT8 X2.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => u2 _ (by omega)).trans hR.glue_next
  fat_run Lua.Vm.AtF.ExitHandler h acc until [0x80032580]
  have h3 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stderrFile⟩] (sp - 80) 0x800340b4#64 (fwFr stderrFile f))
      (ArmPay m2 o) _ := h.repin (by pins_of h)
  obtain ⟨c3, s3, m3, hr3, q3⟩ := fclose_err (sp - 80) 0x800340b4#64 (fwFr stderrFile f) m2 o (by decide)
    (by omega) (by omega) (by omega)
    (hR.stderr.congrT fun a h1 h2 => u2 a (by omega))
    ((bytesT4_congrT fun i _ => u2 _ (by omega)).trans hu.fds.fd2)
    (by rw [bytesT8_congrT fun i _ => u2 _ (by omega)]; exact hu.init)
    (by rw [bytesT4_congrT fun i _ => u2 _ (by omega)]; exact hs.ready) _ h3
  have acc := acc.trans s3
  -- root 3: `__sglue`'s end, the return
  have hS3 : HdSlots m3 sp r f := hS2.keep (fun a h1 h2 => q3 a (by
    simp only [QuietW, Rng, Below, stderrFile, symSf]; omega)) (by omega)
  let X3 := abiCx sp r f m3 o
  have hX3 : Lua.Vm.AtF.ExitHandler.Ok X3 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr3
  have h : SegSt 0x800340b4#64 (Lua.Vm.AtF.ExitHandler.r9 X3) (ArmPay X3.m X3.o) c3 := hr3.repin (by pins_of hr3)
  hd_slots hS3 X3
  have hc8 : bytesT8 X3.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => (q3 _ (by simp only [QuietW, Rng, Below, stderrFile, symSf]; omega)).trans
      (u2 _ (by omega))).trans hR.glue_next
  fat_run Lua.Vm.AtF.ExitHandler h acc
  fcx_unfold at h
  exact ⟨_, acc, _, h.repin (by pins_of h)⟩

/-! ## `exit(0)` -/

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, Ret.sl_negX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    Nat.reduceAdd, symGlobalPointer, Ret.bytesT8_wm8_hitX, Ret.bytesT8_wm8_out', sext64_id, hat,
    hsx] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (rw [Ret.rtgt _ (by decide)]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          Nat.reduceAdd, symGlobalPointer, Ret.bytesT8_wm8_hitX, Ret.bytesT8_wm8_out', sext64_id, hat,
          hsx, Vsa.Sim.sext_zero, BitVec.add_zero]
         first | decide | (rw [Ret.rtgt _ (by decide)]; decide)))

/-- **`exit(0)` once `stdout` is set up halts with code 0**: no `atexit`
handler, `__stdio_exit_handler = stdio_exit_handler` (`exit_handler_sum`),
then `_exit`'s `tohost` store; the console unchanged (`stdout` is flushed). -/
theorem exit_run_up (hF : FreeR_Statement) {M : Mem} {o : Array String} {c : Config}
    {q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64} {buf : Nat} {H : HeapIx}
    (h : SegSt (BitVec.ofNat 64 symCExit) (exitRow q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27)
      (ArmPay M o) c)
    (hat : bytesT8 M symAtexit = 0#64) (hs : StdoutAt M buf []) (hu : StdioUp M) (hR : StdioRest M)
    (hb : BufOwned H buf) (hH : HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins) :
    Vsa.Machine.Halts c (Vsa.Machine.output c.σ) 0 := by
  have acc := Steps.refl c
  have hout := h.armOut
  have hsx : bytesT8 M symStdioExitHandler = 0x80032af8#64 := hR.handler
  simp only [symAtexit, symStdioExitHandler] at hat hsx
  simp only [exitRow, symCExit] at h
  kit_run h acc
  have h := h.at (Ret.rtgt _ (by decide))
  kit_run h acc
  have h := h.at (Ret.rtgt _ (by decide))
  kit_run h acc until [0x80032af8]
  rename_i c1
  have hm1 := h.armMem
  have h := h.mem_eq hm1.symm
  have lo1 : ∀ a, a < 0x87ff0000 → bytesT1 c1.σ.mem a = bytesT1 M a := fun a ha => by
    rw [hm1]; exact AtF.bT1_congr (by fs_off)
  have hb0 := hs.buf_lo; have hbl := hb.lo; have hbh := hb.hi
  fs_nums
  stdio_nums
  have lo1' : ∀ a, a < 0x87ff0000 → c1.σ.mem[a]? = M[a]? := fun a ha => by rw [hm1]; fs_off
  obtain ⟨c2, s2, M2, h2⟩ := exit_handler_sum hF 0x87fffff0 buf H 0x8002f880#64
    ⟨0#64, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27⟩ c1.σ.mem o (by decide) (by decide) (by decide)
    (by decide) (hs.congrF fun a ha => lo1 a (by simp only [Rng] at ha; omega))
    (hu.below fun a ha => lo1' a (by omega))
    (hR.congrT fun a ha => lo1 a (by have := ha.range; omega)) hb
    (hH.ofTotal fun a hr _ => by
      rw [lo1 a (by simp only [HeapReads] at hr; omega), bytesT1_fill]) _ (h.repin (by pins_of h))
  have acc := acc.trans s2
  simp only [voidRet, AbiFrame.pins] at h2
  have h := h2
  kit_run h acc until [0x8000064c]
  obtain ⟨σf, hh, ho⟩ := Ret.exit_halt (L := []) (h.repin (by pins_of h))
  refine ⟨_, σf, acc, hh, ho.trans ?_⟩
  exact output_congr (h.armOut.trans hout.symm)

/-- **Where `exit` may find the memory changed** on the `CALL` invariant:
the C stack, or chunks in use apart from `stdout`'s buffer (the `lua_State`,
the `CallInfo`, the register slots). -/
theorem exitFree_kept {p : Lua.Bytecode.Proto} {w : RelPtrs} {buf : Nat} {F FL : Nat → Prop} {ls : LitPtrs}
    (hI : CallInvAt p w (.up buf []) F FL ls) {a : Nat} (h : ExitFree p w a) :
    RuntimeData.spEntry - cStackBudget ≤ a ∨ Kept w.rt.hix (.up buf []) a := by
  rcases h with h | h | h | h
  · exact .inl h.1
  · exact .inr (hI.L_in a h.1 h.2)
  · exact .inr (hI.ci_in a h.1 h.2)
  · have := hI.fits
    simp only [Slots, RelPtrs.base, stackValueSize] at h this
    exact .inr (hI.stack_in a (by omega) (by omega))

/-- **`exit(0)` once `stdout` is set up**, from `_free_r`'s summary. -/
theorem exitUp_of_free (hF : FreeR_Statement) : ExitUp_Statement := by
  intro p w buf F FL ls hI hH M o c q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 hM h
  obtain ⟨hs, hu, hb, hR⟩ : StdoutAt w.mo buf [] ∧ StdioUp w.mo ∧ BufOwned w.rt.hix buf ∧ StdioRest w.mo := by
    cases hI.io with
    | up a b c d => exact ⟨a, b, c, d⟩
  have e1 : RuntimeData.spEntry - cStackBudget = 0x87fefe20 := rfl
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have hbh := hb.hi
  -- off the C stack and the chunks in use, `M` reads as the complement
  have kS : ∀ a, a < 0x87fefe20 → ¬ Kept w.rt.hix (.up buf []) a → bytesT1 M a = bytesT1 w.mo a :=
    fun a h1 h2 => hM a fun hf => (exitFree_kept hI hf).elim (fun h => by omega) h2
  have kLo : ∀ a, a < heapStart → bytesT1 M a = bytesT1 w.mo a := fun a ha =>
    kS a (by omega) fun hk => by have := hk.lo; omega
  have kBuf : ∀ a, Rng buf 1024 a → bytesT1 M a = bytesT1 w.mo a := fun a ha =>
    kS a (by simp only [Rng] at ha; omega) fun hk => hk.nbuf ha
  fs_nums
  stdio_nums
  have hs' : StdoutAt M buf [] := hs.congrF fun a ha => by
    rcases ha with ha | ha | ha | ha
    · exact kLo a (by simp only [Rng] at ha; omega)
    · exact kLo a (by simp only [Rng] at ha; omega)
    · exact kLo a (by simp only [Rng] at ha; omega)
    · exact kBuf a ha
  exact exit_run_up hF h
    ((bytesT8_congrT fun i _ => kLo _ (by have : symAtexit = 0x8005d450 := rfl; omega)).trans hI.atexit) hs'
    (hu.congrT fun a ha => kLo a (by simp only [StdioGlob] at ha; omega))
    (hR.congrT fun a ha => kLo a (by have := ha.range; omega)) hb
    (hH.ofTotal fun a hr hu => kS a (by simp only [HeapReads] at hr; omega) fun hk => hu hk.inuse)

/-- (lane F1-14; lane F1-A0-M) `exit(0)` after a `print`, `_free_r` discharged. -/
theorem exitUp_proved : ExitUp_Statement := exitUp_of_free AllocProof.freeR_proved

theorem CallOpen.exitUp (_O : CallOpen) : ExitUp_Statement := exitUp_proved

end Lua.Vm.Sim.Kit
