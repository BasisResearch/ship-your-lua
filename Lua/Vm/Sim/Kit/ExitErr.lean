import Lua.Vm.Sim.Kit.ExitUp
import Lua.Vm.AtF.FcloseErrW
import Lua.Vm.AtF.FcloseOut9
import Lua.Vm.AtF.FcloseOutF
import Lua.Vm.AtF.ExitHandlerE9
import Lua.Vm.AtF.ExitHandlerEF
import Lua.Vm.AtF.ExitHandlerEU

/-!
# `exit(2)` after a Lua error (lane F1-26)

After `main`'s `fprintf(stderr, "lua: %s\n", msg)` newlib's stdio is set up
(`__sinit` ran, by a `print` or by the `fprintf`), `stderr` has been written
(unbuffered: `_p = _bf._base = _nbuf`, `_flags` `__SORD | __SWR | __SRW |
__SNBF`) and `stdout` is in one of three states: as `std()` left it (no
`print` ran), as an empty first write left it (`_flags` `0x2009`), or set up
and flushed. `exit(2)` closes the three streams through `stdio_exit_handler`
(lane F1-14's walk, `Lua/Vm/AtF/ExitHandlerE*.lean`) and halts with code 2.

* the write streams with nothing pending, closed: `fclose_errW`,
  `fclose_out9`, `fclose_outF` (`__sflush_r`'s write path, the `_close` hook;
  `Lua/Vm/AtF/{FcloseErrW,FcloseOut9,FcloseOutF}.lean`);
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

-- discipline: allow(R7-conj-tower-def) the existentials are a summary's returned memory (`∃ m', wrRet … ∧ keep`) and reached configuration, the posts named structures (`ErrRest`, `ErrOut`, `WQuiet`)
/-- `stderr`'s one-byte buffer `_nbuf` (`__smakebuf_r` on an unbuffered stream). -/
abbrev errNbuf : Nat := stderrFile + 0x77

/-- **A write stream `exit` closes with nothing pending**: `_flags` `fl`
(`__SWR`, no `__SMBF`), `_file` `fd`, `_bf._base` `base` (`_p` too when
`base ≠ 0`: nothing buffered), the cookie, `_close = __sclose`, no `ungetc`
or line buffer, `_flags2 = 0`. -/
structure WQuiet (m : Mem) (fp : Nat) (fl fd : BitVec 16) (base : Nat) : Prop where
  flags : bytesT2 m (fp + 16) = fl
  file : bytesT2 m (fp + 18) = fd
  base : bytesT8 m (fp + 24) = BitVec.ofNat 64 base
  cookie : bytesT8 m (fp + 48) = BitVec.ofNat 64 fp
  close : bytesT8 m (fp + 80) = BitVec.ofNat 64 symSclose
  ub : bytesT8 m (fp + 88) = 0#64
  lb : bytesT8 m (fp + 120) = 0#64
  flags2 : bytesT4 m (fp + 176) = 0#32

theorem WQuiet.congrT {m m' : Mem} {fp : Nat} {fl fd : BitVec 16} {base : Nat} (h : WQuiet m fp fl fd base)
    (hk : ∀ a, fp + 16 ≤ a → a < fp + fileSize → bytesT1 m' a = bytesT1 m a) : WQuiet m' fp fl fd base := by
  have : fileSize = 184 := rfl
  exact ⟨(bT2_congrT fun i _ => (hk _ (by omega) (by omega)).symm).symm.trans h.flags,
    (bT2_congrT fun i _ => (hk _ (by omega) (by omega)).symm).symm.trans h.file,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.base,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.cookie,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.close,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ub,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.lb,
    (bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.flags2⟩

/-- **What `_fclose_r` of a write stream with nothing pending writes**: the
stream's `_p`, `_r`, `_w`, `_flags`, its descriptor's `kind`, `errno`, its
stack. -/
def WCloseW (sp fp fd a : Nat) : Prop :=
  Rng fp 20 a ∨ Rng (symFds + 24 * fd) 4 a ∨ Rng errnoAddr 4 a ∨ Below sp 128 a

set_option hygiene false in
/-- The one-root `_fclose_r` run of a write stream: its at-lemmas, then the keep. -/
macro "wclose_run" ns:ident ok:ident r0:ident : tactic => `(tactic| (
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
  simp only [WCloseW, Rng, Below, not_or, not_and, Nat.not_lt] at ha
  simp only [stdoutFile, stderrFile, symSf, fileSize] at ha
  simp only [show X.n 0 = sp from rfl, show X.m = m from rfl]
  exact AtF.bT1_congr (by fs_off)))

/-- The guards every `_fclose_r` at `exit` reads: `__cleanup` set, `fs_ready` set. -/
structure ExitGuards (m : Mem) : Prop where
  init : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64
  ready : bytesT4 m symFsReady ≠ 0#32

/-- **`_fclose_r(_REENT, stderr)` after the error**: `0` returned, `WCloseW` written. -/
theorem fclose_errW (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stderrFile 0x201a#16 2#16 errNbuf) (hp : bytesT8 m stderrFile = BitVec.ofNat 64 errNbuf)
    (hk : bytesT4 m (symFds + 24 * 2) = 3#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stderrFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stderrFile 2 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hp; have hc4 := hq.close
  have hc5 := hq.cookie; have hc6 := hq.file; have hc7 := hk; have hc8 := hq.ub; have hc9 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stderrFile, errNbuf, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseErrW Lua.Vm.AtF.FcloseErrW.Ok Lua.Vm.AtF.FcloseErrW.r0

/-- **`_fclose_r(_REENT, stdout)` on `stdout` as `std()` left it**. -/
theorem fclose_out9 (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stdoutFile 0x9#16 1#16 0) (hk : bytesT4 m (symFds + 24 * 1) = 2#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stdoutFile 1 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hq.close
  have hc4 := hq.cookie; have hc5 := hq.file; have hc6 := hk; have hc7 := hq.ub; have hc8 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stdoutFile, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseOut9 Lua.Vm.AtF.FcloseOut9.Ok Lua.Vm.AtF.FcloseOut9.r0

/-- **`_fclose_r(_REENT, stdout)` on `stdout` after an empty first write**. -/
theorem fclose_outF (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stdoutFile 0x2009#16 1#16 0) (hk : bytesT4 m (symFds + 24 * 1) = 2#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stdoutFile 1 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hq.close
  have hc4 := hq.cookie; have hc5 := hq.file; have hc6 := hk; have hc7 := hq.ub; have hc8 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stdoutFile, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseOutF Lua.Vm.AtF.FcloseOutF.Ok Lua.Vm.AtF.FcloseOutF.r0

/-! ## `stdio_exit_handler` after an error -/

/-- **What `exit` reads of stdio after an error**, besides `stdout`: the exit
handler, `__sglue`, `stdin` quiet, `stderr` written with nothing pending, the
guards, htif.c's standard descriptors. -/
structure ErrRest (m : Mem) : Prop where
  handler : bytesT8 m symStdioExitHandler = BitVec.ofNat 64 symStdioExitHandlerFn
  glue_next : bytesT8 m symSglue = 0#64
  glue_niobs : bytesT4 m (symSglue + 8) = 3#32
  glue_iobs : bytesT8 m (symSglue + 16) = BitVec.ofNat 64 symSf
  stdin : StdQuiet m stdinFile 0x4#16 0#16
  stderr : WQuiet m stderrFile 0x201a#16 2#16 errNbuf
  err_p : bytesT8 m stderrFile = BitVec.ofNat 64 errNbuf
  guards : ExitGuards m
  fds : FdsStd m
  out_fd : bytesT4 m (symFds + 24) = 2#32

/-- **The walk's `_fclose_r(stdout)`** from any memory the `stdin` close
leaves (off `QuietW` and the walk's frame, `M`'s bytes): `0` returned,
`OutW` written. -/
def OutCloseAt (M : Mem) (sp : Nat) (f : AbiFrame) : Prop :=
  ∀ (m1 : Mem) (o : Array String),
    (∀ a, ¬ QuietW (sp - 80) stdinFile 0 a → (a < sp - 80 ∨ sp ≤ a) → bytesT1 m1 a = bytesT1 M a) →
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (sp - 80) 0x800340b4#64 (fwFr stdoutFile f)) (ArmPay m1 o))
      (fun c => ∃ m', wrRet 0x800340b4#64 (sp - 80) 0 (fwFr stdoutFile f) m' o c ∧
        ∀ a, ¬ OutW (sp - 80) a → bytesT1 m' a = bytesT1 m1 a)

/-- A quiet close's writes lie in `OutW`. -/
theorem wclose_outW {sp a : Nat} (h : WCloseW sp stdoutFile 1 a) : OutW sp a := by
  fs_nums
  simp only [WCloseW, OutW, MallocGlobal, Rng, Below] at h ⊢
  have : fileSize = 184 := rfl
  omega

set_option hygiene false in
/-- **The walk after an error**, over the at-lemmas `ns` (one module per
`stdout` `_flags`): `stdin` (`fclose_in`), `stdout` (`hcl`), `stderr`
(`fclose_errW`), the return. In context: `hR : ErrRest M`, `hcl :
OutCloseAt M sp f`, `hfl : bytesT2 M 0x8005e678 = fl`. -/
macro "err_walk" ns:ident ok:ident m0:ident r0:ident r3:ident r6:ident r9:ident : tactic => `(tactic| (
  intro c h
  fs_nums
  stdio_nums
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : stdinFile = 0x8005e5b0 := rfl
  have : stderrFile = 0x8005e720 := rfl
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have hlo : 0x87800000 + 8192 ≤ sp := by omega
  let X0 := abiCx sp r f M o
  have hX0 : $ok X0 := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.nil_append] at h
  have h : SegSt 0x80032af8#64 ($r0 X0) (ArmPay X0.m X0.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT4 X0.m 0x8005cee8 = 0x3#32 := hR.glue_niobs
  have hc1 : bytesT8 X0.m 0x8005cef0 = 0x8005e5b0#64 := hR.glue_iobs
  have hc2 : bytesT2 X0.m 0x8005e5c0 = 0x4#16 := hR.stdin.flags
  have hc3 : bytesT2 X0.m 0x8005e5c2 = 0x0#16 := hR.stdin.file
  have hc4 := hfl
  have hc5 : bytesT2 X0.m 0x8005e67a = 0x1#16 := hfile
  have hc6 : bytesT2 X0.m 0x8005e730 = 0x201a#16 := hR.stderr.flags
  have hc7 : bytesT2 X0.m 0x8005e732 = 0x2#16 := hR.stderr.file
  have hc8 : bytesT8 X0.m 0x8005cee0 = 0x0#64 := hR.glue_next
  fat_run $ns h acc until [0x80032580]
  have h1 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdinFile⟩] (sp - 80) 0x800340b4#64 (fwFr stdinFile f))
      (ArmPay ($m0 X0) o) _ := h.repin (by pins_of h)
  have k0 : ∀ a, (a < sp - 80 ∨ sp ≤ a) → bytesT1 ($m0 X0) a = bytesT1 M a := fun a ha =>
    AtF.bT1_congr (by
      simp only [$m0:ident, show X0.n 0 = sp from rfl, show X0.m = M from rfl]; fs_off)
  have hS0 : HdSlots ($m0 X0) sp r f := fun k hk => by
    simp only [$m0:ident, show X0.n 0 = sp from rfl]
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      simp (disch := omega) only [fw8_same, fw8_wm8] <;> rfl
  obtain ⟨c1, s1, m1, hr1, q1⟩ := fclose_in (sp - 80) 0x800340b4#64 (fwFr stdinFile f) _ o (by decide)
    (by omega) (by omega) (by omega)
    (hR.stdin.congrT fun a h1 h2 => k0 a (.inl (by omega)))
    ((bytesT4_congrT fun i _ => k0 _ (.inl (by omega))).trans hR.fds.fd0)
    (by rw [bytesT8_congrT fun i _ => k0 _ (.inl (by omega))]; exact hR.guards.init)
    (by rw [bytesT4_congrT fun i _ => k0 _ (.inl (by omega))]; exact hR.guards.ready) _ h1
  have acc := acc.trans s1
  have t1 : ∀ a, ¬ QuietW (sp - 80) stdinFile 0 a → (a < sp - 80 ∨ sp ≤ a) → bytesT1 m1 a = bytesT1 M a :=
    fun a h1 h2 => (q1 a h1).trans (k0 a h2)
  have hS1 : HdSlots m1 sp r f := hS0.keep (fun a h1 h2 => q1 a (by
    simp only [QuietW, Rng, Below, stdinFile, symSf]; omega)) (by omega)
  let X1 := abiCx sp r f m1 o
  have hX1 : $ok X1 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr1
  have h : SegSt 0x800340b4#64 ($r3 X1) (ArmPay X1.m X1.o) c1 := hr1.repin (by pins_of hr1)
  have u1 : ∀ a, (stdoutFile ≤ a ∧ a < stdoutFile + fileSize) ∨ (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨
      (symFsReady ≤ a ∧ a < symFsReady + 4) ∨ (symFds + 24 ≤ a ∧ a < symFds + 52) ∨
      (symSglue ≤ a ∧ a < symSglue + 24) ∨ (stderrFile ≤ a ∧ a < stderrFile + fileSize) →
      bytesT1 m1 a = bytesT1 M a := fun a ha => t1 a (by
        simp only [QuietW, Rng, Below, stdinFile, stderrFile, symSf, not_or, not_and, Nat.not_lt]; omega) (by omega)
  hd_slots hS1 X1
  have hc4 : bytesT2 X1.m 0x8005e678 = _ := (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hfl
  have hc5 : bytesT2 X1.m 0x8005e67a = 0x1#16 := (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hfile
  have hc6 : bytesT2 X1.m 0x8005e730 = 0x201a#16 :=
    (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hR.stderr.flags
  have hc7 : bytesT2 X1.m 0x8005e732 = 0x2#16 :=
    (bT2_congrT fun i _ => (u1 _ (by omega)).symm).symm.trans hR.stderr.file
  have hc8 : bytesT8 X1.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => u1 _ (by omega)).trans hR.glue_next
  fat_run $ns h acc until [0x80032580]
  have h2 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (sp - 80) 0x800340b4#64 (fwFr stdoutFile f))
      (ArmPay m1 o) _ := h.repin (by pins_of h)
  obtain ⟨c2, s2, m2, hr2, q2⟩ := hcl m1 o t1 _ h2
  have acc := acc.trans s2
  have u2 : ∀ a, (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨ (symFsReady ≤ a ∧ a < symFsReady + 4) ∨
      (symFds + 48 ≤ a ∧ a < symFds + 52) ∨ (symSglue ≤ a ∧ a < symSglue + 24) ∨
      (stderrFile ≤ a ∧ a < stderrFile + fileSize) → bytesT1 m2 a = bytesT1 M a := fun a ha =>
    (q2 a (by simp only [OutW, MallocGlobal, Rng, Below, not_or, not_and, Nat.not_lt]; omega)).trans
      (u1 a (by omega))
  have hS2 : HdSlots m2 sp r f := hS1.keep (fun a h1 h2 => q2 a (by
    simp only [OutW, MallocGlobal, Rng, Below, not_or, not_and, Nat.not_lt]; omega)) (by omega)
  let X2 := abiCx sp r f m2 o
  have hX2 : $ok X2 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr2
  have h : SegSt 0x800340b4#64 ($r6 X2) (ArmPay X2.m X2.o) c2 := hr2.repin (by pins_of hr2)
  hd_slots hS2 X2
  have hc6 : bytesT2 X2.m 0x8005e730 = 0x201a#16 :=
    (bT2_congrT fun i _ => (u2 _ (by omega)).symm).symm.trans hR.stderr.flags
  have hc7 : bytesT2 X2.m 0x8005e732 = 0x2#16 :=
    (bT2_congrT fun i _ => (u2 _ (by omega)).symm).symm.trans hR.stderr.file
  have hc8 : bytesT8 X2.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => u2 _ (by omega)).trans hR.glue_next
  fat_run $ns h acc until [0x80032580]
  have h3 : SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stderrFile⟩] (sp - 80) 0x800340b4#64 (fwFr stderrFile f))
      (ArmPay m2 o) _ := h.repin (by pins_of h)
  obtain ⟨c3, s3, m3, hr3, q3⟩ := fclose_errW (sp - 80) 0x800340b4#64 (fwFr stderrFile f) m2 o (by decide)
    (by omega) (by omega) (by omega)
    (hR.stderr.congrT fun a h1 h2 => u2 a (by omega))
    ((bytesT8_congrT fun i _ => u2 _ (by omega)).trans hR.err_p)
    ((bytesT4_congrT fun i _ => u2 _ (by omega)).trans hR.fds.fd2)
    ⟨by rw [bytesT8_congrT fun i _ => u2 _ (by omega)]; exact hR.guards.init,
     by rw [bytesT4_congrT fun i _ => u2 _ (by omega)]; exact hR.guards.ready⟩ _ h3
  have acc := acc.trans s3
  have hS3 : HdSlots m3 sp r f := hS2.keep (fun a h1 h2 => q3 a (by
    simp only [WCloseW, Rng, Below, stderrFile, symSf]; omega)) (by omega)
  let X3 := abiCx sp r f m3 o
  have hX3 : $ok X3 := ⟨hlo, hhi, hal, hra⟩
  simp only [wrRet] at hr3
  have h : SegSt 0x800340b4#64 ($r9 X3) (ArmPay X3.m X3.o) c3 := hr3.repin (by pins_of hr3)
  hd_slots hS3 X3
  have hc8 : bytesT8 X3.m 0x8005cee0 = 0x0#64 :=
    (bytesT8_congrT fun i _ => (q3 _ (by simp only [WCloseW, Rng, Below, stderrFile, symSf]; omega)).trans
      (u2 _ (by omega))).trans hR.glue_next
  fat_run $ns h acc
  fcx_unfold at h
  exact ⟨_, acc, _, h.repin (by pins_of h)⟩))

/-- **`stdio_exit_handler()` after an error, `stdout` as `std()` left it.** -/
theorem exit_handler_err9 (sp : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo' : 0x87800000 + 16384 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hR : ErrRest M) (hcl : OutCloseAt M sp f) (hfl : bytesT2 M 0x8005e678 = 0x9#16)
    (hfile : bytesT2 M 0x8005e67a = 0x1#16) :
    Triple (SegSt 0x80032af8#64 (callPre [] sp r f) (ArmPay M o)) (fun c => ∃ M', voidRet r sp f M' o c) := by
  err_walk Lua.Vm.AtF.ExitHandlerE9 Lua.Vm.AtF.ExitHandlerE9.Ok Lua.Vm.AtF.ExitHandlerE9.m0 Lua.Vm.AtF.ExitHandlerE9.r0
    Lua.Vm.AtF.ExitHandlerE9.r3 Lua.Vm.AtF.ExitHandlerE9.r6 Lua.Vm.AtF.ExitHandlerE9.r9

/-- **`stdio_exit_handler()` after an error, `stdout` after an empty first write.** -/
theorem exit_handler_errF (sp : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo' : 0x87800000 + 16384 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hR : ErrRest M) (hcl : OutCloseAt M sp f) (hfl : bytesT2 M 0x8005e678 = 0x2009#16)
    (hfile : bytesT2 M 0x8005e67a = 0x1#16) :
    Triple (SegSt 0x80032af8#64 (callPre [] sp r f) (ArmPay M o)) (fun c => ∃ M', voidRet r sp f M' o c) := by
  err_walk Lua.Vm.AtF.ExitHandlerEF Lua.Vm.AtF.ExitHandlerEF.Ok Lua.Vm.AtF.ExitHandlerEF.m0 Lua.Vm.AtF.ExitHandlerEF.r0
    Lua.Vm.AtF.ExitHandlerEF.r3 Lua.Vm.AtF.ExitHandlerEF.r6 Lua.Vm.AtF.ExitHandlerEF.r9

/-- **`stdio_exit_handler()` after an error, `stdout` set up.** -/
theorem exit_handler_errU (sp : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo' : 0x87800000 + 16384 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hR : ErrRest M) (hcl : OutCloseAt M sp f) (hfl : bytesT2 M 0x8005e678 = 0x2889#16)
    (hfile : bytesT2 M 0x8005e67a = 0x1#16) :
    Triple (SegSt 0x80032af8#64 (callPre [] sp r f) (ArmPay M o)) (fun c => ∃ M', voidRet r sp f M' o c) := by
  err_walk Lua.Vm.AtF.ExitHandlerEU Lua.Vm.AtF.ExitHandlerEU.Ok Lua.Vm.AtF.ExitHandlerEU.m0 Lua.Vm.AtF.ExitHandlerEU.r0
    Lua.Vm.AtF.ExitHandlerEU.r3 Lua.Vm.AtF.ExitHandlerEU.r6 Lua.Vm.AtF.ExitHandlerEU.r9

/-- **`stdout` at `exit` after an error**, per phase of the `CALL`
invariant before it: as `std()` left it (no `print` ran: the `fprintf`'s
`__sinit`), after an empty first write, or set up and flushed (its buffer
owned in the heap `H`). -/
inductive ErrOut (m : Mem) (H : HeapIx) : StdoutPh → Prop where
  | boot : WQuiet m stdoutFile 0x9#16 1#16 0 → ErrOut m H .boot
  | fresh : WQuiet m stdoutFile 0x2009#16 1#16 0 → ErrOut m H .fresh
  | up {buf : Nat} : StdoutAt m buf [] → bytesT4 m (stdoutFile + fileFlags2Off) = 0#32 → StdoutTail m →
      BufOwned H buf → HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins → ErrOut m H (.up buf [])

/-- The walk's `stdin` close keeps `stdout`'s `FILE`, the guards, `fds[1]`. -/
theorem quietW_out {sp a : Nat} (hsp : 0x87800000 + 16384 ≤ sp)
    (h : (stdoutFile ≤ a ∧ a < stdoutFile + fileSize) ∨ (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨
      (symFsReady ≤ a ∧ a < symFsReady + 4) ∨ (symFds + 24 ≤ a ∧ a < symFds + 28) ∨
      (heapStart ≤ a ∧ a < heapEnd + 32) ∨
      (0x8005c6d0 ≤ a ∧ a < 0x8005e5b0 ∧ (a < 0x8005d408 ∨ 0x8005d40c ≤ a) ∧ (a < 0x8005d460 ∨ 0x8005d464 ≤ a))) :
    ¬ QuietW (sp - 80) stdinFile 0 a ∧ (a < sp - 80 ∨ sp ≤ a) := by
  fs_nums
  have : symSf = 0x8005e5b0 := rfl
  have : fileSize = 184 := rfl
  simp only [QuietW, Rng, Below, stdinFile, symSf, not_or, not_and, Nat.not_lt]
  omega

/-- **The walk's `stdout` close, per phase.** -/
theorem outCloseAt_of {M : Mem} {H : HeapIx} {ph : StdoutPh} {sp : Nat} {f : AbiFrame}
    (hsp : 0x87800000 + 16384 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hO : ErrOut M H ph) (hR : ErrRest M) : OutCloseAt M sp f := by
  intro m1 o k1
  have k : ∀ a, (stdoutFile ≤ a ∧ a < stdoutFile + fileSize) ∨ (0x8005d200 ≤ a ∧ a < 0x8005d208) ∨
      (symFsReady ≤ a ∧ a < symFsReady + 4) ∨ (symFds + 24 ≤ a ∧ a < symFds + 28) ∨
      (heapStart ≤ a ∧ a < heapEnd + 32) ∨
      (0x8005c6d0 ≤ a ∧ a < 0x8005e5b0 ∧ (a < 0x8005d408 ∨ 0x8005d40c ≤ a) ∧ (a < 0x8005d460 ∨ 0x8005d464 ≤ a)) →
      bytesT1 m1 a = bytesT1 M a := fun a ha => k1 a (quietW_out hsp ha).1 (quietW_out hsp ha).2
  fs_nums
  stdio_nums
  have : fileSize = 184 := rfl
  have hG : ExitGuards m1 :=
    ⟨by rw [bytesT8_congrT fun i _ => k _ (by omega)]; exact hR.guards.init,
     by rw [bytesT4_congrT fun i _ => k _ (by omega)]; exact hR.guards.ready⟩
  have hk : bytesT4 m1 (symFds + 24 * 1) = 2#32 := (bytesT4_congrT fun i _ => k _ (by omega)).trans hR.out_fd
  cases hO with
  | boot hq =>
    intro c h
    obtain ⟨c', s, m', hr, q⟩ := fclose_out9 (sp - 80) _ _ m1 o (by decide) (by omega) (by omega) (by omega)
      (hq.congrT fun a h1 h2 => k a (.inl ⟨by omega, h2⟩)) hk hG c h
    exact ⟨c', s, m', hr, fun a ha => q a fun hw => ha (wclose_outW hw)⟩
  | fresh hq =>
    intro c h
    obtain ⟨c', s, m', hr, q⟩ := fclose_outF (sp - 80) _ _ m1 o (by decide) (by omega) (by omega) (by omega)
      (hq.congrT fun a h1 h2 => k a (.inl ⟨by omega, h2⟩)) hk hG c h
    exact ⟨c', s, m', hr, fun a ha => q a fun hw => ha (wclose_outW hw)⟩
  | up hs hf2 ht hb hH =>
    rename_i buf
    have hb0 := hs.buf_lo; have hbl := hb.lo; have hbh := hb.hi
    have hs1 : StdoutAt m1 buf [] := hs.congrF fun a ha => k a (by simp only [Rng] at ha; omega)
    have hH1 : HeapAt (fillZeroMem m1) H.top H.brk H.chunks H.bins :=
      hH.ofTotal fun a hr _ => by
        rw [k a (by simp only [HeapReads, MallocGlobal] at hr; omega), bytesT1_fill]
    exact fclose_out AllocProof.freeR_proved (sp - 80) buf H _ _ m1 o (by decide) (by omega) (by omega)
      (by omega) hs1 ((bytesT4_congrT fun i _ => k _ (by omega)).trans hf2)
      (ht.congrT fun a h1 h2 => k a (by omega)) hG.init hb hH1

/-! ## `exit(2)` -/

/-- **`_exit(2)`'s store halts with code 2**: at `0x8000064c` with `a4` the
`auipc` base of `tohost` and `a5 = (2 << 1) | 1`, the console so far. -/
theorem exit_halt2 {m : Mem} {o : Array String} {c : Config} {L : List Pin}
    (h : SegSt 0x8000064c#64 (⟨Register.x14, 0x8005c648#64⟩ :: ⟨Register.x15, 5#64⟩ :: L)
      (ArmPay m o) c) :
    ∃ σf, Vsa.Machine.Halted c 2 σf ∧ Vsa.Machine.output σf = Vsa.Machine.output c.σ := by
  obtain ⟨σ, i, u⟩ := c
  have hG := h.good
  have hpc := h.pcAt
  obtain ⟨vm, hvm⟩ := h.minstret
  have hok := h.armOk
  obtain ⟨th, hth⟩ := hG.htif_tohost
  have hx14 := h.pins.1
  have hx15 := h.pins.2.1
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Lua.Vm.Code._exit_at_8000064c
    (Lua.Vm.Code.textLoaded__exitLoaded h.armText)
  have hstep := stepOnce_tohost_G σ i u (0x8000064c#64) vm (0x06f73c23#32) (0x078#12)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) (0x8005c648#64) (5#64) (5#64) (2#64) th
    (0x23#8) (0x3c#8) (0xf7#8) (0x06#8) hG hpc hvm (by decide) (by decide)
    (Vsa.Sim.decodeW (w := 0x06f73c23#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x14 _ _ (by rw [get?_afterNextPC σ _ _ (by decide) (by decide)]; exact hx14))
    (rX_bits_x15 _ _ (by rw [get?_afterNextPC σ _ _ (by decide) (by decide)]; exact hx15))
    (by decide) rfl hok.htifIdle hth (by decide) (by decide) hb0 hb1 hb2 hb3
    (by decide) (by decide) (by decide)
  exact ⟨_, .mk hstep, rfl⟩

/-- `exit`'s entry with the code `2` (`_start`'s `tail exit` after `main`
returns 2). -/
abbrev exitRow2 (q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64) : List Pin :=
  [⟨Register.x10, 2#64⟩, ⟨Register.x1, 0x80000038#64⟩, ⟨Register.x2, 0x88000000#64⟩,
   ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩, ⟨Register.x8, q8⟩, ⟨Register.x9, q9⟩,
   ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩, ⟨Register.x21, q21⟩,
   ⟨Register.x22, q22⟩, ⟨Register.x23, q23⟩, ⟨Register.x24, q24⟩, ⟨Register.x25, q25⟩,
   ⟨Register.x26, q26⟩, ⟨Register.x27, q27⟩]

/-- **What `exit(2)` reads after an error**: no `atexit` handler, the stdio
words (`ErrRest`), `stdout` in the phase `ph` (`ErrOut`). -/
structure ErrExitMem (M : Mem) (H : HeapIx) (ph : StdoutPh) : Prop where
  atexit : bytesT8 M symAtexit = 0#64
  rest : ErrRest M
  out : ErrOut M H ph

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

/-- **`exit(2)` after an error halts with code 2**: no `atexit` handler,
`stdio_exit_handler` closes the three streams (`exit_handler_err9`/`F`/`U`),
`_exit(2)`'s `tohost` store. -/
theorem exit_run_err {M : Mem} {o : Array String} {c : Config} {H : HeapIx} {ph : StdoutPh}
    {q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64}
    (h : SegSt (BitVec.ofNat 64 symCExit) (exitRow2 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27)
      (ArmPay M o) c) (hE : ErrExitMem M H ph) :
    ∃ out, Vsa.Machine.Halts c out 2 := by
  have acc := Steps.refl c
  have hat := hE.atexit
  have hsx : bytesT8 M symStdioExitHandler = 0x80032af8#64 := hE.rest.handler
  simp only [symAtexit, symStdioExitHandler] at hat hsx
  simp only [exitRow2, symCExit] at h
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
  fs_nums
  stdio_nums
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : fileSize = 184 := rfl
  have e1 : symStdioExitHandler = 0x8005d3e0 := rfl
  have : stderrFile = 0x8005e720 := rfl
  have : stdinFile = 0x8005e5b0 := rfl
  have hR := hE.rest
  -- the handler's memory: `M` below the stack
  have hR1 : ErrRest c1.σ.mem :=
    { handler := (bytesT8_congrT fun i _ => lo1 _ (by omega)).trans hR.handler
      glue_next := (bytesT8_congrT fun i _ => lo1 _ (by omega)).trans hR.glue_next
      glue_niobs := (bytesT4_congrT fun i _ => lo1 _ (by omega)).trans hR.glue_niobs
      glue_iobs := (bytesT8_congrT fun i _ => lo1 _ (by omega)).trans hR.glue_iobs
      stdin := hR.stdin.congrT fun a h1 h2 => lo1 a (by simp only [stdinFile] at h2; omega)
      stderr := hR.stderr.congrT fun a h1 h2 => lo1 a (by simp only [stderrFile] at h2; omega)
      err_p := (bytesT8_congrT fun i _ => lo1 _ (by omega)).trans hR.err_p
      guards := ⟨by rw [bytesT8_congrT fun i _ => lo1 _ (by omega)]; exact hR.guards.init,
        by rw [bytesT4_congrT fun i _ => lo1 _ (by omega)]; exact hR.guards.ready⟩
      fds := hR.fds.congrT fun a h1 h2 => lo1 a (by omega)
      out_fd := (bytesT4_congrT fun i _ => lo1 _ (by omega)).trans hR.out_fd }
  have hfile : ∀ m : Mem, (∀ a, a < 0x87ff0000 → bytesT1 m a = bytesT1 M a) →
      bytesT2 M 0x8005e67a = 0x1#16 → bytesT2 m 0x8005e67a = 0x1#16 := fun m hm h2 =>
    (bT2_congrT fun i _ => (hm _ (by omega)).symm).symm.trans h2
  have hflx : ∀ (fl : BitVec 16), bytesT2 M 0x8005e678 = fl → bytesT2 c1.σ.mem 0x8005e678 = fl := fun fl h2 =>
    (bT2_congrT fun i _ => (lo1 _ (by omega)).symm).symm.trans h2
  have hO1 : ErrOut c1.σ.mem H ph := by
    cases hE.out with
    | boot hq => exact .boot (hq.congrT fun a h1 h2 => lo1 a (by omega))
    | fresh hq => exact .fresh (hq.congrT fun a h1 h2 => lo1 a (by omega))
    | up hs hf2 ht hb hH =>
      have hbh := hb.hi
      have hb0 := hs.buf_lo
      exact .up (hs.congrF fun a ha => lo1 a (by simp only [Rng] at ha; omega))
        ((bytesT4_congrT fun i _ => lo1 _ (by omega)).trans hf2)
        (ht.congrT fun a h1 h2 => lo1 a (by omega)) hb
        (hH.ofTotal fun a hr _ => by
          rw [lo1 a (by simp only [HeapReads] at hr; omega), bytesT1_fill])
  have hcl : OutCloseAt c1.σ.mem 0x87fffff0 ⟨2#64, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27⟩ :=
    outCloseAt_of (by decide) (by decide) (by decide) hO1 hR1
  have hsum : Triple (SegSt 0x80032af8#64 (callPre [] 0x87fffff0 0x8002f880#64
      ⟨2#64, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27⟩) (ArmPay c1.σ.mem o))
      (fun c => ∃ M', voidRet 0x8002f880#64 0x87fffff0 ⟨2#64, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27⟩
        M' o c) := by
    cases hE.out with
    | boot hq =>
      exact exit_handler_err9 _ _ _ _ o (by decide) (by decide) (by decide) (by decide) hR1 hcl
        (hflx _ hq.flags) (hfile _ lo1 hq.file)
    | fresh hq =>
      exact exit_handler_errF _ _ _ _ o (by decide) (by decide) (by decide) (by decide) hR1 hcl
        (hflx _ hq.flags) (hfile _ lo1 hq.file)
    | up hs _ _ _ _ =>
      exact exit_handler_errU _ _ _ _ o (by decide) (by decide) (by decide) (by decide) hR1 hcl
        (hflx _ hs.flags) (hfile _ lo1 hs.file)
  obtain ⟨c2, s2, M2, h2⟩ := hsum _ (h.repin (by pins_of h))
  have acc := acc.trans s2
  simp only [voidRet, AbiFrame.pins] at h2
  have h := h2
  kit_run h acc until [0x8000064c]
  obtain ⟨σf, hh, ho⟩ := exit_halt2 (L := []) (h.repin (by pins_of h))
  exact ⟨_, _, σf, acc, hh, rfl⟩

end Lua.Vm.Sim.Kit
