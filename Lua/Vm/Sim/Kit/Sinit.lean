import Lua.Vm.Sim.Kit.Stdio
import Lua.Vm.AtF.Sinit

/-!
# `__sinit(_REENT)` from the boot state (lane F1-10)

The first `fwrite` runs `CHECK_INIT` → `__sinit`, whose `global_stdio_init`
installs the exit handler and runs newlib's `std()` on the three `FILE`s of
`__sf`. The generated at-lemmas (`Lua/Vm/AtF/Sinit.lean`,
`gen_lua_at.py --fn __sinit`) have three roots: the entry, and the returns
of the two `__retarget_lock_init_recursive` calls between the `std()`s
(`calls`: each root carries the stack slots, so no store chain is longer
than one `std()`; the epilogue reads the saved slots as the last root's
carried facts). The lock init is a bare `ret`; its splice (`sin_lock`) is
its one segment.

Each root's memory keeps everything off its `FILE` (`sin_keep*`), so the
fields one `std()` writes survive the later roots (`FileStd.congr`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- `stdin`, `stderr`: the first and third `FILE` of `__sf`. -/
abbrev stdinFile : Nat := symSf
abbrev stderrFile : Nat := symSf + 2 * fileSize

/-- `__sinit`'s cleanup hook (`_REENT->__cleanup`) and the exit handler
(`__stdio_exit_handler`), `cleanup_stdio` and `stdio_exit_handler`. -/
abbrev symCleanupStdio : Nat := 0x80032b0c
abbrev symStdioExitHandlerFn : Nat := 0x80032af8

/-- **A `FILE` after newlib's `std(fp, flags, file)`**: `fl` the word
`flags | file << 16` at `_flags`; the buffer, counts and `_flags2` cleared;
the cookie the `FILE`; the hooks `__sread`, `__swrite`, `__sseek`, `__sclose`. -/
structure FileStd (m : Mem) (fp : Nat) (fl : BitVec 32) : Prop where
  p : bytesT8 m fp = 0#64
  rw : bytesT8 m (fp + 8) = 0#64
  flags : bytesT4 m (fp + 16) = fl
  base : bytesT8 m (fp + 24) = 0#64
  size : bytesT4 m (fp + 32) = 0#32
  lbf : bytesT4 m (fp + 40) = 0#32
  cookie : bytesT8 m (fp + 48) = BitVec.ofNat 64 fp
  read : bytesT8 m (fp + 56) = 0x80034eb4#64
  write : bytesT8 m (fp + 64) = 0x80034f18#64
  seek : bytesT8 m (fp + 72) = 0x80034fa0#64
  close : bytesT8 m (fp + 80) = 0x80035004#64
  flags2 : bytesT4 m (fp + 176) = 0#32

/-- **What `__sinit` leaves**: the hooks installed, the three `FILE`s set up
by `std()`, everything else but its frame `[sp - 64, sp)` kept. -/
structure SinitPost (m m' : Mem) (sp : Nat) : Prop where
  cleanup : bytesT8 m' (symImpureData + reentCleanupOff) = BitVec.ofNat 64 symCleanupStdio
  handler : bytesT8 m' symStdioExitHandler = BitVec.ofNat 64 symStdioExitHandlerFn
  stdin : FileStd m' stdinFile 0x4#32
  stdout : FileStd m' stdoutFile 0x10009#32
  stderr : FileStd m' stderrFile 0x20012#32
  /-- `stdout`'s padding after `_file`, which `std()` leaves -/
  pad : bytesT4 m' (stdoutFile + 20) = bytesT4 m (stdoutFile + 20)
  keep : ∀ a, (a + 64 < sp ∨ sp ≤ a) → (a < symSf ∨ symSf + 3 * fileSize ≤ a) →
    (a < symImpureData + reentCleanupOff ∨ symImpureData + reentCleanupOff + 8 ≤ a) →
    (a < symStdioExitHandler ∨ symStdioExitHandler + 8 ≤ a) → m'[a]? = m[a]?

/-- A return that sets no result: `ra`, `sp`, `gp` and the caller's frame. -/
abbrev voidRet (r : BitVec 64) (sp : Nat) (f : AbiFrame) (m : Mem) (o : Array String) : Config → Prop :=
  SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins)
    (ArmPay m o)

/-- A `FILE`'s fields across stores off it. -/
theorem FileStd.congr {m m' : Mem} {fp : Nat} {fl : BitVec 32} (h : FileStd m fp fl)
    (hk : ∀ a, fp ≤ a → a < fp + fileSize → m'[a]? = m[a]?) : FileStd m' fp fl := by
  have : fileSize = 184 := rfl
  refine ⟨(bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.p,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.rw,
    (bT4_congr fun i _ => hk _ (by omega) (by omega)).trans h.flags,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.base,
    (bT4_congr fun i _ => hk _ (by omega) (by omega)).trans h.size,
    (bT4_congr fun i _ => hk _ (by omega) (by omega)).trans h.lbf,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.cookie,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.read,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.write,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.seek,
    (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.close,
    (bT4_congr fun i _ => hk _ (by omega) (by omega)).trans h.flags2⟩

/-- A root memory's stores off an address (`writeMap8`/`4`, `insert`), by
`omega` on each. -/
macro "sin_off" : tactic => `(tactic|
  simp (disch := omega) only [getElem?_writeMap8_out, getElem?_writeMap4_out, ins_out])

/-- A `std()` field: forwarded through the root's stores (`fat_rd`), then ground. -/
macro "sin_fld" : tactic => `(tactic| (
  try simp only [stdinFile, stderrFile, stdoutFile, symSf, fileSize, symImpureData, reentCleanupOff,
    symStdioExitHandler, symCleanupStdio, symStdioExitHandlerFn, Nat.reduceAdd, Nat.reduceMul, abiCx,
    List.getD_cons_zero, List.getD_cons_succ]
  fat_rd; first | done | decide))

open Lua.Vm.AtF.Sinit in
/-- **The root memories keep what lies off their `FILE`.** -/
theorem sin_keep0 (X : FCx) (hX : Ok X) (a : Nat) (h1 : a + 64 < X.n 0 ∨ X.n 0 ≤ a)
    (h2 : a < symSf ∨ symSf + fileSize ≤ a) (h3 : a < 0x8005d200 ∨ 0x8005d208 ≤ a)
    (h4 : a < 0x8005d3e0 ∨ 0x8005d3e8 ≤ a) : (m11 X)[a]? = X.m[a]? := by
  have : symSf = 0x8005e5b0 := rfl; have : fileSize = 184 := rfl; have := hX.sp_lo
  simp only [m11]; sin_off

open Lua.Vm.AtF.Sinit in
theorem sin_keep1 (X : FCx) (a : Nat) (h : a < stdoutFile ∨ stdoutFile + fileSize ≤ a) :
    (m21 X)[a]? = X.m[a]? := by
  have : stdoutFile = 0x8005e668 := rfl; have : fileSize = 184 := rfl
  simp only [m21]; sin_off

open Lua.Vm.AtF.Sinit in
theorem sin_keep2 (X : FCx) (a : Nat) (h : a < stderrFile ∨ stderrFile + fileSize ≤ a) :
    (m32 X)[a]? = X.m[a]? := by
  have : stderrFile = 0x8005e720 := rfl; have : fileSize = 184 := rfl
  simp only [m32]; sin_off

open Lua.Vm.AtF.Sinit in
/-- **`std()`'s fields**, one root each. -/
theorem sin_std0 (X : FCx) (hX : Ok X) : FileStd (m11 X) stdinFile 0x4#32 := by
  have := hX.sp_lo
  constructor <;> simp only [m11] <;> sin_fld

open Lua.Vm.AtF.Sinit in
theorem sin_std1 (X : FCx) : FileStd (m21 X) stdoutFile 0x10009#32 := by
  constructor <;> simp only [m21] <;> sin_fld

open Lua.Vm.AtF.Sinit in
theorem sin_std2 (X : FCx) : FileStd (m32 X) stderrFile 0x20012#32 := by
  constructor <;> simp only [m32] <;> sin_fld

/-- `__sinit`'s and `global_stdio_init`'s saved slots in `[sp - 64, sp)`. -/
structure SinFrame (M : Mem) (X : FCx) : Prop where
  ra : bytesT8 M (X.n 0 - 8) = X.b 0
  s0 : bytesT8 M (X.n 0 - 16) = X.b 1
  ra2 : bytesT8 M (X.n 0 - 24) = 0x80032f1c#64
  a0 : bytesT8 M (X.n 0 - 32) = 0x8005d1b8#64
  s1 : bytesT8 M (X.n 0 - 40) = X.b 2
  s2 : bytesT8 M (X.n 0 - 48) = X.b 3
  s3 : bytesT8 M (X.n 0 - 56) = X.b 4
  s4 : bytesT8 M (X.n 0 - 64) = X.b 5

theorem SinFrame.congr {M M' : Mem} {X : FCx} (h : SinFrame M X) (h64 : 64 ≤ X.n 0)
    (hk : ∀ a, X.n 0 - 64 ≤ a → a < X.n 0 → M'[a]? = M[a]?) : SinFrame M' X :=
  ⟨(bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.ra,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.s0,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.ra2,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.a0,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.s1,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.s2,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.s3,
   (bT8_congr fun i _ => hk _ (by omega) (by omega)).trans h.s4⟩

open Lua.Vm.AtF.Sinit in
/-- Root 0 saves the frames. -/
theorem sin_frame0 (X : FCx) (hX : Ok X) : SinFrame (m11 X) X := by
  have := hX.sp_lo
  constructor <;> simp only [m11] <;> fat_rd

set_option hygiene false in
/-- **The lock init's splice**: `__retarget_lock_init_recursive` is a bare
`ret` to the literal `ra`; the next root's row from the call row. -/
macro "sin_lock" : tactic => `(tactic| (
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
    (Lua.Vm.Arms.seg_8003b418_8003b41c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by fat_side))
  have h := Vsa.Sim.SegSt.at h (by fat_ret)))

/-- **`__sinit(_REENT)` from the boot state** (`_REENT->__cleanup` and
`__stdio_exit_handler` NULL): the hooks installed and the three `FILE`s set
up (`SinitPost`); the callee-saved registers restored. -/
theorem sinit_boot (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : symSf + 3 * fileSize + 64 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hcl : bytesT8 m (symImpureData + reentCleanupOff) = 0#64) (heh : bytesT8 m symStdioExitHandler = 0#64) :
    Triple (SegSt 0x80032ed0#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', voidRet r sp f m' o c ∧ SinitPost m m' sp) := by
  intro c h
  have e0 : symSf = 0x8005e5b0 := rfl; have e1 : fileSize = 184 := rfl
  have e2 : symImpureData = 0x8005d1b8 := rfl; have e3 : reentCleanupOff = 72 := rfl
  have e4 : symStdioExitHandler = 0x8005d3e0 := rfl
  have e5 : stdinFile = 0x8005e5b0 := rfl; have e6 : stderrFile = 0x8005e720 := rfl
  let X0 := abiCx sp r f m o
  have e7 : X0.n 0 = sp := rfl
  have hX0 : Lua.Vm.AtF.Sinit.Ok X0 := ⟨show 0x8005e7d8 + 64 ≤ sp by omega, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032ed0#64 (Lua.Vm.AtF.Sinit.r0 X0) (ArmPay X0.m X0.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT8 X0.m 0x8005d200 = 0x0#64 := hcl
  have hc1 : bytesT8 X0.m 0x8005d3e0 = 0x0#64 := heh
  -- root 0: the hooks, the frames, `std(stdin)`
  fat_run Lua.Vm.AtF.Sinit h acc until [0x8003b418]
  sin_lock
  let X1 : FCx := ⟨X0.n, X0.b, Lua.Vm.AtF.Sinit.m11 X0, o⟩
  have hX1 : Lua.Vm.AtF.Sinit.Ok X1 := ⟨hX0.sp_lo, hX0.sp_hi, hX0.sp_al, hX0.ra⟩
  have h : SegSt 0x80032ca0#64 (Lua.Vm.AtF.Sinit.r3 X1) (ArmPay X1.m X1.o) _ := h.repin (by pins_of h)
  -- root 1: `std(stdout)`
  fat_run Lua.Vm.AtF.Sinit h acc until [0x8003b418]
  sin_lock
  let X2 : FCx := ⟨X0.n, X0.b, Lua.Vm.AtF.Sinit.m21 X1, o⟩
  have hX2 : Lua.Vm.AtF.Sinit.Ok X2 := ⟨hX0.sp_lo, hX0.sp_hi, hX0.sp_al, hX0.ra⟩
  have h : SegSt 0x80032d00#64 (Lua.Vm.AtF.Sinit.r3 X2) (ArmPay X2.m X2.o) _ := h.repin (by pins_of h)
  -- root 2: `std(stderr)`, the epilogue (the saved slots carried from root 0),
  -- the tail calls
  have fr := (sin_frame0 X0 hX0).congr (M' := X2.m) (by show 64 ≤ sp; omega) fun a h1 h2 =>
    sin_keep1 X1 a (by stdio_nums; omega)
  have hc2 := fr.a0; have hc3 := fr.ra2; have hc4 := fr.s1; have hc5 := fr.s2; have hc6 := fr.s3
  have hc7 := fr.s4; have hc8 := fr.s0; have hc9 := fr.ra
  fat_run Lua.Vm.AtF.Sinit h acc
  refine ⟨_, acc, Lua.Vm.AtF.Sinit.m32 X2, h.repin (by pins_of h), ?_⟩
  -- the post-memory
  have k0 := sin_keep0 X0 hX0; have k1 := sin_keep1 X1; have k2 := sin_keep2 X2
  have hm1 : X1.m = Lua.Vm.AtF.Sinit.m11 X0 := rfl
  have hm2 : X2.m = Lua.Vm.AtF.Sinit.m21 X1 := rfl
  have hm0 : X0.m = m := rfl
  stdio_nums
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bT8_congr fun i _ => (k2 _ (by omega)).trans ((congrArg (·[_]?) hm2).trans (k1 _ (by omega)))]
    show bytesT8 (Lua.Vm.AtF.Sinit.m11 X0) _ = _
    simp only [Lua.Vm.AtF.Sinit.m11]; sin_fld
  · rw [bT8_congr fun i _ => (k2 _ (by omega)).trans ((congrArg (·[_]?) hm2).trans (k1 _ (by omega)))]
    show bytesT8 (Lua.Vm.AtF.Sinit.m11 X0) _ = _
    simp only [Lua.Vm.AtF.Sinit.m11]; sin_fld
  · exact (sin_std0 X0 hX0).congr fun a h1 h2 =>
      (k2 a (by omega)).trans ((congrArg (·[a]?) hm2).trans ((k1 a (by omega)).trans (congrArg (·[a]?) hm1.symm)))
  · exact (sin_std1 X1).congr fun a h1 h2 => (k2 a (by omega)).trans (congrArg (·[a]?) hm2)
  · exact sin_std2 X2
  · have p2 : bytesT4 (Lua.Vm.AtF.Sinit.m32 X2) 0x8005e67c = bytesT4 X2.m 0x8005e67c :=
      bT4_congr fun i _ => k2 _ (by omega)
    have p1 : bytesT4 (Lua.Vm.AtF.Sinit.m21 X1) 0x8005e67c = bytesT4 X1.m 0x8005e67c := by
      simp only [Lua.Vm.AtF.Sinit.m21]; fat_rd
    have p0 : bytesT4 (Lua.Vm.AtF.Sinit.m11 X0) 0x8005e67c = bytesT4 X0.m 0x8005e67c :=
      bT4_congr fun i _ => k0 _ (by omega) (by omega) (by omega) (by omega)
    show bytesT4 (Lua.Vm.AtF.Sinit.m32 X2) 0x8005e67c = bytesT4 m 0x8005e67c
    rw [p2, hm2, p1, hm1, p0]
  · intro a h1 h2 h3 h4
    rw [k2 a (by omega), hm2, k1 a (by omega), hm1, k0 a (by omega) (by omega) (by omega) (by omega)]

end Lua.Vm.Sim.Kit
