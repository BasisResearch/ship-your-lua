import Lua.Vm.Sim.Kit.Sinit
import Lua.Vm.Sim.Kit.Malloc
import Lua.Vm.AtF.Fstat_r
import Lua.Vm.AtF.Isatty_r

/-!
# The first write's set-up, its leaves (lane F1-10)

`__smakebuf_r` asks htif.c what descriptor 1 is: `_fstat_r` (`errno = 0`,
`_fstat`: the lazy `fs_init`, the console's `kind`, `memset` of the `stat`,
`st_mode = S_IFCHR`) and `_isatty_r` (`1`). Their summaries over the
generated at-lemmas (`Lua/Vm/AtF/{Fstat_r,Isatty_r}.lean`): one `fat_run`
each, then the post-memory read off the path's stores.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- htif.c's descriptor tables and `errno`: what `fs_init`, `_fstat_r` and
`_isatty_r` write outside their frames (`fs_ready`, `fds[0..2].kind`,
`files[0]`'s first half-word). -/
def FsGlobal (a : Nat) : Prop :=
  (errnoAddr ≤ a ∧ a < errnoAddr + 4) ∨ (symFsReady ≤ a ∧ a < symFsReady + 4) ∨
  (symFds ≤ a ∧ a < symFds + 52) ∨ (symFiles ≤ a ∧ a < symFiles + 2)

/-- The numbers of htif.c's tables, for `omega`. -/
macro "fs_nums" : tactic => `(tactic| (
  have : errnoAddr = 0x8005d408 := rfl
  have : symFsReady = 0x8005d3c0 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFiles = 0x8005d760 := rfl))

/-- **What `_fstat_r(_REENT, 1, sp + 24)` leaves**: the `stat`'s `st_mode`
`S_IFCHR` (at `sp + 28`), `fs_init` run, descriptor 1 the console; the bytes
off its frames, the `stat` and htif.c's tables kept. -/
structure FstatPost (m m' : Mem) (sp : Nat) : Prop where
  mode : bytesT4 m' (sp + 28) = 0x2000#32
  ready : bytesT4 m' symFsReady = 1#32
  console : bytesT4 m' (symFds + 24) = 2#32
  keep : ∀ a, ¬ FsGlobal a → (a + 32 ≤ sp ∨ (sp ≤ a ∧ a < sp + 24) ∨ sp + 128 ≤ a) → m'[a]? = m[a]?

/-- The stores of a path, off an address (`writeMap8`/`4`/`2`, `insert`). -/
macro "fs_off" : tactic => `(tactic|
  simp (disch := omega) only [getElem?_writeMap8_out, getElem?_writeMap4_out, getElem?_writeMap2_out, ins_out])

/-- **`_fstat_r(_REENT, 1, st)`** before `fs_init`, `st = sp + 24` (the
caller's frame: `__smakebuf_r`'s `struct stat`): `0` returned. -/
theorem fstat_sum (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e7d8 + 64 ≤ sp) (hst : sp + 128 ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hrd : bytesT4 m symFsReady = 0#32) :
    Triple (SegSt 0x8003b0e8#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩, ⟨Register.x11, 1#64⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp + 24)⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ FstatPost m m' sp) := by
  intro c h
  let X := abiCx sp r f m o
  have e0 : X.n 0 = sp := rfl
  have hX : Lua.Vm.AtF.Fstat_r.Ok X := ⟨hlo, hst, by omega, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8003b0e8#64 (Lua.Vm.AtF.Fstat_r.r0 X) (ArmPay X.m X.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT4 X.m 0x8005d3c0 = 0x0#32 := hrd
  fat_run Lua.Vm.AtF.Fstat_r h acc
  refine ⟨_, acc, Lua.Vm.AtF.Fstat_r.m17 X, h.repin (by pins_of h), ?_, ?_, ?_, ?_⟩
  · simp only [Lua.Vm.AtF.Fstat_r.m17, e0]; fat_rd; decide
  · simp only [Lua.Vm.AtF.Fstat_r.m17, show symFsReady = 0x8005d3c0 from rfl]; fat_rd; decide
  · simp only [Lua.Vm.AtF.Fstat_r.m17, show symFds = 0x8005d460 from rfl]; fat_rd; decide
  · intro a ha hb
    fs_nums
    simp only [FsGlobal] at ha
    simp only [Lua.Vm.AtF.Fstat_r.m17, e0]
    fs_off
    rfl

/-- **`_isatty_r(_REENT, 1)`** after `fs_init` (descriptor 1 the console):
`1` returned; `errno` and the frame `[sp - 16, sp)` written. -/
theorem isatty_sum (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x8005e7d8 + 64 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hrd : bytesT4 m symFsReady = 1#32) (hcon : bytesT4 m (symFds + 24) = 2#32) :
    Triple (SegSt 0x8004a170#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩, ⟨Register.x11, 1#64⟩]
        sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 1 f m' o c ∧
        ∀ a, ¬ FsGlobal a → (a + 16 < sp ∨ sp ≤ a) → m'[a]? = m[a]?) := by
  intro c h
  let X := abiCx sp r f m o
  have e0 : X.n 0 = sp := rfl
  have hX : Lua.Vm.AtF.Isatty_r.Ok X := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8004a170#64 (Lua.Vm.AtF.Isatty_r.r0 X) (ArmPay X.m X.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT4 X.m 0x8005d3c0 = 0x1#32 := hrd
  have hc1 : bytesT4 X.m 0x8005d478 = 0x2#32 := hcon
  fat_run Lua.Vm.AtF.Isatty_r h acc
  refine ⟨_, acc, Lua.Vm.AtF.Isatty_r.m0 X, h.repin (by pins_of h), ?_⟩
  intro a ha hb
  fs_nums
  simp only [FsGlobal] at ha
  simp only [Lua.Vm.AtF.Isatty_r.m0, e0]
  fs_off
  rfl

end Lua.Vm.Sim.Kit
