import Lua.Vm.Sim.Kit.Swrite
import Lua.Vm.Arms.Segs.Hsflush_r
import Vsa.Sim.Generic.MapReads

/-!
# newlib's `stdout` while `print` runs, and `__sflush_r` on it (A0.2, lane F1-6)

`StdoutAt m buf pend`: the state of newlib's `stdout` `FILE` once the first
`fwrite` has set it up (`__sinit`, `__swsetup_r`, `__smakebuf_r`): line-buffered
(`_flags = __SWR | __SLBF | __SMBF | __SNPT | __SORD = 0x2889`), its 1024-byte
buffer at `buf` holding the pending bytes `pend` (`_p = buf + |pend|`,
`_w = -|pend|`), the hooks `_cookie = stdout`, `_write = __swrite`, and htif.c's
descriptor table initialised. The field values are the ones the emulator trace
of `c/tests/while.lua` shows after the first `print` (lane F1-6 ledger).

`sflush_sum`: `__sflush_r(ptr, stdout)` (`0x800326f8`) on that state writes the
pending bytes through the `FILE`'s hook (`jalr a5`: `swrite_sum`) and returns
`0` with the buffer empty (`_p = _bf._base`, `_w = 0`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **newlib's `stdout`, set up and line-buffered**, its buffer at `buf`
holding `pend` (up to a full buffer), its write count `_w` the word `wv`
(`StdoutAt`: `-|pend|`; `__sfvwrite_r`'s fill path advances `_p` alone
before the flush, which resets `_w` without reading it). -/
structure StdoutAtW (m : Mem) (buf : Nat) (pend : List (BitVec 8)) (wv : BitVec 32) : Prop where
  p : bytesT8 m (stdoutFile + fileBufPOff) = BitVec.ofNat 64 (buf + pend.length)
  w : bytesT4 m (stdoutFile + fileWOff) = wv
  flags : bytesT2 m (stdoutFile + fileFlagsOff) = 0x2889#16
  file : bytesT2 m (stdoutFile + fileFileOff) = 1#16
  base : bytesT8 m (stdoutFile + fileBfBaseOff) = BitVec.ofNat 64 buf
  size : bytesT4 m (stdoutFile + fileBfSizeOff) = 1024#32
  lbf : bytesT4 m (stdoutFile + fileLbfsizeOff) = 0#32 - 1024#32
  cookie : bytesT8 m (stdoutFile + fileCookieOff) = BitVec.ofNat 64 stdoutFile
  write : bytesT8 m (stdoutFile + fileWriteOff) = BitVec.ofNat 64 symSwrite
  bytes : bytesAt m buf pend.length = pend
  room : pend.length ≤ 1024
  /-- the buffer is heap memory: above the C runtime's globals, apart from `stdout` -/
  buf_lo : stdoutFile + fileSize ≤ buf
  buf_hi : buf + 1024 ≤ 2 ^ 32
  /-- htif.c's descriptor table: `fs_init` ran, `fds[1]` is the console -/
  ready : bytesT4 m symFsReady ≠ 0#32
  stdout : bytesT4 m (symFds + 24) = 2#32

/-- **`stdout` between calls**: `_w = -|pend|`. -/
abbrev StdoutAt (m : Mem) (buf : Nat) (pend : List (BitVec 8)) : Prop :=
  StdoutAtW m buf pend (0#32 - BitVec.ofNat 32 pend.length)

/-! ## Reads through the stores of the write path -/

theorem b8_wm2_out {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 8 ≤ a ∨ a + 2 ≤ x) :
    bytesT8 (writeMap2 m a d) x = bytesT8 m x :=
  bytesT8_congr fun _ _ => getElem?_writeMap2_out m a d _ (by omega)

theorem b2_wm4_out {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 2 ≤ a ∨ a + 4 ≤ x) :
    bytesT2 (writeMap4 m a d) x = bytesT2 m x := by
  simp only [bytesT2]
  rw [getElem?_writeMap4_out m a d x (by omega), getElem?_writeMap4_out m a d (x + 1) (by omega)]

theorem b2_wm2_out {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 2 ≤ a ∨ a + 2 ≤ x) :
    bytesT2 (writeMap2 m a d) x = bytesT2 m x := by
  simp only [bytesT2]
  rw [getElem?_writeMap2_out m a d x (by omega), getElem?_writeMap2_out m a d (x + 1) (by omega)]

theorem bytesT2_writeMap2 (m : Mem) (a : Nat) (d : BitVec (8 * 2)) : bytesT2 (writeMap2 m a d) a = d := by
  simp only [bytesT2, writeMap2]
  rw [Std.ExtHashMap.getElem?_insert_self, Std.ExtHashMap.getElem?_insert,
    if_neg (by simp), Std.ExtHashMap.getElem?_insert_self]
  simp only [Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  show (BitVec.extractLsb' 8 8 d ++ BitVec.extractLsb' 0 8 d).getLsbD i = d.getLsbD i
  rw [BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · simp [h8, BitVec.getLsbD_extractLsb']
  · simp [h8, BitVec.getLsbD_extractLsb', show i - 8 < 8 by omega]; congr 1; omega

theorem bytesT4_wm4_self (m : Mem) (a : Nat) (d : BitVec (8 * 4)) : bytesT4 (writeMap4 m a d) a = d := by
  simp only [bytesT4, getElem_writeMap4_0, getElem_writeMap4_1, getElem_writeMap4_2, getElem_writeMap4_3,
    Option.getD_some]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  show (((BitVec.extractLsb' 24 8 d ++ BitVec.extractLsb' 16 8 d) ++ BitVec.extractLsb' 8 8 d) ++
    BitVec.extractLsb' 0 8 d).getLsbD i = d.getLsbD i
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h1 : i < 8
  · simp [h1]
  · by_cases h2 : i - 8 < 8
    · simp [h1, h2]; congr 1; omega
    · by_cases h3 : i - 8 - 8 < 8
      · simp [h1, h2, h3]; congr 1; omega
      · simp [h1, h2, h3, show i - 8 - 8 - 8 < 8 by omega]; congr 1; omega

/-! ## `__sflush_r` on `stdout` -/

/-- `__sflush_r`'s entry: `a0 = ptr`, `a1 = stdout`. -/
abbrev sflPre (ptr : BitVec 64) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  ⟨Register.x10, ptr⟩ :: ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- The stack `__sflush_r` and its callees use: `[sp - 208, sp)` above the buffer. -/
structure SflCtx (sp buf : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : buf + 1024 + 512 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption)

set_option hygiene false in
local macro "sfl_ctx" hx:ident hs:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hFD : symFds = 0x8005d460 := rfl
  have hFS : symFdsSize = 768 := rfl
  have hGP : symGlobalPointer = 0x8005ced0 := rfl
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hFR : symFsReady = 0x8005d3c0 := rfl
  have hSF : stdoutFile = 0x8005e668 := rfl
  have hFZ : fileSize = 184 := rfl
  have hra := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hs).buf_lo; have := ($hs).buf_hi; have := ($hs).room))

/-! ### Values on the write path -/

theorem ofNat_beq0 {b : Nat} (h1 : 0 < b) (h2 : b < 2 ^ 64) : (BitVec.ofNat 64 b == 0#64) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt h2] at this; omega

/-- `subw s1, s1, s2`: the pending count `_p - _bf._base`. -/
theorem subw_len {b l : Nat} (h1 : b + l < 2 ^ 32) (h2 : l < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 (b + l)) 31 0 -
      Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) = BitVec.ofNat 64 l := by
  have e : Sail.BitVec.extractLsb (BitVec.ofNat 64 (b + l)) 31 0 - Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0 =
      BitVec.ofNat 32 l := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.toNat_sub, BitVec.extractLsb_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt (show b + l < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
    omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  have hl : (BitVec.ofNat 32 l).toNat = l := by simp; omega
  have hm : (BitVec.ofNat 32 l).msb = false := by rw [BitVec.msb_eq_decide, hl]; simp; omega
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, hm, hl, BitVec.toNat_ofNat]
  simp; omega

theorem subw_self (x : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0 - Sail.BitVec.extractLsb x 31 0) = 0#64 := by
  rw [BitVec.sub_self]; decide

theorem slt0_ofNat {l : Nat} (h : l < 2 ^ 63) : zopz0zI_s (0#64) (BitVec.ofNat 64 l) = decide (0 < l) := by
  have e : (BitVec.ofNat 64 l).toInt = l := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  unfold zopz0zI_s
  rw [e]; simp

theorem bytesT8_sd_self (m : Mem) (a : Nat) (v : BitVec 64) : bytesT8 (writeMap8 m a (sdData_val v)) a = v := by
  rw [bytesT8_writeMap8, sdData_id]

/-- The forwarding of a read through the write path's stores (each side
condition a separation over `Nat`). -/
macro "sfl_fwd" : tactic => `(tactic| simp (disch := omega) only [
  bytesT8_wm8_out, bytesT8_wm4_out, b8_wm2_out, bytesT4_wm8_out, b4_wm4_out, b4_wm2_out, b2_wm8_out,
  b2_wm4_out, b2_wm2_out, bytesT1_writeMap8_out, bytesT1_wm4_out, b1_wm2_out])

/-- The facts after `__sflush_r` on `stdout`: the buffer empty, and every byte
the caller and the heap hold but `stdout`'s and `errno`'s kept. -/
structure SflOut (m m' : Mem) (sp buf : Nat) : Prop where
  stdout : StdoutAt m' buf []
  keep_hi : ∀ a, sp ≤ a → bytesT1 m' a = bytesT1 m a
  keep_lo : ∀ a, a + 512 ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) →
    (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 m a
  /-- `stdout` past `_flags` (`_file`, the hooks, `_lock`, `_flags2`) -/
  keep_file : ∀ a, stdoutFile + fileFileOff ≤ a → a < stdoutFile + fileSize → bytesT1 m' a = bytesT1 m a

/-- **`__sflush_r`'s return**: `a0 = 0`, `sp` and the frame restored, the
pending bytes on the console. -/
def SflRet (r : BitVec 64) (sp buf : Nat) (f : AbiFrame) (m : Mem) (o : Array String) (c : Config) : Prop :=
  ∃ m', wrRet r sp 0 f m' o c ∧ SflOut m m' sp buf

/-- A return target `ra` with its low bit cleared. -/
theorem upd_ret (r : BitVec 64) (h : r.toNat % 4 = 0) : BitVec.update r 0 0#1 = r := by
  have := Vsa.Sim.ret_tgt r h; rwa [Vsa.Sim.sext_zero, BitVec.add_zero] at this

/-- `__sflush_r`'s stores up to the count's test: its saves (`s0`, `s3`, `ra`,
`s2`, `s1`) and `_p := _bf._base`. -/
abbrev sflMem3 (m : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) (buf : Nat) : Mem :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m (sp - 48 + 32)
    (sdData_val f.s0)) (sp - 48 + 8) (sdData_val f.s3)) (sp - 48 + 40) (sdData_val r)) (sp - 48 + 16)
    (sdData_val f.s2)) (sp - 48 + 24) (sdData_val f.s1)) stdoutFile (sdData_val (BitVec.ofNat 64 buf))

/-- … and `_w := 0`: the stores before the write. -/
abbrev sflMem (m : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) (buf : Nat) : Mem :=
  writeMap4 (sflMem3 m sp r f buf) (stdoutFile + 12) (swData 0#64)

/-- The pins at the pending count's test (`0x80032868`). -/
abbrev sflP68 (sp buf n : Nat) (ptr : BitVec 64) (f : AbiFrame) : List Pin :=
  [⟨Register.x15, 0#64⟩, ⟨Register.x9, BitVec.ofNat 64 n⟩,
   ⟨Register.x14, sign_extend (m := 64) (0x2889#16 : BitVec 16) &&& sign_extend (m := 64) (0x003#12)⟩,
   ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩, ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩,
   ⟨Register.x18, BitVec.ofNat 64 buf⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x19, ptr⟩,
   ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- The frame `__swrite` sees: `s0 = stdout`, `s1 = n`, `s2 = buf`, `s3 = ptr`. -/
abbrev sflFrame (f : AbiFrame) (ptr : BitVec 64) (buf n : Nat) : AbiFrame :=
  ⟨BitVec.ofNat 64 stdoutFile, BitVec.ofNat 64 n, BitVec.ofNat 64 buf, ptr, f.s4, f.s5, f.s6, f.s7, f.s8,
    f.s9, f.s10, f.s11⟩

set_option hygiene false in
/-- A segment state's pins normalised: addresses to `Nat`, reads forwarded
through the stores to the entry memory's fields. -/
local macro "sfl_norm" : tactic => `(tactic|
  simp (disch := omega) only [Vsa.Sim.sext_zero, BitVec.add_zero, add_imm,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id, bytesT8_sd_self, bytesT8_wm8_out, bytesT8_wm4_out,
    b8_wm2_out, bytesT4_wm8_out, b4_wm4_out, b4_wm2_out, b2_wm8_out, b2_wm4_out, b2_wm2_out,
    hflg, hp, hbase, hck, hwr, subw_len, subw_self] at h)

set_option hygiene false in
/-- … and a side condition's. -/
local macro "sfl_normg" : tactic => `(tactic|
  simp (disch := omega) only [Vsa.Sim.sext_zero, BitVec.add_zero, add_imm,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id, bytesT8_sd_self, bytesT8_wm8_out, bytesT8_wm4_out,
    b8_wm2_out, bytesT4_wm8_out, b4_wm4_out, b4_wm2_out, b2_wm8_out, b2_wm4_out, b2_wm2_out,
    hflg, hp, hbase, hck, hwr, upd_ret _ hra])

/-- The saved registers in `__sflush_r`'s frame. -/
structure SflSaved (M : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  s0 : bytesT8 M (sp - 48 + 32) = f.s0
  s1 : bytesT8 M (sp - 48 + 24) = f.s1
  s2 : bytesT8 M (sp - 48 + 16) = f.s2
  s3 : bytesT8 M (sp - 48 + 8) = f.s3
  ra : bytesT8 M (sp - 48 + 40) = r

set_option hygiene false in
/-- … the tail's pins, the saved registers read back. -/
local macro "sfl_tnorm" : tactic => `(tactic|
  simp (disch := omega) only [Vsa.Sim.sext_zero, BitVec.add_zero, add_imm,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id, hM.s0, hM.s1, hM.s2, hM.s3, hM.ra] at h)

set_option hygiene false in
local macro "sfl_tnormg" : tactic => `(tactic|
  simp (disch := omega) only [Vsa.Sim.sext_zero, BitVec.add_zero, add_imm,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id, hM.ra, upd_ret _ hra])

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (sfl_normg; exact hra)
      | (sfl_normg; decide)
      | (sfl_tnormg; exact hra))

/-- The pins at `0x800328d4` (`__sflush_r`'s common exit): `sp - 48`, and the
callee-saved registers, `s0`–`s3` about to be reloaded. -/
abbrev sflT (sp : Nat) (a8 a9 a18 a19 : BitVec 64) (f : AbiFrame) : List Pin :=
  [⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, a8⟩, ⟨Register.x9, a9⟩, ⟨Register.x18, a18⟩, ⟨Register.x19, a19⟩,
   ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- **`__sflush_r`'s exit** (`0x800328d4`): `s1`–`s3`, `s0`, `ra` reloaded, `0`
returned. -/
theorem sfl_ret (sp : Nat) (r : BitVec 64) (f : AbiFrame) (a8 a9 a18 a19 : BitVec 64) (M : Mem)
    (o : Array String) (hra : r.toNat % 4 = 0) (h1 : tohostAddr + 64 ≤ sp) (h2 : sp ≤ 2 ^ 32) (hM : SflSaved M sp r f) :
    Triple (SegSt 0x800328d4#64 (sflT sp a8 a9 a18 a19 f) (ArmPay M o)) (wrRet r sp 0 f M o) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  kit_run h acc
  sfl_tnorm
  have h := h.at (upd_ret r hra)
  rw [show sp - 48 + 0x030 = sp by omega] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

set_option hygiene false in
/-- The context and `stdout`'s fields the prologue and the hook call read. -/
local macro "sfl_facts" : tactic => `(tactic| (
  sfl_ctx hx hs
  have hflg : bytesT2 m (stdoutFile + 16) = 0x2889#16 := hs.flags
  have hp : bytesT8 m stdoutFile = BitVec.ofNat 64 (buf + pend.length) := hs.p
  have hbase : bytesT8 m (stdoutFile + 24) = BitVec.ofNat 64 buf := hs.base
  have hck : bytesT8 m (stdoutFile + 48) = BitVec.ofNat 64 stdoutFile := hs.cookie
  have hwr : bytesT8 m (stdoutFile + 64) = BitVec.ofNat 64 symSwrite := hs.write))

/-- `__sflush_r`'s first saves (`s0`, `s3`, `ra`). -/
abbrev sflMem0 (m : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m (sp - 48 + 32) (sdData_val f.s0)) (sp - 48 + 8) (sdData_val f.s3))
    (sp - 48 + 40) (sdData_val r)

/-- The pins at the write-mode branch target (`0x8003283c`). -/
abbrev sflP3c (sp : Nat) (ptr r : BitVec 64) (f : AbiFrame) : List Pin :=
  [⟨Register.x19, ptr⟩, ⟨Register.x8, BitVec.ofNat 64 stdoutFile⟩,
   ⟨Register.x14, sign_extend (m := 64) (0x2889#16 : BitVec 16)⟩,
   ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩, ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x1, r⟩,
   ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x18, f.s2⟩,
   ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- **`__sflush_r`'s entry on `stdout`** (to `0x8003283c`): the saves, the
write-mode test (`__SWR`). -/
theorem sfl_pro1 (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) :
    Triple (SegSt 0x800326f8#64 (sflPre ptr sp r f) (ArmPay m o))
      (SegSt 0x8003283c#64 (sflP3c sp ptr r f) (ArmPay (sflMem0 m sp r f) o)) := by
  intro c h
  have acc := Steps.refl c
  sfl_facts
  have hg1 : (((sign_extend (m := 64) (bytesT2 m (BitVec.ofNat 64 stdoutFile + sign_extend (m := 64) (0x010#12)).toNat :
      BitVec (8 * 2))) &&& sign_extend (m := 64) (0x008#12)) != (0#64)) = true := by
    rw [addr_add (by decide) (by omega), hflg]; decide
  kit_run h acc until [0x8003283c]
  rw [imm_sub 48 (0xfd0#12) (by decide) (by omega) (by omega)] at h
  sfl_norm
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- The pins after the buffer test (`0x80032848`). -/
abbrev sflP48 (sp buf : Nat) (ptr : BitVec 64) (f : AbiFrame) : List Pin :=
  [⟨Register.x18, BitVec.ofNat 64 buf⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩,
   ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
   ⟨Register.x8, BitVec.ofNat 64 stdoutFile⟩, ⟨Register.x9, f.s1⟩,
   ⟨Register.x14, sign_extend (m := 64) (0x2889#16 : BitVec 16)⟩, ⟨Register.x19, ptr⟩,
   ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- **The buffer test** (`0x8003283c` → `0x80032848`): `_bf._base ≠ NULL`,
`s2` saved. -/
theorem sfl_pro2 (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) :
    Triple (SegSt 0x8003283c#64 (sflP3c sp ptr r f) (ArmPay (sflMem0 m sp r f) o))
      (SegSt 0x80032848#64 (sflP48 sp buf ptr f)
        (ArmPay (writeMap8 (sflMem0 m sp r f) (sp - 48 + 16) (sdData_val f.s2)) o)) := by
  intro c h
  have acc := Steps.refl c
  sfl_facts
  have hg2 : (sign_extend (m := 64) (bytesT8 (writeMap8 (sflMem0 m sp r f)
      ((BitVec.ofNat 64 (sp - 48) + sign_extend (m := 64) (0x010#12)).toNat) (sdData_val f.s2))
      (BitVec.ofNat 64 stdoutFile + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8)) == 0#64) = false := by
    rw [addr_add (by decide) (by omega), addr_add (by decide) (by omega)]
    sfl_fwd
    rw [hbase, sext64_id]; exact ofNat_beq0 (by omega) (by omega)
  kit_run h acc until [0x80032848]
  sfl_norm
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`__sflush_r`'s prologue on `stdout`** up to the pending count's test
(`0x80032868`): the saves, `_p := _bf._base`, the count `_p - _bf._base`. -/
theorem sfl_pro (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) :
    Triple (SegSt 0x800326f8#64 (sflPre ptr sp r f) (ArmPay m o))
      (SegSt 0x80032868#64 (sflP68 sp buf pend.length ptr f) (ArmPay (sflMem3 m sp r f buf) o)) := by
  intro c h
  obtain ⟨_, acc, h⟩ := sfl_pro1 ptr sp buf pend r f m o hx hs c h
  obtain ⟨_, s2, h⟩ := sfl_pro2 ptr sp buf pend r f m o hx hs _ h
  have acc := acc.trans s2
  sfl_facts
  have hg3 : ((sign_extend (m := 64) (0x2889#16 : BitVec 16) &&& sign_extend (m := 64) (0x003#12)) != (0#64)) = true := by
    decide
  kit_run h acc until [0x80032868]
  sfl_norm
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- The pins on the return from `__swrite` (`0x80032894`). -/
abbrev sflR (sp buf n : Nat) (ptr : BitVec 64) (f : AbiFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: (sflFrame f ptr buf n).pins

/-- **The write loop's exit** after the one full write (`0x80032894` →
`0x800328d4`): `n - n = 0` bytes left. -/
theorem sfl_mid (sp buf n : Nat) (ptr : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (h0 : 0 < n) (hn : n < 2 ^ 31) :
    Triple (SegSt 0x80032894#64 (sflR sp buf n ptr f) (ArmPay M o))
      (SegSt 0x800328d4#64 (sflT sp (BitVec.ofNat 64 stdoutFile) 0#64
        (BitVec.ofNat 64 buf + BitVec.ofNat 64 n) ptr f) (ArmPay M o)) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hgl := slt0_ofNat (l := n) (by omega)
  simp only [h0, decide_true] at hgl
  have hge : zopz0zKzJ_s (0#64) (0#64) = true := by decide
  kit_run h acc until [0x80032874]
  simp only [subw_self] at h
  kit_run h acc until [0x800328d4]
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`__sflush_r` up to the write** (pending bytes): `__swrite`'s entry with
the pending count, the `FILE`'s `_p`, `_w` reset. -/
theorem sfl_head (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (hn : 0 < pend.length) :
    Triple (SegSt 0x800326f8#64 (sflPre ptr sp r f) (ArmPay m o))
      (SegSt 0x80034f18#64 (swPre ptr (sp - 48) buf pend.length 0x80032894#64 (sflFrame f ptr buf pend.length))
        (ArmPay (sflMem m sp r f buf) o)) := by
  intro c h
  obtain ⟨_, acc, h⟩ := sfl_pro ptr sp buf pend r f m o hx hs c h
  sfl_facts
  have hgl := slt0_ofNat (l := pend.length) (by omega)
  simp only [hn, decide_true] at hgl
  kit_run h acc until [0x8003287c]
  sfl_norm
  kit_run h acc
  sfl_norm
  rw [show BitVec.update (BitVec.ofNat 64 symSwrite) 0 0#1 = 0x80034f18#64 by decide] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`__sflush_r` with nothing pending**: straight to the exit. -/
theorem sfl_head0 (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (hn : pend.length = 0) :
    Triple (SegSt 0x800326f8#64 (sflPre ptr sp r f) (ArmPay m o))
      (SegSt 0x800328d4#64 (sflT sp (BitVec.ofNat 64 stdoutFile) (BitVec.ofNat 64 pend.length)
        (BitVec.ofNat 64 buf) ptr f) (ArmPay (sflMem m sp r f buf) o)) := by
  intro c h
  obtain ⟨_, acc, h⟩ := sfl_pro ptr sp buf pend r f m o hx hs c h
  sfl_facts
  have hgl := slt0_ofNat (l := pend.length) (by omega)
  simp only [hn, Nat.lt_irrefl, decide_false] at hgl
  rw [hn] at h
  kit_run h acc until [0x800328d4]
  rw [hn]
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ### The memory after the flush -/

theorem bytesT2_wm2_same {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x = a) :
    bytesT2 (writeMap2 m a d) x = d := by subst h; exact bytesT2_writeMap2 m x d

theorem bytesT4_wm4_same {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x = a) :
    bytesT4 (writeMap4 m a d) x = d := by subst h; exact bytesT4_wm4_self m x d

theorem bytesT8_wm8_same {m : Mem} {a x : Nat} {v : BitVec 64} (h : x = a) :
    bytesT8 (writeMap8 m a (sdData_val v)) x = v := by subst h; exact bytesT8_sd_self m x v

/-- The flush's whole memory: `__swrite`'s and its callees' stores over `sflMem`. -/
abbrev sflMemW (m : Mem) (sp : Nat) (r : BitVec 64) (f : AbiFrame) (buf : Nat) : Mem :=
  wrrRetMem (swMem (sflMem m sp r f buf) (sp - 48) 0x80032894#64 0x2889#16) (sp - 48)
    (BitVec.ofNat 64 stdoutFile) 0x80032894#64

set_option hygiene false in
/-- A read of the flushed memory, forwarded to its store or to the entry memory. -/
local macro "sfl_rd" : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hSF : stdoutFile = 0x8005e668 := rfl
  have hFZ : fileSize = 184 := rfl
  have hFL : fileFlagsOff = 16 := rfl
  have hFR : symFsReady = 0x8005d3c0 := rfl
  have hFD : symFds = 0x8005d460 := rfl
  have hBP : fileBufPOff = 0 := rfl
  have hWO : fileWOff = 12 := rfl
  have hFF : fileFileOff = 18 := rfl
  have hBB : fileBfBaseOff = 24 := rfl
  have hBS : fileBfSizeOff = 32 := rfl
  have hLB : fileLbfsizeOff = 40 := rfl
  have hCK : fileCookieOff = 48 := rfl
  have hWR : fileWriteOff = 64 := rfl
  simp (disch := omega) only [bytesT8_wm8_same, bytesT4_wm4_same, bytesT2_wm2_same,
    bytesT8_wm8_out, bytesT8_wm4_out, b8_wm2_out, bytesT4_wm8_out, b4_wm4_out, b4_wm2_out, b2_wm8_out,
    b2_wm4_out, b2_wm2_out, bytesT1_writeMap8_out, bytesT1_wm4_out, b1_wm2_out]))

theorem sfl_saved (m : Mem) (sp buf : Nat) (r : BitVec 64) (f : AbiFrame) (h1 : stdoutFile + 1700 ≤ sp)
    (h2 : sp ≤ 2 ^ 32) : SflSaved (sflMem m sp r f buf) sp r f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sfl_rd

theorem sfl_savedW (m : Mem) (sp buf : Nat) (r : BitVec 64) (f : AbiFrame) (h1 : stdoutFile + 1700 ≤ sp)
    (h2 : sp ≤ 2 ^ 32) : SflSaved (sflMemW m sp r f buf) sp r f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> sfl_rd

set_option hygiene false in
/-- The `StdoutAt … []` and keep facts of a flushed memory. -/
local macro "sfl_out_tac" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, by decide, hs.buf_lo, hs.buf_hi, ?_, ?_⟩, ?_, ?_, ?_⟩
  · sfl_rd; rfl
  · sfl_rd; decide
  · sfl_rd; first | decide | exact hs.flags
  · sfl_rd; exact hs.file
  · sfl_rd; exact hs.base
  · sfl_rd; exact hs.size
  · sfl_rd; exact hs.lbf
  · sfl_rd; exact hs.cookie
  · sfl_rd; exact hs.write
  · sfl_rd; exact hs.ready
  · sfl_rd; exact hs.stdout
  · intro a ha; sfl_rd
  · intro a ha hf he; sfl_rd
  · intro a h1 h2; sfl_rd))

theorem sfl_out (m : Mem) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (h1 : buf + 1024 + 512 ≤ sp) (h2 : sp ≤ 2 ^ 32) :
    SflOut m (sflMem m sp r f buf) sp buf := by
  have := hs.buf_lo
  sfl_out_tac

theorem sfl_outW (m : Mem) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (h1 : buf + 1024 + 512 ≤ sp) (h2 : sp ≤ 2 ^ 32) :
    SflOut m (sflMemW m sp r f buf) sp buf := by
  have := hs.buf_lo
  sfl_out_tac

/-- `__swrite`'s facts at the flush's call. -/
theorem sfl_swctx (m : Mem) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) (h1 : buf + 1024 + 512 ≤ sp) (h2 : sp ≤ 2 ^ 32) (h3 : sp % 16 = 0) :
    SwCtx (sflMem m sp r f buf) (sp - 48) buf pend.length 0x80032894#64 0x2889#16 := by
  have := hs.buf_lo; have := hs.room
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hSF : stdoutFile = 0x8005e668 := rfl
  have hFZ : fileSize = 184 := rfl
  refine ⟨by decide, by omega, by omega, by omega, by omega, by omega, .inr (by omega), ?_, ?_, ?_, by decide, ?_⟩
  · sfl_rd; exact hs.ready
  · sfl_rd; exact hs.stdout
  · sfl_rd; exact hs.flags
  · sfl_rd; exact hs.file

/-- **`__sflush_r(ptr, stdout)`**: the pending bytes `pend` written to the
console through `__swrite` → `_write_r` → `_write`, `0` returned, the buffer
empty (`SflOut`). -/
theorem sflush_sum (ptr : BitVec 64) (sp buf : Nat) (pend : List (BitVec 8)) (r : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (hx : SflCtx sp buf r) {wv : BitVec 32} (hs : StdoutAtW m buf pend wv) :
    Triple (SegSt 0x800326f8#64 (sflPre ptr sp r f) (ArmPay m o)) (SflRet r sp buf f m (pushes o pend)) := by
  intro c h
  have hb := hs.buf_lo; have hr := hs.room
  have h1 := hx.sp_lo; have h2 := hx.sp_hi; have h3 := hx.sp_al
  have hSF : stdoutFile = 0x8005e668 := rfl
  have hFZ : fileSize = 184 := rfl
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have h4 : stdoutFile + 1700 ≤ sp := by
    have hb' := hb; rw [hSF, hFZ] at hb'; rw [hSF]; omega
  have h5 : tohostAddr + 64 ≤ sp := by
    have hb' := hb; rw [hSF, hFZ] at hb'; rw [hTH]; omega
  by_cases h0 : pend.length = 0
  · obtain ⟨c1, s1, h1'⟩ := sfl_head0 ptr sp buf pend r f m o hx hs h0 c h
    obtain ⟨c2, s2, h2'⟩ := sfl_ret sp r f _ _ _ _ (sflMem m sp r f buf) o hx.ra h5 h2
      (sfl_saved m sp buf r f h4 h2) c1 h1'
    have hp : pend = [] := List.eq_nil_of_length_eq_zero h0
    subst hp
    exact ⟨c2, s1.trans s2, _, h2', sfl_out m sp buf [] r f hs h1 h2⟩
  · obtain ⟨c1, s1, h1'⟩ := sfl_head ptr sp buf pend r f m o hx hs (by omega) c h
    obtain ⟨c2, s2, h2'⟩ := swrite_sum ptr (sp - 48) buf pend.length 0x80032894#64 (sflFrame f ptr buf pend.length)
      (sflMem m sp r f buf) o 0x2889#16 (sfl_swctx m sp buf pend r f hs h1 h2 h3) c1 h1'
    obtain ⟨c3, s3, h3'⟩ := sfl_mid sp buf pend.length ptr f _ _ (by omega) (by omega) c2 h2'
    obtain ⟨c4, s4, h4'⟩ := sfl_ret sp r f _ _ _ _ (sflMemW m sp r f buf) _ hx.ra h5 h2
      (sfl_savedW m sp buf r f h4 h2) c3 h3'
    have hby : bytesAt (sflMem m sp r f buf) buf pend.length = pend := by
      rw [bytesAt_congr (m := m) fun i hi => by
        have hEA : errnoAddr = 0x8005d408 := rfl
        sfl_rd]
      exact hs.bytes
    rw [hby] at h4'
    exact ⟨c4, s1.trans (s2.trans (s3.trans s4)), _, h4', sfl_outW m sp buf pend r f hs h1 h2⟩

end Lua.Vm.Sim.Kit