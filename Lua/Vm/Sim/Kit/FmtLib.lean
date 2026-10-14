import Lua.Vm.Sim.Kit.AtFn
import Lua.Vm.Sim.Kit.Umoddi3

/-!
# The formatting callees' library (lane F1-FMT)

What the at-lemmas of `snprintf(buf, 44, "%lld", i)` (`Lua/Vm/AtF/SnprintfLld.lean`,
`gen_lua_at.py --fn snprintf/lld`) use beside the callee-context rows:

* `udivdi3_sumF`: `__udivdi3` as a call node whose caller's row has no `t0`
  (`_svfprintf_r`'s digit loop: `t0` dead there, `gen_lua_arms.py`
  `PASS_THROUGH_FOR`), `udivdi3_sumT` with `t0` at whatever it holds.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

/-- **`__udivdi3` on every divisor, `t0` not in the caller's row.** -/
theorem udivdi3_sumF (n d r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f734#64 (⟨Register.x10, n⟩ :: ⟨Register.x11, d⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m o))
      (SegSt r (⟨Register.x10, udivT n d⟩ :: ⟨Register.x11, n % d⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m o)) := by
  intro c h
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 5 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x5, t⟩ :: _) h ⟨ht, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨c', hs, h'⟩ := udivdi3_sumT n d r t f m o hr c (h.repin (by pins_of h))
  exact ⟨c', hs, h'.repin (by pins_of h')⟩

/-- **`fmt_pin h n R`**: register `R` (GPR `n`) pinned at whatever it holds
(every GPR holds a value, `RegsOk`): a register a segment carries that the
path never set (`gen_lua_at.py` `junk`). -/
macro "fmt_pin " h:ident n:num R:ident : tactic => `(tactic| (
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk $h) $n (by decide) (by decide))
  have $h := Vsa.Sim.SegSt.repin (L' := ⟨$R, t⟩ :: _) $h ⟨ht, Vsa.Sim.SegSt.pins $h⟩))

/-! ## 32-bit arithmetic on small counts

The generator keeps `sext.w`/`addiw`/`addw`/`subw` of counts whose ranges stay
in the signed 32-bit range as their 64-bit values (`gen_lua_at.py`
`small32`); the at-lemmas close the machine's terms against them by
`fmt_w32`: the truncations commute with the subtraction (`extract_sub`), a
value in range is its own sign extension (`sxw_id`), then `toNat` and `omega`. -/

theorem extract_sub (a b : BitVec 64) :
    Sail.BitVec.extractLsb a 31 0 - Sail.BitVec.extractLsb b 31 0 = Sail.BitVec.extractLsb (a - b) 31 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.toNat_sub, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  have ha := a.isLt; have hb := b.isLt
  omega

theorem extract_add (a b : BitVec 64) :
    Sail.BitVec.extractLsb a 31 0 + Sail.BitVec.extractLsb b 31 0 = Sail.BitVec.extractLsb (a + b) 31 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.toNat_add, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  have ha := a.isLt; have hb := b.isLt
  omega

/-- A 64-bit value in the signed 32-bit range is its own `sext.w`. -/
theorem sxw_id (x : BitVec 64) (h : x.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ x.toNat) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have e32 : (Sail.BitVec.extractLsb x 31 0).toNat = x.toNat % 2 ^ 32 := by
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, e32]
  split <;> rename_i hm <;> simp only [decide_eq_true_eq] at hm <;> omega

/-- A 32-bit literal's `sext.w` (a `lw` of a small word). -/
theorem sext32_ofNat {n : Nat} (h : n < 2 ^ 31) :
    sign_extend (m := 64) (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  split <;> rename_i hm <;> simp only [decide_eq_true_eq] at hm <;> omega

theorem extract_ofNat (n : Nat) : Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

/-- `sext.w` of a negative 32-bit difference (`subw` of a count from `0`). -/
theorem sext32_neg {n : Nat} (h0 : 0 < n) (h : n ≤ 2 ^ 31) :
    sign_extend (m := 64) (BitVec.ofNat 32 0 - BitVec.ofNat 32 n) = BitVec.ofNat 64 0 - BitVec.ofNat 64 n := by
  have e1 : (BitVec.ofNat 32 0 - BitVec.ofNat 32 n).toNat = 2 ^ 32 - n := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, e1]
  split <;> rename_i hm <;> simp only [decide_eq_true_eq] at hm <;> omega

/-- **`subw` from `0`** of a count. -/
theorem subw_neg0 {n : Nat} (h0 : 0 < n) (h : n ≤ 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (0#64) 31 0 - Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 n := by
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, extract_ofNat, extract_ofNat]
  exact sext32_neg h0 h

/-- **`subw` from `-1`** (the precision's default) of a count. -/
theorem subw_m1 {n : Nat} (h : n < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (0xffffffffffffffff#64) 31 0 -
      Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0) = BitVec.ofNat 64 0 - BitVec.ofNat 64 (n + 1) := by
  have e : Sail.BitVec.extractLsb (0xffffffffffffffff#64 : BitVec 64) 31 0 = BitVec.ofNat 32 0 - BitVec.ofNat 32 1 := by
    decide
  rw [e, extract_ofNat, BitVec.sub_sub, show BitVec.ofNat 32 1 + BitVec.ofNat 32 n = BitVec.ofNat 32 (n + 1) by
    rw [BitVec.ofNat_add_ofNat, Nat.add_comm]]
  exact sext32_neg (by omega) (by omega)

/-- The `Nat` of a sum or difference of `ofNat`s, by `omega` (the at-lemma's
bounds in context). -/
macro "fmt_nat" : tactic => `(tactic| (
  simp (disch := omega) only [add_imm, Vsa.Sim.sext_zero, Vsa.Sim.sext_one, BitVec.add_zero, sext32_ofNat,
    BitVec.ofNat_add_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;>
  omega))

/-- **`fmt_w32`**: a machine `sext.w`/`addiw`/`addw`/`subw` term equal to
its value (an `at_eq` goal). -/
macro "fmt_w32" : tactic => `(tactic| (
  (try simp only [extract_sub, extract_add])
  rw [sxw_id _ (by fmt_nat)]
  first | done | (apply BitVec.eq_of_toNat_eq; fmt_nat)))

macro_rules
  | `(tactic| at_eq_ext) => `(tactic| fmt_w32)

/-- The negative counts' forms first (never `simp` a `toNat` of the literal
`-1`: its evaluation does not terminate in memory). -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| first
      | (rw [subw_m1 (by omega)]; done)
      | (rw [subw_neg0 (by omega) (by omega)]; done))

/-- A count read back and stepped (`resid - len`): its `Nat`. -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (fat_rd; apply BitVec.eq_of_toNat_eq; fmt_nat))

/-- A byte load at an address in another affine form. -/
theorem zx_ld1_congr {m : Mem} {a b : Nat} (h : a = b) :
    zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) = zero_extend (m := 64) (bytesT1 m b : BitVec (8 * 1)) := by
  subst h; rfl

macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (fat_rd; exact zx_ld1_congr (by omega)))

/-! ## Signed tests of small counts -/

theorem fmt_toInt_ofNat {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega

theorem fmt_toInt_neg {n : Nat} (h0 : 0 < n) (h : n ≤ 2 ^ 63) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 n).toInt = -(n : Int) := by
  have hc := BitVec.toInt_eq_toNat_cond (BitVec.ofNat 64 0 - BitVec.ofNat 64 n)
  have e : (BitVec.ofNat 64 0 - BitVec.ofNat 64 n).toNat = 2 ^ 64 - n := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [e] at hc; split at hc <;> omega

theorem toInt_m1 : (0xffffffffffffffff#64 : BitVec 64).toInt = -1 := by decide
theorem toInt_z : (0x0#64 : BitVec 64).toInt = 0 := by decide

/-- **`fmt_scmp`**: a signed test (`blt`/`bge`) of small counts, literals and
their negations. -/
macro "fmt_scmp" : tactic => `(tactic| (
  simp (disch := omega) only [zopz0zI_s, zopz0zKzJ_s, fmt_toInt_ofNat, fmt_toInt_neg, toInt_m1, toInt_z]
  (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, ge_iff_le, Bool.not_eq_true]) <;>
  omega))

macro_rules
  | `(tactic| fat_hyp) => `(tactic| (fmt_scmp; done))

end Lua.Vm.Sim.Kit
