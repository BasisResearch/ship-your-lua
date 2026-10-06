import Lua.Vm.Image
import Vsa.Sim.CodeRangeInsert
import Vsa.Sim.Code.FixedImage
import Vsa.Sim.StoreHalf

/-!
# The Lua ELF's `.text` as the code predicate of the generated arm segments

`TextLoaded m`: the exact `.text` bytes of `c/lua-riscv-htif.elf`
(`MachineAt.text` of `Lua/Vm/Loaded.lean`). The site batteries of
`Lua/Vm/Arms/Sites/*` fetch their four code bytes from it through the
generated pins (`Lua.Vm.Code.luaV_execute_at_<addr>` of the part
`textLoaded_LuaV_execute_p<k>Loaded`), and the segment theorems of
`Lua/Vm/Arms/Segs/*` carry it across every store with the three survival
lemmas below (`writeMap2`: `sh`, `Vsa/Sim/StoreHalf.lean`): a store the site lemmas accept lies at or above
`tohostAddr + 16`, above the whole of `.text`.
-/

open Vsa.Sim

namespace Lua.Vm.Arms

/-- The exact `.text` of the Lua ELF is loaded. -/
abbrev TextLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize Image.textByte m

/-- `.text` ends below the HTIF mailbox. -/
theorem text_below_tohost : Image.textBase + Image.textSize ≤ tohostAddr := by decide

theorem TextLoaded.writeMap8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : TextLoaded m)
    {k : Nat} (d : BitVec (8 * 8)) (hk : tohostAddr + 16 ≤ k) :
    TextLoaded (Vsa.Sim.writeMap8 m k d) :=
  Vsa.Sim.Code.FixedBytesLoaded.transport h fun a h1 h2 =>
    getElem?_writeMap8_outside Image.textBase (Image.textBase + Image.textSize) m k d
      (Or.inr (by have := text_below_tohost; omega)) a h1 h2

theorem TextLoaded.writeMap4 {m : Std.ExtHashMap Nat (BitVec 8)} (h : TextLoaded m)
    {k : Nat} (d : BitVec (8 * 4)) (hk : tohostAddr + 16 ≤ k) :
    TextLoaded (Vsa.Sim.writeMap4 m k d) :=
  Vsa.Sim.Code.FixedBytesLoaded.transport h fun a h1 h2 =>
    getElem?_writeMap4_outside Image.textBase (Image.textBase + Image.textSize) m k d
      (Or.inr (by have := text_below_tohost; omega)) a h1 h2

theorem TextLoaded.insert {m : Std.ExtHashMap Nat (BitVec 8)} (h : TextLoaded m)
    {k : Nat} (v : BitVec 8) (hk : tohostAddr + 16 ≤ k) :
    TextLoaded (m.insert k v) :=
  Vsa.Sim.Code.FixedBytesLoaded.transport h fun a h1 h2 =>
    getElem?_insert_outside Image.textBase (Image.textBase + Image.textSize) m k v
      (Or.inr (by have := text_below_tohost; omega)) a h1 h2

theorem TextLoaded.writeMap2 {m : Std.ExtHashMap Nat (BitVec 8)} (h : TextLoaded m)
    {k : Nat} (d : BitVec (8 * 2)) (hk : tohostAddr + 16 ≤ k) :
    TextLoaded (Vsa.Sim.writeMap2 m k d) :=
  (h.insert _ hk).insert _ (by omega)

end Lua.Vm.Arms
