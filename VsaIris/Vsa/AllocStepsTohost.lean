import VsaIris.Vsa.SymRun

/-!
# Why four allocator step tables are not ported (PHASES A0.2b)

`VsaIris/Vsa/AllocSteps/Part{00,02,08,10}.lean` (ship-your-interpreter,
`scripts/gen_alloc_steps.py` on the WHILE ELF) contain seven store lemmas
(`st_80000130`, `st_80000144`, `st_80004bd0`, `st_80004bdc`, `st_8000697c`,
`st_800072f4`, `st_80007348`) whose side condition `StOK ea w` discharges by
`decide`. Each `ea` is a `gp`-relative dlmalloc global of the WHILE ELF
(`gp = 0x8001b510`). `StOK` asks the store to lie above the HTIF mailbox
(`tohostAddr + 16 ≤ ea`). With `tohostAddr` the Lua ELF's `0x80048400`
(PHASES A0.1), those addresses lie below it, so the side conditions are false
and the lemmas are unprovable as stated. The other eight parts port unchanged.

The step tables are instances at WHILE addresses. PHASES A0.5 regenerates
them at the Lua ELF's addresses, where they are not needed.
-/

namespace VsaIris.Sym

open LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The obstruction, machine-checked: the side conditions of the seven
unported store lemmas are false at the Lua image's `tohost`. -/
theorem allocSteps_whileGlobals_not_stOK :
    ¬ StOK ((0x8001b510#64) + sign_extend (m := 64) (0x480#12)).toNat 8 ∧
    ¬ StOK ((0x8001b510#64) + sign_extend (m := 64) (0x488#12)).toNat 8 ∧
    ¬ StOK ((0x8001b510#64) + sign_extend (m := 64) (0x490#12)).toNat 8 ∧
    ¬ StOK ((0x8001b510#64) + sign_extend (m := 64) (0x4f8#12)).toNat 4 ∧
    ¬ StOK ((0x8001b510#64) + sign_extend (m := 64) (0x508#12)).toNat 8 := by
  decide

end VsaIris.Sym
