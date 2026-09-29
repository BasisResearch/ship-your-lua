import LeanRiscv
import Vsa.Elf
/-! Discovery tool for `scripts/gen_lua_decode.py` (not part of any library).

Usage: `lake env lean --run scripts/lua_decode_ast_dump.lean ELF WORDS`
prints `<word>;OK;<repr of the decoded instruction>` per line of WORDS,
decoding with `ext_decode` in the machine state right after
`Vsa.setupElf` on ELF (so `misa`, `cur_privilege` and `mseccfg` hold the
values the decode lemmas pin). The printed ASTs only supply the lemma
statements; every lemma is kernel-checked when its module builds. This is
ship-your-interpreter's `experiments/M2_decode_ast_dump.lean` with the ELF
and the word list as arguments. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

def parseHex (s : String) : Nat :=
  s.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0

def main (args : List String) : IO Unit := do
  let [elfPath, wordsPath] := args | throw (IO.userError "usage: ELF WORDS")
  let lines ← IO.FS.lines wordsPath
  match ← readElf elfPath with
  | .error e => IO.println s!"ELF-ERR {e}"
  | .ok (.elf32 _) => IO.println "ELF-ERR 32-bit"
  | .ok (.elf64 elf) =>
    let σ0 : SequentialState RegisterType trivialChoiceSource :=
      ⟨Std.ExtDHashMap.emptyWithCapacity, (), initializeMemory MachineBits.B64 elf,
        default, default, default⟩
    match (Vsa.setupElf elf).run σ0 with
    | .error e _ => IO.println s!"SETUP-ERR {e.print}"
    | .ok _ σ' =>
      for l in lines do
        let t := l.trimAscii.toString
        if t.isEmpty then continue
        let w : BitVec 32 := BitVec.ofNat 32 (parseHex t)
        match (ext_decode w).run σ' with
        | .ok ast _ => IO.println s!"{t};OK;{(toString (repr ast)).replace "\n" " "}"
        | .error e _ => IO.println s!"{t};ERR;{e.print}"
