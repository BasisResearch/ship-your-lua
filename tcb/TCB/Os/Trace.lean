import TCB.Os.Syscall

/-!
# Trace format

One step per line, `CALL => RET`, in the spirit of SibylFS's check traces
(`sibylfs_src/fs_test/traces.md`). Strings are double-quoted with `\\`,
`\"`, `\n` and `\xHH` escapes. A file holds several traces, each starting
with a line `## NAME`; `#` lines are comments.

```
open "/d/f" O_RDWR|O_CREAT => num 3
write 3 "abc" 3 => num 3
lseek 3 0 0 => num 0
read 3 10 => bytes "abc"
fstat 3 => stats reg 3 1
stat "/d" => stats dir 0 2
mkdir "/d" => err EEXIST
opendir "/d" => num 1
readdir 1 => bytes "."
closedir 1 => none
```

A driver that cannot run a call writes `=> unsupported`; the checker then
skips the rest of that trace (and counts it).
-/

namespace TCB.Os.Trace

open Fs

/-! ## Tokens -/

inductive Tok where
  | word (s : String)
  | str (b : List UInt8)
  deriving Repr, BEq

private def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Split a line into words and quoted strings (strings are bytes: the
line is read as UTF-8, a string's characters are its UTF-8 bytes). `buf`
is `some` inside a string literal. -/
partial def tokenizeAux : List Char → Option (List UInt8) → List Tok → Except String (List Tok)
  | [], none, acc => .ok acc.reverse
  | [], some _, _ => .error "unterminated string"
  | '"' :: rest, some buf, acc => tokenizeAux rest none (.str buf.reverse :: acc)
  | '\\' :: 'n' :: rest, some buf, acc => tokenizeAux rest (some (10 :: buf)) acc
  | '\\' :: '\\' :: rest, some buf, acc => tokenizeAux rest (some (92 :: buf)) acc
  | '\\' :: '"' :: rest, some buf, acc => tokenizeAux rest (some (34 :: buf)) acc
  | '\\' :: 'x' :: a :: b :: rest, some buf, acc =>
    match hexVal a, hexVal b with
    | some x, some y => tokenizeAux rest (some ((x * 16 + y).toUInt8 :: buf)) acc
    | _, _ => .error "bad \\x escape"
  | c :: rest, some buf, acc =>
    tokenizeAux rest (some ((String.singleton c).toUTF8.toList.reverse ++ buf)) acc
  | c :: rest, none, acc =>
    if c == ' ' || c == '\t' then tokenizeAux rest none acc
    else if c == '"' then tokenizeAux rest (some []) acc
    else
      let w := (c :: rest).takeWhile (fun d => d != ' ' && d != '\t' && d != '"')
      tokenizeAux ((c :: rest).drop w.length) none (.word (String.ofList w) :: acc)

def tokenize (s : String) : Except String (List Tok) := tokenizeAux s.toList none []

def bytesToString (b : List UInt8) : String :=
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => s
  | none => String.ofList (b.map fun x => Char.ofNat x.toNat)

def showBytes (b : List UInt8) : String :=
  let esc (x : UInt8) : String :=
    if x == 34 then "\\\"" else if x == 92 then "\\\\" else if x == 10 then "\\n"
    else if x ≥ 32 && x < 127 then String.singleton (Char.ofNat x.toNat)
    else "\\x" ++ (if x.toNat < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)
  "\"" ++ String.join (b.map esc) ++ "\""

/-! ## Calls and returns -/

def parseFlags (s : String) : Except String OpenFlags := do
  let parts := s.splitOn "|"
  let acc ← match parts.filter (fun p => p == "O_RDONLY" || p == "O_WRONLY" || p == "O_RDWR") with
    | ["O_RDONLY"] => pure Access.rdonly
    | ["O_WRONLY"] => pure Access.wronly
    | ["O_RDWR"] => pure Access.rdwr
    | _ => throw s!"need exactly one access mode: {s}"
  for p in parts do
    unless ["O_RDONLY", "O_WRONLY", "O_RDWR", "O_CREAT", "O_EXCL", "O_TRUNC", "O_APPEND",
            "O_DIRECTORY"].contains p do throw s!"unknown flag {p}"
  pure { access := acc, creat := parts.contains "O_CREAT", excl := parts.contains "O_EXCL",
         trunc := parts.contains "O_TRUNC", append := parts.contains "O_APPEND",
         directory := parts.contains "O_DIRECTORY" }

def showFlags (f : OpenFlags) : String :=
  let a := match f.access with | .rdonly => "O_RDONLY" | .wronly => "O_WRONLY" | .rdwr => "O_RDWR"
  "|".intercalate ([a] ++ (if f.creat then ["O_CREAT"] else []) ++ (if f.excl then ["O_EXCL"] else [])
    ++ (if f.trunc then ["O_TRUNC"] else []) ++ (if f.append then ["O_APPEND"] else [])
    ++ (if f.directory then ["O_DIRECTORY"] else []))

private def nat? (t : Tok) : Except String Nat :=
  match t with
  | .word w => match w.toNat? with | some n => .ok n | none => .error s!"not a number: {w}"
  | _ => .error "expected a number"

private def int? (t : Tok) : Except String Int :=
  match t with
  | .word w => match w.toInt? with | some n => .ok n | none => .error s!"not an integer: {w}"
  | _ => .error "expected an integer"

private def str? (t : Tok) : Except String String :=
  match t with | .str b => .ok (bytesToString b) | _ => .error "expected a string"

def parseCall : List Tok → Except String Call
  | [.word "open", p, .word f] => do pure (.«open» (← str? p) (← parseFlags f))
  | [.word "close", a] => do pure (.close (← nat? a))
  | [.word "read", a, n] => do pure (.read (← nat? a) (← nat? n))
  | [.word "write", a, .str b, n] => do pure (.write (← nat? a) b (← nat? n))
  | [.word "lseek", a, o, w] => do pure (.lseek (← nat? a) (← int? o) (← int? w))
  | [.word "stat", p] => do pure (.stat (← str? p))
  | [.word "fstat", a] => do pure (.fstat (← nat? a))
  | [.word "unlink", p] => do pure (.unlink (← str? p))
  | [.word "rename", a, b] => do pure (.rename (← str? a) (← str? b))
  | [.word "mkdir", p] => do pure (.mkdir (← str? p))
  | [.word "rmdir", p] => do pure (.rmdir (← str? p))
  | [.word "opendir", p] => do pure (.opendir (← str? p))
  | [.word "readdir", a] => do pure (.readdir (← nat? a))
  | [.word "closedir", a] => do pure (.closedir (← nat? a))
  | [.word "clock"] => pure .clock
  | [.word "getenv", n] => do pure (.getenv (← str? n))
  | [.word "exit", c] => do pure (.exit (← nat? c))
  | ts => .error s!"cannot parse call {repr ts}"

def showCall : Call → String
  | .«open» p f => s!"open {showBytes p.toUTF8.toList} {showFlags f}"
  | .close a => s!"close {a}"
  | .read a n => s!"read {a} {n}"
  | .write a b n => s!"write {a} {showBytes b} {n}"
  | .lseek a o w => s!"lseek {a} {o} {w}"
  | .stat p => s!"stat {showBytes p.toUTF8.toList}"
  | .fstat a => s!"fstat {a}"
  | .unlink p => s!"unlink {showBytes p.toUTF8.toList}"
  | .rename a b => s!"rename {showBytes a.toUTF8.toList} {showBytes b.toUTF8.toList}"
  | .mkdir p => s!"mkdir {showBytes p.toUTF8.toList}"
  | .rmdir p => s!"rmdir {showBytes p.toUTF8.toList}"
  | .opendir p => s!"opendir {showBytes p.toUTF8.toList}"
  | .readdir a => s!"readdir {a}"
  | .closedir a => s!"closedir {a}"
  | .clock => "clock"
  | .getenv n => s!"getenv {showBytes n.toUTF8.toList}"
  | .exit c => s!"exit {c}"

/-- A parsed return, or the driver's `unsupported`. -/
inductive PRet where
  | ret (r : Ret)
  | unsupported

def parseKind : String → Except String Kind
  | "reg" => .ok .reg | "dir" => .ok .dir | "chr" => .ok .chr
  | k => .error s!"unknown kind {k}"

def parseRet : List Tok → Except String PRet
  | [.word "unsupported"] => .ok .unsupported
  | [.word "none"] => .ok (.ret .none)
  | [.word "num", n] => do pure (.ret (.num (← int? n)))
  | [.word "bytes", .str b] => .ok (.ret (.bytes b))
  | [.word "stats", .word k, s, n] => do pure (.ret (.stats ⟨← parseKind k, ← nat? s, ← nat? n⟩))
  | [.word "err", .word e] => match Errno.ofName? e with
    | some e => .ok (.ret (.err e))
    | none => .error s!"unknown errno {e}"
  | ts => .error s!"cannot parse return {repr ts}"

def showKind : Kind → String | .reg => "reg" | .dir => "dir" | .chr => "chr"

def showRet : Ret → String
  | .none => "none"
  | .num n => s!"num {n}"
  | .bytes b => s!"bytes {showBytes b}"
  | .stats st => s!"stats {showKind st.kind} {st.size} {st.nlink}"
  | .err e => s!"err {e.name}"

/-- A trace as read from a file: its steps, and whether the driver gave
up (`unsupported`) at some step. -/
structure Parsed where
  name : String
  steps : List (Call × Ret)
  lines : List String
  unsupportedAt : Option Nat

/-- Split a multi-trace file at `## NAME` lines and parse each trace. -/
def parseFile (text : String) : Except String (List Parsed) := do
  let mut out : Array Parsed := #[]
  let mut cur : Option Parsed := none
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "## " then
      if let some p := cur then out := out.push { p with steps := p.steps.reverse, lines := p.lines.reverse }
      cur := some ⟨(line.drop 3).toString, [], [], none⟩
    else if line.isEmpty || line.startsWith "#" then pure ()
    else
      let some p := cur | throw s!"step before any ## header: {line}"
      if p.unsupportedAt.isSome then continue
      match line.splitOn " => " with
      | [c, r] =>
        let call ← (tokenize c >>= parseCall).mapError (s!"{p.name}: {line}: " ++ ·)
        let ret ← (tokenize r >>= parseRet).mapError (s!"{p.name}: {line}: " ++ ·)
        match ret with
        | .unsupported => cur := some { p with unsupportedAt := some p.steps.length }
        | .ret r => cur := some { p with steps := (call, r) :: p.steps, lines := line :: p.lines }
      | _ => throw s!"{p.name}: no ' => ' in {line}"
  if let some p := cur then out := out.push { p with steps := p.steps.reverse, lines := p.lines.reverse }
  pure out.toList

/-- The returns the spec allows for `c` in `s` (for reports; the clock's
allowed set is infinite and shown as a bound). -/
def allowedRets (s : OsState) (c : Call) : List String :=
  match c with
  | .clock => [s!"num ≥ {s.clock.now}"]
  | c => ((outs s c).map fun | .ok _ r => showRet r | .special m => s!"special({m})").eraseDups

end TCB.Os.Trace
