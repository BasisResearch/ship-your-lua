/-!
# Console streams (TRUSTED: part of the OS interface)

The standard streams, after CakeML's basis file-system model
(`CakeML/cakeml` at `530c7deec135ad421cce7ca768eed2f5801261b2`, BSD-3,
`tcb/LICENSE-cakeml`; `tcb/upstream/cakeml/fsFFIScript.sml`, cited as
`fsFFI:LINE`). There, stdin/stdout/stderr are unnamed streams
(`inode = UStream`, fsFFI:15), and reads and writes may transfer fewer
bytes than asked, decided by an oracle stream `numchars` (fsFFI:34):

* `read` (fsFFI:106): `k = MIN n (MIN (LENGTH content - off) (SUC strm))`,
  so a read of `n > 0` bytes with input left returns between 1 and
  `min n remaining` bytes, and 0 only at end of input;
* `write` (fsFFI:131): `k = MIN n strm`, so between 0 and `n` bytes.

Here the oracle is replaced by the equivalent nondeterministic choice: the
spec allows every `k` the oracle could produce, and the observed `k` is
checked against that range. Output streams are append-only.
-/

namespace TCB.Os

inductive Stream where
  | stdin | stdout | stderr
  deriving DecidableEq, Repr, Inhabited

structure Streams where
  /-- input not yet read -/
  input : List UInt8
  /-- everything written to stdout / stderr -/
  out : List UInt8
  err : List UInt8
  /-- the interleaving of stdout and stderr, as a console shows it -/
  console : List UInt8
  deriving DecidableEq, Repr

namespace Streams

def init (input : List UInt8 := []) : Streams := ⟨input, [], [], []⟩

/-- The lengths a `read` of `n` bytes may return (fsFFI:106). -/
def readLengths (st : Streams) (n : Nat) : List Nat :=
  let hi := min n st.input.length
  let lo := min hi 1
  (List.range (hi + 1)).filter (lo ≤ ·)

/-- The lengths a `write` of `n` bytes may return (fsFFI:131). -/
def writeLengths (n : Nat) : List Nat := List.range (n + 1)

def doRead (st : Streams) (k : Nat) : Streams := { st with input := st.input.drop k }

def doWrite (st : Streams) (s : Stream) (bs : List UInt8) : Streams :=
  match s with
  | .stdout => { st with out := st.out ++ bs, console := st.console ++ bs }
  | .stderr => { st with err := st.err ++ bs, console := st.console ++ bs }
  | .stdin => st

end Streams
end TCB.Os
