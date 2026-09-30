import Lua.Fragment
import Lua.Bytecode.Exec
import Lua.Vm.Host
/-! Law check (abstraction-discovery step 2), NOT a proof: random testing of
the bytecode footprint law on the executable stepper `step?`.

L-B1 (footprint): two states that agree on pc, output and the registers
`reads w` step alike: both stuck, or both step to the same pc and output,
agree on every register the edge writes, and leave every other register
as it was.
L-B3 (edges): the successor pc is an edge of `edgesOf`, and the registers
that changed are within that edge's write mask.

    lake env lean --run abstractions/checks/FootprintLaw.lean [trials] -/
open Lua.Bytecode Lua.Vm

def f1ops : Array OpCode := OpCode.all.toArray.filter (·.fragment == .F1)

def rnd (n : Nat) : IO Nat := IO.rand 0 (n - 1)

def rValue : IO Value := do
  match ← rnd 6 with
  | 0 => pure .nil
  | 1 => pure (.bool ((← rnd 2) == 1))
  | 2 => pure (.builtin .print)
  | 3 => pure (.int (BitVec.ofNat 64 (← rnd 5)))
  | 4 => pure (.int (0 - BitVec.ofNat 64 (← rnd 5)))
  | _ => pure (.int (BitVec.ofNat 64 (← rnd (2^64 - 1))))

def mkWord (op a k b c : Nat) : Word := BitVec.ofNat 32 (op + a * 2^7 + k * 2^15 + b * 2^16 + c * 2^24)
def mkBx (op a bx : Nat) : Word := BitVec.ofNat 32 (op + a * 2^7 + bx * 2^15)
def mkJ (sj : Int) : Word := BitVec.ofNat 32 (OpCode.JMP.toNat + (sj + 16777215).toNat * 2^7)

def regsOf (l : List Value) : Nat → Value := fun j => l.getD j .nil

def main (args : List String) : IO UInt32 := do
  let trials := (args.head? >>= String.toNat?).getD 20000
  let H := binaryHost
  let mut bad := 0; let mut stepped := 0; let mut stuck := 0
  for _ in [0:trials] do
    let op := f1ops[← rnd f1ops.size]!
    let a ← rnd 6; let b ← rnd 6; let c ← rnd 6; let k ← rnd 2
    let sel ← rnd 3; let sel2 ← rnd 4; let d5 ← rnd 5; let d4 ← rnd 4
    let w := if sel == 0 then mkBx op.toNat a (65535 + d5 - 2)
             else if sel2 == 0 then mkBx op.toNat a d4
             else mkWord op.toNat a k (b + if op == .EQI || op == .LTI || op == .LEI || op == .GTI || op == .GEI then 125 else 0) c
    let ks : List Const := [.str printKey, .int (BitVec.ofNat 64 (← rnd 7)), .nil, .bool true, .int 0, .int 1]
    let code : List Word := [.ofNat 32 (OpCode.VARARGPREP.toNat)] ++ [w, mkJ ((← rnd 5) - 2)] ++ List.replicate 20 (BitVec.ofNat 32 OpCode.RETURN0.toNat)
    let p : Proto := .mk 0 true 20 code ks [⟨true, 0, 0⟩] []
    let r1 ← (List.range 12).mapM fun _ => rValue
    let rd := reads w
    let r2 ← (List.range 12).mapM fun j => if rd.testBit j then pure r1[j]! else rValue
    -- precondition (what `Supported` guarantees at a reachable pc): the edges exist
    if (edgesOf p 1 w op).isNone then continue
    let s1 : State := ⟨1, regsOf r1, "x"⟩
    let s2 : State := ⟨1, regsOf r2, "x"⟩
    match step? H p s1, step? H p s2 with
    | none, none => stuck := stuck + 1
    | some t1, some t2 =>
      stepped := stepped + 1
      let es := (edgesOf p 1 w op).getD []
      -- some edge to the successor explains both steps
      let okEdge (wr : Nat) := (List.range 12).all fun j =>
        if wr.testBit j then t1.regs j == t2.regs j
        else t1.regs j == s1.regs j && t2.regs j == s2.regs j
      let edge := es.find? fun e => e.1 == t1.pc && okEdge e.2
      let okPc := t1.pc == t2.pc && t1.out == t2.out
      let okRegs := edge.isSome
      unless okPc && okRegs do
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"COUNTEREXAMPLE {repr op} w={w.toNat} pc {t1.pc}/{t2.pc} edgeOk={okRegs}"
    | _, _ =>
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"COUNTEREXAMPLE {repr op} w={w.toNat}: one state stuck, the other steps"
  IO.println s!"footprint law: {trials} trials, {stepped} stepped, {stuck} both stuck, {bad} counterexamples, {f1ops.size} F1 opcodes"
  pure (if bad == 0 then 0 else 1)
