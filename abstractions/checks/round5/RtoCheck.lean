import Lua.Vm.Fn.Spec

set_option linter.unusedVariables false

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic
open Lua.Vm.Sim
open Lua.Num

namespace Lua.Vm.Fn.RtoCheck

/-- One step of a traced run: a node with its live-ins; a round site's
pre-round mantissa `x` at semiraw exponent `e` (`probe`: the operand of the
site's own inexactness test; `folded`: a site the compiler folded into a
constant); the pack join's mantissa and exponent. -/
inductive Ev where
  | node (pc : Nat) (args : List (BitVec 64))
  | probe (pc : Nat) (x e : BitVec 64)
  | folded (pc : Nat) (x e : BitVec 64)
  | join (pc : Nat) (x e : BitVec 64)
  deriving Repr, BEq

abbrev Tr := List Ev × BitVec 64

-- BEGIN rto_trace.py (GENERATED from Lua/Vm/Fn/{Adddf3,Subdf3}/Defs.lean; rerun the script, do not edit)
namespace Adddf3T
open Lua.Vm.Fn.Adddf3

def T_8002db68 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v29 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| v14) ||| (shift_bits_left v29 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002db68 [v10, v14, v29]] ++ t.1, t.2)

def T_8002dcc8 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v29 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r v10 (((0#64) + sign_extend (m := 64) (0x000#12))) v29
  ([Ev.node 0x8002dcc8 [v10, v29]] ++ t.1, t.2)

def T_8002de08 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r ((v15 &&& sign_extend (m := 64) (0x7ff#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x0c#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((v17 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002de08 [v14, v15, v17]] ++ t.1, t.2)

def T_8002d940 (m : Mem) (s : Nat) (r : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x7ff#12))) ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x33#6) 5 0))) (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002d940 []] ++ t.1, t.2)

def T_8002d93c (m : Mem) (s : Nat) (r : BitVec 64) (v12 v14 v15 v17 : BitVec 64) : Tr :=
  let t := if (v12 == (0#64)) = true then T_8002de08 (m) s r v14 v15 v17 else T_8002d940 (m) s r
  ([Ev.node 0x8002d93c [v12, v14, v15, v17]] ++ t.1, t.2)

def T_8002d934 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0)) == (0#64)) = true then T_8002de08 (m) s r ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v17 else T_8002d93c (m) s r v12 ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v17
  ([Ev.node 0x8002d934 [v12, v13, v15, v17]] ++ t.1, t.2)

def T_8002d92c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d934 (m) s r ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (v15 + sign_extend (m := 64) (0x801#12)) (sign_extend (m := 64) (0x001#12)))))) v13 v15 v17
  ([Ev.node 0x8002d92c [v13, v15, v17], Ev.join 0x8002d92c (v13) (v15)] ++ t.1, t.2)

def T_8002dc80 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r v13 ((v10 + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002dc80 [v10, v13, v17]] ++ t.1, t.2)

def T_8002dc7c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v17 : BitVec 64) : Tr :=
  let t := T_8002dc80 (m) s r v10 ((v13 + sign_extend (m := 64) (0x004#12))) v17
  ([Ev.node 0x8002dc7c [v10, v13, v17]] ++ t.1, t.2)

def T_8002dc70 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002dc80 (m) s r v10 v13 v17 else T_8002dc7c (m) s r v10 v13 v17
  ([Ev.node 0x8002dc70 [v10, v13, v17]] ++ t.1, t.2)

def T_8002dc60 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v17 v30 : BitVec 64) : Tr :=
  let t := if (((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002dc80 (m) s r v10 ((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x01#6) 5 0))) v17 else T_8002dc70 (m) s r v10 ((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x01#6) 5 0))) v17
  ([Ev.node 0x8002dc60 [v10, v13, v17, v30], Ev.probe 0x8002dc60 ((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x01#6) 5 0))) (v10)] ++ t.1, t.2)

def T_8002dc58 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v10 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002dcc8 (m) s r v10 v29 else T_8002dc60 (m) s r v10 v13 v17 v30
  ([Ev.node 0x8002dc58 [v10, v13, v17, v29, v30]] ++ t.1, t.2)

def T_8002dd04 (m : Mem) (s : Nat) (r : BitVec 64) (v17 v30 : BitVec 64) : Tr :=
  let t := T_8002d934 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) ((v30 + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x7ff#12))) v17
  ([Ev.node 0x8002dd04 [v17, v30]] ++ t.1, t.2)

def T_8002dd00 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 v30 : BitVec 64) : Tr :=
  let t := if (v13 != (0#64)) = true then T_8002d940 (m) s r else T_8002dd04 (m) s r v17 v30
  ([Ev.node 0x8002dd00 [v13, v17, v30]] ++ t.1, t.2)

def T_8002dd98 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v29 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) ((v6 + sign_extend (m := 64) (0x000#12))) v29
  ([Ev.node 0x8002dd98 [v6, v29]] ++ t.1, t.2)

def T_8002ddb8 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v29 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) v14 v29
  ([Ev.node 0x8002ddb8 [v14, v29]] ++ t.1, t.2)

def T_8002dda4 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v12 v13 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v13 + v30) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002db68 (m) s r v10 (((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12)) v29 else T_8002ddb8 (m) s r (((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12)) v29
  ([Ev.node 0x8002dda4 [v10, v12, v13, v29, v30]] ++ t.1, t.2)

def T_8002db60 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v13 v14 v29 v30 : BitVec 64) : Tr :=
  let t := if (v30 != (0#64)) = true then T_8002dda4 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v12 v13 v29 v30 else T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v14 v29
  ([Ev.node 0x8002db60 [v12, v13, v14, v29, v30]] ++ t.1, t.2)

def T_8002db5c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v13 v14 v29 v30 : BitVec 64) : Tr :=
  let t := if (v13 == (0#64)) = true then T_8002dd98 (m) s r v6 v29 else T_8002db60 (m) s r v12 v13 v14 v29 v30
  ([Ev.node 0x8002db5c [v6, v12, v13, v14, v29, v30]] ++ t.1, t.2)

def T_8002db58 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v13 v14 v15 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002dd00 (m) s r v13 v17 v30 else T_8002db5c (m) s r v6 v12 v13 v14 v29 v30
  ([Ev.node 0x8002db58 [v6, v12, v13, v14, v15, v17, v29, v30]] ++ t.1, t.2)

def T_8002db4c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v13 v14 v15 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (((v15 + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x7fe#12)) != (0#64)) = true then T_8002dc58 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v13 v17 v29 v30 else T_8002db58 (m) s r v6 v12 v13 v14 v15 v17 v29 v30
  ([Ev.node 0x8002db4c [v6, v12, v13, v14, v15, v17, v29, v30]] ++ t.1, t.2)

def T_8002da40 (m : Mem) (s : Nat) (r : BitVec 64) (v17 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002d934 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) ((v30 + sign_extend (m := 64) (0x000#12))) ((v28 + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002da40 [v17, v28, v30]] ++ t.1, t.2)

def T_8002de04 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002de08 (m) s r ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v17
  ([Ev.node 0x8002de04 [v13, v15, v17]] ++ t.1, t.2)

def T_8002d9c0 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v29 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r v10 ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) v29
  ([Ev.node 0x8002d9c0 [v10, v14, v29]] ++ t.1, t.2)

def T_8002dd80 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v29 : BitVec 64) : Tr :=
  let t := T_8002d9c0 (m) s r ((v15 &&& sign_extend (m := 64) (0x7ff#12))) ((v13 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) v29
  ([Ev.node 0x8002dd80 [v13, v15, v29]] ++ t.1, t.2)

def T_8002dd68 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002db68 (m) s r (((v15 + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12))) ((v17 + sign_extend (m := 64) (0x000#12))) else T_8002dd80 (m) s r v13 ((v15 + sign_extend (m := 64) (0x001#12))) ((v17 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dd68 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dd5c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v13 + sign_extend (m := 64) (0x004#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002d92c (m) s r ((v13 + sign_extend (m := 64) (0x004#12))) v15 v17 else T_8002dd68 (m) s r ((v13 + sign_extend (m := 64) (0x004#12))) v15 v17
  ([Ev.node 0x8002dd5c [v13, v15, v17]] ++ t.1, t.2)

def T_8002dd50 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002d92c (m) s r v13 v15 v17 else T_8002dd5c (m) s r v13 v15 v17
  ([Ev.node 0x8002dd50 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dd48 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002de04 (m) s r v13 v15 v17 else T_8002dd50 (m) s r v13 v15 v17
  ([Ev.node 0x8002dd48 [v13, v15, v17], Ev.probe 0x8002dd48 (v13) (v15)] ++ t.1, t.2)

def T_8002dcc4 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v29 : BitVec 64) : Tr :=
  let t := T_8002dcc8 (m) s r ((v15 + sign_extend (m := 64) (0x000#12))) v29
  ([Ev.node 0x8002dcc4 [v15, v29]] ++ t.1, t.2)

def T_8002dbfc (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v13 + sign_extend (m := 64) (0x004#12))) v15 v17
  ([Ev.node 0x8002dbfc [v13, v15, v17]] ++ t.1, t.2)

def T_8002dbf0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002d92c (m) s r v13 v15 v17 else T_8002dbfc (m) s r v13 v15 v17
  ([Ev.node 0x8002dbf0 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dbcc (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if (((((shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v13 &&& sign_extend (m := 64) (0x001#12))) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002d92c (m) s r ((((shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v13 &&& sign_extend (m := 64) (0x001#12)))) v15 v17 else T_8002dbf0 (m) s r ((((shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v13 &&& sign_extend (m := 64) (0x001#12)))) v15 v17
  ([Ev.node 0x8002dbcc [v13, v15, v17], Ev.probe 0x8002dbcc ((((shift_bits_right v13 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v13 &&& sign_extend (m := 64) (0x001#12)))) (v15)] ++ t.1, t.2)

def T_8002dbc0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 v29 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002dcc4 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v29 else T_8002dbcc (m) s r v13 ((v15 + sign_extend (m := 64) (0x001#12))) v17
  ([Ev.node 0x8002dbc0 [v13, v15, v17, v29]] ++ t.1, t.2)

def T_8002dbb8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left v13 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dd48 (m) s r v13 v15 v17 else T_8002dbc0 (m) s r v13 v15 v17 v29
  ([Ev.node 0x8002dbb8 [v13, v15, v17, v29]] ++ t.1, t.2)

def T_8002dcd0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := T_8002dbb8 (m) s r ((((shift_bits_right v13 (Sail.BitVec.extractLsb v14 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v13 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v14 31 0))) 5 0)))))) + v30)) ((v28 + sign_extend (m := 64) (0x000#12))) v17 v29
  ([Ev.node 0x8002dcd0 [v13, v14, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dc4c (m : Mem) (s : Nat) (r : BitVec 64) (v17 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v30 + sign_extend (m := 64) (0x005#12))) ((v28 + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002dc4c [v17, v28, v30], Ev.folded 0x8002dc4c (v30 + 1) (v28)] ++ t.1, t.2)

def T_8002dc44 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v14 = true then T_8002dcd0 (m) s r v13 v14 v17 v28 v29 v30 else T_8002dc4c (m) s r v17 v28 v30
  ([Ev.node 0x8002dc44 [v13, v14, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dc34 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := T_8002dc44 (m) s r ((v13 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)))) ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (0#64) 31 0) - (Sail.BitVec.extractLsb v16 31 0)))) v17 v28 v29 v30
  ([Ev.node 0x8002dc34 [v13, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dc2c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v28 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002da40 (m) s r v17 v28 v30 else T_8002dc34 (m) s r v13 v16 v17 v28 v29 v30
  ([Ev.node 0x8002dc2c [v13, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dd3c (m : Mem) (s : Nat) (r : BitVec 64) (v17 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v30 + sign_extend (m := 64) (0x000#12))) ((v28 + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002dd3c [v17, v28, v30]] ++ t.1, t.2)

def T_8002ddd0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r v13 v15 v17
  ([Ev.node 0x8002ddd0 [v13, v15, v17]] ++ t.1, t.2)

def T_8002ddc0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v13 + v30) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dbc0 (m) s r ((v13 + v30)) ((v28 + sign_extend (m := 64) (0x000#12))) v17 v29 else T_8002ddd0 (m) s r ((v13 + v30)) ((v28 + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002ddc0 [v13, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002da38 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v28 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002dc44 (m) s r v13 v14 v17 v28 v29 v30 else T_8002da40 (m) s r v17 v28 v30
  ([Ev.node 0x8002da38 [v13, v14, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002da30 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if ((v16 ^^^ sign_extend (m := 64) (0xfff#12)) == (0#64)) = true then T_8002ddc0 (m) s r v13 v17 v28 v29 v30 else T_8002da38 (m) s r v13 ((v16 ^^^ sign_extend (m := 64) (0xfff#12))) v17 v28 v29 v30
  ([Ev.node 0x8002da30 [v13, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002da2c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v13 == (0#64)) = true then T_8002dd3c (m) s r v17 v28 v30 else T_8002da30 (m) s r v13 v16 v17 v28 v29 v30
  ([Ev.node 0x8002da2c [v13, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002da28 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002dc2c (m) s r v13 v16 v17 v28 v29 v30 else T_8002da2c (m) s r v13 v16 v17 v28 v29 v30
  ([Ev.node 0x8002da28 [v13, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002da24 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v13 v14 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v16 == (0#64)) = true then T_8002db4c (m) s r v6 v12 v13 v14 v15 v17 v29 v30 else T_8002da28 (m) s r v13 v15 v16 v17 v28 v29 v30
  ([Ev.node 0x8002da24 [v6, v12, v13, v14, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dcb0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r v13 v15 v17
  ([Ev.node 0x8002dcb0 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dca4 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right (v13 + v30) (Sail.BitVec.extractLsb (0x37#6) 5 0)) != (0#64)) = true then T_8002dbc0 (m) s r ((v13 + v30)) v15 v17 v29 else T_8002dcb0 (m) s r ((v13 + v30)) v15 v17
  ([Ev.node 0x8002dca4 [v13, v15, v17, v29, v30]] ++ t.1, t.2)

def T_8002db9c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := T_8002dbb8 (m) s r ((v13 + ((shift_bits_right v30 (Sail.BitVec.extractLsb v16 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v30 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v16 31 0))) 5 0)))))))) v15 v17 v29
  ([Ev.node 0x8002db9c [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d928 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v13 + sign_extend (m := 64) (0x005#12))) v15 v17
  ([Ev.node 0x8002d928 [v13, v15, v17], Ev.folded 0x8002d928 (v13 + 1) (v15)] ++ t.1, t.2)

def T_8002d920 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v16 = true then T_8002db9c (m) s r v13 v15 v16 v17 v29 v30 else T_8002d928 (m) s r v13 v15 v17
  ([Ev.node 0x8002d920 [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d9e0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d934 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) v13 v15 v17
  ([Ev.node 0x8002d9e0 [v13, v15, v17]] ++ t.1, t.2)

def T_8002d9d8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v15 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d920 (m) s r v13 v15 v16 v17 v29 v30 else T_8002d9e0 (m) s r v13 v15 v17
  ([Ev.node 0x8002d9d8 [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d9d0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0xfff#12)) 31 0)) == (0#64)) = true then T_8002dca4 (m) s r v13 v15 v17 v29 v30 else T_8002d9d8 (m) s r v13 v15 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0xfff#12)) 31 0))) v17 v29 v30
  ([Ev.node 0x8002d9d0 [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d9cc (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v30 == (0#64)) = true then T_8002d92c (m) s r v13 v15 v17 else T_8002d9d0 (m) s r v13 v15 v16 v17 v29 v30
  ([Ev.node 0x8002d9cc [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d8fc (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d934 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) v13 v15 v17
  ([Ev.node 0x8002d8fc [v13, v15, v17]] ++ t.1, t.2)

def T_8002d914 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := T_8002d920 (m) s r v13 v15 v16 v17 v29 ((v30 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))))
  ([Ev.node 0x8002d914 [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d90c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v15 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d8fc (m) s r v13 v15 v17 else T_8002d914 (m) s r v13 v15 v16 v17 v29 v30
  ([Ev.node 0x8002d90c [v13, v15, v16, v17, v29, v30]] ++ t.1, t.2)

def T_8002d908 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002d9cc (m) s r v13 v15 v16 v17 v29 v30 else T_8002d90c (m) s r v13 v15 v16 v17 v29 v30
  ([Ev.node 0x8002d908 [v13, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002d904 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v13 v14 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (0#64) v16 = true then T_8002da24 (m) s r v6 v12 v13 v14 v15 v16 v17 v28 v29 v30 else T_8002d908 (m) s r v13 v15 v16 v17 v28 v29 v30
  ([Ev.node 0x8002d904 [v6, v12, v13, v14, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002d8b8 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v29 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| v14) ||| (shift_bits_left v29 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002d8b8 [v10, v14, v29]] ++ t.1, t.2)

def T_8002de1c (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d8b8 (m) s r ((v15 &&& sign_extend (m := 64) (0x7ff#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x0c#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((v17 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002de1c [v14, v15, v17]] ++ t.1, t.2)

def T_8002dae0 (m : Mem) (s : Nat) (r : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left ((0#64) + sign_extend (m := 64) (0x7ff#12)) (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x33#6) 5 0))) ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x000#12)) (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002dae0 []] ++ t.1, t.2)

def T_8002dadc (m : Mem) (s : Nat) (r : BitVec 64) (v12 v14 v15 v17 : BitVec 64) : Tr :=
  let t := if (v12 == (0#64)) = true then T_8002de1c (m) s r v14 v15 v17 else T_8002dae0 (m) s r
  ([Ev.node 0x8002dadc [v12, v14, v15, v17]] ++ t.1, t.2)

def T_8002dacc (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0)) == (0#64)) = true then T_8002de1c (m) s r ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v17 else T_8002dadc (m) s r ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (v15 + sign_extend (m := 64) (0x801#12)) (sign_extend (m := 64) (0x001#12)))))) ((shift_bits_right v13 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v17
  ([Ev.node 0x8002dacc [v13, v15, v17]] ++ t.1, t.2)

def T_8002d89c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v29 : BitVec 64) : Tr :=
  let t := T_8002d8b8 (m) s r ((v15 &&& sign_extend (m := 64) (0x7ff#12))) ((shift_bits_right (shift_bits_left (v13 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) v29
  ([Ev.node 0x8002d89c [v13, v15, v29]] ++ t.1, t.2)

def T_8002da9c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v29 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| v14) ||| (shift_bits_left v29 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002da9c [v10, v14, v29]] ++ t.1, t.2)

def T_8002da84 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d89c (m) s r v13 ((v15 + sign_extend (m := 64) (0x001#12))) ((v17 + sign_extend (m := 64) (0x000#12))) else T_8002da9c (m) s r (((v15 + sign_extend (m := 64) (0x001#12)) + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12))) ((v17 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002da84 [v13, v15, v17]] ++ t.1, t.2)

def T_8002da78 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v13 + sign_extend (m := 64) (0x004#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dacc (m) s r ((v13 + sign_extend (m := 64) (0x004#12))) v15 v17 else T_8002da84 (m) s r ((v13 + sign_extend (m := 64) (0x004#12))) v15 v17
  ([Ev.node 0x8002da78 [v13, v15, v17]] ++ t.1, t.2)

def T_8002da6c (m : Mem) (s : Nat) (r : BitVec 64) (v12 v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v12 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002dacc (m) s r v13 v15 v17 else T_8002da78 (m) s r v13 v15 v17
  ([Ev.node 0x8002da6c [v12, v13, v15, v17]] ++ t.1, t.2)

def T_8002da50 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v12 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v12 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002dacc (m) s r ((v12 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) ((v15 - v10)) v17 else T_8002da6c (m) s r v12 ((v12 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) ((v15 - v10)) v17
  ([Ev.node 0x8002da50 [v10, v12, v15, v17], Ev.probe 0x8002da50 (v12) (v15 - v10)] ++ t.1, t.2)

def T_8002dac8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 : BitVec 64) : Tr :=
  let t := T_8002dacc (m) s r v13 (((0#64) + sign_extend (m := 64) (0x000#12))) v17
  ([Ev.node 0x8002dac8 [v13, v17]] ++ t.1, t.2)

def T_8002d894 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 : BitVec 64) : Tr :=
  let t := T_8002d89c (m) s r v13 (((0#64) + sign_extend (m := 64) (0x001#12))) ((v17 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002d894 [v13, v17]] ++ t.1, t.2)

def T_8002d88c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left v13 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dac8 (m) s r v13 v17 else T_8002d894 (m) s r v13 v17
  ([Ev.node 0x8002d88c [v13, v17]] ++ t.1, t.2)

def T_8002dab8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left v13 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002d89c (m) s r v13 (((0#64) + sign_extend (m := 64) (0x001#12))) ((v17 + sign_extend (m := 64) (0x000#12))) else T_8002dac8 (m) s r v13 v17
  ([Ev.node 0x8002dab8 [v13, v17]] ++ t.1, t.2)

def T_8002d888 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v17 : BitVec 64) : Tr :=
  let t := T_8002d88c (m) s r ((v13 + v14)) v17
  ([Ev.node 0x8002d888 [v13, v14, v17]] ++ t.1, t.2)

def T_8002d87c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002dab8 (m) s r v13 v17 else T_8002d888 (m) s r v13 (((0#64) + sign_extend (m := 64) (0x004#12))) v17
  ([Ev.node 0x8002d87c [v13, v17]] ++ t.1, t.2)

def T_8002d854 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v12 v15 v17 : BitVec 64) : Tr :=
  let t := if ((((shift_bits_right v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0)))))) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002d88c (m) s r (((shift_bits_right v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0))))))) v17 else T_8002d87c (m) s r (((shift_bits_right v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0))))))) v17
  ([Ev.node 0x8002d854 [v10, v12, v15, v17], Ev.probe 0x8002d854 (((shift_bits_right v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v12 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0))))))) (0#64)] ++ t.1, t.2)

def T_8002d83c (m : Mem) (s : Nat) (r : BitVec 64) (v10 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8))) = true then T_8002da50 (m) s r ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0))) ((shift_bits_left (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) 5 0))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8)))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8)))) else T_8002d854 (m) s r ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0))) ((shift_bits_left (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) 5 0))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8)))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8))))
  ([Ev.node 0x8002d83c [v10]] ++ t.1, t.2)

def T_8002d820 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d83c (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat) (sdData_val v17)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat) (sdData_val v15)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val v12)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x028#12)).toNat) (sdData_val r)) s r (Lua.Vm.Sim.clz64 ((v12 + sign_extend (m := 64) (0x000#12))))
  ([Ev.node 0x8002d820 [v12, v15, v17]] ++ t.1, t.2)

def T_8002dc88 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v15 v30 : BitVec 64) : Tr :=
  let t := T_8002d820 (m) s r ((v30 - v13)) v15 ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dc88 [v11, v13, v15, v30]] ++ t.1, t.2)

def T_8002db8c (m : Mem) (s : Nat) (r : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002db8c []] ++ t.1, t.2)

def T_8002db88 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v15 v17 : BitVec 64) : Tr :=
  let t := if (v12 != (0#64)) = true then T_8002d820 (m) s r v12 v15 v17 else T_8002db8c (m) s r
  ([Ev.node 0x8002db88 [v12, v15, v17]] ++ t.1, t.2)

def T_8002db7c (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v15 v17 v30 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v13 - v30) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dc88 (m) s r v11 v13 v15 v30 else T_8002db88 (m) s r ((v13 - v30)) v15 v17
  ([Ev.node 0x8002db7c [v11, v13, v15, v17, v30]] ++ t.1, t.2)

def T_8002dd2c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v30 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r v10 ((v6 + sign_extend (m := 64) (0x000#12))) ((v11 &&& (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v30)))))
  ([Ev.node 0x8002dd2c [v6, v10, v11, v30]] ++ t.1, t.2)

def T_8002dde0 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v12 v14 v17 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r v10 (((shift_bits_right v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12)) ((v17 &&& (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v14)))))
  ([Ev.node 0x8002dde0 [v10, v12, v14, v17]] ++ t.1, t.2)

def T_8002ddf4 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v12 v14 : BitVec 64) : Tr :=
  let t := T_8002db68 (m) s r v10 (((shift_bits_right v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12)) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ddf4 [v10, v11, v12, v14]] ++ t.1, t.2)

def T_8002d9a8 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v14 v16 : BitVec 64) : Tr :=
  let t := T_8002d9c0 (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((v14 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002d9a8 [v11, v14, v16]] ++ t.1, t.2)

def T_8002d99c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v12 v13 v16 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v30 - v13) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ddf4 (m) s r v10 v11 v12 ((v30 - v13)) else T_8002d9a8 (m) s r v11 ((v30 - v13)) v16
  ([Ev.node 0x8002d99c [v10, v11, v12, v13, v16, v30]] ++ t.1, t.2)

def T_8002d988 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v12 v13 v17 v30 : BitVec 64) : Tr :=
  let t := if (((v13 - v30) &&& (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))) == (0#64)) = true then T_8002dde0 (m) s r v10 v12 ((v13 - v30)) v17 else T_8002d99c (m) s r v10 v11 v12 v13 (((0#64) + sign_extend (m := 64) (0x001#12))) v30
  ([Ev.node 0x8002d988 [v10, v11, v12, v13, v17, v30]] ++ t.1, t.2)

def T_8002d980 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v13 v14 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v30 == (0#64)) = true then T_8002db68 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v14 v29 else T_8002d988 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v11 v12 v13 v17 v30
  ([Ev.node 0x8002d980 [v11, v12, v13, v14, v17, v29, v30]] ++ t.1, t.2)

def T_8002d97c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v12 v13 v14 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v13 == (0#64)) = true then T_8002dd2c (m) s r v6 v10 v11 v30 else T_8002d980 (m) s r v11 v12 v13 v14 v17 v29 v30
  ([Ev.node 0x8002d97c [v6, v10, v11, v12, v13, v14, v17, v29, v30]] ++ t.1, t.2)

def T_8002d978 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v12 v13 v14 v15 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002d940 (m) s r else T_8002d97c (m) s r v6 v10 v11 v12 v13 v14 v17 v29 v30
  ([Ev.node 0x8002d978 [v6, v10, v11, v12, v13, v14, v15, v17, v29, v30]] ++ t.1, t.2)

def T_8002d96c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v12 v13 v14 v15 v17 v29 v30 : BitVec 64) : Tr :=
  let t := if (((v15 + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x7fe#12)) != (0#64)) = true then T_8002db7c (m) s r v11 v13 v15 v17 v30 else T_8002d978 (m) s r v6 (((v15 + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x7fe#12))) v11 v12 v13 v14 v15 v17 v29 v30
  ([Ev.node 0x8002d96c [v6, v11, v12, v13, v14, v15, v17, v29, v30]] ++ t.1, t.2)

def T_8002d8f0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002d8fc (m) s r ((v30 + sign_extend (m := 64) (0x000#12))) ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002d8f0 [v11, v28, v30]] ++ t.1, t.2)

def T_8002d818 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d820 (m) s r ((shift_bits_right (shift_bits_left v13 (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x09#6) 5 0))) v15 v17
  ([Ev.node 0x8002d818 [v13, v15, v17]] ++ t.1, t.2)

def T_8002db44 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v13 + v12)) v15 v17
  ([Ev.node 0x8002db44 [v12, v13, v15, v17]] ++ t.1, t.2)

def T_8002db38 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002d92c (m) s r v13 v15 v17 else T_8002db44 (m) s r (((0#64) + sign_extend (m := 64) (0x004#12))) v13 v15 v17
  ([Ev.node 0x8002db38 [v13, v15, v17]] ++ t.1, t.2)

def T_8002db30 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if ((v13 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002de04 (m) s r v13 v15 v17 else T_8002db38 (m) s r v13 v15 v17
  ([Ev.node 0x8002db30 [v13, v15, v17], Ev.probe 0x8002db30 (v13) (v15)] ++ t.1, t.2)

def T_8002db28 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left v13 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002d818 (m) s r v13 v15 v17 else T_8002db30 (m) s r v13 v15 v17
  ([Ev.node 0x8002db28 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dc04 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v13 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002db28 (m) s r ((v30 - ((shift_bits_right v13 (Sail.BitVec.extractLsb v10 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v13 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v10 31 0))) 5 0)))))))) ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dc04 [v10, v11, v13, v28, v30]] ++ t.1, t.2)

def T_8002d814 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d818 (m) s r (((0#64) + sign_extend (m := 64) (0xfff#12))) v15 v17
  ([Ev.node 0x8002d814 [v15, v17]] ++ t.1, t.2)

def T_8002dcf4 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v28 : BitVec 64) : Tr :=
  let t := T_8002d814 (m) s r ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dcf4 [v11, v28]] ++ t.1, t.2)

def T_8002da1c (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v14 + sign_extend (m := 64) (0x004#12))) v15 v17
  ([Ev.node 0x8002da1c [v14, v15, v17], Ev.folded 0x8002da1c (v14) (v15)] ++ t.1, t.2)

def T_8002da14 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v14 v28 : BitVec 64) : Tr :=
  let t := T_8002da1c (m) s r v14 ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002da14 [v11, v14, v28]] ++ t.1, t.2)

def T_8002da08 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v28 v30 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v30 + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002dcf4 (m) s r v11 v28 else T_8002da14 (m) s r v11 ((v30 + sign_extend (m := 64) (0xfff#12))) v28
  ([Ev.node 0x8002da08 [v11, v28, v30]] ++ t.1, t.2)

def T_8002da00 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v13 v28 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v10 = true then T_8002dc04 (m) s r v10 v11 v13 v28 v30 else T_8002da08 (m) s r v11 v28 v30
  ([Ev.node 0x8002da00 [v10, v11, v13, v28, v30]] ++ t.1, t.2)

def T_8002d9f0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v16 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002da00 (m) s r ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (0#64) 31 0) - (Sail.BitVec.extractLsb v16 31 0)))) v11 ((v13 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)))) v28 v30
  ([Ev.node 0x8002d9f0 [v11, v13, v16, v28, v30]] ++ t.1, t.2)

def T_8002d9e8 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v16 v28 v30 : BitVec 64) : Tr :=
  let t := if (v28 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d8f0 (m) s r v11 v28 v30 else T_8002d9f0 (m) s r v11 v13 v16 v28 v30
  ([Ev.node 0x8002d9e8 [v11, v13, v16, v28, v30]] ++ t.1, t.2)

def T_8002dc94 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v28 v30 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r ((v30 + sign_extend (m := 64) (0x000#12))) ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dc94 [v11, v28, v30]] ++ t.1, t.2)

def T_8002ddd4 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 : BitVec 64) : Tr :=
  let t := T_8002d818 (m) s r v13 ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ddd4 [v11, v13, v28]] ++ t.1, t.2)

def T_8002dd20 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r v13 ((v28 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002dd20 [v11, v13, v28]] ++ t.1, t.2)

def T_8002dd14 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 v30 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v30 - v13) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ddd4 (m) s r v11 ((v30 - v13)) v28 else T_8002dd20 (m) s r v11 ((v30 - v13)) v28
  ([Ev.node 0x8002dd14 [v11, v13, v28, v30]] ++ t.1, t.2)

def T_8002d8e8 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v13 v28 v30 : BitVec 64) : Tr :=
  let t := if (v28 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002da00 (m) s r v10 v11 v13 v28 v30 else T_8002d8f0 (m) s r v11 v28 v30
  ([Ev.node 0x8002d8e8 [v10, v11, v13, v28, v30]] ++ t.1, t.2)

def T_8002d8e0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v16 v28 v30 : BitVec 64) : Tr :=
  let t := if ((v16 ^^^ sign_extend (m := 64) (0xfff#12)) == (0#64)) = true then T_8002dd14 (m) s r v11 v13 v28 v30 else T_8002d8e8 (m) s r ((v16 ^^^ sign_extend (m := 64) (0xfff#12))) v11 v13 v28 v30
  ([Ev.node 0x8002d8e0 [v11, v13, v16, v28, v30]] ++ t.1, t.2)

def T_8002d8dc (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v16 v28 v30 : BitVec 64) : Tr :=
  let t := if (v13 == (0#64)) = true then T_8002dc94 (m) s r v11 v28 v30 else T_8002d8e0 (m) s r v11 v13 v16 v28 v30
  ([Ev.node 0x8002d8dc [v11, v13, v16, v28, v30]] ++ t.1, t.2)

def T_8002d8d8 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v15 v16 v28 v30 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002d9e8 (m) s r v11 v13 v16 v28 v30 else T_8002d8dc (m) s r v11 v13 v16 v28 v30
  ([Ev.node 0x8002d8d8 [v11, v13, v15, v16, v28, v30]] ++ t.1, t.2)

def T_8002d8d4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v16 == (0#64)) = true then T_8002d96c (m) s r v6 v11 v12 v13 v14 v15 v17 v29 v30 else T_8002d8d8 (m) s r v11 v13 v15 v16 v28 v30
  ([Ev.node 0x8002d8d4 [v6, v11, v12, v13, v14, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_8002dcc0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d92c (m) s r v13 v15 v17
  ([Ev.node 0x8002dcc0 [v13, v15, v17]] ++ t.1, t.2)

def T_8002dcb4 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 v30 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v13 - v30) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002d818 (m) s r ((v13 - v30)) v15 v17 else T_8002dcc0 (m) s r ((v13 - v30)) v15 v17
  ([Ev.node 0x8002dcb4 [v13, v15, v17, v30]] ++ t.1, t.2)

def T_8002db0c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := T_8002db28 (m) s r ((v13 - ((shift_bits_right v30 (Sail.BitVec.extractLsb v16 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v30 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v16 31 0))) 5 0)))))))) v15 v17
  ([Ev.node 0x8002db0c [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d808 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v13 + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002da1c (m) s r ((v13 + sign_extend (m := 64) (0xfff#12))) v15 v17 else T_8002d814 (m) s r v15 v17
  ([Ev.node 0x8002d808 [v13, v15, v17]] ++ t.1, t.2)

def T_8002d800 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v16 = true then T_8002db0c (m) s r v13 v15 v16 v17 v30 else T_8002d808 (m) s r v13 v15 v17
  ([Ev.node 0x8002d800 [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d968 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v17 : BitVec 64) : Tr :=
  let t := T_8002d8fc (m) s r v13 v15 v17
  ([Ev.node 0x8002d968 [v13, v15, v17]] ++ t.1, t.2)

def T_8002d960 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := if (v15 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d800 (m) s r v13 v15 v16 v17 v30 else T_8002d968 (m) s r v13 v15 v17
  ([Ev.node 0x8002d960 [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d958 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := if ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0xfff#12)) 31 0)) == (0#64)) = true then T_8002dcb4 (m) s r v13 v15 v17 v30 else T_8002d960 (m) s r v13 v15 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0xfff#12)) 31 0))) v17 v30
  ([Ev.node 0x8002d958 [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d954 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := if (v30 == (0#64)) = true then T_8002d92c (m) s r v13 v15 v17 else T_8002d958 (m) s r v13 v15 v16 v17 v30
  ([Ev.node 0x8002d954 [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d7f4 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := T_8002d800 (m) s r v13 v15 v16 v17 ((v30 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))))
  ([Ev.node 0x8002d7f4 [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d7ec (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v30 : BitVec 64) : Tr :=
  let t := if (v15 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002d8fc (m) s r v13 v15 v17 else T_8002d7f4 (m) s r v13 v15 v16 v17 v30
  ([Ev.node 0x8002d7ec [v13, v15, v16, v17, v30]] ++ t.1, t.2)

def T_8002d7e8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v15 v16 v17 v28 v30 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002d954 (m) s r v13 v15 v16 v17 v30 else T_8002d7ec (m) s r v13 v15 v16 v17 v30
  ([Ev.node 0x8002d7e8 [v13, v15, v16, v17, v28, v30]] ++ t.1, t.2)

def T_8002d7e4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (0#64) v16 = true then T_8002d8d4 (m) s r v6 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 else T_8002d7e8 (m) s r v13 v15 v16 v17 v28 v30
  ([Ev.node 0x8002d7e4 [v6, v11, v12, v13, v14, v15, v16, v17, v28, v29, v30]] ++ t.1, t.2)

def T_F (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0)) == (shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) = true then T_8002d904 (m) s r (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11)) ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10) (Sail.BitVec.extractLsb (0x03#6) 5 0))) (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10)) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) ((sign_extend (m := 64) ((Sail.BitVec.extractLsb ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) 31 0) - (Sail.BitVec.extractLsb ((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) 31 0)))) ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0)) + sign_extend (m := 64) (0x000#12))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (Sail.BitVec.extractLsb (0x03#6) 5 0))) else T_8002d7e4 (m) s r (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11)) ((shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10) (Sail.BitVec.extractLsb (0x03#6) 5 0))) (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10)) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) ((sign_extend (m := 64) ((Sail.BitVec.extractLsb ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) 31 0) - (Sail.BitVec.extractLsb ((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) 31 0)))) ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0)) + sign_extend (m := 64) (0x000#12))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (Sail.BitVec.extractLsb (0x03#6) 5 0)))
  ([Ev.node 0 [v10, v11]] ++ t.1, t.2)

end Adddf3T

namespace Subdf3T
open Lua.Vm.Fn.Subdf3

def T_8002ea8c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 v15 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v15 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| v14) ||| (shift_bits_left v6 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002ea8c [v6, v14, v15]] ++ t.1, t.2)

def T_8002f024 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12))) ((v13 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f024 [v13, v16]] ++ t.1, t.2)

def T_8002ef18 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x0c#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((v15 &&& sign_extend (m := 64) (0x7ff#12)))
  ([Ev.node 0x8002ef18 [v14, v15, v16]] ++ t.1, t.2)

def T_8002ea64 (m : Mem) (s : Nat) (r : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x33#6) 5 0))) (((0#64) + sign_extend (m := 64) (0x7ff#12)))
  ([Ev.node 0x8002ea64 []] ++ t.1, t.2)

def T_8002ea60 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 v15 v16 : BitVec 64) : Tr :=
  let t := if (v6 == (0#64)) = true then T_8002ef18 (m) s r v14 v15 v16 else T_8002ea64 (m) s r
  ([Ev.node 0x8002ea60 [v6, v14, v15, v16]] ++ t.1, t.2)

def T_8002ea58 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0)) == (0#64)) = true then T_8002ef18 (m) s r ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v16 else T_8002ea60 (m) s r v6 ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v16
  ([Ev.node 0x8002ea58 [v6, v15, v16, v28]] ++ t.1, t.2)

def T_8002ea50 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (v15 + sign_extend (m := 64) (0x801#12)) (sign_extend (m := 64) (0x001#12)))))) v15 v16 v28
  ([Ev.node 0x8002ea50 [v15, v16, v28], Ev.join 0x8002ea50 (v28) (v15)] ++ t.1, t.2)

def T_8002efe8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 v28
  ([Ev.node 0x8002efe8 [v13, v16, v28]] ++ t.1, t.2)

def T_8002efe4 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002efe8 (m) s r v13 v16 ((v28 + sign_extend (m := 64) (0x004#12)))
  ([Ev.node 0x8002efe4 [v13, v16, v28]] ++ t.1, t.2)

def T_8002efd8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002efe8 (m) s r v13 v16 v28 else T_8002efe4 (m) s r v13 v16 v28
  ([Ev.node 0x8002efd8 [v13, v16, v28]] ++ t.1, t.2)

def T_8002efc8 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002efe8 (m) s r v13 v16 ((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x01#6) 5 0))) else T_8002efd8 (m) s r v13 v16 ((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x01#6) 5 0)))
  ([Ev.node 0x8002efc8 [v13, v16, v28, v29], Ev.probe 0x8002efc8 ((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x01#6) 5 0))) (v13)] ++ t.1, t.2)

def T_8002efc0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002f024 (m) s r v13 v16 else T_8002efc8 (m) s r v13 v16 v28 v29
  ([Ev.node 0x8002efc0 [v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002f070 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r v6 (((0#64) + sign_extend (m := 64) (0x7ff#12))) v16 ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f070 [v6, v16, v29]] ++ t.1, t.2)

def T_8002f06c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 != (0#64)) = true then T_8002ea64 (m) s r else T_8002f070 (m) s r v6 v16 v29
  ([Ev.node 0x8002f06c [v6, v16, v28, v29]] ++ t.1, t.2)

def T_8002f014 (m : Mem) (s : Nat) (r : BitVec 64) (v16 v17 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((v17 + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f014 [v16, v17]] ++ t.1, t.2)

def T_8002ee4c (m : Mem) (s : Nat) (r : BitVec 64) (v14 v16 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) v14 (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ee4c [v14, v16]] ++ t.1, t.2)

def T_8002eef8 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r v6 v14 (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002eef8 [v6, v14]] ++ t.1, t.2)

def T_8002efb8 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r v6 v14 (((0#64) + sign_extend (m := 64) (0x001#12)))
  ([Ev.node 0x8002efb8 [v6, v14]] ++ t.1, t.2)

def T_8002efa0 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v28 + v29) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002eef8 (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) (((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12)) else T_8002efb8 (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) (((shift_bits_right (v28 + v29) (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12))
  ([Ev.node 0x8002efa0 [v12, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef9c (m : Mem) (s : Nat) (r : BitVec 64) (v12 v14 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v29 == (0#64)) = true then T_8002ee4c (m) s r v14 v16 else T_8002efa0 (m) s r v12 v16 v28 v29
  ([Ev.node 0x8002ef9c [v12, v14, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef98 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v14 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002f014 (m) s r v16 v17 else T_8002ef9c (m) s r v12 v14 v16 v28 v29
  ([Ev.node 0x8002ef98 [v12, v14, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ef94 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002f06c (m) s r v6 v16 v28 v29 else T_8002ef98 (m) s r v12 v14 v16 v17 v28 v29
  ([Ev.node 0x8002ef94 [v6, v12, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ef88 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v12 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (((v15 + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x7fe#12)) != (0#64)) = true then T_8002efc0 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 v28 v29 else T_8002ef94 (m) s r v6 v12 v14 v15 v16 v17 v28 v29
  ([Ev.node 0x8002ef88 [v6, v12, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002f07c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v13 v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r v6 ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f07c [v6, v13, v16, v29]] ++ t.1, t.2)

def T_8002ef14 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ef18 (m) s r ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v16
  ([Ev.node 0x8002ef14 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ee40 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) (((0#64) + sign_extend (m := 64) (0x000#12))) v15
  ([Ev.node 0x8002ee40 [v15, v16]] ++ t.1, t.2)

def T_8002edf8 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) v15
  ([Ev.node 0x8002edf8 [v14, v15, v16]] ++ t.1, t.2)

def T_8002eec4 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002edf8 (m) s r ((v28 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) ((v15 &&& sign_extend (m := 64) (0x7ff#12))) v16
  ([Ev.node 0x8002eec4 [v15, v16, v28]] ++ t.1, t.2)

def T_8002eeb8 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ee40 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 else T_8002eec4 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 v28
  ([Ev.node 0x8002eeb8 [v15, v16, v28]] ++ t.1, t.2)

def T_8002eeac (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v28 + sign_extend (m := 64) (0x004#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ea50 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x004#12))) else T_8002eeb8 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x004#12)))
  ([Ev.node 0x8002eeac [v15, v16, v28]] ++ t.1, t.2)

def T_8002eea0 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002ea50 (m) s r v15 v16 v28 else T_8002eeac (m) s r v15 v16 v28
  ([Ev.node 0x8002eea0 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ee98 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002ef14 (m) s r v15 v16 v28 else T_8002eea0 (m) s r v15 v16 v28
  ([Ev.node 0x8002ee98 [v15, v16, v28], Ev.probe 0x8002ee98 (v28) (v15)] ++ t.1, t.2)

def T_8002ecf0 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x004#12)))
  ([Ev.node 0x8002ecf0 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ece4 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002ea50 (m) s r v15 v16 v28 else T_8002ecf0 (m) s r v15 v16 v28
  ([Ev.node 0x8002ece4 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ed70 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 v28
  ([Ev.node 0x8002ed70 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ed4c (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if (((((shift_bits_right v28 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v28 &&& sign_extend (m := 64) (0x001#12))) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true then T_8002ece4 (m) s r v15 v16 ((((shift_bits_right v28 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v28 &&& sign_extend (m := 64) (0x001#12)))) else T_8002ed70 (m) s r v15 v16 ((((shift_bits_right v28 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v28 &&& sign_extend (m := 64) (0x001#12))))
  ([Ev.node 0x8002ed4c [v15, v16, v28], Ev.probe 0x8002ed4c ((((shift_bits_right v28 (Sail.BitVec.extractLsb (0x01#6) 5 0)) &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x1ff#12)) (Sail.BitVec.extractLsb (0x36#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) ||| (v28 &&& sign_extend (m := 64) (0x001#12)))) (v15)] ++ t.1, t.2)

def T_8002ed40 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ee40 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 else T_8002ed4c (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 v28
  ([Ev.node 0x8002ed40 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ed38 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left v28 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ee98 (m) s r v15 v16 v28 else T_8002ed40 (m) s r v15 v16 v28
  ([Ev.node 0x8002ed38 [v15, v16, v28]] ++ t.1, t.2)

def T_8002eff0 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ed38 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((((shift_bits_right v28 (Sail.BitVec.extractLsb v14 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v28 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v14 31 0))) 5 0)))))) + v29))
  ([Ev.node 0x8002eff0 [v13, v14, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef7c (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((v29 + sign_extend (m := 64) (0x005#12)))
  ([Ev.node 0x8002ef7c [v13, v16, v29], Ev.folded 0x8002ef7c (v29 + 1) (v13)] ++ t.1, t.2)

def T_8002ef74 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v14 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v14 = true then T_8002eff0 (m) s r v13 v14 v16 v28 v29 else T_8002ef7c (m) s r v13 v16 v29
  ([Ev.node 0x8002ef74 [v13, v14, v16, v28, v29]] ++ t.1, t.2)

def T_8002f09c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ef74 (m) s r v13 ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (0#64) 31 0) - (Sail.BitVec.extractLsb v10 31 0)))) v16 ((v28 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)))) v29
  ([Ev.node 0x8002f09c [v10, v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002f094 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002f07c (m) s r v6 v13 v16 v29 else T_8002f09c (m) s r v10 v13 v16 v28 v29
  ([Ev.node 0x8002f094 [v6, v10, v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002f088 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f088 [v13, v16, v29]] ++ t.1, t.2)

def T_8002f044 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 v28
  ([Ev.node 0x8002f044 [v15, v16, v28]] ++ t.1, t.2)

def T_8002f034 (m : Mem) (s : Nat) (r : BitVec 64) (v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v28 + v29) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ed40 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((v28 + v29)) else T_8002f044 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) v16 ((v28 + v29))
  ([Ev.node 0x8002f034 [v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef6c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v13 v14 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002f07c (m) s r v6 v13 v16 v29 else T_8002ef74 (m) s r v13 v14 v16 v28 v29
  ([Ev.node 0x8002ef6c [v6, v13, v14, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef64 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if ((v10 ^^^ sign_extend (m := 64) (0xfff#12)) == (0#64)) = true then T_8002f034 (m) s r v13 v16 v28 v29 else T_8002ef6c (m) s r v6 v13 ((v10 ^^^ sign_extend (m := 64) (0xfff#12))) v16 v28 v29
  ([Ev.node 0x8002ef64 [v6, v10, v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef60 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002f088 (m) s r v13 v16 v29 else T_8002ef64 (m) s r v6 v10 v13 v16 v28 v29
  ([Ev.node 0x8002ef60 [v6, v10, v13, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef5c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002f094 (m) s r v6 v10 v13 v16 v28 v29 else T_8002ef60 (m) s r v6 v10 v13 v16 v28 v29
  ([Ev.node 0x8002ef5c [v6, v10, v13, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ef58 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v12 v13 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v10 == (0#64)) = true then T_8002ef88 (m) s r v6 v12 v14 v15 v16 v17 v28 v29 else T_8002ef5c (m) s r v6 v10 v13 v15 v16 v28 v29
  ([Ev.node 0x8002ef58 [v6, v10, v12, v13, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ed1c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ed38 (m) s r v15 v16 ((v28 + ((shift_bits_right v29 (Sail.BitVec.extractLsb v10 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v29 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v10 31 0))) 5 0))))))))
  ([Ev.node 0x8002ed1c [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ed14 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x005#12)))
  ([Ev.node 0x8002ed14 [v15, v16, v28], Ev.folded 0x8002ed14 (v28 + 1) (v15)] ++ t.1, t.2)

def T_8002ed0c (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v10 = true then T_8002ed1c (m) s r v10 v15 v16 v28 v29 else T_8002ed14 (m) s r v15 v16 v28
  ([Ev.node 0x8002ed0c [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ed00 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ed0c (m) s r v10 v15 v16 v28 ((v29 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))))
  ([Ev.node 0x8002ed00 [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ecf8 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ea58 (m) s r v6 v15 v16 v28 else T_8002ed00 (m) s r v10 v15 v16 v28 v29
  ([Ev.node 0x8002ecf8 [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ed88 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 v28
  ([Ev.node 0x8002ed88 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ed7c (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v28 + v29) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ed40 (m) s r v15 v16 ((v28 + v29)) else T_8002ed88 (m) s r v15 v16 ((v28 + v29))
  ([Ev.node 0x8002ed7c [v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eabc (m : Mem) (s : Nat) (r : BitVec 64) (v6 v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r v6 v15 v16 v28
  ([Ev.node 0x8002eabc [v6, v15, v16, v28]] ++ t.1, t.2)

def T_8002eab4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ed0c (m) s r v10 v15 v16 v28 v29 else T_8002eabc (m) s r v6 v15 v16 v28
  ([Ev.node 0x8002eab4 [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eaac (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xfff#12)) 31 0)) == (0#64)) = true then T_8002ed7c (m) s r v15 v16 v28 v29 else T_8002eab4 (m) s r v6 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xfff#12)) 31 0))) v15 v16 v28 v29
  ([Ev.node 0x8002eaac [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eaa8 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v29 == (0#64)) = true then T_8002ea50 (m) s r v15 v16 v28 else T_8002eaac (m) s r v6 v10 v15 v16 v28 v29
  ([Ev.node 0x8002eaa8 [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eaa4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 != (0#64)) = true then T_8002ecf8 (m) s r v6 v10 v15 v16 v28 v29 else T_8002eaa8 (m) s r v6 v10 v15 v16 v28 v29
  ([Ev.node 0x8002eaa4 [v6, v10, v13, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eaa0 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v12 v13 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (0#64) v10 = true then T_8002ef58 (m) s r v6 v10 v12 v13 v14 v15 v16 v17 v28 v29 else T_8002eaa4 (m) s r v6 v10 v13 v15 v16 v28 v29
  ([Ev.node 0x8002eaa0 [v6, v10, v12, v13, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ee70 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v15 v17 v29 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v11 &&& (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v29))))) ((v17 + sign_extend (m := 64) (0x000#12))) v15
  ([Ev.node 0x8002ee70 [v11, v15, v17, v29]] ++ t.1, t.2)

def T_8002eee8 (m : Mem) (s : Nat) (r : BitVec 64) (v12 v14 v16 : BitVec 64) : Tr :=
  let t := T_8002eef8 (m) s r ((v16 &&& (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) v14))))) (((shift_bits_right v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)) &&& v12))
  ([Ev.node 0x8002eee8 [v12, v14, v16]] ++ t.1, t.2)

def T_8002ef00 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v14 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r ((v11 + sign_extend (m := 64) (0x000#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ef00 [v11, v14]] ++ t.1, t.2)

def T_8002ede0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v14 : BitVec 64) : Tr :=
  let t := T_8002edf8 (m) s r ((v14 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) (((0#64) + sign_extend (m := 64) (0x001#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ede0 [v11, v14]] ++ t.1, t.2)

def T_8002edd4 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v29 - v28) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ef00 (m) s r v11 ((v29 - v28)) else T_8002ede0 (m) s r v11 ((v29 - v28))
  ([Ev.node 0x8002edd4 [v11, v28, v29]] ++ t.1, t.2)

def T_8002edc0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (((v28 - v29) &&& (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))) == (0#64)) = true then T_8002eee8 (m) s r v12 ((v28 - v29)) v16 else T_8002edd4 (m) s r v11 v28 v29
  ([Ev.node 0x8002edc0 [v11, v12, v16, v28, v29]] ++ t.1, t.2)

def T_8002edbc (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v29 == (0#64)) = true then T_8002ee4c (m) s r v14 v16 else T_8002edc0 (m) s r v11 v12 v16 v28 v29
  ([Ev.node 0x8002edbc [v11, v12, v14, v16, v28, v29]] ++ t.1, t.2)

def T_8002edb8 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002ee70 (m) s r v11 v15 v17 v29 else T_8002edbc (m) s r v11 v12 v14 v16 v28 v29
  ([Ev.node 0x8002edb8 [v11, v12, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002edb4 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002ea64 (m) s r else T_8002edb8 (m) s r v11 v12 v14 v15 v16 v17 v28 v29
  ([Ev.node 0x8002edb4 [v11, v12, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002eb90 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 v15 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v15 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| v14) ||| (shift_bits_left v6 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002eb90 [v6, v14, v15]] ++ t.1, t.2)

def T_8002f048 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 : BitVec 64) : Tr :=
  let t := T_8002eb90 (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((shift_bits_right (shift_bits_left v14 (Sail.BitVec.extractLsb (0x0c#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((v15 &&& sign_extend (m := 64) (0x7ff#12)))
  ([Ev.node 0x8002f048 [v14, v15, v16]] ++ t.1, t.2)

def T_8002ec8c (m : Mem) (s : Nat) (r : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left ((0#64) + sign_extend (m := 64) (0x7ff#12)) (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x33#6) 5 0))) ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x000#12)) (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002ec8c []] ++ t.1, t.2)

def T_8002ec88 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 v15 v16 : BitVec 64) : Tr :=
  let t := if (v6 == (0#64)) = true then T_8002f048 (m) s r v14 v15 v16 else T_8002ec8c (m) s r
  ([Ev.node 0x8002ec88 [v6, v14, v15, v16]] ++ t.1, t.2)

def T_8002ec78 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0)) == (0#64)) = true then T_8002f048 (m) s r ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v16 else T_8002ec88 (m) s r ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (v15 + sign_extend (m := 64) (0x801#12)) (sign_extend (m := 64) (0x001#12)))))) ((shift_bits_right v28 (Sail.BitVec.extractLsb (0x03#6) 5 0))) v15 v16
  ([Ev.node 0x8002ec78 [v15, v16, v28]] ++ t.1, t.2)

def T_8002eb70 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002eb90 (m) s r ((v16 + sign_extend (m := 64) (0x000#12))) ((shift_bits_right (shift_bits_left (v28 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12))) (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) ((v15 &&& sign_extend (m := 64) (0x7ff#12)))
  ([Ev.node 0x8002eb70 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ec40 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 : BitVec 64) : Tr :=
  let t := ([], (((shift_bits_left v15 (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| ((0#64) + sign_extend (m := 64) (0x000#12))) ||| (shift_bits_left (v16 + sign_extend (m := 64) (0x000#12)) (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
  ([Ev.node 0x8002ec40 [v15, v16]] ++ t.1, t.2)

def T_8002ec34 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v15 + sign_extend (m := 64) (0x001#12)) != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002eb70 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16 v28 else T_8002ec40 (m) s r ((v15 + sign_extend (m := 64) (0x001#12))) v16
  ([Ev.node 0x8002ec34 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ec28 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v28 + sign_extend (m := 64) (0x004#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ec78 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x004#12))) else T_8002ec34 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0x004#12)))
  ([Ev.node 0x8002ec28 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ec1c (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v14 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002ec78 (m) s r v15 v16 v28 else T_8002ec28 (m) s r v15 v16 v28
  ([Ev.node 0x8002ec1c [v14, v15, v16, v28]] ++ t.1, t.2)

def T_8002ec00 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v15 v16 : BitVec 64) : Tr :=
  let t := if ((v14 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002ec78 (m) s r ((v15 - v10)) v16 ((v14 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12)))) else T_8002ec1c (m) s r v14 ((v15 - v10)) v16 ((v14 &&& ((shift_bits_left ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)) + sign_extend (m := 64) (0xfff#12))))
  ([Ev.node 0x8002ec00 [v10, v14, v15, v16], Ev.probe 0x8002ec00 (v14) (v15 - v10)] ++ t.1, t.2)

def T_8002ec74 (m : Mem) (s : Nat) (r : BitVec 64) (v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ec78 (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v16 v28
  ([Ev.node 0x8002ec74 [v16, v28]] ++ t.1, t.2)

def T_8002ec64 (m : Mem) (s : Nat) (r : BitVec 64) (v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))) != (0#64)) = true then T_8002eb70 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) v16 v28 else T_8002ec74 (m) s r v16 v28
  ([Ev.node 0x8002ec64 [v16, v28]] ++ t.1, t.2)

def T_8002eb5c (m : Mem) (s : Nat) (r : BitVec 64) (v14 v16 v28 : BitVec 64) : Tr :=
  let t := if (((v28 + v14) &&& (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))) == (0#64)) = true then T_8002ec74 (m) s r v16 ((v28 + v14)) else T_8002eb70 (m) s r (((0#64) + sign_extend (m := 64) (0x001#12))) v16 ((v28 + v14))
  ([Ev.node 0x8002eb5c [v14, v16, v28]] ++ t.1, t.2)

def T_8002eb50 (m : Mem) (s : Nat) (r : BitVec 64) (v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x00f#12)) == ((0#64) + sign_extend (m := 64) (0x004#12))) = true then T_8002ec64 (m) s r v16 v28 else T_8002eb5c (m) s r (((0#64) + sign_extend (m := 64) (0x004#12))) v16 v28
  ([Ev.node 0x8002eb50 [v16, v28]] ++ t.1, t.2)

def T_8002eb28 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v14 v15 v16 : BitVec 64) : Tr :=
  let t := if ((((shift_bits_right v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0)))))) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002ec64 (m) s r v16 (((shift_bits_right v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0))))))) else T_8002eb50 (m) s r v16 (((shift_bits_right v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0)))))))
  ([Ev.node 0x8002eb28 [v10, v14, v15, v16], Ev.probe 0x8002eb28 (((shift_bits_right v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v14 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v10 31 0) - (Sail.BitVec.extractLsb v15 31 0))) + sign_extend (m := 64) (0x001#12)) 31 0)) 31 0))) 5 0))))))) (0#64)] ++ t.1, t.2)

def T_8002eb10 (m : Mem) (s : Nat) (r : BitVec 64) (v10 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8))) = true then T_8002ec00 (m) s r ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0))) ((shift_bits_left (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) 5 0))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8)))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8)))) else T_8002eb28 (m) s r ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0))) ((shift_bits_left (sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8))) (Sail.BitVec.extractLsb (sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xff8#12)) 31 0)) 5 0))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8)))) ((sign_extend (m := 64) (bytesT8 (m) ((BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat : BitVec (8 * 8))))
  ([Ev.node 0x8002eb10 [v10]] ++ t.1, t.2)

def T_8002eaf4 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 : BitVec 64) : Tr :=
  let t := T_8002eb10 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (m) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x018#12)).toNat) (sdData_val v16)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x010#12)).toNat) (sdData_val v15)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x008#12)).toNat) (sdData_val v14)) ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) + sign_extend (m := 64) (0x028#12)).toNat) (sdData_val r)) s r (Lua.Vm.Sim.clz64 ((v14 + sign_extend (m := 64) (0x000#12))))
  ([Ev.node 0x8002eaf4 [v14, v15, v16]] ++ t.1, t.2)

def T_8002ee58 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v15 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002eaf4 (m) s r ((v29 - v28)) v15 ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ee58 [v11, v15, v28, v29]] ++ t.1, t.2)

def T_8002eda8 (m : Mem) (s : Nat) (r : BitVec 64) (v14 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r (((0#64) + sign_extend (m := 64) (0x000#12))) v14 (((0#64) + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002eda8 [v14]] ++ t.1, t.2)

def T_8002eda4 (m : Mem) (s : Nat) (r : BitVec 64) (v14 v15 v16 : BitVec 64) : Tr :=
  let t := if (v14 != (0#64)) = true then T_8002eaf4 (m) s r v14 v15 v16 else T_8002eda8 (m) s r v14
  ([Ev.node 0x8002eda4 [v14, v15, v16]] ++ t.1, t.2)

def T_8002ed98 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v28 - v29) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ee58 (m) s r v11 v15 v28 v29 else T_8002eda4 (m) s r ((v28 - v29)) v15 v16
  ([Ev.node 0x8002ed98 [v11, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ed8c (m : Mem) (s : Nat) (r : BitVec 64) (v11 v12 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (((v15 + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x7fe#12)) == (0#64)) = true then T_8002edb4 (m) s r v11 v12 v14 v15 v16 v17 v28 v29 else T_8002ed98 (m) s r v11 v15 v16 v28 v29
  ([Ev.node 0x8002ed8c [v11, v12, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ef48 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v13 v29 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r v6 ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ef48 [v6, v11, v13, v29]] ++ t.1, t.2)

def T_8002eaec (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002eaf4 (m) s r ((shift_bits_right (shift_bits_left v28 (Sail.BitVec.extractLsb (0x09#6) 5 0)) (Sail.BitVec.extractLsb (0x09#6) 5 0))) v15 v16
  ([Ev.node 0x8002eaec [v15, v16, v28]] ++ t.1, t.2)

def T_8002ecdc (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if ((v28 &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = true then T_8002ef14 (m) s r v15 v16 v28 else T_8002ece4 (m) s r v15 v16 v28
  ([Ev.node 0x8002ecdc [v15, v16, v28], Ev.probe 0x8002ecdc (v28) (v15)] ++ t.1, t.2)

def T_8002ecd4 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left v28 (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002eaec (m) s r v15 v16 v28 else T_8002ecdc (m) s r v15 v16 v28
  ([Ev.node 0x8002ecd4 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ee18 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 v29 v30 : BitVec 64) : Tr :=
  let t := T_8002ecd4 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) ((v29 - ((shift_bits_right v28 (Sail.BitVec.extractLsb v30 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v28 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v30 31 0))) 5 0))))))))
  ([Ev.node 0x8002ee18 [v11, v13, v28, v29, v30]] ++ t.1, t.2)

def T_8002eae8 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 : BitVec 64) : Tr :=
  let t := T_8002eaec (m) s r v15 v16 (((0#64) + sign_extend (m := 64) (0xfff#12)))
  ([Ev.node 0x8002eae8 [v15, v16]] ++ t.1, t.2)

def T_8002ee64 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 : BitVec 64) : Tr :=
  let t := T_8002eae8 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ee64 [v11, v13]] ++ t.1, t.2)

def T_8002ebe4 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 ((v29 + sign_extend (m := 64) (0x004#12)))
  ([Ev.node 0x8002ebe4 [v15, v16, v29], Ev.folded 0x8002ebe4 (v29) (v15)] ++ t.1, t.2)

def T_8002ebdc (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v29 : BitVec 64) : Tr :=
  let t := T_8002ebe4 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) v29
  ([Ev.node 0x8002ebdc [v11, v13, v29]] ++ t.1, t.2)

def T_8002ebd0 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v29 + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ee64 (m) s r v11 v13 else T_8002ebdc (m) s r v11 v13 ((v29 + sign_extend (m := 64) (0xfff#12)))
  ([Ev.node 0x8002ebd0 [v11, v13, v29]] ++ t.1, t.2)

def T_8002ebc8 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v30 = true then T_8002ee18 (m) s r v11 v13 v28 v29 v30 else T_8002ebd0 (m) s r v11 v13 v29
  ([Ev.node 0x8002ebc8 [v11, v13, v28, v29, v30]] ++ t.1, t.2)

def T_8002ef34 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 v13 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ebc8 (m) s r v11 v13 ((v28 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0)))) v29 ((sign_extend (m := 64) ((Sail.BitVec.extractLsb (0#64) 31 0) - (Sail.BitVec.extractLsb v10 31 0))))
  ([Ev.node 0x8002ef34 [v10, v11, v13, v28, v29]] ++ t.1, t.2)

def T_8002ef2c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v13 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ef48 (m) s r v6 v11 v13 v29 else T_8002ef34 (m) s r v10 v11 v13 v28 v29
  ([Ev.node 0x8002ef2c [v6, v10, v11, v13, v28, v29]] ++ t.1, t.2)

def T_8002f05c (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v29 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002f05c [v11, v13, v29]] ++ t.1, t.2)

def T_8002eedc (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 : BitVec 64) : Tr :=
  let t := T_8002eaec (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) v28
  ([Ev.node 0x8002eedc [v11, v13, v28]] ++ t.1, t.2)

def T_8002ee8c (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r ((v13 + sign_extend (m := 64) (0x000#12))) ((v11 + sign_extend (m := 64) (0x000#12))) v28
  ([Ev.node 0x8002ee8c [v11, v13, v28]] ++ t.1, t.2)

def T_8002ee80 (m : Mem) (s : Nat) (r : BitVec 64) (v11 v13 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v29 - v28) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002eedc (m) s r v11 v13 ((v29 - v28)) else T_8002ee8c (m) s r v11 v13 ((v29 - v28))
  ([Ev.node 0x8002ee80 [v11, v13, v28, v29]] ++ t.1, t.2)

def T_8002ebc0 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v13 v28 v29 v30 : BitVec 64) : Tr :=
  let t := if (v13 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ef48 (m) s r v6 v11 v13 v29 else T_8002ebc8 (m) s r v11 v13 v28 v29 v30
  ([Ev.node 0x8002ebc0 [v6, v11, v13, v28, v29, v30]] ++ t.1, t.2)

def T_8002ebb8 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v13 v28 v29 : BitVec 64) : Tr :=
  let t := if ((v10 ^^^ sign_extend (m := 64) (0xfff#12)) == (0#64)) = true then T_8002ee80 (m) s r v11 v13 v28 v29 else T_8002ebc0 (m) s r v6 v11 v13 v28 v29 ((v10 ^^^ sign_extend (m := 64) (0xfff#12)))
  ([Ev.node 0x8002ebb8 [v6, v10, v11, v13, v28, v29]] ++ t.1, t.2)

def T_8002ebb4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v13 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002f05c (m) s r v11 v13 v29 else T_8002ebb8 (m) s r v6 v10 v11 v13 v28 v29
  ([Ev.node 0x8002ebb4 [v6, v10, v11, v13, v28, v29]] ++ t.1, t.2)

def T_8002ebb0 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v13 v15 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002ef2c (m) s r v6 v10 v11 v13 v28 v29 else T_8002ebb4 (m) s r v6 v10 v11 v13 v28 v29
  ([Ev.node 0x8002ebb0 [v6, v10, v11, v13, v15, v28, v29]] ++ t.1, t.2)

def T_8002ebac (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v10 == (0#64)) = true then T_8002ed8c (m) s r v11 v12 v14 v15 v16 v17 v28 v29 else T_8002ebb0 (m) s r v6 v10 v11 v13 v15 v28 v29
  ([Ev.node 0x8002ebac [v6, v10, v11, v12, v13, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ecb8 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ecd4 (m) s r v15 v16 ((v28 - ((shift_bits_right v29 (Sail.BitVec.extractLsb v10 5 0)) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (shift_bits_left v29 (Sail.BitVec.extractLsb (sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) - (Sail.BitVec.extractLsb v10 31 0))) 5 0))))))))
  ([Ev.node 0x8002ecb8 [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eadc (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (shift_bits_left (v28 + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002ebe4 (m) s r v15 v16 ((v28 + sign_extend (m := 64) (0xfff#12))) else T_8002eae8 (m) s r v15 v16
  ([Ev.node 0x8002eadc [v15, v16, v28]] ++ t.1, t.2)

def T_8002ead4 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s ((0#64) + sign_extend (m := 64) (0x038#12)) v10 = true then T_8002ecb8 (m) s r v10 v15 v16 v28 v29 else T_8002eadc (m) s r v15 v16 v28
  ([Ev.node 0x8002ead4 [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eac8 (m : Mem) (s : Nat) (r : BitVec 64) (v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := T_8002ead4 (m) s r v10 v15 v16 v28 ((v29 ||| (shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x37#6) 5 0))))
  ([Ev.node 0x8002eac8 [v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002eac0 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 == ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ea58 (m) s r v6 v15 v16 v28 else T_8002eac8 (m) s r v10 v15 v16 v28 v29
  ([Ev.node 0x8002eac0 [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ee14 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r v15 v16 v28
  ([Ev.node 0x8002ee14 [v15, v16, v28]] ++ t.1, t.2)

def T_8002ee08 (m : Mem) (s : Nat) (r : BitVec 64) (v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zI_s (shift_bits_left (v28 - v29) (Sail.BitVec.extractLsb (0x08#6) 5 0)) (0#64) = true then T_8002eaec (m) s r v15 v16 ((v28 - v29)) else T_8002ee14 (m) s r v15 v16 ((v28 - v29))
  ([Ev.node 0x8002ee08 [v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ebfc (m : Mem) (s : Nat) (r : BitVec 64) (v6 v15 v16 v28 : BitVec 64) : Tr :=
  let t := T_8002ea58 (m) s r v6 v15 v16 v28
  ([Ev.node 0x8002ebfc [v6, v15, v16, v28]] ++ t.1, t.2)

def T_8002ebf4 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != ((0#64) + sign_extend (m := 64) (0x7ff#12))) = true then T_8002ead4 (m) s r v10 v15 v16 v28 v29 else T_8002ebfc (m) s r v6 v15 v16 v28
  ([Ev.node 0x8002ebf4 [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ebec (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xfff#12)) 31 0)) == (0#64)) = true then T_8002ee08 (m) s r v15 v16 v28 v29 else T_8002ebf4 (m) s r v6 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v10 + sign_extend (m := 64) (0xfff#12)) 31 0))) v15 v16 v28 v29
  ([Ev.node 0x8002ebec [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea4c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v29 != (0#64)) = true then T_8002ebec (m) s r v6 v10 v15 v16 v28 v29 else T_8002ea50 (m) s r v15 v16 v28
  ([Ev.node 0x8002ea4c [v6, v10, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea48 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v13 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v13 != (0#64)) = true then T_8002eac0 (m) s r v6 v10 v15 v16 v28 v29 else T_8002ea4c (m) s r v6 v10 v15 v16 v28 v29
  ([Ev.node 0x8002ea48 [v6, v10, v13, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea44 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if zopz0zKzJ_s (0#64) v10 = true then T_8002ebac (m) s r v6 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 else T_8002ea48 (m) s r v6 v10 v13 v15 v16 v28 v29
  ([Ev.node 0x8002ea44 [v6, v10, v11, v12, v13, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ea38 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v12 v13 v14 v15 v16 v17 v28 v29 : BitVec 64) : Tr :=
  let t := if (v16 == (v11 ^^^ sign_extend (m := 64) (0x001#12))) = true then T_8002eaa0 (m) s r v6 ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v15 31 0) - (Sail.BitVec.extractLsb v13 31 0)))) v12 v13 v14 v15 v16 v17 v28 v29 else T_8002ea44 (m) s r v6 ((sign_extend (m := 64) ((Sail.BitVec.extractLsb v15 31 0) - (Sail.BitVec.extractLsb v13 31 0)))) ((v11 ^^^ sign_extend (m := 64) (0x001#12))) v12 v13 v14 v15 v16 v17 v28 v29
  ([Ev.node 0x8002ea38 [v6, v11, v12, v13, v14, v15, v16, v17, v28, v29]] ++ t.1, t.2)

def T_8002ea80 (m : Mem) (s : Nat) (r : BitVec 64) (v6 : BitVec 64) : Tr :=
  let t := T_8002ea8c (m) s r v6 ((shift_bits_left ((0#64) + sign_extend (m := 64) (0x001#12)) (Sail.BitVec.extractLsb (0x33#6) 5 0))) (((0#64) + sign_extend (m := 64) (0x7ff#12)))
  ([Ev.node 0x8002ea80 [v6]] ++ t.1, t.2)

def T_8002ea2c (m : Mem) (s : Nat) (r : BitVec 64) (v16 v29 : BitVec 64) : Tr :=
  let t := T_8002ea50 (m) s r (((0#64) + sign_extend (m := 64) (0x7ff#12))) v16 ((v29 + sign_extend (m := 64) (0x000#12)))
  ([Ev.node 0x8002ea2c [v16, v29]] ++ t.1, t.2)

def T_8002ed78 (m : Mem) (s : Nat) (r : BitVec 64) (v6 : BitVec 64) : Tr :=
  let t := T_8002ea80 (m) s r v6
  ([Ev.node 0x8002ed78 [v6]] ++ t.1, t.2)

def T_8002ed74 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 == (0#64)) = true then T_8002ea2c (m) s r v16 v29 else T_8002ed78 (m) s r v6
  ([Ev.node 0x8002ed74 [v6, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea7c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 == (0#64)) = true then T_8002ed74 (m) s r v6 v16 v28 v29 else T_8002ea80 (m) s r v6
  ([Ev.node 0x8002ea7c [v6, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea78 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v14 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v14 == (0#64)) = true then T_8002ea80 (m) s r v6 else T_8002ea7c (m) s r v6 v15 v16 v28 v29
  ([Ev.node 0x8002ea78 [v6, v14, v15, v16, v28, v29]] ++ t.1, t.2)

def T_8002ea24 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v28 v29 : BitVec 64) : Tr :=
  let t := if (v28 != (0#64)) = true then T_8002ea80 (m) s r v6 else T_8002ea2c (m) s r ((v11 + sign_extend (m := 64) (0x000#12))) v29
  ([Ev.node 0x8002ea24 [v6, v11, v28, v29]] ++ t.1, t.2)

def T_8002ea20 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v15 v28 v29 : BitVec 64) : Tr :=
  let t := if (v15 != (0#64)) = true then T_8002ea80 (m) s r v6 else T_8002ea24 (m) s r v6 v11 v28 v29
  ([Ev.node 0x8002ea20 [v6, v11, v15, v28, v29]] ++ t.1, t.2)

def T_8002ea1c (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v14 v15 v28 v29 : BitVec 64) : Tr :=
  let t := if (v14 == (0#64)) = true then T_8002ea80 (m) s r v6 else T_8002ea20 (m) s r v6 v11 v15 v28 v29
  ([Ev.node 0x8002ea1c [v6, v11, v14, v15, v28, v29]] ++ t.1, t.2)

def T_8002ea14 (m : Mem) (s : Nat) (r : BitVec 64) (v6 v11 v15 v16 v28 v29 : BitVec 64) : Tr :=
  let t := if (v16 == v11) = true then T_8002ea78 (m) s r v6 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v15 + sign_extend (m := 64) (0x801#12)) 31 0))) v15 v16 v28 v29 else T_8002ea1c (m) s r v6 v11 ((sign_extend (m := 64) (Sail.BitVec.extractLsb (v15 + sign_extend (m := 64) (0x801#12)) 31 0))) v15 v28 v29
  ([Ev.node 0x8002ea14 [v6, v11, v15, v16, v28, v29]] ++ t.1, t.2)

def T_F (m : Mem) (s : Nat) (r : BitVec 64) (v10 v11 : BitVec 64) : Tr :=
  let t := if (((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) + sign_extend (m := 64) (0x801#12))))) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (sign_extend (m := 64) (0x001#12)))))) != (0#64)) = true then T_8002ea38 (m) s r (((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) + sign_extend (m := 64) (0x801#12))))) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (sign_extend (m := 64) (0x001#12))))))) ((shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10)) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) (((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11)) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10) (Sail.BitVec.extractLsb (0x03#6) 5 0))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (Sail.BitVec.extractLsb (0x03#6) 5 0))) else T_8002ea14 (m) s r (((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (((shift_bits_right v11 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12)) + sign_extend (m := 64) (0x801#12))))) ||| (zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (sign_extend (m := 64) (0x001#12))))))) ((shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) (((shift_bits_right v10 (Sail.BitVec.extractLsb (0x34#6) 5 0)) &&& sign_extend (m := 64) (0x7ff#12))) ((shift_bits_right v10 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v10) (Sail.BitVec.extractLsb (0x03#6) 5 0))) ((shift_bits_left ((shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) &&& v11) (Sail.BitVec.extractLsb (0x03#6) 5 0)))
  ([Ev.node 0 [v10, v11]] ++ t.1, t.2)

end Subdf3T
-- END rto_trace.py

/-! ## Vectors

`SpecTest`'s 2,900 pairs (copied: `SpecTest` is not a module), plus edge
vectors: exponent differences, cancellation, subnormal results, ties. Every
edge pair is also run with `b`'s sign flipped (so `__subdf3` cancels too). -/

def edges : List (BitVec 64) :=
  [0x0, 0x8000000000000000, 0x1, 0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000,
   0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
   0x4340000000000000, 0x4340000000000001, 0x433fffffffffffff, 0xc3e0000000000000,
   0x43e0000000000000, 0x43dfffffffffffff, 0x41dfffffffc00000, 0xc1e0000000000000,
   0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000,
   0x7ff8000000000000, 0xfff8000000000000, 0x7ff0000000000001, 0x4000000000000000,
   0x3fe0000000000000, 0x3cb0000000000000, 0x0008000000000000, 0x4059000000000000]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def rands (n : Nat) (seed : UInt64) : List (BitVec 64) := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let v := if i % 3 == 0 then (s >>> 11).toBitVec ||| 0x3ff0000000000000
      else s.toBitVec
    out := v :: out
  return out

def specPairs : List (BitVec 64 × BitVec 64) :=
  (edges.flatMap fun a => edges.map fun b => (a, b)) ++ (rands 2000 7).zip (rands 2000 11)

/-- A hash for the edge vectors. -/
def h (x : Nat) : Nat := ((lcg (lcg (lcg (UInt64.ofNat x)))) >>> 3).toNat

def mk (neg : Bool) (E f : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + E * 2 ^ 52 + f % 2 ^ 52)

/-- Exponent differences `d`, both orders, random fractions and signs; every
fifth `b` has a zero fraction, every fifth an all-ones one. -/
def dList : List Nat := [0, 1, 2, 3, 4, 55, 56, 57, 60, 1000]
def expDiffPairs : List (BitVec 64 × BitVec 64) :=
  dList.flatMap fun d =>
    let base := if d ≥ 1000 then 1500 else if d ≥ 55 then 1100 else 700
    (List.range 60).flatMap fun i =>
      let fa := h (d * 1000 + i)
      let fb := if i % 5 == 0 then 0 else if i % 5 == 1 then 2 ^ 52 - 1 else h (d * 1000 + i + 500000)
      let a := mk (fa / 2 ^ 60 % 2 == 1) base fa
      let b := mk (h (d * 1000 + i + 900000) % 2 == 1) (base - d) fb
      [(a, b), (b, a)]

/-- Cancellation: equal exponents and nearby fractions, `d = 1` with a
borrow, and a power of two minus just under it; normal and near-subnormal. -/
def cancelPairs : List (BitVec 64 × BitVec 64) :=
  (List.range 300).flatMap fun i =>
    let f := h (7000000 + i) % 2 ^ 52
    let E := if i % 3 == 0 then 1100 else if i % 3 == 1 then 2 else 1
    let δ := h (8000000 + i) % 17
    let g := (f + δ + 2 ^ 52 - 8) % 2 ^ 52
    [(mk false E f, mk true E g), (mk false (E + 1) 0, mk true E (2 ^ 52 - 1 - δ)),
     (mk false (E + 1) (h (8500000 + i) % 64), mk true E (h (9000000 + i)))]

/-- Subnormal operands and results. -/
def subnPairs : List (BitVec 64 × BitVec 64) :=
  (List.range 100).flatMap fun i =>
    let f := h (10000000 + i); let g := h (11000000 + i)
    [(mk false 0 f, mk true 0 g), (mk false 0 f, mk true 1 g), (mk false 1 f, mk true 1 g),
     (mk false 0 f, mk false 0 g)]

/-- Ties and near-ties: `b` half an ulp of `a` (exact tie), a quarter, just
over and just under half; `d = 1` with odd `b` (the dropped bit is a tie). -/
def tiePairs : List (BitVec 64 × BitVec 64) :=
  (List.range 100).flatMap fun i =>
    let f := h (12000000 + i) % 2 ^ 52
    let E := if i % 2 == 0 then 1100 else 60
    let j := h (13000000 + i) % 2 ^ 51
    [(mk false E f, mk false (E - 53) 0), (mk false E f, mk false (E - 54) 0),
     (mk false E f, mk false (E - 53) 1), (mk false E f, mk false (E - 54) (2 ^ 52 - 1)),
     (mk false E f, mk false (E - 1) (2 * j + 1)), (mk false E (2 * j), mk false (E - 1) (2 * j + 1))]

def edgePairs : List (BitVec 64 × BitVec 64) :=
  let base := expDiffPairs ++ cancelPairs ++ subnPairs ++ tiePairs
  base ++ base.map fun (a, b) => (a, b ^^^ 0x8000000000000000#64)

def sp : Nat := 0x80100000
def m0 : Mem := ∅
def ra : BitVec 64 := 0x8001ca88

/-! ## The observation and the three checks -/

/-- What a run shows at its rounding stage: the first round site on the path
(`probe`/`folded`), or, on a path with none, the pack join. -/
structure Obs where
  site : Nat
  kind : String
  v : Nat
  E : Nat
  nrounds : Nat

def obs (t : List Ev) : Option Obs :=
  let rs := t.filterMap fun
    | .probe pc x e => some (pc, "probe", x, e)
    | .folded pc x e => some (pc, "folded", x, e)
    | _ => none
  match rs with
  | (pc, k, x, e) :: _ => some ⟨pc, k, x.toNat, e.toNat, rs.length⟩
  | [] =>
    match t.filterMap (fun | .join pc x e => some (pc, x, e) | _ => none) with
    | (pc, x, e) :: _ => some ⟨pc, "join", x.toNat, e.toNat, 0⟩
    | [] => none

/-- Round to odd. -/
def rto (n k : Nat) : Nat := n / 2 ^ k ||| (if n % 2 ^ k ≠ 0 then 1 else 0)

/-- The exact sum (`sub`: difference) of two finite operands as
`(-1)^neg · M · 2^emin`, `emin` the smaller operand exponent (`F64.add`'s own). -/
def exact (sub : Bool) (a b : F64) : Option (Bool × Nat × Int) :=
  match a.cls, b.cls with
  | .fin sa m₁ e₁, .fin sb m₂ e₂ =>
    let sb := if sub then !sb else sb
    let t := min e₁ e₂
    let S := F64.sgnApply sa (F64.align m₁ e₁ t) + F64.sgnApply sb (F64.align m₂ e₂ t)
    some (decide (S < 0), S.natAbs, t)
  | _, _ => none

structure Row where
  a : BitVec 64
  b : BitVec 64
  site : Nat
  kind : String
  nr : Nat
  v : Nat
  r : Nat
  k : Int
  /-- (1): `"eq"`: `v = rto M k`; `"hid"`: equal but for the hidden bit
  `2^55` the machine keeps implicit; `"bad"`. -/
  c1 : String
  inexact : Bool
  /-- (2) W1's hypothesis `2^54 ≤ rto M k`. -/
  w1 : Bool
  /-- (2) `F64.round` of the rto'd value at the machine's scale = of the exact value. -/
  agree : Bool
  /-- The bits `F64.round` drops below the machine's last work bit. -/
  margin : Int
  /-- (3) the routine = `F64.add`/`F64.sub`. -/
  c3 : Bool
  /-- (1′) on a `"bad"` row: the least `j ≥ 1` with `vfull = rto M (k + j) · 2^j`
  (round to odd at a scale `j` bits coarser, then an exact left shift); 0 if none. -/
  shiftJ : Nat
  /-- (2′) `F64.round` of the machine's own value (hidden bit restored) = of the exact value. -/
  agreeV : Bool

def row (sub : Bool) (T : BitVec 64 → BitVec 64 → Tr) (a b : BitVec 64) : Option Row := do
  let (neg, M, emin) ← exact sub a b
  guard (M ≠ 0)
  let (t, res) := T a b
  let o ← obs t
  let ev : Int := (max o.E 1 : Nat) - 1078
  let k := ev - emin
  let r := if 0 ≤ k then rto M k.toNat else M <<< (-k).toNat
  let c1 := if o.v == r then "eq" else if r == o.v + 2 ^ 55 then "hid" else "bad"
  let vfull := if 1 ≤ o.E && o.v < 2 ^ 55 then o.v + 2 ^ 55 else o.v
  let shiftJ := if c1 != "bad" then 0 else
    ((List.range 60).map (· + 1)).find? (fun (j : Nat) => decide (0 ≤ k + (j : Int)) && vfull == rto M (k + (j : Int)).toNat <<< j) |>.getD 0
  let spec := if sub then F64.sub a b else F64.add a b
  some { a, b, site := o.site, kind := o.kind, nr := o.nrounds, v := o.v, r, k, c1
         inexact := decide (0 < k) && M % 2 ^ k.toNat != 0
         w1 := decide (2 ^ 54 ≤ r)
         agree := F64.round neg r ev false false == F64.round neg M emin false false
         margin := F64.target M emin - ev
         c3 := res == spec, shiftJ
         agreeV := F64.round neg vfull ev false false == F64.round neg M emin false false }

/-- Per site: n, (1) eq / hid / bad, inexact, W1 holds, W1 ∧ agree,
¬W1 ∧ agree, ¬W1 ∧ ¬agree (inexact), min margin, min `r` on inexact rows,
(3) failures, paths with more than one round site. -/
def summary (rows : List Row) : List String :=
  let sites := (rows.map fun x => (x.site, x.kind)).eraseDups
  sites.map fun (s, kd) =>
    let rs := rows.filter (·.site == s)
    let cnt (p : Row → Bool) := (rs.filter p).length
    let minM := (rs.map (·.margin)).foldl min 100000
    let ri := (rs.filter (·.inexact)).map (·.r)
    let minR := ri.foldl min (2 ^ 64)
    s!"{String.ofList (Nat.toDigits 16 s)} {kd}: n={rs.length} (1) eq={cnt (·.c1 == "eq")} hid={cnt (·.c1 == "hid")} bad={cnt (·.c1 == "bad")} (1′) bad=rto·2^j: j=1:{cnt (·.shiftJ == 1)} j=2:{cnt (·.shiftJ == 2)} j≥3:{cnt (·.shiftJ ≥ 3)} none:{cnt fun x => x.c1 == "bad" && x.shiftJ == 0} | inexact={cnt (·.inexact)} | (2) W1={cnt (·.w1)} W1∧agree={cnt fun x => x.w1 && x.agree} ¬W1∧agree={cnt fun x => !x.w1 && x.agree} ¬W1∧¬agree={cnt fun x => !x.w1 && !x.agree} ¬agree={cnt (!·.agree)} ¬agreeV={cnt (!·.agreeV)} minMargin={minM} minR(inexact)={if ri.isEmpty then 0 else Nat.log2 minR}(log2) | (3) bad={cnt (!·.c3)} | multiRound={cnt (·.nr > 1)}"

def cex (rows : List Row) : List (String × BitVec 64 × BitVec 64 × Nat × Nat × Int × Int) :=
  ((rows.filter fun x => (x.c1 == "bad" && x.shiftJ == 0) || (x.w1 && !x.agree) || !x.agreeV || !x.c3).take 8).map
    fun x => (x.c1 ++ (if x.w1 && !x.agree then " W1-violated" else "") ++ (if x.c3 then "" else " (3)"),
              x.a, x.b, x.v, x.r, x.k, x.margin)

def runAll (sub : Bool) (T : BitVec 64 → BitVec 64 → Tr) (F spec : BitVec 64 → BitVec 64 → BitVec 64)
    (ps : List (BitVec 64 × BitVec 64)) : List String × Nat × Nat × List (String × BitVec 64 × BitVec 64 × Nat × Nat × Int × Int) :=
  let rows := ps.filterMap fun (a, b) => row sub T a b
  let traceBad := (ps.filter fun (a, b) => (T a b).2 != F a b).length
  let specBad := (ps.filter fun (a, b) => F a b != spec a b).length
  (summary rows, traceBad, specBad, cex rows)

def addT (a b : BitVec 64) : Tr := Adddf3T.T_F m0 sp ra a b
def subT (a b : BitVec 64) : Tr := Subdf3T.T_F m0 sp ra a b

#eval (specPairs.length, edgePairs.length)
-- `__adddf3`, SpecTest pairs: (per-site lines, traced ≠ F, F ≠ F64.add, counterexamples)
#eval runAll false addT (Adddf3.F m0 sp ra) F64.add specPairs
#eval runAll false addT (Adddf3.F m0 sp ra) F64.add edgePairs
#eval runAll true subT (Subdf3.F m0 sp ra) F64.sub specPairs
#eval runAll true subT (Subdf3.F m0 sp ra) F64.sub edgePairs

end Lua.Vm.Fn.RtoCheck
