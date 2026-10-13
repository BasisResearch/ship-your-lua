import Lua.Vm.Fn.SfRefFloor

/-!
# `floor`'s chambers `1049 ≤ e < 1062` (lane float-sf3, (b1))

One chamber per exponent and sign (`fl_chambers`, `Lua/Vm/Fn/SfRefFloor.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Lua.Vm.Fn.SfLens Lua.Vm.Fn.SfCmpLens Lua.Vm.Sim

namespace Lua.Vm.Fn.FloorFn
open Lua.Vm.Fn.FloorLens Lua.Num

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

fl_chambers 1049 1062

end Lua.Vm.Fn.FloorFn
