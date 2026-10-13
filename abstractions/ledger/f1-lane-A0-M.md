# Lane F1-A0-M: `MallocR_Statement`, `FreeR_Statement` (the A0 allocator premises of `CallOpen`)

Base: main `0f36bdc`. Route: CLAUDE.md's allocator row (SWP over the generated
step tables), ship-your-interpreter's dlmalloc proofs ported, not retyped.
Lines are non-blank, non-comment lines. CPU and peak memory are one
`lake env lean <file>` each (`/usr/bin/time -v`). No limit raised; every
declaration of the new bridge files is under 50k heartbeats.

## Result

| target | status | theorem / file |
|---|---|---|
| `MallocR_Statement` | **proved** | `AllocProof.mallocR_proved` (`Lua/Vm/Sim/Kit/AllocProof.lean`) |
| `FreeR_Statement` | **proved** | `AllocProof.freeR_proved` (same file) |
| `CallOpen` | `print` only | `extendCI_proved`, `exitUp_proved` have no premise |

Axioms of both: `[propext, Classical.choice, Quot.sound]` (check.sh stage 6
lists them, `malloc_all`, `free_body`, `LocalRun.reach`, `heapV`, `heapL`).

## 1. Survey: the code is syi's, relocated

`experiments/port/alloc/cmp.py`, `diff2.py` (objdump, addresses normalised):

* `_free_r`, `_realloc_r`, `_sbrk_r`, `_sbrk`, the locks: identical to the
  WHILE ELF's modulo addresses and `gp` offsets.
* `_malloc_r`: identical but for two inserted `auipc`: the WHILE ELF reached
  `__malloc_current_mallinfo` `gp`-relative, the Lua ELF's is out of `gp`
  range (`auipc t4; addi t4` at `0x8002fd44`, `0x800301ec`).
* `_malloc_trim_r`: three inserted `auipc` for the same global.

So the proof ports by relocation: `pcmap.py` aligns each function's
instructions (pc map, the inserted `auipc` mapped to the pair's first),
`reloc.py` rewrites every address literal (hex and decimal, pcs by the map,
data by symbol + offset) and every pc-suffixed name (`st_<pc>`, ...). The
term census (`term_census.py closure` over `MallocRunAll`, `FreeRunAll`)
reached one WHILE-root constant (`roundUp16`); the few declarations of
untaken modules are `VsaIris/Vsa/AllocKit.lean`.

## 2. `brk_hi` checked

* The code: `malloc_extend_top` asks `_sbrk` for `sbReq nb = (nb + 32 + 4095)
  & ~4095` (`lui 0x1; addi 31; and ~4095`), `nb = physSize n ≤ n + 31`; with
  the break page-aligned (it is, after the boot's first call) and contiguous,
  no correction `_sbrk`. Growth ≤ `n + 4158` ≤ `n + 16384 + 4096`.
* Sail: `experiments/port/alloc/brk_probe.lua` (allocations of 100 B to 1 MB)
  traced by `brktrace.py`: 246 `_malloc_r` calls, 27 extending, all within
  the bound, `growth − n ≤ 4096`. The statement stands; the proof threads the
  bound as `MBrk` (one growth by `sbReq` from the call's break `C.brk0`).

## 3. What the port needed

| piece | lines | note |
|---|---|---|
| relocated syi proofs (`Vsa/Sim/DlHeap.lean`, `VsaIris/Vsa/{Heap,Malloc,Free}*.lean`, `Sbrk`, `AllocTac`, `AllocBase`) | 14,162 (38 files) | 188 lines changed after relocation: `allocGlobal` split around htif.c's `fs_ready` (`0x8005d3c0`, between `brk.0` and `__malloc_max_total_mem` in the Lua ELF); the stack/global disjointness (`glob_off_of`) narrowed (the Lua globals cluster has 4 KiB gaps); `_malloc_trim_r`'s `auipc` steps; immediates of one `auipc`/`addi` pair; the `sext*_64` simp facts syi saw privately; `MBrk`, `Starved`, `MOK.room` |
| `AllocKit.lean` | 133 | `physSize`, `stackBase`, `ChunkWalk.extend`, ... |
| exact frames (`Machine`, `Step`, `MachWP`, `Call`, `LocalRun{,O}`, `Example`, `Instance`, `Tools`, `SegRun`, `SymObs`, `SymJalr`, `SymLeaf`, `Console`, `AllocSltu`) | +59/−43 | `MachineModel.pres`/`quiet`, `LocalStep.pres_frame`, `OutStep none` quiet, `SegFrom` carries both, `AluStep`/`JalrStep` exact |
| `SWPReach.lean` | 65 | `LocalRun.reach`: the machine run with exact frames |
| `AllocHeap.lean` | 229 | `heapV`/`heapL`, `inUse_iff`, addresses tied |
| `AllocProof.lean` | 478 | the context, `MQ`/`FQ`, the two theorems |

CPU / peak: `AllocProof` 18.5 s / 4.7 GB; `AllocHeap` 2.7 s / 2.4 GB;
`FreePaths` (largest ported) 61 s / 3.3 GB; `MallocExtend` 41 s / 2.9 GB.
Full `lake build Lua Vsa VsaIris` after the changes: 2,223 jobs, OK; the
boot witnesses re-checked with the new `heapCheck`.

## 4. Statement corrections (each true of the machine, checked)

1. **`HeapAt` gains `brk_page`, `top_room`, `bb_lt`** (syi's `PHeapAt`/
   `BlockHeapAt` fields). `brk_page` excludes `malloc_extend_top`'s fencepost
   path (which calls `_free_r`). `heapCheck` and `gen_lua_boot_witness.py`
   check them at both entries; `HeapAt.congr`/`ofExt`/`congrU`/`toBinsList`
   carry them.
2. **`MallocGlobal` is the proof's footprint**: `_REENT->_errno` (written by
   `_sbrk_r` on failure), `__malloc_trim_threshold` (read by `_free_r`) and
   `__malloc_top_pad` (read) join it; `AllocWords` likewise, and `ExtendCI`'s
   `kL` ranges narrowed off them. (Loads need ownership on the SWP route.)
3. **The step tables drop `malloc`/`free`/`realloc` and `__errno`**
   (`gen_alloc_steps.py` `ROOTS`, `CUT`): the wrappers' and `__errno`'s
   `ld _impure_ptr` put a `.data` word in the text the run must find loaded,
   which a Lua call cannot guarantee. `_sbrk`'s failure (the only `__errno`
   caller) is refuted from the caller's room (`MOK.room`; `_free_r`'s trim
   only shrinks).

## 5. Obstacles (with evidence)

1. **The SWP route's frames were too weak for the Lua route.** `SegFrom`
   framed bytes by total read and the console by its concatenation; `ArmPay`
   pins `σ.mem` and `sailOutput` exactly and `MallocPost.keep` is
   presence-level. `segEval_sound` has both exactly, so the run facts now keep
   them (`pres`, `quiet`): no consumer of `MallocPost` changed.
2. **syi's `Starved`** (`heapEnd + 4096 < top0 + 2·physSize n + extendSlack`)
   does not refute NULL under the statement's room for large `n`; replaced by
   the precise `2^31 ≤ physSize n ∨ heapEnd < brk0 + sbReq (physSize n)`.
3. **syi's top-level `DlLayout` adapters** (`malloc{Chg,Local}Run_proved`,
   `free{Chg,Local}Run_proved`, `malloc_entry`, `free_entry`) were dropped:
   they go through the wrappers and the WHILE capacity budget.

## Gate

`abstractions/gate.py`: see the report. `scripts/check.sh`: see the report.
