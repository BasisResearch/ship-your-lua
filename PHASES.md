# Phases

The goal is `endToEnd_lua`: for every supported Lua chunk `s` and the
bare-metal ELF running its compiled `Proto`, the machine halts cleanly
printing `out` iff `LuaSem s out`. We get there compositionally:

```
LuaSem s out  ↔  BcSem (compile s) out  ↔  Halts c out 0
   Layer B: compile_refinement      Layer A: vm_refinement
```

This file is the plan and the obligation ledger. The three headline
statements are `def …_Statement : Prop`s in `Lua/Theorems.lean`. None is an
axiom or a `sorry`. Their compositions are proved:

* `vm_refinement_of_sim` gives Layer A from `VmSim`;
* `compile_refinement_of_tv` gives Layer B from `CompileTV`;
* `endToEnd_of_layers` and `endToEnd_of_obligations` give the composition.

## Obligations

Every row is currently unassigned.

| statement / obligation | file | discharged in | status |
|---|---|---|---|
| `VmLayout.runtimeReady` concrete instance `luaLayout` | `Lua/Vm/Runtime.lean` | A0 | **defined** (`luaRuntimeReady`); every field holds at both traced entries (checked natively by `gen_lua_boot_witness.py`) |
| `VmLoaded luaLayout p (fillZero c)` at real entry states (boot witness) | `Lua/Vm/Boot/` | A0 | **proved** for `while.lua` and `f1_ops.lua` (`vmLoaded_while_entry`, `vmLoaded_f1Ops_entry`, `Lua/Vm/Boot/Witness/`), for every state with the traced registers (`EntryRegs`) and the boot memory; the register file itself is a hypothesis (A0.6) |
| `VmSim luaLayout` (F1: `term_sim`, `stuck_sim`) | `Lua/Vm/Sim/` | A1 | open, **reduced to named premises**: `vm_refinement_of_open' : OpenArms → FloatArms → ErrorSimRest → vm_refinement_Statement luaLayout` (`Lua/Vm/Sim/StuckErr.lean`; lane float-s1: no `NoEscape`, since no supported program escapes, `noEscape_of_supported`; also `vm_refinement_of_error : OpenArms → FloatArms → ErrorSim → …`, `vm_refinement_of_open : OpenArms → FloatArms → FinalSim → StuckSim → …` in `Fold.lean`). Discharged inside it: the entry (`entrySim`), `VARARGPREP` (`Kit.varargSim`), `FinalSim`, and, off their float paths (`SimArm.split`), 47 of the 57 arms of `armTable` (UNM but its string path; GETTABUP by lane F1-7); under `FloatArms.soft` (`SoftFloatSpec`), `LOADF` and the float paths of `SUB`, `ADDI`, `LTI`, `GEI`, `FORLOOP`, and of `EQI`, `FORPREP` but for their named premises (round 5 integration); lane F2: `LEI`, `GTI`, `ADD`, `ADDK`, `SUBK`, `UNM`, `LE`, and under `FloorSpec` `LT`, `LE`'s f2i paths, `BNOT`, `BAND`, `BOR`, `BXOR`; lane F3, under `FloorSpec`: `BANDK`, `BORK`, `BXORK`, `SHL`, `SHR`, `SHLI`, `SHRI`; lane F1-F5: `MUL`, `MULK`, `EQI` (`eqiFlt_proved`), and `FloorSpec` itself (`floorSpec_proved`, passed by the generated at-lemmas); lane F4: `EQ`, `EQK`; lane F1-F6: `DIV`, `DIVK` (every path), `IDIV`, `IDIVK` (float paths); lane F1-F7: `MOD`, `MODK` (float paths: libm `fmod`, its `errno` store); lane F1-21: `POW`, `POWK` (every path on quiet float operands, from `__ieee754_pow`'s level (b), `Ieee754Pow.spec_proved` since lane float-sf7; lane F1-22: every related state's operands are quiet, `SimArmOnM.of_all powQuiet_of`). Left: the 6 fields of `OpenArms` (MMBIN, MMBINI, MMBINK, UNM_str, CONCAT, `CALL_open : Kit.CallOpen` and `CALL_heap`; lane F1-13: `SimArm .CALL` is `Kit.sim_CALL (Kit.printCall_of h.CALL_open) h.CALL_heap`), the fields of `FloatArms` (row below), and `ErrorSimRest` |
| `vmRel_final_Statement` / `FinalSim` (the `RETURN*` arms: from `VmRel` at a `Final` state the machine halts with code 0 and console `s.out`) | `Lua/Vm/Sim/Kit/Ret*.lean`, `Lua/Vm/Sim/Kit/Exit.lean`, `Lua/Vm/Sim/Fold.lean` | A1 | **proved** (lane F1-4): `Ret.vmRel_final` (no `Reach`, no `Supported` needed; every `RETURN`/`RETURN0`/`RETURN1`, any operands), `finalSim`. The `exit(0)` at its end is `Complement.exit` (`ExitOk`): proved at the entry and after `VARARGPREP` (`exitOk_entry`: no `atexit`, no stdio exit handler); **an arm that changes the complement must re-establish it** — after a `print`, newlib's `stdio_exit_handler` runs `_fwalk_sglue(_fclose_r)` over the standard streams (`__sflush_r`, htif `_close`, `_free_r` of the buffer), so `OpenArms.CALL` now carries the post-print `exit` (lane F1-13: `CallInvAt.atexit` carries `__atexit = NULL`, `call_close` re-establishes `ExitOk` after a `print` from `ExitUp_Statement`; lane F1-14: `ExitUp_Statement` proved from `FreeR_Statement`, `exitUp_of_free`) |
| `vmRel_entry_Statement` (the prologue run from `VmLoaded luaLayout` to `VmRel … State.init`) | `Lua/Vm/Sim/Rel.lean` | A1 | **proved** (`vmRel_entry`, `Lua/Vm/Sim/Entry.lean`) |
| `StuckSim` (`stuck_sim`'s error paths: from `VmRel` at a reachable state that is neither final nor stepping, the machine diverges or halts nonzero) | `Lua/Vm/Sim/Fold.lean`, `Lua/StuckCases.lean`, `Lua/Vm/Sim/{Stuck,StuckErr}.lean` | A1 | **reduced to `ErrorSim`** (`stuckSim_of_error`, lane float-s1). The stuck states are enumerated (`stuck_cases`: every reachable stuck non-final state is a `StuckAt` with a failing `Fault`; `reach_regs`, `opKernel_wf`, `body_fault`, lane F1-5); with floats and string coercion in `δ` every fault but a stuck `OP_FORLOOP` is a Lua error (`Fault.Escape`, exact), and a supported program never reaches one (`loop_inv`, `forloop_regs`, `noEscape_of_supported`). The former escapes (`Lua/Programs/Escape.lean`) are proved `BcSem` outputs equal to the ELF's on Sail (`escStrflt_bcSem` `2.5`, `escForstr_bcSem` `1 2`, `escUnmflt_bcSem` `-1.5`). `ErrorSim` from `ErrorSimRest` (`errorSim_of_rest`, `runerrorSim`); `ErrorSimRest` open |
| `ErrorSimRest` (the error sites: from `VmRel` at a non-escaping stuck state, `StuckOut`) | `Lua/Vm/Sim/StuckErr.lean`, `Lua/Vm/Sim/Kit/{AtErr,Throw,ErrTail}.lean` | A1 | **narrowed** (lane F1-16, `abstractions/ledger/f1-lane-16.md`). `Fault.site` relabelled after floats (`UNM` of a string: `strarith`; `BNOT` of a float: `tointerror`; `FORPREP`'s float zero step: `runerror`), `site_ops` (the opcodes per site). `ThrowFrom f msg` restated with an entry contract (`ErrIn`: `a0 = L`, `a1` the message (`LayoutErr.msg*`, generated), `sp`, `gp`, the memory off `ErrW`), delivered by every `At.*_err`; the old form (pc only) was not dischargeable. Every site ends at the seam `Kit.ErrMsgIn` (`luaG_errormsg`'s entry, the message pushed, memory off `HeadW`); the shared tail `Kit.ErrorTail_Statement` is proved from `Kit.Unwind_Statement` (`errorTail_of_unwind`) by the throw `Kit.throw_land` (`luaG_errormsg` → `luaD_throw` → `longjmp` → `luaD_rawrunprotected` returns 2 into `luaD_pcall`, proved on generated segments). Open fields: `runerrorHead` (`RunerrorHead_Statement`: `luaO_pushvfstring` (the three messages have no `%`: `addstr2buff`), `luaG_addinfo`'s `"%s:%d: %s"` (its `%d` is `snprintf("%lld")`, proved: `integerToStr_proved`, lane F1-FMT), `luaS_newlstr` → `luaC_newobj` → `_malloc_r`, `luaC_step`; its allocator premise is now `mallocR_proved` (lane F1-A0-M), the rest not started), `unwind` (`Unwind_Statement`: `luaD_pcall`'s error branch, `luaD_shrinkstack` (`_realloc_r`)/`luaE_shrinkCI` (`_free_r`), `main`'s `fprintf(stderr, ...)` (`_vfprintf_r`, 3,395 instructions: `__sinit`, `__swsetup_r`, the unbuffered `__sbprintf`; a second `--fn` spec of the `snprintf/lld` kind), `exit(2)`; `_free_r` is `freeR_proved` (lane F1-A0-M), `_realloc_r` has no summary yet), `fpFltZero` (`FpFltZero_Statement`, FORPREP's float zero step's arm path), and per other site `SiteHead_Statement e` (the helper on the failing operands and the `luaG_*error` formatting, into the seam) |
| `NoEscape` hypothesis of Layer A, or a semantics with floats | `Lua/StuckCases.lean`, `Lua/Bytecode/Semantics.lean` | A1/Float | **proved** (lane float-s1, `abstractions/ledger/float-s1.md`): floats in `δ` (FLOAT-DESIGN.md S1), the loop check `loopsOk` in `Supported`, `noEscape_of_supported : Supported p → NoEscape H p`; `vm_refinement_of_ne : vm_refinement_ne_Statement → vm_refinement_Statement luaLayout` |
| Float S1/S1b: floats and string coercion in `δ`; the metatheory re-run | `Lua/Bytecode/Semantics.lean`, `Lua/Num/{Arith,Pow,PowFacts}.lean`, `Lua/Fragment.lean`, `Lua/StuckCases.lean` | Float | **done** (lane float-s1): `Value.flt` (the model's value and the double's sign bit); `δ`, `fastArith` (`luaO_rawarith`, three-way `opArith`), `LTnum`/`LEnum`/`luaV_equalobj` (`ltNum`, `leNum`, `eqNum`, `Value.rawEq`), the string metamethods over `str2number`, `forprep`/`forlimit` and `floatforloop` (`forprepK`, `forLimit`, `forloopK`), `tostringbuff` for `print`/`..`; new kernels `LOADF`, `DIV`, `DIVK`, `POW`, `POWK` (in F1; the `Float` fragment is gone); `^` is newlib 4.5.0's fdlibm `pow` transcribed (`Lua/Num/Pow.lean`, not a `Host` field; 1,570 Sail vectors bit-exact; signalling-NaN constants are not values, `isSNaN`). `kstep_iff`, `footprint`, `certain_answers`, `opKernel_wf`, `body_fault`, `stuck_cases` and every corpus `Supported`/`BcSem` proof rebuilt |
| `FloatArms` (the float paths of Layer A, FLOAT-DESIGN.md §3 tiers T0–T5) | `Lua/Vm/Sim/Fold.lean` | A6/Float | open, 2 named premises: `soft : SoftFloatSpec` (empty since lane float-sf2: every field proved); and one narrowed to what its float proof leaves: `FORPREP : FpStrFlt_Statement` (lane F1-F8: `FpCoerce_Statement` from the string classes, the integer loop with a float limit and the float loops with integer control values proved; lane F1-F9: `fpCoerce_of_flt : FpStrFlt_Statement → FpCoerce_Statement`, `Kit/FpCoerce.lean`: string integer numerals proved, non-numerals stuck; a float numeral string open) (`EQI`'s `EqiFlt_Statement` is `eqiFlt_proved`, lane F1-F5). `LOADF`, `SUB`, `ADDI`, `LTI`, `GEI`, `FORLOOP`, and (lane F2) `LEI`, `GTI`, `ADD`, `ADDK`, `SUBK`, `UNM`, `LT`, `LE`, `BNOT`, `BAND`, `BOR`, `BXOR`, and (lane F3) `BANDK`, `BORK`, `BXORK`, `SHL`, `SHR`, `SHLI`, `SHRI`, and (lane F1-F5) `MUL`, `MULK`, `EQI`, and (lane F4) `EQ`, `EQK`, and (lane F1-F6) `DIV`, `DIVK`, `IDIV`, `IDIVK`, and (lane F1-F7) the float paths of `MOD`, `MODK` left the structure (proved under `soft`, which is empty; joined in `armTable`). The `floor` field is discharged (lane F1-F5: the at-lemmas of both the arm route and the callee route pass `floorSpec_proved`). The field `pow_spec` (lane F1-21) is discharged: lane float-sf7 proved `PowR.Ieee754PowSpec_Statement` (`Ieee754Pow.spec_proved`), and `armTable`'s `POW`, `POWK` pass it. Open field: `FORPREP`'s float numeral strings (`FpStrFlt_Statement`: `luaO_str2num` → `l_str2d` → `strtod`). `__divdf3` (lane float-sf4) is a call node since lane F1-F6. |
| Float M0: machine summaries of the soft-float routines (`__floatsidf`, `__floatdidf`, `__fixdfdi`, `__eqdf2`, `__ledf2`, `__gedf2`, `__adddf3`, `__subdf3`, `__clzdi2`), FLOAT-DESIGN.md §3 | `Lua/Vm/Fn/*`, `Lua/Vm/Sim/Kit/{Fn,Clzdi2}.lean`, `scripts/gen_lua_fn.py` | A6/Float | level (a) **proved** (lane float-m0, `abstractions/ledger/float-m0.md`): per routine a generated lifted function `F` (`Fm` its stack frame) and `sum`, keyed by entry pc (`SegSt` from the call to the return, `FnSp` stack facts; `__clzdi2` by `scan_loop`, `clzdi2_sum`). Level (b) **proved for all eight** (`F = S`, `S` the `F64` operation, equal to `Float.Model` by S0a); `SoftFloatSpec` (`Lua/Vm/Fn/Spec.lean`) has no field left (kept, empty, while `FloatArms.soft` names it). `__adddf3`, `__subdf3` **proved** (round 5, B-SFREF, adopted): `Lua.Vm.Fn.Adddf3.spec_proved` (`Lua/Vm/Fn/SfRefAdd.lean`), `Lua.Vm.Fn.Subdf3.spec_proved` (`Lua/Vm/Fn/SfRefSub.lean`), by (b1) `F_eq_sfref` (chambers over the `Nat` lens, `Lua/Vm/Fn/SfLens.lean`) and (b2) `SfRef.add_eq`/`sub_eq` (`Lua/Num/SfRef{,Spec}.lean`); `gen_lua_at.py`'s `FPROVED` uses them at the call sites. `__eqdf2`, `__ledf2`, `__gedf2`, `__fixdfdi`, `__floatdidf`, `__floatsidf` **proved** (lane float-sf2, `abstractions/ledger/float-sf2.md`): `Lua.Vm.Fn.<R>.spec_proved`; comparisons (`Lua/Vm/Fn/SfRefCmp.lean`) by (b2) `SfRef.cmp_eq`/`eqv_eq` (`_FP_CMP`/`_FP_CMP_EQ` = `F64.compare` by `compare_key`, `Lua/Num/SfRefCmp.lean`) and (b1) the chamber generator `sfc_chambers`; conversions (`Lua/Vm/Fn/SfRefInt.lean`) by (b2) `SfRef.toInt_eq`/`ofInt_eq` (`_FP_TO_INT`/`_FP_FROM_INT`, `Lua/Num/SfRefInt.lean`, `roundPack_eq`/`round_scale`/`round_rto` reused) and (b1) four exponent chambers (`__fixdfdi`) and stage lemmas at the machine's sites (`__floatdidf`: `g_2a8`, `g_308`, `g_2a0`, `g_248`); all in `FPROVED`. |
| Float M1 pilot: arms' float paths on the location-list route | `Lua/Vm/Sim/Kit/AtFlt*.lean`, `Lua/Vm/At/{Loadf,Lti,Eqi,Gei,Addi,Forloop}.lean` | A6/Float | **proved under `SoftFloatSpec`** (lane float-m0): `sim_LOADF_flt`, `sim_LTI_flt`, `sim_GEI_flt`, `sim_ADDI_flt`, `sim_FORLOOP_flt`; `sim_EQI_flt` also under `EqiFlt_Statement` (open: `δ .eq` on a float and an 8-bit immediate is `Float.Model.beq`, `Lua/Vm/Sim/Kit/FltVal.lean`). Joined into `armTable` under `FloatArms.soft` (round 5 integration); `EQI`'s field is now `EqiFlt_Statement` |
| `FpStrFlt_Statement` (`FORPREP` with a float numeral string among `init`, limit, step: every string a numeral (`str2number`), one of them no integer numeral (`l_str2int` rejects it); `luaV_tonumber_`/`luaV_tointeger` → `luaO_str2num` → `l_str2d`: `strpbrk`, `l_str2dloc` → newlib `strtod` → `_strtod_l` (`0x800309b4`, 1601 instructions), whose bignum and hex paths allocate by `_Balloc` and whose overflow stores `errno`) | `Lua/Vm/Sim/Kit/FpCoerce.lean` | A6/Float | open, **named premise** (lane F1-F9, `FloatArms.FORPREP`; narrowed from lane F1-F8's `FpStr_Statement`, now `fpStr_of : FpStrFlt_Statement → FpStr_Statement`). Proved beside it: `fpCoerce_of_flt` (`FpCoerce_Statement` from it): the number classes (lane F1-F8: `fp_ti`, `fp_c{IIF,IFF,FII,FIF,FFI}`), a string that is no numeral (the kernel stuck: `tonumber`/`forLimit` fail), and (lane F1-F9) every class with string integer numerals: the integer loop with a string limit `fp_sISI` (`luaV_tointeger`'s string summary `tois_sum`, `AtF/Toint{SS,SL}`, call node `tois_at`, `At/ForprepSI`) and the 18 float-loop classes `fp_s{IIS,…,SSS}` (`luaV_tonumber_`'s string summary `tons_sum`, `AtF/Tonum{SS,SL}`, call node `tons_at`, `At/ForprepC*`, `Kit/AtFltForprepS.lean`); both summaries splice lane F1-F8's `str2num_int` at their `luaO_str2num` call (`Kit/TonumStr.lean`), the string live and apart from the callee frames by `Core.unseal`/`Ranges.own_apart` (`tsCtx_at`, `Kit/AtCoerceS.lean`). Left: `luaO_str2num`'s float path, i.e. `l_str2int`'s failing exits to `0x80011b5c`, `strpbrk`, `l_str2dloc`'s trailing-space loop, and newlib `_strtod_l` (no summary: the decimal fast path through `__floatunsidf`, `__muldf3`/`__adddf3`/`__divdf3` on `tens` needs a level-(a) walk with its digit loops and a level-(b) exactness proof against `Float.Model.ofScientific`; the bignum path's `_Balloc` → `_calloc_r` writes the heap and `_REENT`'s freelists, which `Complement` does not carry (shared with lane F1-19's float printing); `__gethex`; `errno` on overflow); then `luaV_tonumber_`'s float result (tag `19`) and `luaV_tointeger`'s `luaV_flttointeger` on it |
| Round 5 bake-off A-JOIN (float arms: pair atoms, Boolean forks, join cuts) | `Lua/Vm/Sim/Kit/{AtJoin,AtJoinRow,AtFltSub,AtFltForprep,AtFltLt}.lean`, `Lua/Vm/At/{Sub,ForprepF,LtF}.lean`, `scripts/gen_lua_at.py` (`JOINS`, `OP_FORPREP_F`, `OP_LT_F`) | A6/Float | **proved under `SoftFloatSpec`**: `sim_SUB_flt` (`FloatArms.SUB`), `fp_flt3` (FORPREP on three floats), `sim_FORLOOP_flt` refactored; `sim_FORPREP_flt` also under **`FpCoerce_Statement`** (open: the coerced classes through `luaV_tonumber_`/`luaV_tointeger`, whose call nodes need summaries with their frames), `sim_LT_flt` also under **`LtF2I_Statement`** (open: an integer outside `l_intfitsf` against a float, `luaV_flttointeger`'s chain through `floor`). Adopted (round 5 §7) and joined into `armTable` under `FloatArms.soft`; `FloatArms.LT`/`.FORPREP` are now `LtF2I_Statement`/`FpCoerce_Statement`; the gate cluster `a1-float-arm` re-baselined at the adoption merge. Report: `abstractions/bakeoff5/A-JOIN.md` |
| Lane F2: float arms on the join route | `Lua/Vm/Sim/Kit/{AtJoinOps,AtJoinF2I,FltNeg,FltValLt,AtFltLei,AtFltGti,AtFltAdd,AtFltAddk,AtFltSubk,AtFltUnm,AtFltLe,AtFltF2I,AtFltBnot,AtFltBand,AtFltBor,AtFltBxor}.lean`, `Lua/Vm/Fn/Floor.lean`, `Lua/Vm/At/{Lei,Gti,Add,Addk,Subk,UnmF,LeF,BnotF,BandF,BorF,BxorF}.lean`, `scripts/gen_lua_at.py` (Floor/Fixdfdi call nodes, `PREMISED`, `auipc`, `xori`) | A6/Float | **proved under `SoftFloatSpec`** (empty since lane float-sf2, so unconditional): `sim_LEI_flt`, `sim_GTI_flt`, `sim_ADD_flt`, `sim_ADDK_flt`, `sim_SUBK_flt`, `sim_UNM_flt`, `sim_LE_flt`; **under `SoftFloatSpec` and `FloorSpec`**: `lt_flt_f2i` (`LtF2I_Statement` discharged), `le_flt_f2i` (`LeF2I_Statement` discharged), `sim_BNOT_flt`, `sim_BAND_flt`, `sim_BOR_flt`, `sim_BXOR_flt`. `FloorSpec` was a named premise (`FloatArms.floor`) until lane F1-F5 discharged it with `floorSpec_proved`. Joined into `armTable`; ledger `abstractions/ledger/f1-lane-F2.md` |
| Lane F3: the K bitwise arms and the shifts on the join route | `Lua/Vm/Sim/Kit/{AtFrame,AtJoinInt,AtJoinShift,AtFltBandk,AtFltBork,AtFltBxork,AtFltShl,AtFltShr,AtFltShli,AtFltShri}.lean`, `Lua/Vm/At/{BandkF,BorkF,BxorkF,ShlF,ShrF,ShliF,ShriF}.lean`, `scripts/gen_lua_at.py` (`OP_*K_F`, `OP_SH*_F`), `scripts/gen_lua_arms.py` (the shifts in `FLOAT_ARMS`) | A6/Float | **proved under `SoftFloatSpec` and `FloorSpec`**: `sim_BANDK_flt`, `sim_BORK_flt`, `sim_BXORK_flt` (`K[C]` read through `floor`'s frame: `at_fwd_k`, `proveBy` without error recovery), `sim_SHL_flt`, `sim_SHR_flt`, `sim_SHLI_flt`, `sim_SHRI_flt` (the amount's tests as residual atoms: `shiftl_m`/`shiftr_m`/`shiftr_K`, `at_kfork`; one declaration per `F2Ieq` outcome: `shift_flt_arm`, `shift2_flt_arm`). Joined into `armTable`; ledger `abstractions/ledger/f1-lane-F3.md` |
| Lane float-sf3: libm `floor` on the `SfRef` route; `__muldf3`/`__divdf3` level (a) | `scripts/gen_lua_fn.py` (`CALLEES`: call nodes to proved summaries, framed callees; `FORWARD`: frame-slot forwarding), `Lua/Vm/Sim/Kit/FnCall.lean`, `Lua/Vm/Fn/FloorFn.lean`, `Lua/Num/SfRefFloor.lean`, `Lua/Vm/Fn/SfRefFloor{,A,B,C,D,Spec}.lean` | A6/Float | **proved**: `FloorFn.sum` (level (a): 31 nodes, `__adddf3`/`__gedf2` as call nodes), `FloorFn.F_eq_ref` ((b1): 104 per-exponent chambers and 6 range chambers from the one-operand chamber generator `fl_chambers`/`fl_cover`), `SfRef.floor_cls`, `SfRef.floor_model` ((b2): `SfRef.floor` = `Lua.Num.floor`), so `floorSpec_proved : FloorSpec` (`Lua/Vm/Fn/SfRefFloorSpec.lean`). `gen_lua_at.py` passes `floorSpec_proved` (`PREMISE_PROOF`, `Floor` in `FPROVED`; lane F1-F5). Evidence: `Lua/Vm/Fn/FloorTest.lean` (machine `F` = `SfRef.floor` = model = host C `floor` on 3,058 operands). `__muldf3` **proved** at both levels: `Muldf3.sum` (level (a): 76 nodes; `__muldi3` call nodes keep gcc's `-fipa-ra` temporaries, `muldi3_sumK`, `PASS_THROUGH`), `SfRef.mul_eq` ((b2): `_FP_MUL` = `F64.mul` by `roundPack_eq`/`round_rto`/`round_scale`), `Muldf3.F_eq_ref` ((b1): pack, product-join and product stages `g_e8ec`/`g_e660`/`g_e7a4`/`g_e628`/`g_e5bc`, 25 class-pair chambers from `smc_chambers`), `Muldf3.spec_proved : F = F64.mul` (`Lua/Vm/Fn/SfRefMul.lean`; `Muldf3` in `gen_lua_at.py` `FPROVED`; its call node `0x8002e504` is in `FCALLS` since lane F1-F5). Evidence: `Lua/Vm/Fn/MulTest.lean` (7,600 pairs). `__divdf3`: lane float-sf4 (row below) |
| Lane float-sf5: libm `__ieee754_fmod` on the `SfRef` route; loops in lifted functions | `scripts/gen_lua_fn.py` (cycles: Tarjan SCCs, `fuel`-indexed node functions, termination functions `T_<pc>`, `SIDE` conditions into `T`, premise callees, `MEMLESS`, `DISCH`), `Lua/Vm/Sim/Kit/FnLoop.lean`, `Lua/Vm/Fn/DivSum.lean`, `Lua/Vm/Fn/Ieee754Fmod{,/Defs,/L0,/L1,/L2}.lean`, `Lua/Num/SfRefFmod.lean`, `Lua/Vm/Fn/SfRefFmodModel.lean`, `Lua/Vm/Fn/Fmod{Lens,Pack,Norm,Fin,Loop,Entry,Ilogb,SetY,SetX,SetN,Deep,Pre,Top,Spec}.lean` | A6/Float | **proved**: `Ieee754Fmod.sum` (level (a): 90 nodes, 6 cycles, `__muldf3` a call node, `__divdf3` a call node of the proved `Divdf3.sum_div`), `SfRef.fmod_cls`, `SfRef.fmod_model` ((b2): `SfRef.fmod` = `Lua.Num.fmod` on the model), `Ieee754Fmod.F_eq_ref` ((b1): `F = SfRef.fmod` and `T = true` on every operand pair; the loop by induction (`loop_bf60`), the `ilogb` cycles (`ilog_*`), per-exponent chambers from the generators `fm_psub_chambers`, `fm_yc0b4_chambers`, `fm_ybe94_chambers`, `fm_xbe78_chambers`, `fm_dc0e8_chambers`, `fm_dc0d8_chambers` joined by `fm_cover`; the classes `L_be1c`), `Ieee754Fmod.spec_proved : F = SfRef.fmod` (`Ieee754Fmod` in `gen_lua_at.py` `FPROVED`), `Ieee754Fmod.sum_ref` (no premise). Evidence: `Lua/Vm/Fn/FmodTest.lean` (machine `F` = `SfRef.fmod` = model on 7,600 pairs). `DivSpec` discharged at the sf4/sf5 integration: it was unsatisfiable as stated (its `Fm` could not depend on the caller's frame, which `__divdf3` stores), and is replaced by the call node `Divdf3.sum_div` (`Lua/Vm/Fn/DivSum.lean`: `Divdf3.sum` with `spec_proved`; the caller's memory functions take `g`). The `fmod` wrapper and its call node: lane F1-F7 (row below). Open: `pow` (forecast in `abstractions/ledger/float-sf5.md`) |
| Lane float-sf6: libm `__ieee754_sqrt` and `pow` on the `SfRef` route | `scripts/gen_lua_fn.py` (tail nodes `TAILS`, `CALLEES_FOR` (`F64`-valued callee summaries), `val_g`, `CYC_SPLIT`, outer callees, wide windows `fn_sp_factsW`), `Lua/Vm/Sim/Kit/FnTail.lean`, `Lua/Vm/Fn/FSum.lean`, `Lua/Num/SfRefSqrt.lean`, `Lua/Vm/Fn/{Ieee754Sqrt{,/Defs,/L0,/L1},SqrtLoop,SqrtLoop1,SqrtLoop2,SqrtNorm,SqrtSpec}.lean`, `Lua/Vm/Fn/{Fabs,Finite,WithErrno,Xflow,MathOflow,MathUflow,Scalbn,Pow,PowR}.lean`, `Lua/Vm/Fn/Ieee754Pow{,/Defs,/L0..L6}.lean` | A6/Float | **`__ieee754_sqrt` proved** at (a) and (b): `Ieee754Sqrt.sum` (53 nodes, 4 cycles), `SfRef.sqrt_eq : SfRef.sqrt = F64.sqrt` ((b2), correctly rounded), `F_eq_ref`/`spec_proved : F = F64.sqrt` ((b1)), `spec_model : F = Float.Model.sqrt`, `sum_ref` (no premise); `Ieee754Sqrt` in `gen_lua_at.py` `FPROVED`. **`pow`, level (a) proved**: `Pow.sum` (wrapper, `errno` stores), `Ieee754Pow.sum` (247 nodes, 320 segments, tail jumps to `__ieee754_sqrt`/`__math_oflow`/`__math_uflow`), `Scalbn.sum`, `Fabs.sum`, `Finite.sum`, `WithErrno.sum`, `Xflow.sum`, `MathOflow.sum`, `MathUflow.sum`. **Level (b)**: `Unorddf2.spec_proved` (in `FPROVED`); the wrapper `PowR.model : Ieee754PowModel → … → toModel (Pow.F …) = Lua.Num.pow …` (`w_pow.c`); **open**: `PowR.Ieee754PowSpec_Statement` (`Ieee754Pow.F` = the canonical datum of `Lua.Num.Pow.ieee754Pow` on quiet operands; lane F1-21 stated it in bits, since an arm stores the result's sign bit; its model form `Ieee754PowModel` by `PowQ.powModel_of`; evidence `Lua/Vm/Fn/PowTest.lean`, 16,900 pairs, the bits exact). `FCALLS` untouched: the POW/POWK call nodes are an arm lane's. Ledger `abstractions/ledger/float-sf6.md` |
| Lane F1-F5: `FloorSpec` discharged; MUL and MULK on the join route | `scripts/gen_lua_at.py` (`PREMISE_PROOF`, `Floor` in `FPROVED`, `__muldf3` in `FCALLS`, `OP_MUL`/`OP_MULK`), `scripts/gen_lua_arms.py` (`__muldf3` in `FLOAT_CALLS`, MUL/MULK in `FLOAT_ARMS`), `Lua/Vm/Sim/Kit/{AtJoinMul,AtFltMul,AtFltMulk}.lean`, `Lua/Vm/At/{Mul,Mulk}.lean`, the float at-files regenerated | A6/Float | **proved**: `FloatArms.floor` removed (the generated at-lemmas pass `Lua.Vm.Sim.floorSpec_proved`; the f2i, bitwise and shift arms no longer take `FloorSpec`); `sim_MUL_flt`, `sim_MULK_flt` (`at_jarith`/`at_jarithK` with the stored-float rule of `Kit/AtJoinMul.lean`: `Muldf3.S`, `F64.mul_eq_model`, `model_mul_comm`), joined into `armTable`; `EqiFlt_Statement` proved (`eqiFlt_proved`, `Kit/FltEqi.lean`: `F2Ieq` against an 8-bit immediate is `==` with it, on words: `eq_cls`, `cls_inj`, `floor_cls`, `ofInt_exact`, the 256 immediates decided by `ImmFacts`), so the `EQI` field is gone. Ledger `abstractions/ledger/f1-lane-F5.md` |
| Lane F4: `EQ`, `EQK` with a float operand, through `luaV_equalobj`'s float summary | `Lua/Vm/Sim/Kit/{AtFnFlt,EqualobjF,AtEqF,AtFltEq}.lean`, `Lua/Vm/AtF/Eqobj{FF,IF,FI}.lean`, `Lua/Vm/At/{EqF,EqkF}.lean`, `scripts/gen_lua_at.py` (`--fn` specs with `float=True`: soft-float call nodes; `OP_EQ_F`, `OP_EQK_F`), `scripts/gen_lua_arms.py` (`luaV_equalobj`'s float paths as segments) | A6/Float | **proved** (`floor` by `floorSpec_proved`, passed on the callee route by `PREMISE_PROOF`): `Kit.equalobj_flt_sum` (`luaV_equalobj` on two represented values, one a float: `a0` is `Value.rawEq`'s 0/1, the memory `eqfMem`, changed only in `[sp - 160, sp)`), from the callee-context at-lemmas of its three float classes (`eqo_ff`, `eqo_if`, `eqo_fi`: `fat_walk`, leaves by `eqf_res`) and `eqo_diff_gen`; `At.sim_EQ_flt`, `At.sim_EQK_flt` (the summary a call node, `eqf_at`). Joined into `armTable`; ledger `abstractions/ledger/f1-lane-F4.md` |
| Lane float-sf4: `__divdf3` on the `SfRef` route | `scripts/gen_lua_fn.py` (`JUMPS`: jump-table nodes; `saves`: callee-saved registers spilled mid-body; `Callee.clobbers`), `scripts/gen_lua_arms.py` (`__divdf3` in `FN_HELPERS`, `FN_ROOTS`, `PASS_THROUGH_FOR`; `__umoddi3` from its entry), `Lua/Vm/Sim/Kit/{FnCall,Umoddi3}.lean`, `Lua/Vm/Fn/Divdf3*`, `Lua/Num/SfRefDiv.lean`, `Lua/Vm/Fn/SfRefDiv.lean` | A6/Float | **proved** at both levels: `Divdf3.sum` (level (a): 77 nodes over 140 segments; `__udivdi3`/`__umoddi3` call nodes on every divisor, `udivdi3_sumT`/`umoddi3_sum`, so no path facts; the two class-switch jump tables as nodes cased on the index the bound check fixes, one declaration per entry, `fn_jt_tgt` reading `.rodata`; `s0`-`s3` saved and reassigned as live registers with save-slot facts, `fn_sv_ld`), `SfRef.div_eq` ((b2): `_FP_DIV`/`_FP_DIV_MEAT_1_udiv_norm`/`__udiv_qrnnd_c` = `F64.div`: Knuth D `udivQrnnd_eq`, the remainder sticky bit `jam` and W1 for a quotient `round_jam`, `round_refine` (a quotient's rounding depends only on its rational)), `Divdf3.F_eq_ref` ((b1): pack `g_pack`/`g_e22c`, low and high digits `g_e1c4`/`g_e178` by the machine's corrections `qr_fix_m`, the divide `g_e114`, 25 class-pair chambers from `sdc_chambers`), `Divdf3.spec_proved : F = F64.div` (`Lua/Vm/Fn/SfRefDiv.lean`). Evidence: `Lua/Vm/Fn/DivTest.lean` (10,356 pairs: machine `F` = `SfRef.div` = `F64.div` = host). In `gen_lua_at.py`'s `FPROVED`/`FCALLS` since lane F1-F6 (row below). Ledger `abstractions/ledger/float-sf4.md` |
| Lane F1-F6: DIV, DIVK, and IDIV's and IDIVK's float paths on the join route | `scripts/gen_lua_at.py` (`__divdf3` in `FCALLS`/`FPROVED`; `FRAME_G`: a frame over the caller's saved registers; `FCALL_ARM`: an arm's own call node; `OP_DIV`, `OP_DIVK`, `OP_IDIV_F`, `OP_IDIVK_F`), `scripts/gen_lua_arms.py` (`__divdf3` in `FLOAT_CALLS`; the four arms in `FLOAT_ARMS`; DIV, DIVK in `EXTRA_ARMS`), `Lua/Vm/Sim/Kit/{AtFloat,AtJoinDiv,AtFltDiv,AtFltDivk,AtFltIdiv,AtFltIdivk}.lean`, `Lua/Vm/Fn/FloorR.lean`, `Lua/Vm/At/{Div,Divk,IdivF,IdivkF}.lean`, the float at-files regenerated | A6/Float | **proved**: `sim_DIV`, `sim_DIVK` (`SimArm`: every operand class, `at_jarithA`/`at_jarithAK`), `sim_IDIV_flt`, `sim_IDIVK_flt` (`at_jarith`/`at_jarithK`), joined into `armTable`, their four `FloatArms` fields removed. `__divdf3`'s frame stores the caller's `s0`-`s3`, so its call node uses `divdf3_sumG` (the frame over `frame4` of the row's registers; `divdf3_Fm_frame4` by `rfl`). `luai_numidiv` stores `floor`'s result, whose bits `FloorSpec`'s chosen function does not fix: IDIV's call node is `FloorR` (the reference `SfRef.floor`, `Floor.sum_ref`; `FloorR.S_bits`: its bits are the canonical datum of `Lua.Num.floor`). Ledger `abstractions/ledger/f1-lane-F6.md` |
| Lane F1-F7: libm `fmod`, and MOD's and MODK's float paths on the join route | `scripts/gen_lua_fn.py` (`__unorddf2`, `__errno` (`LEAF_MF`), `fmod`: prologue saves `PRO_SAVES`, callee frames from the current registers (`call_g`), node facts `FACTS`, the store outside the frame `OUTER`, constant propagation), `Lua/Vm/Fn/{Unorddf2,Errno,ErrnoR,FmodW,FmodR}.lean`, `Lua/Vm/Sim/Kit/{FnOuter,Errno,AtErrno,AtFmod,AtJoinMod,AtFltMod,AtFltModk}.lean`, `Lua/Vm/Sim/Rel.lean` (`ErrnoW`, `ExitFree`), `scripts/gen_lua_at.py` (`OP_MOD_F`, `OP_MODK_F`, `FCALL_ARM` `FmodR`, `FRAME_FN`, `FARGS`, `FSP`, `FOUTER`, `AtFinE` fin lemmas), `scripts/gen_lua_arms.py` (`fmod` in `FLOAT_CALLS`, MOD/MODK in `FLOAT_ARMS`, `FLOAT_CALL_KEEP`), `Lua/Vm/At/{ModF,ModkF}.lean` | A6/Float | **proved**: `FmodW.sum` (level (a): 9 nodes, call nodes `__ieee754_fmod` (`sum_ref`), `__eqdf2`, `__unorddf2`, `__errno`, `__divdf3`; the `errno` store a second patch window), `FmodR.F_eq : FmodW.F = SfRef.fmod` (on `y = ±0` both are the canonical NaN), `FmodR.model` (`= Lua.Num.fmod` on the model), `FmodR.S_bits` (the stored bits are `Lua.Num.fmod`'s canonical datum); `Complement.errno` (the complement after an `errno` store, from the `CALL` invariant's footprints; `exit` finds `errno` free: `ErrnoW ⊆ ExitFree`), `AtFinE.close`, `sim_arm_onE`; `sim_MOD_flt`, `sim_MODK_flt` (one declaration per (float operand, the other's class), `mod_flt_arm`/`modk_flt_arm`), joined into `armTable`, the `MOD`/`MODK` fields of `FloatArms` removed. `luai_nummod` calls `fmod` with `y = 0` for `x % 0.0` (NaN, no error): that path stores `errno`, so its relation is at the pointers after the store (`RelPtrs.errno`). Ledger `abstractions/ledger/f1-lane-F7.md` |
| Lane F1-21: POW and POWK on the join route | `scripts/gen_lua_arms.py` (POW/POWK in `EXTRA_ARMS`, `STANDALONE`: their segment modules outside the index `Lua/Vm/Arms.lean`; `pow` in `FLOAT_CALLS`, `FLOAT_CALL_KEEP`), `scripts/gen_lua_at.py` (`OP_POW`, `OP_POWK`; `PowQ` in `FCALL_ARM`, `FRAME_G`, `FRAME_FN`, `FOUTER`; `FRAME_F`: a value over the frame; `FSPEC_HYP`: a conditional level (b)), `Lua/Vm/Fn/{PowR,PowQ}.lean`, `Lua/Vm/Sim/Kit/{AtPow,AtJoinPow,AtFltPow,AtFltPowk}.lean`, `Lua/Vm/At/{Pow,Powk}.lean`, `Lua/Vm/Arms/{Segs/XPOW,Segs/XPOWK,Sites/SXPOW,Sites/SXPOWK}.lean` | A6/Float | **proved on quiet operands, given `Ieee754PowSpec_Statement`**: `At.sim_POW : Ieee754PowSpec_Statement → SimArmOnM .POW PowQuiet`, `At.sim_POWK : … → SimArmOnM .POWK PowKQuiet` (every operand class: `luai_numpow`'s `__eqdf2(b, 2.0)`, `__muldf3(a, a)` or libm `pow` by `PowQ.spec`, its `errno` stores by `AtFinE`); `SimArmOnM` (a path family over the machine's memory: `SimArmOnM.split`, `At.sim_arm_onEM`); `PowQ.notSNaN_toBits`, `wrap_bits`. **Obstruction**: `NotSNaN` is not dischargeable from the relation (`ValRepr.flt`, `Rel.lean`, holds of every bit pattern; `Core.kconst`), so `FloatArms.POW`/`POWK` are the signalling-NaN states, false as stated (`pow(sNaN, 0)` is NaN on the ELF, `1` in the kernel). Ledger `abstractions/ledger/f1-lane-21.md` |
| Lane F1-22: float payloads quiet in the relation; `FloatArms.POW`/`POWK` closed | `Lua/Vm/Sim/{Quiet,Rel,Close,Entry}.lean`, `Lua/Vm/Sim/Kit/{FltVal,FltNeg,AtJoin,AtJoinOps,AtJoinPow,CallClose}.lean`, `Lua/Vm/Fn/PowQ.lean`, `Lua/Vm/Sim/Fold.lean` | A6/Float | **proved**: `ValRepr.flt` takes `isSNaN x = false` (`Lua.Bytecode.isSNaN`, the test `Const.toValue?` makes); its sources: a model datum's bits (`isSNaN_toBits`, in `ValRepr.ofFloat_of`: every stored result and conversion), a sign flip (`isSNaN_xor_sign`, `ValRepr.flt_neg`), a copy of an entry payload (`ValRepr.flt_lit` by the tactic `at_quiet`: the read register's `ValRepr`, `ValRepr.quiet`/`quiet_of_tag`), a constant (`ConstRepr.valRepr`: `Const.toValue?` has no value for an sNaN), a transfer (`ValRepr.transfer`); `isSNaN_eq_false_iff` bridges to `PowR.NotSNaN`. `powQuiet_of`, `powKQuiet_of` (`Kit/AtJoinPow.lean`): every related state that steps has quiet operands, so `SimArmOnM.of_all` gives `SimArm .POW`/`.POWK` from `At.sim_POW`/`sim_POWK`; `FloatArms.POW`, `POWK` and `SimArmOnM.split` deleted. Statement change: none to `vm_refinement_Statement`'s hypotheses (constants were already quiet by `Const.toValue?`; no boot check needed); `FloatArms` lost its two false fields. Ledger `abstractions/ledger/f1-lane-22.md` |
| Lane float-sf7: `__ieee754_pow` at level (b) | `Lua/Vm/Fn/{PowAttr,PowStage,PowLens,PowLeaves,PowFacts,ScalbnSpec,PowExp,PowLog,PowSpecial,PowYi,PowSpec}.lean`, `scripts/gen_pow_rod.py` → `Lua/Vm/Fn/PowRod.lean` (generated), `scripts/gen_lua_fn.py` (`FORWARD`: `__ieee754_pow`, `scalbn`) | A6/Float | **`PowR.Ieee754PowSpec_Statement` proved** (`Ieee754Pow.spec_proved`, `Lua/Vm/Fn/PowSpec.lean`): on quiet operands the lifted `Ieee754Pow.F` is the canonical datum of `Lua.Num.Pow.ieee754Pow`. The machine's fork tree is walked beside the model (`pw_walk`: machine lens, model lens `pw_mlens`, generalisation of the values both compute, the model's `if`s decided by the machine's split facts, cuts at joins) over the stages of `PowStage.lean` (`ieee754Pow_stage : ieee754Pow = powTop`, `log2Exp_eq`, `exp2Tail_split`), one lemma per join (35, each `pw_walk using [cuts]`); per-amount shifts by the chamber generator `pw_chambers` (`n_cf98`: `exp2`'s `n`, 12 chambers; `e_c580`: `yisint`, 53 chambers); `scalbn` (`Scalbn.F_model`), `__math_oflow`/`__math_uflow`, `fabs`, `__floatsidf` as lens rules; NaN operands of any quiet payload by their words (`F_nan_*`, `W_ofInt_nan`). `FloatArms.pow_spec` discharged (`Fold.lean`). Ledger `abstractions/ledger/float-sf7.md` |
| Layer B with floats (S3-minimal) | `Lua/Ast/Semantics.lean`, `Lua/Compile/Corpus.lean` | B/Float | **done for the operators and `for`** (lane float-s1): `LuaSem`'s operators are Lua's value operations shared with `δ` (`Value.arith`, `δ .lt`/`.le`/`.concat`/`.unm`/`.bnot`/`.len`, `Value.rawEq`), its numeric `for` has `forlimit`'s coercion and the float loop (`forIterF`); the three former escapes are corpus pairs (`escStrflt_tv`, `escForstr_tv`, `escUnmflt_tv`, `compile_refinement_corpus`). **S3 done** (lane B-S3): float numerals (one rulebook arm, `Const.toValue?` of the parsed bits; the parser's numerals checked against `Lua.Num.str2number` by `LexOk` over the generated `…AstNumerals`, `corpus_lexOk`), `/` and `^` (through `Value.arith`) in `AstSupported`, except a `^` `luac` may constant-fold (`powOk`: both operands `mayFold`, exponent not the numeral `2`), since `luac` folds `^` with the host's glibc `pow` and the ELF's is newlib's: `powFold_counterexample` (`c/tests/fold/powfold.lua`: `0.5 ^ -0.5`, `K` = `0x3ff6a09e667f3bcd`, newlib `…bcc`; Sail prints `false`, `LuaSem` `true`), `powFold_kfold`, `powFold_not_astSupported`. Every float constant of a corpus chunk is the model's (`KAccounted`: a numeral or `lcode.c`'s `constfolding` on `Lua.Num`, `corpus_kAccounted`, `Lua/Compile/Consts.lean`). Corpus: `f3_float.lua`, `f3_floop.lua` (`f3Float_tv`, `f3Floop_tv`) |
| Float S0a: an exact binary64 library equal to `Float.Model` (δ's float spec, `abstractions/FLOAT-DESIGN.md` §1) | `Lua/Num/F64.lean`, `Lua/Num/Arith.lean` | Float | **proved** (lane float-s0a, `abstractions/ledger/float-s0a.md`): `F64` over `BitVec 64` with closed-form rounding; bit-equal to the model, NaN included: `ofInt_eq_model`, `add_eq_model`, `sub_eq_model`, `mul_eq_model`, `div_eq_model`, `sqrt_eq_model`, `compare_eq_model` (`lt`/`le`/`eq`), `neg_eq_model` (off NaN: Lua's `neg` flips a NaN's sign, the model's does not); sanity lemmas `add_comm`, `mul_comm`, `neg_neg`, `compare_swap`, `trichotomy`, `lt_irrefl`, `ofInt_exact`. `Lua/Num/Arith.lean` defines over the model what it lacks: `floor`, `fmod`, `numberToInteger`, `flttointeger` (F2I modes), `numidiv`, `nummod`. Evidence: `Lua/Num/F64Test.lean` (host `Float` on ~10⁵ vectors, host `math.fmod` on 6,844, the ELF on Sail on 428 lines, `c/tests/float/`); the canonical NaN `0x7ff8000000000000` checked on the ELF. Open: `F64` versions of `floor`/`fmod` and their equalities |
| Float S0b: the decimal side (`l_str2int`, `l_str2d`/`strtod`/`gethex`, `luaO_str2num`, `%.14g`, `tostringbuff`) over core `Float.Model` | `Lua/Num/Decimal.lean`, `Lua/Num/DecimalBridge.lean`, `Lua/Num/DecimalFacts.lean` | Float | **defined and validated** (lane float-s0b, `abstractions/ledger/float-s0b.md`): `str2int`, `str2d`, `str2number`, `fmt14g`, `tostringbuff`; decimal rounding is `Float.Model.ofScientific`, hex floats transcribe newlib `gethex` including its three measured deviations from correct rounding (`gethex_sticky`, `gethex_subnormal`, `gethex_wrap`); NaN sign explicit (`nanNeg`). One `str2int`: `str2int_bytecode`, `str2int_ast` **proved** (the semantics' copies equal it; S1 swaps them). Evidence, not proof: `c/tests/float/run.sh` (Lean = ELF on Sail on every vector). Machine side (`_dtoa_r`, `_strtod_l` as `G14From`/`Str2dFrom`) open (M0); `G14From` needs `_malloc_r` (now `mallocR_proved`, lane F1-A0-M; not started): every finite non-zero value reaches `__d2b` → `_Balloc` → `_calloc_r` → `_malloc_r` (the reent freelist's first use), so `_dtoa_r`'s fast paths allocate too (lane F1-FMT; the `%.14g` path of `_svfprintf_r` is a second `--fn` spec over the same generator over `mallocR_proved`). Lane F1-18: not started; the float class is the whole-call `PrintFlt_Statement`: `_dtoa_r` frees `_REENT->_result` on entry (`_Bfree`, `ld a1,80(a0)`) and `_Balloc` pops `_REENT->_freelist[k]` (`ld a5,104(a0)`; `_calloc_r(_REENT, 8, 65)` the first time), so `G14From` needs those lists' bignums as an invariant (in chunks in use, apart from what `print`'s caller keeps, `k`/`maxwds` consistent), which neither `PrintIn` nor `CallInv` carries; zero returns `"0"` before any `_Balloc` (`__eqdf2` at `0x8004a814`) |
| `sim_{MOD,MODK,IDIV,IDIVK,EQ,EQK}_Statement` (`SimArm o`, `sim_ADD`'s shape; the round-3 bake-off targets) | `Lua/Vm/Sim/Rel.lean` | A1 | `sim_MOD_Statement` proved on the KIT branch (`Lua.Vm.Sim.Kit.sim_MOD`, with `sim_MUL`); `sim_MODK_Statement` proved (`Kit.sim_MODK`, with `Kit.sim_MULK`; kit lane 1, `abstractions/ledger/kit-arms-1.md`); `sim_EQ_Statement` proved (`Kit.sim_EQ`: `Kit.eq_long` closes `Kit.sim_EQ_of_long` through `luaS_eqlngstr`/`memcmp` summaries on BASE-S's owned strings; round-4 S-SCAN, `abstractions/bakeoff4/S-SCAN.md`); `sim_EQK_Statement` proved (`At.sim_EQK`, `Lua/Vm/Sim/Kit/AtStr.lean`: `Kit.eqk_short`, and the two-long-string path on the location-list route through the call node `At.lngeq_sum` over `Kit.eqo_long_ex`, `luaV_equalobj`'s exact return memory; lane F1-2, `abstractions/ledger/f1-lane-2.md`); the others open |
| `SimArm .LT`, `SimArm .LE` on two strings (the premise of `Kit.sim_LT_of_str`, `Kit.sim_LE_of_str`; integers and the stuck cases proved: `lt_int`, `lt_stuck`, `le_int`, `le_stuck`) | `Lua/Vm/Sim/Kit/{Lt,Le,AtStr}.lean` | A1 | **proved** on the location-list route (`At.sim_LT`, `At.sim_LE`; lane F1-2): the call node `At.lstr_sum` (`Kit.lstrcmp_sum`, now with the observation `Kit.LsObs`: zero iff equal, a sign-extended answer, `LsObs.le` for `slti 1`) fused with its observing instruction (`At.obs_lt`, `At.obs_le`), `docondjump` in the generated at-lemmas (`Lua/Vm/At/{Lt,Le}.lean`); `lt_str_take` costs 14k heartbeats (the kit's 200.3k; the kit's `LtStr` is retired) |
| `SimArm .LEN` (a string `R[B]`; `δ .len` has no other F1 value) | `Lua/Vm/Sim/Kit/{Objlen,AtStr}.lean` | A1 | **proved** (`At.sim_LEN`; lane F1-2): `luaV_objlen`'s string summary `Kit.objlen_sum` (exact memory `olMem`), the call node `At.len_sum`, the arm's segments emitted apart (`gen_lua_arms.py` `EXTRA_ARMS`), `Lua/Vm/At/Len.lean` |
| `SimArm .GETTABUP` (`_ENV.print` only) | `Lua/Vm/Sim/Kit/{AtGettabup,AtEnv,Getshortstr}.lean`, `Lua/Vm/Sim/Env.lean`, `Lua/Vm/At/Gettabup.lean` | A1 | **proved** (lane F1-7, `abstractions/ledger/f1-lane-7.md`): `At.sim_GETTABUP`, on the at-lemma route. The three pieces of lane F1-2's obstruction: (1) `VmEntryData.env_get` (`EnvGetAt`): `luaH_getshortstr`'s chain from the print key's main position reaches `print`'s node (`shrWalk`, fuel `2^lsizenode`), and `_ENV`'s objects lie in the heap apart from the window (`HeapApart`), in every memory agreeing off `luaT_adjustvarargs`'s stores; checked by `envGetCheck` in `entryCheck` and natively by the boot generator, both witnesses re-checked; (2) the closure in the relation, additively: `Core.clptr` (`8(sp)`; `CFrame` now starts at `16(sp)`) and `Complement.env` (`EnvMem` over `HeapRead` regions, re-established at the entry and after `VARARGPREP` by `relParts`); (3) `getshortstr_sum` (`seg_loop` over the walk's fuel), the call node `gss_at` |
| `SimArm .FORPREP` | — | A1 | open (lane KIT-2 stopped at the gate): `luaV_tointeger`'s integer summary `Kit.toint_sum` and the C-frame close `Core.bleachF` are proved; the arm's run (8 segments, two call nodes) exceeds the default heartbeat budget in one declaration and needs a split at the call with an abstract mid-state memory (`abstractions/ledger/kit-arms-2.md`) |
| `SimArm .IDIVK` (`sim_IDIVK_Statement`) | `Lua/Vm/Sim/Kit/AtIdivk.lean` | A1 | **proved** (`At.sim_IDIVK`, the at-lemma route; lane F1-1, `abstractions/ledger/f1-lane-1.md`) |
| `SimArm` of SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK | `Lua/Vm/Sim/Kit/At{Shl,Shr,Shli,Shri,Bandk,Bork,Bxork}.lean` | A1 | **proved** (`At.sim_SHL`, …, `At.sim_BXORK`; `luaV_shiftl` per machine branch in `Kit/Shift.lean`; lane F1-1) |
| `UnmStr_Statement` (`OP_UNM` on a string: `luaT_trybinTM` and the string library's `__unm`; the premise of `At.sim_UNM_of_str`) | `Lua/Vm/Sim/Kit/AtUnm.lean` | A1 (with the `MMBIN`/`CALL` runtime summaries) | open; the integer path (`At.unm_int`) and the stuck values (`At.unm_stuck`) proved |
| the console end of `print`'s stdio chain (toward `SimArm .CALL`, still an `OpenArms` field) | `Lua/Vm/Sim/Kit/{Console,Write,Swrite,Sflush}.lean` | A0.2 | **proved** (lane F1-6, `abstractions/ledger/f1-lane-6.md`): the `tohost` seam `segSt_putc` (the `SegSt` face of `Console.putc_runFact`), htif.c's `_write` on the console (`write_sum`: `seg_loop` over the `htif_putc` loop), `_write_r` (`write_r_sum`), `__swrite` (`swrite_sum`, an `sh`), and `__sflush_r` on the line-buffered `stdout` (`sflush_sum`: the pending bytes through the `FILE`'s hook, an indirect `jalr`); `StdoutAt` is `stdout`'s state as the emulator trace shows it after the first `print` (`_flags = 0x2889`, a 1024-byte heap buffer, `_w = -|pend|`) |
| `FwriteStdout_Statement` (`fwrite(src, 1, n, stdout)` on `StdoutAt`: `__sfvwrite_r`'s line-buffered branch, `memchr`, `memmove`, `_fflush_r`; the callees' stack within 4 KiB below `sp`, `StdoutKeepD`) | `Lua/Vm/Sim/Kit/CallSpec.lean` | A0.2 | **proved** (lane F1-9: `Kit.fwrite_stdout`, `Lua/Vm/Sim/Kit/Sfvwrite.lean`, from `Kit.fwrite_stdout_of_sfv` (lane F1-8) and `sfvwrite_lbf`; `abstractions/ledger/f1-lane-9.md`) |
| `SfvwriteLbf_Statement` (`__sfvwrite_r(_REENT, stdout, uio)`, one iov, on the set-up line-buffered `stdout`: `0` returned, `out ++ pend' = pend ++ bytes`, `SfvKeep`) | `Lua/Vm/Sim/Kit/Fwrite.lean` | A0.2 | **proved** (lane F1-9: `Kit.sfvwrite_lbf`, `Lua/Vm/Sim/Kit/Sfvwrite.lean`): `seg_loop` on `2·len + [buffer full]` over the generated at-lemmas (`Lua/Vm/AtF/Sfvwrite.lean`, 51; roots: the entry, the loop head `L`, the body `D`, the step size `S`, the newline distance `N`, the tail `T`, and the call returns), one splice per callee (`sfv_mc`: `memchr_nl`; `sfv_move`: `memmove_sum`; `sfv_swrite`: `swrite_sum`; `sfv_flush`: `fflush_r_stdout`). `StdoutAt` became `StdoutAtW` with `_w` a parameter and a full buffer allowed (a copy can fill it exactly; the fill path flushes before `_w` is restored) |
| `FflushStdout_Statement` (`fflush(stdout)`: the lock no-ops around `__sflush_r`) | `Lua/Vm/Sim/Kit/Fflush.lean` | A0.2 | **proved** (lane F1-8: `Kit.fflush_stdout`, its 16 at-lemmas generated on the callee-context route; the frame shared with `_fflush_r` is `sfl_mid32`/`flush_fin`) |
| callee-context rows (the at-lemma route for C callees: rows over `FCx`, roots at the entry, loop heads and call returns) | `Lua/Vm/Sim/Kit/AtFn.lean`, `scripts/gen_lua_at.py --fn`, `Lua/Vm/AtF/*.lean` | A1 | **landed** (lane F1-8): `fflush`, `_fflush_r`, `memmove`, `memchr`, `__sfvwrite_r` generated (`FNS`), the summaries `fat_run` over them |
| `StdoutSetup_Statement` (the first `fwrite(src, 1, n, stdout)`, `n ≥ 1`, from `StdioBoot`/`MemfsBoot` and the heap with room for the buffer: `__sinit`, `ORIENT`, `__sfvwrite_r`'s `cantwrite` → `__swsetup_r` → `__smakebuf_r` → `_fstat_r` (`fs_init`, `memset`), `_malloc_r`, `_isatty_r`; then the line-buffered loop; post `SetupPost`) | `Lua/Vm/Sim/Kit/StdoutSetup.lean` | A0.2 | **proved from `MallocR_Statement`** (lane F1-10: `Kit.stdoutSetup_of_malloc`; the callees `sinit_boot`, `fstat_sum`, `isatty_sum`, `smakebuf_sum`, `swsetup_sum`, `sfvwrite_first`, each over generated at-lemmas, `abstractions/ledger/f1-lane-10.md`). Lane F1-11: the boot facts and the heap stated of the zero fill (`StdioBoot (fillZeroMem m)`, `HeapAt (fillZeroMem m)`: `VmRel` holds memory only totally); the source `SrcLo` (`.rodata` literals shorter than the buffer allowed); the other first writes proved: an empty one from boot (`fwrite_boot0`), from the stream `__sinit` left (`fwrite_fresh0`, `stdoutSetup_fresh`), all five cases as one write from any phase, `Kit.fwrite_print` (`Kit/{StdoutEmpty,PrintIO}.lean`) |
| `MallocR_Statement` (`_malloc_r(_REENT, n)` with room for one `_sbrk`: a fresh 16-aligned block of a chunk in use, `HeapAt` again, the chunks in use kept, the break bounded (`brk_le`, `brk_hi`), writes only `MallocGlobal`, the arena off the chunks in use and 1 KiB of stack) | `Lua/Vm/Sim/Kit/Malloc.lean`, `Lua/Vm/Sim/Kit/AllocProof.lean` | A0 | **proved** (lane F1-A0-M: `AllocProof.mallocR_proved`, ledger `abstractions/ledger/f1-lane-A0-M.md`). ship-your-interpreter's dlmalloc proof ported to the Lua ELF (`VsaIris/Vsa/{Heap,Malloc,Free}*.lean`, `Sbrk`, `AllocTac`, `AllocKit`, `Vsa/Sim/DlHeap.lean`; relocated by `experiments/port/alloc/reloc.py`: pcs by instruction alignment, data by symbol + offset; `_malloc_r` is the WHILE code but for two `auipc` (`__malloc_current_mallinfo` out of `gp` range), `_malloc_trim_r` for three, `_free_r`/`_realloc_r` identical) over the step tables; the break bound (`MBrk`, one growth by `sbReq`) and a precise `Starved` threaded through; `_sbrk`'s failure refuted from the caller's room (`MOK.room`), so `__errno` is off the table (`gen_alloc_steps.py` `CUT`). The run lands on the Lua route by `LocalRun.reach` (`VsaIris/Vsa/SWPReach.lean`: exact frames, from `MachineModel.pres`/`quiet`, `LocalStep.pres_frame`), the heap shapes by `AllocHeap.heapV`/`heapL`. Statement corrections: `HeapAt` gains `brk_page`, `top_room`, `bb_lt` (boot-checked), `MallocGlobal`/`AllocWords` are the proof's footprint (`_REENT->_errno`, `__malloc_trim_threshold`, `__malloc_top_pad`); `brk_hi` checked on Sail (246 calls, growth − n ≤ 4096) |
| `luaB_print` (`print`'s body: `lua_gettop`, per argument `luaL_tolstring`, the tab, the string, `lua_pop`; the newline, `fflush`) | `Lua/Vm/Sim/Kit/PrintSum.lean`, `Lua/Vm/AtF/Print.lean` | A1 | **proved over named premises** (lane F1-11: `Kit.print_sum : MallocR_Statement → PrintLua … → Triple …`; every phase of `stdout`, `print("")` included; the loop by `seg_loop`). `PrintLua` is the Lua side, over an abstract invariant `S`: `lua_gettop` (proved as `gettop_sum` on `ApiAt`), `lua_settop(L, -2)` (proved as `settop_pop_sum`), `luaL_tolstring` per value class (**open**: `PrintLua.tolstring`/`TolPost`, the per-class work: string → `luaL_callmeta` with the string metatable, `lua_pushvalue`; nil/booleans → `lua_pushstring` of an interned literal; integers → `lua_pushfstring` (`IntegerToStr_Statement`, proved: `integerToStr_proved`), floats → `%f` (`G14From`)), and `S`'s stability under a write (`PrintLua.stable`). Lane F1-12: `S` concrete (`PrS`, `Kit/PrintS.lean`: the C function's API frame, the bytes it reads kept in chunks in use apart from `stdout`'s buffer, the arguments' predicate); `printLua_of` proves `PrintLua`'s `gettop`, `settop` and `stable` for it, `luaL_tolstring` per argument its premise. `luaL_tolstring` on **nil, `true`, `false` proved over `lua_pushstring`'s summary** (`tol_nil`, `tol_true`, `tol_false`, `Kit/Tolstring.lean`, through `lua_absindex`, `luaL_callmeta` → `lua_getmetatable`, `lua_type`, `lua_toboolean` on generated at-lemmas, and `toltop_sum` for the tail `lua_tolstring(L, -1, &l)`), its `TolPost` by `tolPost_of_lit`; strings, integers, floats and functions open |
| heap room for `CALL print` on an allocating value class (`HeapBudget_Statement`) | `Lua/Vm/Sim/Kit/CallArm.lean` | A8 | **named premise** (lane F1-12): `HeapBudget w args` is a hypothesis of `PrintCall_Statement` for the allocating classes only (`Allocates`: integers, floats, functions); `HeapBudget_Statement I` is the arm on the states without it (`luaM_malloc_` runs the emergency `luaC_fullgc`, which `LUA_GCSTOP` does not block); `sim_CALL_of` splits on it. Strings, nil and booleans need no budget. Lane F1-19: `HeapBudget` is a structure read from the complement: `brk` (the break `callBudget args` below `__heap_end`: one `_malloc_r` with its `_sbrk` room per argument (`argCost`) and per first-use allocation; the table-doubling term of lane F1-18, sized by the boot's `w.rt.strtSize`, is gone) and `strt` (`strtNuse w.mo g + newStrs args ≤ strtSize w.mo g`: `g->strt` has room for every new string, so `internshrstr` never runs `luaS_resize`). The table's growth (`luaS_resize` → `luaM_reallocvector` → `_realloc_r` of a live bucket array, the old block freed, every `u.hnext` rehashed) is therefore A8's, with the emergency collection; its truth there needs `_realloc_r` and, after the resize, the `CALL` invariant at the new array. **Removing `HeapBudget_Statement` needs the GC phase (A8)**: no room invariant on `VmRel` survives every reachable state (lane F1-11, obstacle 2) |
| `IntegerToStr_Statement` (`lua_integer2str` = `snprintf(buf, 44, "%lld", i)`, `_svfprintf_r`) | `Lua/Vm/Sim/Kit/CallSpec.lean`, `Lua/Vm/Sim/Kit/{IntFmt,IntFmtSum,IntFmtLoop,DecDigits,FmtLib}.lean`, `Lua/Vm/AtF/SnprintfLld` | A1 | **proved** (lane F1-FMT, `abstractions/ledger/f1-lane-FMT.md`): `integerToStr_proved`. Restated first: the buffer may lie above `sp` (`tostringbuff`'s caller's frame) and the static words `_svfprintf_r` reads are premises (`IntFmtIn`, `FmtStatic`: `_impure_ptr`, the locale's decimal point, `mbtowc`, `__mb_cur_max`, the conversion switch's two jump-table words). `_svfprintf_r` specialised to the format's bytes on the callee-context route (`gen_lua_at.py --fn snprintf/lld`, 278 at-lemmas in 8 parts); its roots composed by hand over named fact structures and region agreements (`snWk`, `snWd`); the digit loop by `seg_loop` over the quotient (`snp_loop`), the digits as `decBytes` (`Nat.toDigits`), the bytes `toString i.toInt` by `intBytes_eq` (`LUA_MININTEGER`'s magnitude `2 ^ 63` included) |
| `PushLit_Statement` (`lua_pushstring` of one of `luaL_tolstring`'s literals: `luaS_new` → the string cache's row (`strcmp` against its two candidates, `LitCache`/`CandOk`) or `internshrstr`'s bucket walk (`luaHash`, `ChainFirst`), no allocation, `luaC_checkGC` with the collector stopped) | `Lua/Vm/Sim/Kit/{Tolstring,PushLit,Intern,SNew,PushLitProof}.lean` | A1 | **proved** (lane F1-15: `pushLit_proved`). Restated: the literals frozen on a footprint off the string cache (`Frozen FL (LitsHold …)`, which `luaS_new` writes before `internshrstr` reads the table), the literal's string apart from the push's stores (`LitApart`), `PushCx` with room for the callees' frames, `L`/`g`/`top` apart and `top` aligned (`PrintIn.f_al`). Parts: `pushstring_sum` over `SNewSpec`; `snew_nil`/`snew_true`/`snew_false`/`snew_tos` (one tactic `snew_run` over the four generated `AtF/LuaSNew*` modules: `__umoddi3` (`umoddi3_sum`), `strcmp_sumS` with `cand_of_zero`, `strlen_sumS`, the row's shift `LitCache.shift`); `newlstr_sum`, `internshrstr_sum` (hash loop `int_hash` with `hstep_mach`/`hashFrom`, the bucket `bucket_addr`, the walk `int_chain` over `ChainAt` with `memcmp_sumS`, `isdead`'s `changewhite`); `luaC_step_sum`. Boot facts added (`EntryData`, checked by `Boot/Check`): `LitInterned.first` (`ChainFirst`), `LitCache`, `CandOk`, `LitsIn.{hash_lo,hash_hi,size_hi,lit_cands}` |
| `luaL_tolstring` on strings, integers, floats, functions | `Lua/Vm/Sim/Kit/Tolstring.lean` (to come) | A1 | open (lane F1-12): strings through `luaL_callmeta` with the string library's metatable (`lua_pushstring("__tostring")`, allocating on its first use, `lua_rawget` → `luaH_getshortstr`), `lua_pushvalue`; integers (`IntegerToStr_Statement`, proved: `integerToStr_proved`), floats (`G14From`) and functions (`"%s: %p"`) through `lua_pushfstring`, with `HeapBudget` |
| `luaD_precall` on a light C function (`precallC`: tag `LUA_VLCF`, `checkstackGCp` with room, `next_ci`, the C `CallInfo`, no call hook, `jalr` to the C function, `luaD_poscall`) | `Lua/Vm/Sim/Kit/Precall.lean`, `Lua/Vm/AtF/{Precall,PrecallExt}.lean` | A1 | **proved over its callees' summaries** (lane F1-12): `precall_join`, `precall_reuse` (`ci->next` reused), `precall_ext` (`ci->next` NULL: `luaE_extendCI`, the summary `PcExt`); the C function (`PcC`) and `luaD_poscall` (`PcPos`) are hypotheses. The stack-growth path (`L->stack_last - L->top ≤ LUA_MINSTACK`: `luaD_growstack`, `0x8000abe4`) is a stop of the generator, open |
| `PrintCall_Statement I` (`luaD_precall` on `print` from `OP_CALL`, in the relation's terms: back at `0x8001c7d8` with `0`, the line on the console, `CallOut` and the invariant `I` again) | `Lua/Vm/Sim/Kit/CallArm.lean`, `Lua/Vm/Sim/Kit/CallPrint.lean` | A1 | **proved for `I = CallInv` from `CallOpen`** (lane F1-13: `printCall_of : CallOpen → PrintCall_Statement CallInv`; `printCall_room` composes `precall_reuse`/`precall_ext` with one join `JoinIn` (`join_reuse`, `join_ext`), the C function (`call_pcc` over `PrintRel_Statement`), `luaD_poscall` (`call_pcpos`: `poscall_sum` with `C = 1`, `PoscallN_Statement` with `C ≥ 2`), the close (`call_close`); the stack growth by `PrintGrow_Statement`). Lane F1-12 listed its parts: its parts: `precall_reuse`/`precall_ext` (proved), `print_sum` (proved from `MallocR_Statement` and `PrintLua`), `poscall_sum` (`C = 1`, lane F1-4), `luaD_poscall` with `C ≥ 2` results (open: `HluaD_poscall`'s stop `0x8000a4d8`), `luaE_extendCI` (open), the growth path (open), the post-`print` `exit` (`ExitOk` of the new complement: open) and the relation facts below |
| `SimArm .CALL` from the arm on an invariant (`sim_CALL_of : PrintCall_Statement I → HeapBudget_Statement I → SimArmInv .CALL I`) | `Lua/Vm/Sim/Kit/CallArm.lean` | A1 | **proved** (lane F1-12): dispatch, `OP_CALL`'s sim segments (`L->top = ra + B`, `savepc`, the `jal`; generated with `luaD_precall` a call node whose arguments stay live, `gen_lua_arms.py` `CALL_ARGS`), the summary, the `beqz` on `0`, `updatetrap`, the jump to the head; the step by `call_step`; the relation at the summary's pointers (`CallOut`, `Ranges.after`). Lane F1-13: `Complement.call : CallInv p w` carries the invariant (row below), so `sim_CALL : PrintCall_Statement CallInv → HeapBudget_Statement CallInv → SimArm .CALL`; `OpenArms` holds `CALL_open : CallOpen` and `CALL_heap` |
| the `CALL` invariant in `Complement` (`CallInv`/`CallInvAt`, `Rel.lean`: `stdout`'s phase `StdoutIn` (boot with `StdioBoot`/`MemfsBoot`, after an empty write, set up with `StdoutAt`), the heap room before the first `print` or while `ci->next` is NULL, `__atexit = NULL`, the objects the arms read frozen on a footprint `F` (`Frozen F StatFacts`), the interned literals frozen on `FL`, both in chunks in use apart from what a `CALL` writes, the `lua_State`/`g`/`CallInfo`/stack in chunks in use, the C `CallInfo` `NciApart`) | `Lua/Vm/Sim/Rel.lean`, `Lua/Vm/EntryData.lean`, `Lua/Vm/Sim/StdioState.lean`, `Lua/Vm/Boot/Check.lean`, `Lua/Vm/Sim/Entry.lean` | A1 | **done** (lane F1-13): established at the entry and after `VARARGPREP` by `callInv_boot` from `VmEntryData`'s new fields, checked natively (`gen_lua_boot_witness.py`) and in the kernel (`EntryChecks`: `entryBaseCheck`, `frozenCheck`, `litsEntryCheck`, `placedCheck` over `RTree` footprints, `entryCheck_sound`; both witnesses rebuilt); preserved by every arm that keeps `w.mo` (the field is passed unchanged) and re-established after `CALL print` by `call_close` through ONE region lemma `Frozen.trans` (`StdioState.lean`) Lane F1-19: **what an allocating `print` must find apart** is the invariant's: `CallDirty`/`EntryDirty` gain `g->allgc` (`F` off `luaC_newobj`'s link); `CallInvAt.alloc : CallAlloc` (`CallAllocAt` at a region `B` of `_dtoa_r`'s bignums: the string table's chains readable and apart (`StrtSafe` with `X = CallX0 ∨ B`, `W = B`: every node short, its object in chunks in use and off `B`, its mark and `u.hnext` and the bucket array off what the caller keeps), frozen with the literals on `FL`; the bignums `ReentMp` frozen on `B ∪ ReentWord` (the free lists' classes, the last result's class, the `_p5s` cache's values `5^(4·2^j)`, every block apart, in `B`); `B` in chunks in use, off `CallX0`, `FL` and the literals' objects); `LuaStatic.mt_fn` (`G(L)->mt[LUA_TFUNCTION]` NULL) and `StatFacts.locale` (`LocaleWords`: `_impure_ptr` and the C locale's `.data` words `snprintf` reads), frozen on `F` (`stat_in` allows them, `PrintStatic` keeps them). Boot: `VmEntryData.strt_safe` (`strtSafeCheck` on `e.litFoot`, which now holds every chain node's `shrlen`), `mt_fn`, `locale`, `reent` (`ReentBoot`: `_result`, `_p5s`, `_freelist` NULL), one more `EntryChecks` field `strt`; both witnesses re-checked (`decide +kernel`). Re-established by `call_close` from `PrintOut` (`CloseIn.safe`/`big`, `callX0_after`), kept by the `errno` store (`Complement.errno`) | |
| `PrintRel_Statement` (`luaB_print` on the C frame from `PrintIn` to `PrintOut`: the API frame, the kept region `G`, the literals `LitsFoot`, `stdout`'s phase) | `Lua/Vm/Sim/Kit/{CallOpen,PrintRel}.lean` | A1 | **proved from per-class premises** (lane F1-15: `printRel_of`, `PushLit_Statement` now proved; lane F1-A0-M: `MallocR_Statement` is `mallocR_proved`; lane F1-17: `TolStr_Statement` is `tolStr_proved`; lane F1-18: `printRel_of : MallocR_Statement → PushLit_Statement → TolStr_Statement → TolInt_Statement → PrintFlt_Statement → PrintFn_Statement → PrintAllocOff_Statement → PrintRel_Statement`, so `CallOpen.print` (`Kit/TolStrProof.lean`) takes `tolInt`, `printFlt`, `printFn`, `allocOff`). Nil and booleans by `tolLit_proved`; strings by `tolStr_proved` (below); integers per argument by `TolInt_Statement` (below). Lane F1-18: **`print_sum`'s loop invariant carries a per-argument budget**: its state is `S i k` (before argument `i`), `PrSt.room` the break room of the arguments from `i` on (`PrRoom (prCost args i)`, `argCost`: one `_malloc_r`'s room per integer or function, sixteen per float; `stdoutNeed` while `stdout` has no buffer), kept by a write (`PrintPost.room`, from `HeapGrant.brk_hi` = `MallocPost.brk_hi`), consumed by an allocating `luaL_tolstring` (`TolPost` with `PrSt' (i + 1)`), the entry's from `callBudget` (now `Σ argCost + 4 · extRoom + …`); `PrSt.strt` room in `g->strt` for the strings still to make (no `luaS_resize`) and `PrSt.safe` the table's chains (`StrtSafe`, frozen with the literals); `PrSt'` lets the literals' footprint change (a new string changes the table they read); a non-allocating class keeps them all (`PrSt.next0`) Lane F1-19: `printRel_of : MallocR_Statement → PushLit_Statement → TolStr_Statement → TolInt_Statement → PrintFlt_Statement → PrintFn_Statement → PrintRel_Statement` (no `PrintAllocOff_Statement`): `PrintIn` gains `alloc : PrAlloc` (the literals, the string table safe with `X = PrX ∨ B`, `_dtoa_r`'s bignums `B` frozen and apart: `PrBigIn`), `gc` (`g->allgc` off `PrKeep`), `stat` (`AllocStatic`, from the frozen `LocaleWords` and `.rodata`: `fmtStatic_of`), `mt_fn`; `PrintOut.st : PrintOutSt'` carries `PrAlloc` again; `PrintRelIf`'s budget is `PrBudget` (`brk`, and `strt`: room in `g->strt`); `PrSt` carries the bignums (`big`, `bigIn`, `big_fl`, kept by every step: `LitKeeps.big`, `prStrPost`'s `kB`, `reentWord_not_printW`) and `safe` unconditionally Lane F1-23: `printRel_of … tolInt_proved` (`CallOpen.print`, moved to `Kit/TolIntProof.lean`), so `CallOpen` is `printFlt`, `printFn` Lane F1-24: functions per argument, `printRel_of : MallocR_Statement → PushLit_Statement → TolStr_Statement → TolInt_Statement → TolFn_Statement → PrintFlt_Statement → PrintRel_Statement` (`show_ascii` covers `print`'s line; `PrKeep` keeps `G(L)->mt[nil … function]`), `CallOpen.print` moved to `Kit/TolFnProof.lean` with `tolFn_proved`, so `CallOpen` is `printFlt` |
| `TolStr_Statement` (`luaL_tolstring` on a string argument: `luaL_callmeta(L, idx, "__tostring")` → `lua_getmetatable` (the string metatable) → `luaL_getmetafield` → `lua_pushstring("__tostring")` (`pushLit_proved`) → `lua_rawget` → `luaH_get`'s miss (`StrMtMiss`, boot-checked) → `lua_settop`; `lua_pushvalue`; the tail `lua_tolstring`) | `Lua/Vm/Sim/Kit/{Getmetafield,TolStr,TolStrProof}.lean`, `Lua/Vm/AtF/{LuaHGetMiss,GmfMiss,TolStrS,TolStrL,TolTopL}.lean` | A1 | **proved** (lane F1-17: `tolStr_proved`; `luaH_get`'s miss `hget_miss_sum` (`seg_loop` over `HMissAt`, from the boot fact's `NodeMiss` by `NodeMiss.toAt`), `luaL_getmetafield.part.0` `gmf_miss_sum` (over `pushLit_proved`), `luaL_tolstring` per tag module `tol_{s,l}_pre`/`_mid` (one tactic each, `tol_pre_run`/`tol_mid_run`), the tails `tol_tail_s` (`toltop_sum`) and `tol_tail_l` (`toltopl_sum`, `u.lnglen`), `TolPost` by `prStrPost`; the argument's string read where `PrintIn` freezes it (`str_foot`, `str_repr_at`). Statement correction: `PrintIn.args_heap` (the arguments' strings lie in the heap, from `Complement.own`: `call_args_heap`); without it `PrintIn` allowed an argument string in the static image, where `TolPost`'s `SrcLo` fails for 1024 bytes or more) |
| `TolInt_Statement` (`TolArg IsInt`: `luaL_tolstring` on an integer argument, per argument, over `PrSt`'s budget: `lua_pushfstring(L, "%I", i)` → `luaO_pushvfstring` → `tostringbuff` → `lua_integer2str` → `luaS_newlstr` → `internshrstr` (found on a chain or created), the tail `lua_tolstring`) | `Lua/Vm/Sim/Kit/TolIntProof.lean` | A1 | **proved** (lane F1-23): `tolInt_proved`, from `tolint_sum` (lane F1-20) with `MallocR_Statement` and `IntegerToStr_Statement` proved: the run's inputs `tolI_in` (`TolIIn`) and `tolI_tab` (`NlTab`: the chains' walk by `kwalk_of` from `PrSt.safe` and `StrtOff`, no literal the digits `lits_nomatch`, read at any memory agreeing below the stack `KWalk.congr`/`IaTab.congr`); `TolPost` from a found string (`prIntHit`: as a literal's push, `litKeeps_of`, `PrSt.nextKeep`; the string's bytes off the push's stores because the table's strings lie off `D`) or a created one (`prIntNew` over `TiNew`: `TiNew.ins` re-freezes the literals and the table's safety on the footprint with the insertion's by `frozen_insert`, apart from `D` by `PrintIn.dirty_in`/`dirty_g` and `LitsFoot.tab`; `TiNew.st` the state before argument `i + 1`; `TiNew.io`/`heap`/`cells` `stdout`'s state with the new heap by `StdoutIn.congrA`). **The statement fix** (lane F1-20 found it false: `frozen_lits_head_tt`): `PrintIn` bounds the dirty set (`dirty_in`: in chunks in use, so off every block an allocation claims; `dirty_g`: off `g->currentwhite` and `g->allgc`), `LitsFoot.tab` keeps `g->strt`'s header and bucket array in the literals' footprint (so off `D`), and `StrtSafeIn`'s `W` holds `D` (a found string's bytes survive the push at `L->top`). Lane F1-24: the glue is generic in the class (`ArgStr v b`: `print` shows `b`, one to twenty bytes, one allocation's cost, no literal `b`): `tolV_in` (`TolVIn`, the tag, payload and metatable word as parameters; `TolIIn` its integer instance), `tolV_tab`, `prStrHit`, `prStrNew` (over `TiNew … v b …`), and the one lemma `tolPost_of_run` from any run to `TolPost`; `tolInt_proved` is `argStr_int` and `tolint_sum` through it. The caller meets them: `call_printIn` (`CallD` in the heap's chunks in use and apart from `g`'s words by `CallObjs`), `call_lits` from the new invariant field `CallInvAt.tab_fl` (boot-checked: `VmEntryData.lits_tab` by `litsCheck_tab`, from the literals' check over the view restricted to `e.litFoot`; re-established by `call_close` from `LitsFoot.tab`), `call_alloc` from `CallAllocAt.strt`'s `W` (now `B ∨ CallLitDirty ∨ NciAt`; boot-checked: `strSafeCheck`'s `ws` ranges `entryWRanges`, every node's object and the bucket array off the `lua_State`, `g`, the `CallInfo` and the Lua stack from `ci->func`, both boot witnesses re-decided) |
| `PrintFlt_Statement` (`PrintRelOn (HasClass IsFlt)`: `luaB_print` when an argument is a float: `lua_pushfstring(L, "%f")` → `tostringbuff` → `snprintf(buf, 44, "%.14g", x)` (`G14From`) → `_dtoa_r`) | `Lua/Vm/Sim/Kit/CallOpen.lean` | A1 | open, **named premise, true as stated** (lane F1-19; lane F1-18 found it false): `PrintIn.alloc` keeps `_dtoa_r`'s state (`_REENT`'s `_result` at 80, `_result_k` 88, `_p5s` 96, `_freelist` 104: `ReentWord`, `reentP5sOff` generated) and its bignums `B` (`ReentMp`: what `_Balloc` pops, `_Bfree` pushes and `__pow5mult` multiplies by) apart from `G`, the Lua objects, the literals and the string table, `PrintIn.gc`/`alloc` keep the new string's writes off `G`, `PrBudget` has room for every allocation (`argCost`: sixteen `_malloc_r` per float) and no `luaS_resize`, `PrintIn.stat` pins the static words (`LocaleWords`). Sail trace (lane F1-19, `print` of 18 floats from `5e-324` to `1.8e308`, `±inf`, `nan`, `-0.0`): at most four `_malloc_r` per float (the first `%.14g` of the run: the free lists' array of 520 bytes, two bignums, the string), one afterwards (the string); the static words read are `_impure_ptr`, `__global_locale + 0xe8/0x100/0x160`, `_impure_data + 0x50/0x58/0x68` and the allocator's globals. A per-argument `TolFlt` over `PrSt.big` is the next step (`G14From`, row S0b). Lane F1-20: not true as stated (a created string's header joins the literals' footprint, `frozen_lits_head_tt`, and `D` is unbounded: see `TolInt_Statement`) Lane F1-23: **satisfiable again**: the obstruction was `frozen_lits_head_tt` (a created string's tag byte in every footprint the literals' facts are frozen on) against an unbounded `D`; `PrintIn.dirty_in` now puts `D` in the entry's chunks in use, so no fresh block meets it, and `TiNew.ins` (machine-checked for the digits) shows the footprint with the insertion's is apart from `D`; its steps are generic in the string but for `lits_ne_intU8`/`lits_nomatch` (no literal is the string: `%.14g`'s output against `"nil"`, `"true"`, `"false"`, `"__tostring"`) and `TolIIn`'s integer slot |
| `PrintFn_Statement` (`PrintRelOn (HasClass IsFn)`: `luaB_print` when an argument is a function: `lua_getmetatable` (`G(L)->mt[LUA_TFUNCTION]`), `lua_typename`, `lua_topointer`, `lua_pushfstring(L, "%s: %p")` → `lua_pointer2str` = `snprintf(buf, 44, "%p")`) | `Lua/Vm/Sim/Kit/CallOpen.lean`, `Lua/Vm/Sim/Kit/TolFnProof.lean` | A1 | **discharged** (lane F1-24): no longer a premise. Functions go per argument (`TolFn_Statement`, row below), and `PrintFn_Statement` as stated (lists with a function, a float among them too) follows from `PrintFlt_Statement` (`printFn_of_flt`). History: open, **named premise, true as stated** (lane F1-19; lane F1-18 found it false): `PrintIn.mt_fn` pins `G(L)->mt[LUA_TFUNCTION]` NULL (from `LuaStatic.mt_fn`, frozen on `F`, boot-checked: `luaStaticWords`, `entryBaseCheck`), so `luaL_getmetafield` finds no `__name` and the line is `binaryHost`'s `"function: 0x80022f18"` (Sail: `print(print, 42, -7)` makes one string of 45 bytes, one `_malloc_r`); the new string's writes are apart as for floats; `%p` is a second `snprintf` specialisation (`gen_lua_at.py --fn snprintf/p`) Lane F1-20: not true as stated for the same reason as `TolInt_Statement` (a created string's header joins the literals' footprint, `frozen_lits_head_tt`, and `D` is unbounded); its route reuses `newlstr_any_sum` and the `luaO_pushvfstring` at-lemmas, `"%s: %p"` still needs `gen_lua_at.py` specs (`lua_pushfstring/sp`, `snprintf/p`) Lane F1-23: satisfiable again for the same reason as `PrintFlt_Statement` (`"function: 0x…"` is no literal: its length) |
| `TolFn_Statement` (`TolArg IsFn`: `luaL_tolstring` on `print`, per argument, over `PrSt`'s budget: `luaL_callmeta` (`G(L)->mt[LUA_TFUNCTION]` NULL), `lua_type`, `lua_typename`, `lua_topointer`, `lua_pushfstring(L, "%s: %p", "function", print)` → `luaO_pushvfstring` (`strchr`, `addstr2buff` of `"function"` and `": "`, `snprintf(buf, 32, "%p")`, `luaS_newlstr` of `"function: 0x80022f18"`), `luaC_checkGC`, the tail `lua_tolstring`) | `Lua/Vm/Sim/Kit/{PtrFmt,PushfP,TolFn,TolFnProof}.lean`, `Lua/Vm/AtF/{SnprintfP,PushfP,TolFn}.lean` | A1 | **proved** (lane F1-24): `tolFn_proved` from `tolfn_sum` (`TolFIn`, `pushfP_sum`, `toltop_sum`) by the glue `tolPost_of_run` over `argStr_fn` (no literal's length is twenty, `lits_nomatch_fn`). The callee-context specs `snprintf/p` (`snprintfP_sum`: `_svfprintf_r`'s `'p'` conversion, the hex digit loop by `seg_loop`), `lua_pushfstring/sp` (cuts at the conversions, `snprintf` and `luaS_newlstr` call nodes; `pf_newlstr` and `pf_tail` shared with `"%I"`), `luaL_tolstring/fn` (new helpers `lua_typename`, `lua_topointer`). `PrKeep` now keeps `G(L)->mt[nil … function]` (`PrintIn.mt_fn` through the loop) |
| `PrintAllocOff_Statement` (`PrintRelIf`: an integer list (no float, no function) whose new strings do not fit in `g->strt`) | `Lua/Vm/Sim/Kit/CallOpen.lean`, `Lua/Vm/Sim/Kit/PrintRel.lean` | A1 | **proved vacuous** (lane F1-19: `printAllocOff_proved`; no longer a `CallOpen` field). Lane F1-18 found it false: `PrintIn` kept `G` off none of what an allocating `luaL_tolstring` writes (`g->allgc`, the bucket's head, a dead string's mark). Lane F1-19 moved those into the relation (row "the `CALL` invariant") and `PrintIn` (`gc`, `alloc`, `stat`), and the table's growth beyond the budget (`HeapBudget.strt`, A8's), so the off-route entries do not occur (`PrBudget.strt` refutes the restated premise) |
| `ExtendCI_Statement` (`luaE_extendCI(L)` from `next_ci` with `ci->next` NULL: `PcExt` with `ExtPost`) | `Lua/Vm/Sim/Kit/ExtendCI.lean`, `Lua/Vm/AtF/ExtendCI.lean` | A1 | **proved from `MallocR_Statement`** (lane F1-14: `extendCI_of_malloc`; the at-lemmas (`gen_lua_at.py --fn luaE_extendCI`: roots at the entry and at the return from `g->frealloc`, a call node), `lalloc_sum` (`l_alloc` → `realloc` → `_realloc_r(NULL)` → `j _malloc_r` by `kit_run`, then `MallocR_Statement`), `ext_ret` (the links, `L->nci++`), `ext_post` (`ExtPost`: the heap with the links, the keep, `stdout`'s state by `StdoutIn.congrA`, which reads no allocator word: `StdioFoot`)). The earlier statement was false: `luaM_malloc_` adds to `g->GCdebt`, which `ExtPost.keep` claimed kept, and calls `g->frealloc`, which nothing constrained. Fixed: `ExtPost.keep` is also off `g->GCdebt`; `g->frealloc` is frozen in `LuaStatic` (boot-checked: `luaStaticWords` gains `(g, 8)`, `EntryDirty`/`CallDirty` narrowed to `[g + 16, g + 64)`, `g->GCdebt` in `CallLitDirty`); `ExtCx` places the `lua_State`, the `CallInfo` and `g` (the entry contract's `g_al`, the invariant's `g_al`); `ExtPost.stdio` takes `stdout`'s buffer apart from the links. `CallOpen.extendCI` is the theorem; lane F1-A0-M: `extendCI_proved` (no premise) |
| `PoscallN_Statement` (`luaD_poscall(L, ci, 0)` with `wanted ≥ 1`, `C ≥ 2`, after `luaB_print`'s `0` results: `moveresults`' nil fill, `PoscallPost`) | `Lua/Vm/Sim/Kit/PoscallN.lean` | A1 | **proved** (lane F1-14: `Ret.poscallN`; `w = 1` by `pos_one`, `w ≥ 2` by `posN_head`, the nil-fill loop `pn_loop` (`seg_loop` over `compMem`, as `OP_LOADNIL`), `posN_tail`; the post by `pcw_post`). `HluaD_poscall` regenerated past `0x8000a4d8` (stops: the result copies `0x8000a44c`, the close path `0x8000a5e4`; root: the loop `0x8000a4a4`); the earlier segments only gained additions, `poscall_sum` unchanged. The statement now fixes `n = 0` (with results, `moveresults` copies them: the earlier `∀ n` form was false) and `PcCxW` carries the result slots' placement (`res_lo`, `res_hi`, `res_ci`, `res_L`), supplied by `call_pos_run` from `CallNums`. `CallOpen.poscall` is the theorem |
| `PrintGrow_Statement CallInv` (`luaD_precall`'s stack growth, `L->stack_last - L->top ≤ LUA_MINSTACK`: `luaD_growstack`) | `Lua/Vm/Sim/Kit/CallOpen.lean` | A1 | **proved vacuous** (lane F1-14: `printGrow_none`): the `CALL` invariant's `growFree` (`func + 16 (1 + maxstacksize) + 320 < stack_last`) and `call_bounds` (`a + b ≤ maxstacksize`) refute the growth states. `growFree` comes from the entry contract's new `VmEntryData.call_room` (`func + 16 (2 + maxstacksize) + 320 < stack_last`, so it also holds after `VARARGPREP` moves `func` one slot up), kernel-checked by `entryBaseCheck` (both witnesses: 480 and 368 bytes of room above the frame, 32 to spare after the move for `f1_ops`). A program whose frame leaves less than `LUA_MINSTACK` slots fails the entry contract rather than reaching `luaD_growstack`. `CallOpen.grow` is the theorem |
| `ExitUp_Statement` (`exit(0)` once `stdout` is set up: `__stdio_exit_handler` → `_fwalk_sglue(_fclose_r)`) | `Lua/Vm/Sim/Kit/ExitUp.lean` | A1 | **proved from `FreeR_Statement`** (lane F1-14: `exitUp_of_free`; `exit_run_up` (`exit`, `__call_exitprocs`, the handler, `_exit`), `exit_handler_sum` (`_fwalk_sglue`, a root after each stream), `fclose_in`/`fclose_err` (quiet streams: the read path of `__sflush_r`, `__sclose` → `_close_r` → `_close`), `fclose_out` (`sflush_sum`, the `_close` hook, `_free_r`)). The earlier statement (over `StdoutIn` alone) was not provable: `stdin`, `stderr`, `__sglue` and the handler were unconstrained, and `exit` jumps through their hooks. The invariant now carries them (`StdioRest` in `StdoutIn.fresh`/`.up`, `StdoutTail` and `FdsStd` in `StdioUp`), established from `__sinit` (`SinitPost.tail`, `StdQuiet.of_std`) and `fs_init` (`FstatPost.fds`) and kept by every write; the statement takes the `CALL` invariant at `.up buf []` (`ExitFree` lies in the C stack or chunks in use, `exitFree_kept`). `CallOpen.exitUp` is the theorem; lane F1-A0-M: `exitUp_proved` (no premise). The exit path agrees with the Sail trace of `while.lua` (`stdin` quiet, `stdout` closed then `_free_r`, `stderr` quiet) |
| `FreeR_Statement` (`_free_r(_REENT, p)` on `HeapAt`, `p` a chunk in use: returns, writing only `MallocGlobal`, the arena and 1 KiB of stack) | `Lua/Vm/Sim/Kit/Malloc.lean`, `Lua/Vm/Sim/Kit/AllocProof.lean` | A0 | **proved** (lane F1-A0-M: `AllocProof.freeR_proved`, from the ported `free_body` with the ledger of the chunks in use but the freed one); `CallOpen` no longer carries it (`exitUp_proved`) |
| the relation's Lua state across `CALL` (`LuaStateRel`: `ci->next` NULL or the C `CallInfo` `CiNext`, `L->ci = ci`; `g->strt`/`g->strcache` left to the `CALL` arm) | `Lua/Vm/Sim/Rel.lean` | A1 | **done** (lane F1-12): `RuntimeMem.lua : LuaStateRel` (from the boot contract's `LuaStateAt` and `VmEntryData.ci_eq` by `LuaStateAt.rel` in `relParts`, at the entry and after `VARARGPREP`). Before, `LuaStateAt.next` (`ci->next = 0`) made `VmRel` false after the first `print` (`luaE_extendCI` links the C `CallInfo` there) |
| **`vm_refinement_Statement luaLayout`** | `Lua/Theorems.lean` | A1 (by `vm_refinement_of_sim`) | open |
| `CompileTV CorpusCompiles` (translation validation of the host `luac -s` on the corpus) | `Lua/Compile/Corpus.lean` | B1 | **proved** (`corpus_compileTV`) |
| `CompileTV (fun s p => compile s = some p)` for a Lean `compile` | new `Lua/Compile/` | B2 | open |
| the ELF's `lparser`/`lcode` refine `compile` | — | B3 | open |
| **`compile_refinement_Statement`** | `Lua/Theorems.lean` | B1/B2 (by `compile_refinement_of_tv`) | **proved for `CorpusCompiles`** (`compile_refinement_corpus`); open for B2's `compile` |
| **`endToEnd_lua_Statement luaLayout Compiles`** | `Lua/Theorems.lean` | E (by `endToEnd_of_layers`) | open |
| `HtifPrint_Statement`: `htif.c`'s `write` to fds 1-2, `read` from fd 0 and `fstat` of fds 0-2 implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open (traces accept it) |
| `HtifFs_Statement`: all twelve system-call functions implement `TCB.Os.next` | `Lua/Os/Htif.lean` | OS | open; plausibly true within `htif.c`'s resource limits (no trace rejected, `experiments/os/RESULTS.md`); needs a resource bound and the `OsState` frame obligation (OS bullet) |

## P0: validation and scaffold (done)

* **Result.** Recorded in `VALIDATION.md`:
  * The ELF runs on Sail, and 16 difftests pass.
  * The census is written up.
  * F1's `BcSem` reproduces the binary's output on three programs by kernel
    evaluation.
* **Scaffold.**
  * Bytecode syntax and decoding.
  * The F1 semantics.
  * The fragment predicate and ledger.
  * The VM representation skeleton and `VmLoaded`.
  * The Lua 5.4 source syntax and `LuaSem` for F1.
  * The statements.
* **Exit.** `scripts/check.sh` passes. That covers generator drift, the ELF
  hash, forbidden tokens, the copied layer being WHILE-free, `lake build`,
  and the axioms of 14 theorems.

## A0: retarget the machine layer to the Lua image

The copied layer (`Vsa/`, `VsaIris/`) is language-agnostic. Its proof
instances, however, are at the WHILE ELF's addresses.

1. **`tohost` (done).**
   * `Vsa.Sim.tohostAddr` (`Vsa/Sim/InitValues.lean`) is the Lua ELF's
     `tohost`. It is the only place the number is written: the copied proofs
     that used the WHILE literal go through `tohostAddr`, and
     `Lua.Vm.tohostAddr_eq_symTohost : Vsa.Sim.tohostAddr = Layout.symTohost`
     (`rfl`) fails the build when a regenerated ELF moves `tohost`.
   * Changing the value was cheaper than generalising: the whole copied layer
     rebuilt unchanged apart from four literal bounds.
   * `LuaGoodState` is retired; `MachineAt.good` and `Lua/Os/Htif.lean` use
     `Vsa.Sim.GoodState`.
2. **Cut the WHILE import edges (partly done).** `experiments/port/CUTS.txt`
   (`python3 experiments/port/port_census.py`) lists what is left.
   * **Method.** `experiments/port/term/` follows, over a built syi checkout,
     every constant a module set uses (theorem bodies included). The import
     edges into the WHILE layer mostly carried no WHILE constant. The generic
     declarations they did carry are copied verbatim, under their own names,
     into `Vsa/Sim/Generic/*` and `VsaIris/Vsa/Generic/*`. The importing
     modules get rewritten import lines. `port_census.py --copyset` follows
     this repository's import lines, and must stay WHILE-free and complete.
   * **Ported (here):**
     * the segment layer: `SegToTripleFramed` (`segRowFramed`), `DeriveCase`
       (`#derive_case`), `DeriveCaseRow`, `BridgeSeg`, `BridgeSegFull`,
       `BridgeSegFramed`, `FrameMeta`, `SegEffect`, `ExecRetEpilogue`,
       `InterpSpillReads`;
     * the dlmalloc Iris route: `VsaIris.Vsa.{SymRun,Instance,Tools,RunBase,AllocRun}`
       (its code bytes and step table are regenerated at Lua addresses, A0.5);
     * the output/exit machinery of the stdio route: `SymRunO` (`SWPO`),
       `SymObs`, `SymJalr`, `SymLeaf`, `SymBridge`, `SymData`, `SymHavoc`,
       `SymCompact`, `SegRun`, `AllocSltu`, `Console` (`TohostSite`,
       `putc_runFact`, `exit_haltFact`, `vsa_adequacy_exit`), `HtifStepObs`,
       and `Vsa.Sim.Generic.ExitStep`;
     * `SeparationLogic`, `MemPresence`.
   * **Not ported, with the obstruction:**
     * ship-your-interpreter's `_write`/`_exit` `TohostSite` instances: their
       stores miss the Lua mailbox (`VsaIris.Inst.whileSites_not_tohost`). The
       Lua ELF's sites are instantiated in A0.5.
     * `Stdout.*`, `Fprintf.*`, `ExitH.*` (the stdio chain). The step tables
       are WHILE-address instances, and they also need about 27 helper
       declarations and the `ITac`/`AllocTac` tactic layer. The top-level specs
       (`fwrite_out`, `fprintf_out`, …) are stated in the WHILE interpreter's
       Iris world (`VsaIris.Interp.Repr`: `InterpGS`, `Newlib.binImg`,
       `FrameReads`). Following constructors, the census reaches
       `Vsa.MemRepr.CString`, `Vsa.RuntimeRepr.NativeAddrs` and `Vsa.While.*`
       (`experiments/port/term/CtorRoots.lean`). Seventy constants over 24
       modules depend on the WHILE HTIF sites (`RevDeps.lean`). Porting means
       restating that world for Lua. It is done together with A0.5's
       regeneration.
     * `DlHeap`, `AllocLedger`: the ledger is the WHILE runtime's ownership
       (`RuntimeOwnership*`, `Vsa.While.{Ast,Semantics}`; 29 + 26 WHILE-root
       constants reached). Lane F1-A0-M ported the dlmalloc proofs instead:
       the term census (`term_census.py closure` over `MallocRunAll`,
       `FreeRunAll`) reaches one WHILE-root constant (`roundUp16`); `Vsa.Sim.DlHeap`
       (WHILE-free, Lua addresses) and `VsaIris/Vsa/{Heap,Malloc,Free}*.lean` are
       the relocated proofs (`experiments/port/alloc/`), `AllocKit` the few
       declarations they used from untaken modules.
3. **Decode (done).** The generic decoder replaces per-word tables.
   * `Vsa.Sim.decodeW σ hmisa hpriv hsec : (ext_decode w).run σ = .ok i σ`
     (`Vsa/Sim/DecodeNF.lean`, from ship-your-interpreter's `#simp_nf`,
     `Vsa/Meta/SimpNF.lean`). The instruction `i` is found by an autoParam
     `rfl` for any concrete word, so no per-word lemma is generated.
   * Drop-in rule: `DecodeTable.decode_<hex> σ h1 h2 h3` becomes
     `Vsa.Sim.decodeW (w := 0x<hex>#32) σ h1 h2 h3`. A `DecodeFactM`/`DecodeFactT`
     leaf is `fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3`.
   * Coverage: `Lua/Vm/DecodeCheck/*` (`scripts/gen_lua_decode_check.py`)
     kernel-checks one `example` per unique word of `luaV_execute` (1,641
     words, 4,020 instructions), each stating the instruction the Lean
     evaluator decodes the word to. It builds in 13 modules of 128 words:
     6 s wall, 54 s CPU, about 1.7 GB per module. check.sh stage 1 checks drift.
4. **Code pins (done).** `scripts/gen_lua_code.py` emits `Lua/Vm/Code/*`
   (index module `Lua.Vm.Code`). It retargets `gen_code_lemmas.py` and
   `gen_fixed_image.py --projection`.
   * Functions: `luaV_execute`, the non-float callees of the F1 arms read from
     `experiments/census/luaV_execute_arms.tsv`, and `luaB_print`,
     `luaL_tolstring`, `fwrite` (`lua_writestring`) and `luaG_opinterror`.
     That is 25 functions. `__udivdi3` is pinned as `__hidden___udivdi3`,
     the same code.
   * Per function `F`: `<F>Loaded` and fetch lemmas `<f>_at_<addr>`, plus
     `textLoaded_<F>Loaded : FixedBytesLoaded textBase textSize textByte m →
     <F>Loaded m`. Each pinned byte is `h off (by decide)` against
     `Lua/Vm/Image.lean`.
   * `luaV_execute` (252 chunks) is split into 16 parts `LuaV_execute_p<k>Loaded`,
     each of the syi shape. Its fetch lemmas take the part, via
     `luaV_execute_part<k>`.
   * Build: 83 modules, 21 s wall, 5m47 CPU.
5. **Library proofs at Lua addresses.**
   * **Allocator step table (done).** `scripts/syi/gen_alloc_steps.py` reads
     the Lua ELF (`objdump`/`nm`; `gp` = `__global_pointer$`, which is
     `VsaIris.MallocFast.gpV` (`alloc_gp` ties the two), the
     `_impure_ptr` word). `FUNCS` is the call closure of `malloc`, `free`,
     `realloc`, `_malloc_r`, `_free_r`, `_realloc_r`: 15 functions, 1,366
     instructions, one `st_<pc>` each, in `VsaIris/Vsa/AllocSteps/Part{00..11}`
     (aggregator `VsaIris.Vsa.AllocSteps`) over `allocText`
     (`VsaIris/Vsa/AllocCode.lean`). The WHILE-address tables are gone. The
     dlmalloc globals lie at or above `tohost + 16` in the Lua ELF
     (`__malloc_av_` = `0x8005c6d0`), so every `StOK` closes by `decide`.
     Decode is `decodeW` (`jalx_<pc>`, and `chain_facts`' decode leaves). The
     one instruction outside `MKind`, `_realloc_r`'s `sltu a4,a5,a4`
     (`0x80030360`), goes through `AllocSltu.sltuAluStepAt` (any address).
     `check.sh` stage 1 checks drift (`--check`).
   * **The console end of the stdio chain (done, lane F1-6),** on the
     `SegSt` route the arms use, not `SWPO`: the helper segments of `_write`,
     `_write_r`, `__swrite`, `__sflush_r` are `gen_lua_arms.py` `HELPERS`
     (code pins `gen_lua_code.py` `EXTRA`). The generators gained `sh`
     (`writeMap2`, `Vsa/Sim/StoreHalf.lean`, `TextLoaded.writeMap2` in
     `Lua/Vm/Arms/TextHalf.lean`), a linking `jalr` (an indirect call:
     `gen_sites.py` `emit_jalr`, `RegsOk.jalr` in `Lua/Vm/Arms/RegsOkJalr.lean`)
     and `tohost` seams (`TOHOST_SEAMS`: the console store is a stop, the
     liveness flows through it). The summaries are in `Kit/{Console,Write,
     Swrite,Sflush}.lean`; the `FILE` field offsets, `__swrite`, `_lock`,
     `_flags2` and `_reent.__cleanup` are in `Lua/Vm/LayoutRt.lean`. Open:
     `fwrite`'s `__sfvwrite_r`, `fflush`, the first write's set-up
     (`Kit/CallSpec.lean`).
   * Regenerate the other reused functions' step tables and specs with the
     generators (`gen_str_steps.py`, `gen_memcpy_steps.py`, `gen_fn.py`).
   * They are identical code at new addresses: `__udivdi3` (`FORPREP`),
     `__moddi3`/`__divdi3` (`MOD`/`IDIV`), the stdio chain behind `print`,
     `setjmp`/`longjmp`.
6. **`luaLayout` (defined; kernel witness done).**
   * **`luaRuntimeReady`** (`Lua/Vm/Runtime.lean`) is `∃ w : RtPtrs,
     RuntimeReadyAt c L ci w`, eight named structures. Each field's doc
     comment names the callee that reads it:
     * `HarnessAt`: the platform loop's `tick < 2` and the empty console
       (read by A1's `vmRel_entry`);
     * `CStackAt`: `sp`, `ra` (into `ccall`, `retCcall_after_call`), `gp`, the
       saved registers `s0 … s11`, the caller frames' bytes above `sp`, and
       every RAM byte present (true of the zero fill);
     * `ErrorJmpAt`: `L->errorJmp`, `previous = NULL`, and the `jmp_buf`'s
       `ra`/`sp`/`s*` slots (`setjmpRet_after_call`);
     * `StdioBoot`: newlib before its lazy `__sinit` (`__stdio_exit_handler =
       NULL`, the `_reent` stream pointers, `__sglue`, the three `FILE`s zero);
     * `MemfsBoot`: htif.c before its lazy `fs_init` (`fs_ready = 0`, both
       tables zero);
     * `DlHeap.HeapAt` (`Lua/Vm/DlHeap.lean`): ship-your-interpreter's heap
       shape without the WHILE ledger fields;
     * `LuaStateAt`: `hookmask`, `trap`, `errfunc`, `nCcalls`, `openupval`,
       `tbclist`, the stack bounds, `ci->top`,
       `CIST_FRESH`, `nresults = 0`, `ci->previous`/`ci->next`, the `mt` of
       nil/booleans/numbers, the string table (`StrtAt`, chains by
       `StrChain`) and the string cache;
     * `VmRegionsAt`: `L`, `ci`, the Lua stack, the main closure, its `Proto`
       and code array lie in the heap `[_end, __heap_end)`, and `ci` and the
       code array lie apart from the Lua stack (read by `vmRel_entry`: the
       prologue's loads and `VmRel`'s `Ranges`). `RtPtrs` names the closure,
       the `Proto`, `code` and `sizecode`. `L`, `ci`, the code array and the
       constant array are pairwise apart (`L_sep_ci`, `code_sep_*`,
       `k_sep_*`: the scratch words miss them); `L` is apart from the Lua
       stack (`L_sep_stack`: `L->top`'s store misses every slot) and `L`, `ci`
       are 8-aligned (`L_al`, `ci_al`: `savestate`'s `sd`s);
     * `RuntimeReadyAt.top`: `L->top = func + 1`, an entry-only fact
       (`OP_VARARGPREP` → `luaT_adjustvarargs`), not a fetch-head invariant;
     * `RuntimeReadyAt.interned` (`KInterned`): the short-string constants
       are interned (`loadStringN` → `luaS_newlstr`), so `vmRel_entry` builds
       `VmRel`'s intern map `ι.ptr`;
     * `RuntimeReadyAt.kowned` (`KOwned`, round-4 BASE-S): every string
       constant's object (header, contents, terminator) lies in the user range
       of an in-use chunk of `HeapAt`'s walk, in the heap and apart from the
       Lua stack, `L` and `ci` (`StrChunkAt`). `vmRel_entry` turns it into
       `VmRel`'s `Complement.own` (`chunkOwns_of_strChunkAt`): every string a
       register or constant points to (`Strs.own`, carried by `ValRepr.str`)
       is owned by a chunk apart from `Win ∪ Scratch` (`StrOwned`,
       `Core.reg_owned`, `Core.k_owned`, `Core.str_frame`);
     * `TStringRepr.long` (round-4 BASE-S) carries `shrlen = 0xFF` (`+11`,
       `luaS_createlngstrobj`; `l_strcmp` branches on it at `0x8001a720`),
       checked by `tstrCheck` and the generator's `check_tstring`.
     * `RuntimeReadyAt.vararg` and `VmEntryData.vararg_room`/`vararg_proto`
       (lane F1-3): the runtime after `OP_VARARGPREP`'s stores
       (`varargMem`, `RtPtrs.vmoved`), the stack room `luaD_checkstack` needs,
       and the prototype apart from the `CallInfo` and the copied slot
       (`VarargDirty`); checked in the kernel only (`RtPostChecks` over
       `postView`, `entryCheck` over `View.minus`), not by the generator's
       native evaluation.
   * `luaLayout : VmLayout := ⟨luaRuntimeReady⟩`. The boot-invariant values it
     pins (entry `sp`/`ra`, the `jmp_buf`, the caller frames, the return
     chain, `nCcalls`) are `Lua/Vm/RuntimeData.lean`. The offsets are
     `Lua/Vm/LayoutRt.lean`, a second output of `gen_lua_layout.py`, which
     probes `struct lua_longjmp` by including ldo.c.
   * **Generator** `scripts/gen_lua_boot_witness.py` (from
     `scripts/syi/gen_boot_witness.py`):
     * It writes each program's chunk into the committed ELF's `.lua_chunk`
       region; the committed ELF is reproduced from `c/tests/while.luac`.
     * It traces to the first `luaV_execute` step, tracking the open call
       chain.
     * It rebuilds the entry memory: the PT_LOAD `p_filesz` bytes plus the
       store log.
     * It evaluates every field of `VmEntryData` and `luaRuntimeReady`, and
       requires the boot-invariant values to agree across programs. For
       `HarnessAt` it checks `plat_insns_per_tick ≤ 2` and that no boot store
       touches `tohost`.
     * It emits `RuntimeData.lean`, `Boot/ImageData.lean` and
       `Boot/Gen/{While,F1Ops}.lean`: the chunk region, the `PackedLog`, the
       `RunTree`, the registers and the witnesses `e`, `w`, `printSlot`, as
       data.
     * check.sh stage 1 runs `--check`, which re-traces (about 25 s).
     * Measured: `while.lua` enters at step 181,166 (18,137 stores);
       `f1_ops.lua` enters at step 181,079 (18,125 stores). Both have 178 heap
       chunks (one free), 141 interned strings in 256 buckets, and `nCcalls =
       0x20001`. Nothing touched stdio or the file system before the entry.
   * **Kernel side (landed):**
     * `Lua/Vm/Boot/Log.lean`: syi's `PackedLog`/`RunTree`/`LogOk`, with the
       cell check chunked (`runsIn`).
     * `Lua/Vm/Boot/Image.lean`: `bootMem chunk log` (loader plus log) and
       `bootMem_get : LogOk log runs → ViewOf (bootMem chunk log) (bootView
       chunk runs)`.
     * `Lua/Vm/Boot/View.lean`: `PartialView`, reads transported from a view
       (`PartialView.rdLE`), `zeroOk`/`bytesOk`/`segsOk`.
     * `Lua/Vm/Boot/Heap.lean`: `heapCheck`, `heapAt_of_check`.
   * **The kernel witness (done).** For each traced program,
     `Lua/Vm/Boot/Witness/<Prog>.lean` (generated by the same script) proves
     `vmLoaded_<prog>_entry : EntryRegs σ gprs → σ.mem = bootMem chunk log →
     output σ = "" → tick < 2 → VmLoaded luaLayout proto (fillZero ⟨σ, tick,
     steps⟩)`, `vmLoaded_<prog>_view` (any memory extending the boot view) and
     `runtimeReady_<prog>_entry` (`RuntimeReadyAt … w`, the witnessed
     `luaRuntimeReady`). Every check is a `decide +kernel` at default budgets
     over the byte view `bootView chunk runs`; no memory image is reduced.
     * `Lua/Vm/Boot/Check.lean`: one Bool checker per structure with its
       soundness lemma under `PartialView m v`: `entryCheck` (`VmEntryData`,
       with `protoCheck`/`constCheck`/`tstrCheck` for `ProtoRepr` against
       `gen_proto.py`'s `Proto`), `errorJmpCheck`, `stdioCheck`,
       `memfsCheck`, `luaStateCheck` (with `strtCheck`, `strcacheCheck`),
       `regionsCheck` (every round-3 `VmRegionsAt` field), `internedCheck`
       (`KInterned`, by `strDiff`: distinct pointers must differ in bytes),
       `kownedCheck` (`KOwned`, by `strLenV` and a search of the chunk walk),
       `heapCheck`, `runsAvoid` (no store in `.text`/`.rodata`), and
       `logOk_of_chunks`.
     * `Lua/Vm/Boot/Assemble.lean`: `EntryRegs` (`GoodState`, `pc`, the HTIF
       mailbox, the traced GPRs), `gprsCheck`, `runtimeReadyAt_of_checks`,
       `vmLoaded_of_checks`, `vmLoaded_of_boot`.
     * Per program: 18 store chunks of 1024 and 10 run chunks of 64
       (`LogOk`), `regsOk`, `imageOk`, `entryOk`, `rtOk` (10 structure
       checks), each one line.
     * Cost: each witness module ≈ 4–5 min wall, 236 s CPU, 3.0 GB peak
       (a 1024-store chunk ≈ 8 s, a 64-run chunk ≈ 7 s, `rtOk` ≈ 25 s,
       `entryOk` < 1 s); the data modules are unchanged.
     * Not built: the Sail register file. `EntryRegs` is a hypothesis
       (this repository has no copy of syi's `physicalAssignments`), so the
       theorem is over the family of states with the traced registers, not a
       closed `Config`. The step count and tick are free (`tick < 2`).
   * **Found by the witness: a `VmEntryData` bug.** `TStringRepr` required
     the string's header tag `GCObject.tt = vShrStr` (68, the `TValue` tag
     with `BIT_ISCOLLECTABLE`). `luaC_newobj` stores `LUA_VSHRSTR` (4), so
     `VmEntryData` (its `_ENV.print` key and every string constant) held at
     no real entry state, and `VmLoaded` was vacuous. It now uses `gcShrStr`
     and `gcLngStr` (`LayoutRt.lean`), and the traced entries satisfy it.
   * **`VmEntryData.env_print_ptr` (closes the pointer gap).**
     `TableHasShortKey` compares string contents, but `luaH_getshortstr`
     compares pointers. The new field says every short-string constant with
     bytes `"print"` is the key pointer of `_ENV`'s `print` node
     (`TableHasShortKeyPtr`). The generator checks it natively and
     `printPtrCheck` in the kernel.
7. **`disasm_to_segment.py` (done).**
   * It no longer drops rows. An `#UNSUPPORTED` row in the range, or an
     address with no row, is an error; `--allow-unsupported` drafts an
     explicit `UNSUPPORTED` step instead.
   * `disasm_to_sites.py` classifies every instruction of `luaV_execute`
     (4,396 rows, 0 unsupported). The added classes are the immediate and
     register shifts and logic ops, `addw`, `lui`/`auipc`,
     `lb`/`lh`/`lhu`/`lwu`, `sh` and general `jalr`.
   * `scripts/draft_f1_arms.py` drafts all 34 F1 arms: 2,050 instructions in
     496 segments (`experiments/census/demo/f1_arm_drafts.tsv`).
   * Every step has a site class (`draft_f1_arms.py`: 0 steps without one;
     check.sh stage 1). `scripts/syi/gen_sites.py` gained the classes
     `andi`/`ori`/`xori`/`slti`/`sltiu`, `slli`/`srli`/`srai`,
     `slliw`/`srliw`/`sraiw`, `and`/`or`/`xor`/`slt`/`sltu`/`sll`/`srl`/`sra`,
     `addw`/`sllw`/`srlw`/`sraw`, `lui`/`auipc` and the total loads
     `lh`/`lhu`/`lwu`. Each goes through an existing execute characterisation
     (`ExecuteAlu`, `ExecLoadTotal`); decode is `decodeW`.
8. **F1 arm segments (done).** `scripts/gen_lua_arms.py` emits, for every F1
   arm, the site batteries and one theorem per straight-line segment
   (`Lua/Vm/Arms/{Sites,Segs}/*`, index `Lua.Vm.Arms`, per-arm list
   `Lua/Vm/Arms/arms.tsv`).
   * Segments are `draft_f1_arms.py`'s, also cut after every `jal`; a
     segment ending in a conditional branch has a theorem per polarity
     (`_t`/`_n`). 788 segment theorems over 2,111 site lemmas, all built.
   * Each is `Triple (SegSt entry L (TextLoaded ∧ mem = m0)) (SegSt exit L' …)`
     (`Vsa.Sim.SegSt`, `gen_segment.py` `"boundary": "segst"`). `L` pins the
     registers read before written; `L'` gives every written register as the
     exact machine term and the memory as the store expression over `m0`.
     Loads are total (`bytesT*`). The address side conditions, branch guards
     and `jr` alignments are named hypotheses `h*_<step>` over the entry
     values: the arm proof discharges them from the A1 invariant.
   * `.text` (`Lua.Vm.Arms.TextLoaded`, the image's exact bytes) survives each
     store above `tohost + 16` (`TextLoaded.{writeMap8,writeMap4,insert}`).
   * Build: 119 modules; about 1.9 GB and 5–60 s each; built in batches of
     8 modules on this machine.

**Exit:** `VmLoaded luaLayout p (fillZero c)` is kernel-checked for
`while.lua` and `f1_ops.lua` at their real entry states, and check.sh
covers the new stages.

## A1: Layer A for F1

* **Target.** Prove `VmSim luaLayout`, then `vm_refinement_Statement luaLayout`
  by `vm_refinement_of_sim`.
* **Invariant.** The machine state represents a `BcSem` `State`:
  * `L->ci`, `savedpc` = `code + 4·pc`;
  * `FrameRepr` for the registers `Supported` says are definitely
    initialised;
  * output = `s.out`;
  * image, heap and stdio unchanged.
* **Arms.** One simulation lemma per F1 `Step` rule.
  * Each goes from the shared fetch site (`0x8001bfe4`, 10 instructions)
    through one of the 43 arms (2,239 instructions of per-arm reach; 613 on
    the integer fast paths) back to the fetch site.
  * Arms are generated with `gen_fn.py`/`genseg.py`. Integers-only
    `Supported` prunes the float/string slow paths of `LT`/`LE`/`FORPREP`/`MOD`.
* **Calls.** `CALL print` runs `luaD_precall` → `luaB_print` →
  `luaL_tolstring` → `lua_writestring`/`fwrite` → newlib stdout → HTIF. It
  reuses the stdio proofs from A0.5.
* **Errors.** The error paths (`luaG_opinterror`, `luaG_forerror`,
  `luaG_runerror` → `luaD_throw` → `longjmp` → `lua_pcallk` returns →
  `main` exits 2) give `stuck_sim`.
* **Definite initialisation (proved, `Lua/FragmentSound.lean`).** The
  fixpoint `supportedB` computes is a certificate (`Supported.defInit :
  DefInit p (defMask p)`).
  * `DefInit.step` is the invariant to use: two states agreeing on
    `defMask p pc` step to states agreeing on the successor's mask, and a
    `CALL` clobbers nothing in it. So `FrameRepr` is needed only for the
    registers in `defMask p s.pc`; the rest of the frame may hold anything.
  * `bcSemFrom_iff`: `BcSem` from any entry register file equals `BcSem`
    from all-`nil`. `cbcSem_iff`: the same with every register at or above a
    `CALL`'s results clobbered after each call (`CStep`).
  * `reachable_defInit`: at every reached state the pc is in range, the
    reads are in the mask, and the masked registers do not depend on the
    entry registers. `condJump_ne_none`/`condJump_lt`: test targets exist
    and are in range.
  * `Step.deterministic`, `BcSem.deterministic` (`Lua/Bytecode/Exec.lean`,
    via `step?_complete`).
* **Status (pilot, incumbent tooling; `abstractions/pilot/A1-incumbent.md`).**
  * **The relation** (`Lua/Vm/Sim/Rel.lean`). `VmRel p c s := ∃ w, VmRelAt p c s w`,
    all named fields:
    * the machine is at the fetch head `Lua.Vm.Arms.headPc` (`0x8001bfe4`, from
      the census JSON);
    * `Pins` fixes s0 = `L`, s7 = `ci`, s8 = the jump table, s1 = 81, s2 = 3,
      s5 = `trap` = 0, s9 = `base`, s11 = `code + 4·pc` (the cached pc; the
      memory `savedpc` is only written by `savepc`), `sp` and `gp`;
    * `Core.stack`: every defined register `j < maxstacksize` is represented
      (`ValRepr`) by its slot's tag and payload. The kernel's ⊥ already
      encodes the definite-initialisation mask. Nil is exactly `LUA_VNIL`, a
      string's tag is `strTag s`, and a short string's pointer is the intern
      map's `w.ι s` (`luaV_equalobj` decides `δ .eq`);
    * `Core.out`: the HTIF console is `s.out`;
    * `Core.frame`: outside the window (register slots, `luaV_execute`'s C
      frame, and `Scratch`: `ci->u.l.savedpc`, `L->top`, the callee frames
      `[spEntry - cStackBudget, sp)`) memory is a complement `w.mo`. `Complement` holds the image,
      `ProtoRepr`, the code words, `ci->func`, `ci->u.l.trap = 0`,
      `LuaStateAt`, `HeapAt` and `ErrorJmpAt`. `Ranges` holds the address
      bounds and separations.
  * **Relocation.** Registers are decoded from `ci->func` as the complement
    holds it (`base = func + 16`), not from a fixed address. Two operations
    move it; both re-establish `VmRel` with a new `func`, so no rewrite is
    needed:
    * `VARARGPREP` moves `ci->func` in every main chunk;
    * `CALL print` can reallocate the stack at ≥ 15 locals
      (`experiments/a1-falsifiers/REPORT.md`).

    The alternative, recorded but not taken, is a frame bound in `Supported`
    that rules out the reallocation.
  * **Dispatch, proved once** (`Lua/Vm/Sim/Dispatch.lean`, `dispatch`). It
    runs from `VmRelAt` with the instruction `ins` (opcode < 82) to
    `armTarget ins.opNum`, the table entry in `.rodata`
    (`jtWord_eq`, `armTarget_aligned`). It goes through the generated head
    segment `seg_8001bfe4_8001c00c` (`Lua/Vm/Arms/Head.lean`).
  * **Arms** (`scripts/gen_lua_arm.py`, `Lua/Vm/Sim/Arms/`). Each
    `sim_<OP> : Supported p → VmRel p c s → fetch → op → Step binaryHost p s s' →
    ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'` is proved for the 25 arms
    listed below. The proof composes:
    * `dispatch`;
    * the arm's generated segments (one chain per exit, picked by branch
      polarity), whose side conditions are closed by `arm_arith`/`slot_arith`;
    * the kernel combinator's inversion (`step_setR`, `step_jump`,
      `step_opArith`, `step_condjump`, `step_testset`, `step_forloop`);
    * a close: `Core.write`, `Core.jump`, `Core.update` or `Core.forloop`.

    The segments of `SIM_OPS` arms carry the fetch-head registers,
    `sailOutput` and `RegsOk` (`gen_lua_arms.py` `KEEP`, `OK`).
  * **Entry lemma (proved,** `Lua/Vm/Sim/Entry.lean`, `vmRel_entry :
    vmRel_entry_Statement`**).** From `VmLoaded luaLayout p c`, the prologue
    runs to the fetch head in `VmRel p c' State.init`. It composes the two
    generated prologue segments (`Lua/Vm/Arms/Prologue.lean`,
    `gen_lua_arms.py`, cut at `startfunc`):
    * `seg_8001bf68_8001bfb0` (the C frame, `L`/`ci`, the jump table): 52 ground
      side conditions, one `decide` each;
    * `seg_8001bfb0_8001bfe4` (`startfunc`'s loads, s1/s2, the `trap` check,
      `base`): 27 side conditions, one normalising `simp` plus `omega` over
      `VmRegionsAt`.

    The relation's pointers are `VmEntryData`'s and `w.mo` is the entry
    memory; `rdLE_spec` turns `rd32`/`rd64` into the total reads. It needed
    two new `luaRuntimeReady` structures, `VmRegionsAt` and `HarnessAt`
    (A0.6). Costs: `abstractions/pilot/A1-incumbent.md`.
  * **Arms proved (25):** MOVE, LOADI, JMP, ADD, SUB, ADDI, ADDK, SUBK, BAND, BOR, BXOR, EQI, LTI, GTI, LEI, GEI, TEST, TESTSET, NOT, BNOT, LOADK, LOADTRUE, LOADFALSE, LFALSESKIP, FORLOOP (`scripts/gen_lua_arm.py` kinds `copy`,
    `imm`, `jump`, `arith` (register, `sC` and `K` operands, the `op_arith`
    and `op_bitwise` layouts), `condjump`, `cmpI`, `truth`, `bnot`, `settag`,
    `loadk`, `forloop`; costs in `abstractions/pilot/A1-incumbent.md`, "More
    arms"). The relation now also carries:
    * `Core.frame` on total reads (`bytesT1`), `.text` presence separately
      (`Core.text`, the segments' fetches);
    * `Core.ok : RegsOk` (every GPR present, HTIF mailbox idle;
      `MachineAt.regs`, checked on the boot traces; threaded by every
      segment through `gen_segment.py`'s `"ok"` option);
    * the constant array: `Core.kptr` (`0(sp) = k`), `Complement.kconst`,
      `Ranges.k_*`/`frame_sep` (`VmRegionsAt.k*`, checked natively).
  * **The fold (lane F1-3, `Lua/Vm/Sim/Fold.lean`).** `fold_sim` is `Refine.Sim`
    from a relation and four clauses at reachable states (`FoldSim`: a step is a
    non-empty run, a final state halts with 0, a stuck state diverges or halts
    nonzero), by induction on the bytecode run; divergence of an unending run is
    by strong induction on the step count. Its instance `vmSim_of_arms` takes the
    arm table `∀ o ∈ armOps, SimArm o` (`armOps` = every opcode `opKernel` gives a
    kernel, `kernelOps`, but `VARARGPREP`), `EntrySim`, `VarargSim`, `FinalSim`,
    `StuckSim`; `armTable` discharges the 34 proved arms from `OpenArms`, so
    `vm_refinement_of_open : OpenArms → FinalSim → StuckSim →
    vm_refinement_Statement luaLayout`. `fillZero` enters only in
    `vm_refinement_of_sim`; `Supported` through `VmLoadedSupported`.
  * **`VARARGPREP` (proved, `Kit.varargSim`).** `SimArm .VARARGPREP` is not the
    obligation: `luaT_adjustvarargs` reads `L->top`, which `VmRel` leaves free
    (`Scratch`), so from a general `VmRel` state the move of `ci->func` is
    unknown, and an `A > 0` copies uninitialised parameters. So:
    * the kernel admits `VARARGPREP` only at pc 0 with `A = 0` (`lparser.c`
      `mainfunc`: `setvararg(fs, 0)`), and `supportedB` rejects every edge into
      pc 0 (`edges`; `DefInit.pc_pos`), so the one reachable state at a
      `VARARGPREP` is the entry state (`reach_pc_zero`); the corpus stays
      `Supported`;
    * the entry-only facts are `FreshAt` (`Lua/Vm/Sim/Vararg.lean`), proved at the
      fetch head by `entry_fresh` (from `entry_at`, `vmRel_entry` factored, and
      `relParts`, the complement and ranges from `ProtoAt` and `RtPostAt`);
    * the relation after the move: the entry contract now says the runtime is
      ready also at the memory the stores leave (`RuntimeReadyAt.vararg` at
      `varargMem`, for `RtPtrs.vmoved`; `VmEntryData.vararg_room` (no
      `luaD_growstack`) and `vararg_proto` (the prototype framed away from the
      `CallInfo` and the copied slot, `VarargDirty`)). The boot witness checks
      both at `postView`/`View.minus` (`RtPostChecks`, `entryCheck`); the two
      traced entries pass (each witness ≈ 5 min, 3.3 GB);
    * the run: `dispatchM` (dispatch, memory unchanged), the segment-local
      lemmas `vp1` (to the call), the call node `Kit.adjvar_sum` (three
      segment-local lemmas over the generated `HluaT_adjustvarargs` segments,
      `av_guard` for `luaD_checkstack`), `vp2` (`trap`), `vp3` (`updatebase`),
      and the close `vclose` at `w.vmoved ι`, its memory frame `vmem_frame`.
    The at-lemma generator does not express this arm: its close `AtFin.close`
    keeps `w`, `ld a3,24(a5)` loads through a loaded pointer (`gen_lua_at.py`
    `addr_of` stops), and `lw`/`sw` have no `Loc`/`Ent`.
  * **Open, with what each needs:**
    * callee contracts at Lua addresses: `MUL`/`MULK`/`MOD`/`MODK` are
      proved on the kit (`Kit/{Mul,Mulk,Mod,Modk}.lean`). `IDIV`/`IDIVK`
      need a `__divdi3` summary: its helper segments are generated
      (`Lua/Vm/Arms/Segs/{Hdivdi3,Humoddi3}.lean`; the sign fix-ups lie in
      `__umoddi3`'s symbol, and the unsigned case falls through into
      `__hidden___udivdi3`), the summary is open. `FORPREP` (`__udivdi3`
      whenever the step is not 1);
    * callee contracts in `luaV_execute`'s callees: `UNM` (a numeric
      string: `luaT_trybinTM` → the string library's `__unm`), `VARARGPREP`
      (`luaT_adjustvarargs`, which moves `ci->func`: `VmRel` is
      re-established with a new `func`). (`EQ`, `EQK`, `LT`, `LE` on
      strings and `LEN` are proved: `Kit.sim_EQ`, `At.sim_EQK`, `At.sim_LT`,
      `At.sim_LE`, `At.sim_LEN`; lane F1-2 put `docondjump`, observed call
      nodes and calls that store `R[A]` on the location-list route,
      `Kit/AtCond.lean`);
    * `BANDK`/`BORK`/`BXORK`: the arm reads `K[C]`'s payload without a tag
      test (`lvm.c` `op_bitwiseK`: `ivalue(KC(i))`; `lcode.c` `codebitwise`
      emits a `K` operand only for a `VKINT` constant), so their kernel is
      `bitwiseRK`, defined only for an integer `K[C]`
      (`Lua/Bytecode/Semantics.lean`; the corpus stays `Supported`). The arm
      proofs are open;
    * the shifts (`SHL`/`SHR`/`SHLI`/`SHRI`): inline, but a new kind (the
      shift-amount branches against `shiftl`); (`LOADNIL` is proved on the
      kit: `Kit.sim_LOADNIL`, its loop by `Kit.loadnil_loop`);
    * `RETURN*`: proved (`finalSim`, below);
    * `CALL` (print): callee contracts `luaD_precall` → `luaB_print` →
      `luaL_tolstring` → `lua_writestring` = `fwrite` → newlib stdout → HTIF
      (the A0.2 stdio tables at Lua addresses), `checkstackGCp` (possible
      stack reallocation at ≥ 15 locals: `VmRel` with a new `func`), the
      heap, string interning (`luaS_newlstr`) and `StdioBoot`/`MemfsBoot`
      evolving in the complement, the `trap` reload; `GETTABUP` (the
      `_ENV.print` lookup), its companion, is proved (lane F1-7:
      `At.sim_GETTABUP`; `Complement.env` must be re-established by an arm
      that changes the complement, as `exit` is).
      Lane F1-6 proved the console end (`sflush_sum` and below) and stated
      `fwrite`, `fflush`, the set-up and `lua_integer2str`
      (`Kit/CallSpec.lean`). The traced path of `print(i)` (an integer,
      `c/tests/while.lua`): `luaD_precall` → `luaB_print` → `lua_gettop`,
      `luaL_tolstring` (`luaL_callmeta` → `lua_getmetatable`, `lua_type`,
      `lua_isinteger`, `lua_tointegerx`) → `lua_pushfstring` →
      `luaO_pushvfstring` (`strchr`, `addstr2buff`/`memcpy`, `addnum2buff` →
      `snprintf` → `_svfprintf_r` with `__udivdi3`/`__umoddi3`, `__ssprint_r`
      → `__ssputs_r` → `memmove`) → `luaS_newlstr` → `internshrstr` →
      `luaC_newobj` → `luaM_malloc_` → `l_alloc` → `realloc` → `_realloc_r` →
      `_malloc_r` (and `memcpy`); `fwrite` → `_fwrite_r` (`__muldi3`, the lock
      no-ops) → `__sfvwrite_r` (`memchr`, `memmove`); `lua_settop`; the
      `"\n"` `fwrite` reaching `_fflush_r` → `__sflush_r` → `__swrite` →
      `_write_r` → `_write`; `fflush` → `__sflush_r` (empty); then
      `luaD_poscall`. The first `print` also runs `__sinit`
      (`global_stdio_init`, the Duff's-device `memset`), `__swsetup_r`,
      `__smakebuf_r` (`_fstat` → `fs_init`, `_malloc_r`/`_sbrk`, `_isatty`).
      The relation facts `SimArm .CALL` needs and `VmRel` lacks: (1) the stdio
      state in the complement (`StdioBoot ∧ MemfsBoot` before the first
      `print`, `StdoutAt m buf [] ∧ StdioUp m` after; neither is in
      `RuntimeMem`); (2) `LuaStateAt.next` (`ci->next = 0` holds only before
      the first `CALL`); (3) `DlHeap.HeapAt` with the chunks `print` allocates
      (the `stdout` buffer, the interned result strings, the `CallInfo`), and
      the intern map `w.ι` and `Complement.own` growing with them; (4) the
      `L->top`/`ci->top` words `luaD_precall`/`luaD_poscall` write (`Scratch`
      has `L->top`; the C `CallInfo` is new); (5) `Complement.exit`
      (`ExitOk`, lane F1-4) re-established over the post-print stdio state
      (`stdio_exit_handler` → `_fclose_r` → `__sflush_r`, `_close`, `_free_r`);
      Lane F1-8 put C callees on the at-lemma route (callee-context rows,
      `Kit/AtFn.lean`, `gen_lua_at.py --fn`) and proved `fflush(stdout)`
      (`FflushStdout_Statement`), `_fflush_r`, `memmove` and `memchr`; the
      `__sfvwrite_r` loop proof, the set-up, `lua_integer2str`, `luaB_print`,
      `luaD_precall`/`luaD_poscall` and the relation facts above stay open
      (`abstractions/ledger/f1-lane-8.md` lists each with its next step).
      Lanes F1-9/10 proved the loop and the set-up (`stdoutSetup_of_malloc`,
      from the named premise `MallocR_Statement`). Lane F1-11: the
      byte-total keeps give presence-level agreement of the zero fills
      (`Agree.ofTotal`, `Kit/HeapFill.lean`), so `RuntimeMem.heap` holds
      again at the fill of the memory a print leaves (`HeapAt.ofTotal`,
      `HeapAt.ofStdioKeep`; `HeapAt` reads no chunk in use, `HeapAt.congrU`),
      the fill being a complement for `Core.frame` (`bytesT1_fill`); one write
      from any phase of `stdout` (`fwrite_print`: boot, after an empty first
      write, set up) and `luaB_print` over its Lua-side callees
      (`print_sum`, `PrintLua`) are proved; open: `luaL_tolstring` per value
      class, `luaD_precall`'s C path, `luaD_poscall`, the relation facts
      (1)–(5) and the heap-room obstacle (Obligations, lane F1-11 rows). Lane F1-12:
      `luaD_precall`'s C path (`precall_reuse`, `precall_ext`), the arm on an
      invariant (`sim_CALL_of`), `LuaStateRel` (fact (2) and `L->ci`), `HeapBudget`, the
      concrete `S` (`printLua_of`), `luaL_tolstring` on nil and booleans over
      `PushLit_Statement`. Lane F1-13: facts (1), (3)–(5) as the invariant
      `Complement.call` (`CallInv`), established from the boot contract and
      re-established by `call_close`; `printCall_of : CallOpen →
      PrintCall_Statement CallInv`; open: the `CallOpen` field
      `printFlt` (lane F1-24 proved `tolFn`, `tolFn_proved`, and retired
      `printFn`; lane F1-23 proved `tolInt`, `tolInt_proved`,
      after bounding `PrintIn`'s dirty set; lane F1-15 derived `print` by
      `printRel_of`; lane F1-A0-M discharged `mallocR`, `freeR`:
      `AllocProof.{mallocR,freeR}_proved`; lane F1-17 discharged `tolStr`:
      `tolStr_proved`; lane F1-18 split `printAlloc` by value class, the
      integers per argument over `print_sum`'s budget; lane F1-19 made the
      three true as stated by moving what they need into the invariant,
      `CallInvAt.alloc`, and proved `allocOff` vacuous) and
      `HeapBudget_Statement` (Obligations, lane F1-13 rows);
    * the error paths (`StuckSim` is false; `ErrorSimRest` and `NoEscape`,
      Obligations).
  * **`FinalSim` (proved, lane F1-4, `Lua/Vm/Sim/Kit/Ret*.lean`, `Kit/Exit.lean`).**
    * The relation keeps what the return reads: `Core.saved` (`SavedAt`,
      `luaV_execute`'s saved `ra`, `s0 = L`, `s1 … s11` at `72…175(sp)`; the
      callers' values `RuntimeData.calleeSavedEntry`, pinned at the entry by
      `CStackAt.saved`/`s0` and the witnesses' `gprsCheck`); every close keeps
      it (`Core.saved_of`; `CFrame` narrowed to the locals `[sp+8, sp+72)`);
      `Complement.callers` (the caller frames' boot bytes), `Complement.callerL`
      (their copies of `L`, `RuntimeData.callerLSlots`, `RuntimeReadyAt.callerL`),
      `Complement.exit` (`ExitOk`).
    * The run, on the segment-local route (generated `SegSt` segments chained
      by `kit_run`, one declaration per phase): every branch whose polarity the
      relation does not fix is split on its guard (`kit_split`: `B = 0`, `k`,
      `L->top < ci->top`, `C`), and both polarities are run. The memory along
      the run is abstract: it agrees with the head memory off the words the
      run writes (`RAgree`, `RetDirty`; `ret_agree` dispatches each store).
      Pieces: `fclose_sum` (`luaF_close` with nothing open), `poscall_sum`
      (`luaD_poscall`, no hooks, `wanted = 0`), `ret_RETURN` (phases
      `ret_p1`–`ret_p4`), `ret_RETURN0`, `ret_RETURN1`, `ret_fresh`
      (`CIST_FRESH`, the epilogue), `ret_chain` (`ccall` →
      `luaD_rawrunprotected` → `luaD_pcall` → `lua_pcallk` → `main` →
      `_start`, the frames' words by `framesRd` off `RuntimeData.callerFrames`),
      `exit_run` (`__call_exitprocs` with `__atexit = NULL`, no stdio handler,
      `_exit`) and `exit_halt` (the `tohost` store, `stepOnce_tohost_G`).
    * Boot contract additions (checked by the witnesses): `StdioBoot.atexit`,
      `RuntimeReadyAt.callerL`, `CStackAt.s0`/`saved`.
  * **The stuck clause (lane F1-5, `Lua/StuckCases.lean`,
    `Lua/Vm/Sim/{Stuck,StuckErr}.lean`, `Lua/Vm/Sim/Kit/AtErr.lean`).**
    * `stuck_cases` enumerates the reachable stuck non-final states of a
      `Supported` program from the kernel table: the read ports are defined
      (`reach_regs`, from `Kernel.Wf`, one lemma per combinator, `opKernel_wf`),
      so the body fails, and only at a `Fault` (`body_fault`: `n%0`/`n//0`,
      `MMBIN*`'s `δ (.tm o)`, `UNM`, `BNOT`, `LEN`, `CONCAT`, the order tests,
      `FORPREP`, `FORLOOP`, `CALL`; MOVE, the loads, GETTABUP, JMP, EQ*, TEST*,
      NOT, LOADNIL, VARARGPREP never get stuck).
    * `Fault.Escape` (exact since lane float-s1: only `FORLOOP`, which no
      supported program reaches) is where Lua 5.4.7 continues instead of
      raising. `Fault.site` names the C function that raises each other fault
      (`ErrSite`; three labels fixed by lane F1-16), `site_ops` the opcodes.
    * `ErrorSim` (one `ErrorSimAt` per site) gives `StuckSimNE`, and the fold
      (`foldSim_of_arms`, now shared by `vmSim_of_arms`) gives
      `vm_refinement_ne_of_open`/`_of_rest`.
    * Error paths on the at-lemma route: `gen_lua_at.py` walks a path into an
      error exit (`ERRS`) and `at_run` stops at its entry; an error path is
      `ArmErr o Q f` by `at_err` (no kernel run: the facts are the machine's).
      The throw obligation is keyed by the exit's entry pc and message
      (`ThrowFrom f msg` over `ErrIn`, `Lua/Vm/LayoutErr.lean`); every site
      shares the tail from `luaG_errormsg` (`Kit.ErrMsgIn`,
      `Kit.throw_land`, `Kit.Unwind_Statement`, lane F1-16).
* **Exit.** `vm_refinement : vm_refinement_Statement luaLayout` has only
  standard axioms and is listed in check.sh stage 6.

## A2–A8: later fragments (Layer A)

Each fragment extends `Value`, `Step`, `Supported` and the representation,
and removes its opcodes from `ledger` (`Lua/Fragment.lean`;
`ledger_exact` keeps the ledger honest).

* **A2 (F1b): integer bitwise (done).** `BAND`/`BOR`/`BXOR`/`SHL`/`SHR`,
  the `K` forms and `SHRI`/`SHLI` are integer binary operations
  (`intArith`, with `luaV_shiftl` as `shiftl`); `BNOT` is its own rule. The
  opcodes are F1 and left the ledger (29 entries). `c/tests/f1b_bits.lua`
  passes the difftest; `f1b_bcSem` and `f1b_supported` are kernel-checked.
  Layer A's F1 arms now include these 11.
* **A3 (F2): tables.**
  * Semantics: a heap of tables in `State`, and `next` order as the binary's
    order. The array part, and the hash part in node order with
    `lsizenode`/`lastfree`/rehash (`luaH_resize`), are specified exactly,
    since F2's difftest shows `pairs` order is observable.
  * Heap: allocation through the dlmalloc proofs, GC stopped.
  * Address-revealing `tostring` (`table: 0x…`) needs an allocation model in
    the semantics or an exclusion in `Supported`. Decide at the start of A3.
* **A4 (F3): multi-frame semantics.**
  * Closures, upvalues (open/closed, `luaF_close`), Lua calls and returns,
    varargs, multret, tail calls.
  * `BcSem` becomes multi-frame over a `CallInfo` stack; `luaD_precall`
    and `luaD_poscall` are simulated.
* **A5 (F4): strings and metatables.**
  * String interning (`luaS_newlstr`, the short-string table) and
    concatenation.
  * Metatables and metamethods (`luaT_trybinTM`, `__index` chains), and
    to-be-closed variables.
* **A6 (Float): floats.** Soft-float `__adddf3` and the rest (15 routines in
  the census) and `%.14g` via `vfprintf`/`_dtoa_r`. The WHILE ELF has the
  same code; retarget it.
* **A7 (Coroutine): coroutines.** `lua_resume`/`lua_yield`, a separate
  `lua_State`, and `longjmp` across resumes.
* **OS (io/os libraries).** The shared syscall spec of ship-your-ocaml
  (`tcb/`, Lean library `TCB`): SibylFS for the file system, the CakeML
  basis FFI for console streams, `OsStep`/`next`, and the checker `allowed`.
  * **Landed.**
    * `tcb/` is ship-your-ocaml's at `f5-htif` `39e79b2` (ATTRIBUTION.md),
      including spec DEVIATION 10 (`osReaddir`). It builds, and
      `TCB.Os.allowed_sound`/`checkTrace_sound` are in check.sh stage 6.
      Its Linux trace validation reproduces here (6,398 accepted, 0
      rejected, 92 special).
    * `Lua/Os/HtifFs.lean`: `HtifFsImplements`, adapted from
      ship-your-ocaml's `OCaml/Os.lean`. `retOf` also sees the entry, and
      calls the spec leaves unconstrained are allowed.
    * **The ELF opens `io` and `os`** (steps 1-2 of the old plan).
      * `c/src/htif.c` has an in-image file system written against the
        spec: files and directories, the spec's path resolution, one
        descriptor table with `EBADF` outside it, `st_nlink` 1 for the
        console, `_stat`/`_unlink`/`rename`/`mkdir`/`rmdir`, and a clock
        frozen at 0. Its memory comes from `malloc`, so the dlmalloc
        proofs apply.
      * ship-your-ocaml adopted the same file.
      * `experiments/os/run.sh` rejects none of its traces: 5,275
        accepted, 79 special, and 1,136 that stop at `opendir`, which the
        ELF lacks; all 26 console scripts are accepted. check.sh 5b pins
        these verdicts.
      * Difftests `f7_io`/`f7_os`: 18/18 on Sail (VALIDATION.md §6).
    * `Lua/Os/Htif.lean`: the instance for the Lua ELF.
      * `HtifCallAt` decodes the twelve functions `_open`, `_close`,
        `_read`, `_write`, `_lseek`, `_fstat`, `_stat`, `_unlink`,
        `rename`, `mkdir`, `rmdir` and `_gettimeofday` (the clock) at their
        entry. Addresses and newlib's flag, errno, `struct stat` and
        `struct timeval` layout come from `Lua/Vm/Layout.lean`.
      * `HtifRetAt` reads `a0`, `errno` and the out-buffer at the return.
      * Also `LuaCallConv` and `HtifRepr`.
      * Two statements: `HtifPrint_Statement` (now including newlib's
        `_fstat` of the console) and `HtifFs_Statement` (Obligations).
    * `Lua/Os/HtifTraces.lean`: the console verdicts as kernel-checked
      facts about `next`, both the old `htif.c`'s rejected returns and the
      current one's accepted returns.
  * **`HtifFs_Statement` is now plausibly true** (every trace is accepted,
    special or unsupported), with two caveats.
    * **Resources.** Past 64 files and directories, 32 descriptors or the
      heap, `htif.c` returns `EMFILE`/`ENOSPC`, which `next` never allows.
      The proved form needs a resource bound in its scope, like `Fits`.
    * **Vacuity.** `HtifRepr` lets `R` hold at boot only, which satisfies
      the statement vacuously. The frame obligation below is what makes it
      meaningful.
  * **Next.**
    1. **`OsState` in `BcSem`.** The plan:
       * The World gets an `OsState` next to its output: the console
         stream replaces the output string (`st.streams.console`), and the
         initial world is `OsState.init`.
       * The C functions of `io`/`os` (a new `Builtin` per function) are
         specified through `OsStep`: each is a sequence of `TCB.Os.Call`s
         as newlib issues them (buffering made explicit, or an abstract
         `FILE` layer over `OsStep` for `io`), and a Lua-level result
         built from the returns. `os.time`/`os.clock` are `Call.clock`,
         `os.getenv` is `Call.getenv`, and `os.exit` is `Call.exit`.
       * `BcSem` then quantifies over the allowed returns, since `next` is
         nondeterministic. The ELF's are the frozen clock and full writes;
         `Host` records these choices, as it does for function addresses.
       * The frame obligation: every step outside `htif.c` preserves the
         representation relation `R`. This is what makes `HtifFs_Statement`
         non-vacuous.
    2. Prove `HtifPrint_Statement`, then `HtifFs_Statement` (with the
       resource bound), with the whole-function machinery (`gen_fn.py`,
       `FnSummary`).
    3. Optionally, directory streams (`opendir`/`readdir`/`closedir`,
       ship-your-ocaml's `OCAML` part of `htif.c`), so the remaining 1,136
       traces are checked too. Lua does not need them.
  * The ELF must stay free of `ecall` (check.sh stage 2).
* **A8: GC.**
  * Stop calling `lua_gc(L, LUA_GCSTOP)`.
  * Prove the semantics GC-invariant (unreachable objects unobservable);
    handle weak tables and finalizers, or exclude them from `Supported`.

## B: Layer B, source to bytecode

* **B1: translation validation (done for the corpus).** For concrete F1
  chunks and the host `luac -s`'s output, both directions of `CompileTV`.
  * Source syntax: `Lua/Ast/Syntax.lean` is the complete Lua 5.4 syntax
    (manual §9: every `stat`, `retstat`, vars, prefix expressions, method
    calls, the three `args` forms, every `exp` including functions, tables
    and all operators; numerals as integers or float bits, strings as
    bytes).
  * Parser: `scripts/gen_ast.py` parses all of Lua 5.4 following
    `llex.c`/`lparser.c`, including lparser's static errors (`goto`/label
    visibility, `<const>`/`<close>`, `...` outside a vararg function, `break`
    outside a loop, 200 locals). Not enforced: code-generation limits
    (registers, upvalues, C levels, jump length); the parser accepts a
    superset there. It never enforces F1.
    * `--roundtrip`: parse, pretty-print, re-parse to the same AST, and
      `luac -l -l` of the original and the printed text agree. check.sh
      runs it on every `.lua` file in the repo. It also passes on all 33
      files of the Lua 5.4.7 test suite (`lua-5.4.7-tests.tar.gz` from
      lua.org, not committed).
    * `--differential N`: token-level mutants are accepted exactly when
      `luac -p` accepts them (8,100 mutants of the test suite and
      `c/tests`, 0 mismatches).
  * F1 on source: `AstSupported` (`Lua/Ast/Semantics.lean`) is decidable.
    `print(…)` is a call of the free name `print`; other globals, calls,
    tables, functions, `return`, `<close>` and a `^` `luac` may
    constant-fold with the host's `pow` (`powOk`) are outside.
    `goto`/labels follow the manual's visibility rules (a visible label in
    an enclosing block, not jumping into a local's scope unless the label
    ends its block, no label visible twice).
  * `LuaSem` over the full syntax, with rules for F1: names resolve to
    locals or `_ENV.x`; the call rule evaluates the function and arguments
    and calls the builtin `print`; blocks catch `goto`s to their own labels
    (`ExecBF`, `findLabel`, `jumpEnv`); loops catch `break`; multiple
    assignment stores in `restassign`'s order.
  * `LuaSem` side: the fuel-bounded interpreter `luaRun`
    (`Lua/Ast/Exec.lean`) with `luaRun_sound` (`execSound`), by
    `decide +kernel`.
  * `BcSem` side: `bcSem_of_run`, by `decide +kernel`.
  * Determinism: `LuaSem.deterministic` (`Lua/Ast/Determinism.lean`),
    `Step.deterministic`, `Final.not_step`, `BcSem.deterministic`
    (`Lua/Bytecode/Exec.lean`); `agree_of_outputs` turns one common
    output into `∀ out, LuaSem s out ↔ BcSem p out`.
  * Per program: `ProgramTV s p` (`AstSupported s`, `Supported p`, the `↔`)
    and `CompileTV.of_programTV` (`Lua/Compile/TV.lean`).
  * Corpus (`Lua/Compile/Corpus.lean`): `while.lua` (`goto continue`),
    `f1_ops.lua`, `f1_src.lua` (`if`/`elseif`, `repeat` over body locals,
    `break` from `while`/`for`/`repeat`, shadowing, padded/extra `local`
    values), `f1b_bits.lua` (bitwise operators) and `f3_float.lua`,
    `f3_floop.lua` (float numerals, `/`, `^`, `-0.0`, NaN signs, float
    loops); expected outputs are the ELF's on the Sail model
    (`c/tests/*.expected`). `print_print.lua` passes `print` as a value,
    outside `AstSupported`; `fold/powfold.lua` (a `^` folded with glibc's
    `pow`) is the machine-checked counterexample `powFold_counterexample`.
  * Constants (`Lua/Compile/Consts.lean`): `corpus_lexOk` (the parser's
    numerals are `Lua.Num.str2number`'s) and `corpus_kAccounted` (each float
    constant of a chunk is a numeral or `constfolding` computed on
    `Lua.Num`). A B2 compiler folds on the model; its folded constants are
    `luac`'s but for `^` folded with the host's `pow`, which `AstSupported`
    excludes (probe: 291 random `+ - * / // %` folds all the model's, 20 of
    211 `^` folds not; `abstractions/ledger/b-s3.md`).
  * Exit (met): `compile_refinement_corpus :
    compile_refinement_Statement CorpusCompiles`, standard axioms only.
  * Adding a program: write `c/tests/x.lua`, commit `luac -s` output and
    the ELF's output, run `gen_ast.py`/`gen_proto.py`, add both to check.sh's
    drift lists, and add a `ProgramTV` plus a `CorpusCompiles` constructor.
* **B2: a Lean compiler.** Write `compile : Chunk → Option Proto`, a model of
  `lparser.c`/`lcode.c` on the F1 part of the full syntax (register
  allocation, jump patching including `goto`/label resolution, the
  `RK`/immediate/constant selection that `luac` does).
  * Check it against `luac` on the corpus (`compile s = luac s`).
  * Prove `CompileTV` for it.
  * Exit: `compile_refinement_Statement (fun s p => compile s = some p)`.
* **B3: the binary compiler.** `luaY_parser` and `luaK_*` in the ELF (about
  9.4k instructions, statically reachable via `load`) refine `compile` on
  source text. This needs a lexer/parser relation between text and `Chunk`.
  * Until then, the bytecode chunk is the trusted input (the program is
    `luac`'s output).

## E: composition

`endToEnd_lua_Statement luaLayout Compiles` follows from A1 and B1/B2 by
`endToEnd_of_layers`.

* **Extending to boot.** The statement can start from the ELF's `_start`
  instead of `luaV_execute`'s entry. Use A0.6's boot witness generalised
  over programs (as ship-your-interpreter's `loadedEntry_fill`): boot and
  undump reach a `VmLoaded` state for every chunk in the `.lua_chunk`
  region.
* **Exit.** The composed theorem has no hypotheses beyond `Supported` /
  `AstSupported`, and only standard axioms.

## Abstraction discovery (process; `abstractions/`)

`abstractions/gate.py` (check.sh stage 3c) fails when a proof cluster reaches
8 hand proofs without its per-case cost falling by a third. The only allowed
next task is then a round of `/abstraction-discovery`.

Round 1 (`abstractions/ROUND-1.md`) adopted two abstractions by bake-off:

- **bytecode:** per-opcode kernel terms with read/def/kill ports and a shared
  δ;
- **source:** `LuaSem` as the graph of a generic rulebook.

The round changed the plan in three ways:

- **Strings land with floats, not before them.** Lua coerces numeric strings
  in arithmetic (`"1.5"+1` gives `2.5`), so an F4 strings fragment without
  floats is not closed. Merge F4 and Float into one phase.
- **F2 constraints.**
  - `next` order and printed addresses are `Host` fields (functions of the
    history), not a nondeterministic choice.
  - Kernels keep static register ports and add adaptive heap queries for
    data-dependent table reads.
- **A1 prerequisites.** Before any A1 abstraction is built, run the recorded
  falsifiers (ROUND-1 §3 C7–C9):
  - a dependence-graph orbit canonicaliser over the ELF;
  - the exit count of the `ADD` arm (fast path plus fall-through to `MMBIN`);
  - `L->stack` logged at every dispatch head, which tests whether registers
    must be decoded relative to the stack base.
