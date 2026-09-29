| # | opcode | F1 | target | reach | excl | linear | br | tgt-hits while | tgt-hits union | callees (jal; xN = N sites) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | MOVE | F1 | 8001be84 | 15 | 5 | 5 | 0 | 3 | 145 |  |
| 1 | LOADI | F1 | 8001be54 | 12 | 12 | 12 | 0 | 9 | 411 |  |
| 2 | LOADF | F1 | 8001be98 | 14 | 14 | 14 | 0 | 0 | 10 | __floatsidf |
| 3 | LOADK | F1 | 8001ba94 | 14 | 4 | 14 | 0 | 0 | 111 |  |
| 4 | LOADKX |  | 8001bef0 | 15 | 15 | 15 | 0 | 0 | 0 |  |
| 5 | LOADFALSE |  | 8001bd54 | 8 | 8 | 8 | 0 | 0 | 155 |  |
| 6 | LFALSESKIP |  | 8001bed0 | 8 | 8 | 8 | 0 | 0 | 14 |  |
| 7 | LOADTRUE |  | 8001b5d0 | 8 | 8 | 8 | 0 | 0 | 222 |  |
| 8 | LOADNIL |  | 8001bd1c | 14 | 14 | 14 | 1 | 0 | 7 |  |
| 9 | GETUPVAL |  | 8001bb40 | 17 | 17 | 17 | 0 | 0 | 13493 |  |
| 10 | SETUPVAL |  | 8001bca8 | 33 | 29 | 29 | 3 | 0 | 503 | luaC_barrier_ |
| 11 | GETTABUP | F1 | 8001ba1c | 48 | 43 | 20 | 2 | 3 | 240 | luaH_getshortstr, luaV_finishget |
| 12 | GETTABLE |  | 8001bacc | 71 | 71 | 16 | 5 | 0 | 145 | luaH_get, luaH_getint, luaV_finishget |
| 13 | GETI |  | 8001b6e8 | 50 | 45 | 13 | 3 | 0 | 15 | luaH_getint, luaV_finishget |
| 14 | GETFIELD |  | 8001b67c | 45 | 40 | 17 | 2 | 0 | 70 | luaH_getshortstr, luaV_finishget |
| 15 | SETTABUP |  | 8001b5f0 | 68 | 48 | 25 | 6 | 0 | 18 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 16 | SETTABLE |  | 8001b994 | 93 | 73 | 21 | 10 | 0 | 179 | luaC_barrierback_, luaH_get, luaH_getint, luaV_finishset |
| 17 | SETI |  | 8001b8cc | 74 | 54 | 18 | 7 | 0 | 3 | luaC_barrierback_, luaH_getint, luaV_finishset |
| 18 | SETFIELD |  | 8001b84c | 65 | 45 | 22 | 6 | 0 | 32 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 19 | NEWTABLE |  | 8001b7a0 | 48 | 48 | 33 | 4 | 0 | 36 | luaC_step, luaH_new, luaH_resize |
| 20 | SELF |  | 8001b540 | 52 | 52 | 26 | 3 | 0 | 11 | luaH_getstr, luaV_finishget |
| 21 | ADDI | F1 | 8001b4dc | 33 | 31 | 13 | 2 | 123 | 13318 | __adddf3, __floatsidf |
| 22 | ADDK | F1 | 8001b46c | 55 | 51 | 15 | 6 | 0 | 10 | __adddf3, __floatdidf x2 |
| 23 | SUBK | F1 | 8001b41c | 55 | 51 | 15 | 6 | 0 | 0 | __floatdidf x2, __subdf3 |
| 24 | MULK | F1 | 8001c5d4 | 54 | 50 | 17 | 6 | 0 | 16 | __floatdidf x2, __muldf3, __muldi3 |
| 25 | MODK | F1 | 8001c568 | 98 | 88 | 27 | 14 | 100 | 201 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 26 | POWK |  | 8001c29c | 61 | 57 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 27 | DIVK |  | 8001c270 | 48 | 46 | 9 | 5 | 0 | 5 | __divdf3, __floatdidf x2 |
| 28 | IDIVK | F1 | 8001c200 | 80 | 72 | 24 | 9 | 0 | 4 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 29 | BANDK |  | 8001c1a8 | 54 | 52 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 30 | BORK |  | 8001c150 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 31 | BXORK |  | 8001c0f8 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 32 | SHRI |  | 8001c824 | 63 | 63 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 33 | SHLI |  | 8001c7c8 | 62 | 60 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 34 | ADD | F1 | 8001c460 | 52 | 50 | 16 | 6 | 69 | 11354 | __adddf3, __floatdidf x2 |
| 35 | SUB | F1 | 8001c3fc | 53 | 49 | 16 | 6 | 0 | 1 | __floatdidf x2, __subdf3 |
| 36 | MUL | F1 | 8001c760 | 53 | 49 | 16 | 6 | 9 | 921 | __floatdidf x2, __muldf3, __muldi3 |
| 37 | MOD | F1 | 8001c6f0 | 99 | 89 | 19 | 14 | 0 | 629 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 38 | POW |  | 8001bf88 | 57 | 55 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 39 | DIV |  | 8001bf2c | 49 | 45 | 8 | 5 | 0 | 0 | __divdf3, __floatdidf x2 |
| 40 | IDIV | F1 | 8001c944 | 79 | 69 | 19 | 9 | 0 | 1 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 41 | BAND |  | 8001c8e4 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 42 | BOR |  | 8001c508 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 43 | BXOR |  | 8001c4a8 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 44 | SHL |  | 8001c088 | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 45 | SHR |  | 8001c014 | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 46 | MMBIN |  | 8001c888 | 23 | 23 | 23 | 0 | 0 | 2 | luaT_trybinTM |
| 47 | MMBINI |  | 8001bfb4 | 24 | 24 | 24 | 0 | 0 | 1 | luaT_trybiniTM |
| 48 | MMBINK |  | 8001c394 | 26 | 26 | 26 | 0 | 0 | 0 | luaT_trybinassocTM |
| 49 | UNM |  | 8001c33c | 39 | 37 | 11 | 2 | 0 | 4 | luaT_trybinTM |
| 50 | BNOT |  | 8001c9b0 | 54 | 54 | 11 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor, luaT_trybinTM |
| 51 | NOT |  | 8001c2fc | 20 | 20 | 16 | 2 | 0 | 0 |  |
| 52 | LEN |  | 8001c6ac | 17 | 17 | 17 | 0 | 0 | 47 | luaV_objlen |
| 53 | CONCAT |  | 8001c640 | 27 | 27 | 21 | 2 | 0 | 12 | luaC_step, luaV_concat.part.0 |
| 54 | CLOSE |  | 8001c9f4 | 15 | 15 | 15 | 0 | 0 | 12 | luaF_close |
| 55 | TBC |  | 8001b3f0 | 11 | 11 | 11 | 0 | 0 | 0 | luaF_newtbcupval |
| 56 | JMP | F1 | 8001b17c | 9 | 9 | 9 | 0 | 122 | 872 |  |
| 57 | EQ | F1 | 8001b128 | 31 | 31 | 19 | 1 | 0 | 5 | luaV_equalobj |
| 58 | LT | F1 | 8001b32c | 160 | 160 | 11 | 16 | 0 | 17 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 59 | LE | F1 | 8001b0a4 | 166 | 166 | 11 | 16 | 0 | 676 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 60 | EQK | F1 | 8001b2e8 | 27 | 27 | 15 | 1 | 0 | 502 | luaV_equalobj |
| 61 | EQI | F1 | 8001b288 | 41 | 41 | 10 | 4 | 100 | 10835 | __eqdf2, __floatsidf |
| 62 | LTI | F1 | 8001af04 | 53 | 53 | 10 | 4 | 11 | 2000 | __floatsidf, __ledf2, luaT_callorderiTM |
| 63 | LEI | F1 | 8001aea4 | 51 | 51 | 10 | 3 | 16 | 33 | __floatsidf, __ledf2, luaT_callorderiTM |
| 64 | GTI | F1 | 8001b044 | 53 | 53 | 10 | 4 | 101 | 203 | __floatsidf, __gedf2, luaT_callorderiTM |
| 65 | GEI | F1 | 8001afe0 | 52 | 52 | 10 | 3 | 0 | 10 | __floatsidf, __gedf2, luaT_callorderiTM |
| 66 | TEST | F1 | 8001b3b0 | 26 | 26 | 14 | 2 | 0 | 211 |  |
| 67 | TESTSET |  | 8001af64 | 33 | 33 | 14 | 2 | 0 | 0 |  |
| 68 | CALL | F1 | 8001b234 | 42 | 23 | 17 | 3 | 3 | 2738 | luaD_precall, luaG_tracecall |
| 69 | TAILCALL |  | 8001b1a0 | 100 | 48 | 13 | 8 | 0 | 10008 | luaD_poscall, luaD_pretailcall, luaF_closeupval, luaG_tracecall |
| 70 | RETURN | F1 | 8001adf8 | 87 | 47 | 31 | 7 | 1 | 27 | luaD_poscall, luaF_close, luaG_tracecall |
| 71 | RETURN0 | F1 | 8001ad54 | 72 | 38 | 3 | 6 | 0 | 2 | luaD_poscall, luaG_tracecall |
| 72 | RETURN1 | F1 | 8001ace4 | 84 | 50 | 3 | 6 | 0 | 2013 | luaD_poscall, luaG_tracecall |
| 73 | FORLOOP | F1 | 8001ac84 | 55 | 55 | 7 | 4 | 0 | 577 | __adddf3, __gedf2 x2, __ledf2 |
| 74 | FORPREP | F1 | 8001ab90 | 205 | 203 | 11 | 25 | 0 | 21 | __eqdf2, __gedf2 x5, __hidden___udivdi3 x2, __ledf2, luaG_forerror x3, luaG_runerror, luaV_tointeger x2, luaV_tonumber_ x4 |
| 75 | TFORPREP |  | 8001aaa4 | 71 | 15 | 34 | 4 | 0 | 9 | luaD_call, luaF_newtbcupval, luaG_traceexec, memcpy |
| 76 | TFORCALL |  | 8001aae0 | 56 | 0 | 19 | 4 | 0 | 95 | luaD_call, luaG_traceexec, memcpy |
| 77 | TFORLOOP |  | 8001ab88 | 34 | 2 | 2 | 3 | 0 | 0 | luaG_traceexec |
| 78 | SETLIST |  | 8001bd74 | 75 | 75 | 32 | 8 | 0 | 8 | luaC_barrierback_, luaH_realasize, luaH_resizearray |
| 79 | CLOSURE |  | 8001bbc4 | 79 | 77 | 34 | 7 | 0 | 43 | luaC_barrier_, luaC_step, luaF_findupval, luaF_newLclosure |
| 80 | VARARG |  | 8001bb84 | 16 | 16 | 16 | 0 | 0 | 6 | luaT_getvarargs |
| 81 | VARARGPREP |  | 8001b760 | 22 | 22 | 12 | 1 | 1 | 21 | luaD_hookcall, luaT_adjustvarargs |
| 82 | EXTRAARG |  | 8001ac7c | 2 | 0 | 2 | 0 | 0 | 2 |  |
