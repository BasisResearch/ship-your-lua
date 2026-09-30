| # | opcode | F1 | target | reach | excl | linear | br | tgt-hits while | tgt-hits union | callees (jal; xN = N sites) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | MOVE | F1 | 8001d3ec | 15 | 5 | 5 | 0 | 3 | 202 |  |
| 1 | LOADI | F1 | 8001d3bc | 12 | 12 | 12 | 0 | 9 | 429 |  |
| 2 | LOADF | F1 | 8001d400 | 14 | 14 | 14 | 0 | 0 | 10 | __floatsidf |
| 3 | LOADK | F1 | 8001cffc | 14 | 4 | 14 | 0 | 0 | 205 |  |
| 4 | LOADKX |  | 8001d458 | 15 | 15 | 15 | 0 | 0 | 0 |  |
| 5 | LOADFALSE |  | 8001d2bc | 8 | 8 | 8 | 0 | 0 | 155 |  |
| 6 | LFALSESKIP |  | 8001d438 | 8 | 8 | 8 | 0 | 0 | 14 |  |
| 7 | LOADTRUE |  | 8001cb38 | 8 | 8 | 8 | 0 | 0 | 224 |  |
| 8 | LOADNIL |  | 8001d284 | 14 | 14 | 14 | 1 | 0 | 7 |  |
| 9 | GETUPVAL |  | 8001d0a8 | 17 | 17 | 17 | 0 | 0 | 13493 |  |
| 10 | SETUPVAL |  | 8001d210 | 33 | 29 | 29 | 3 | 0 | 503 | luaC_barrier_ |
| 11 | GETTABUP | F1 | 8001cf84 | 48 | 43 | 20 | 2 | 3 | 381 | luaH_getshortstr, luaV_finishget |
| 12 | GETTABLE |  | 8001d034 | 71 | 71 | 16 | 5 | 0 | 145 | luaH_get, luaH_getint, luaV_finishget |
| 13 | GETI |  | 8001cc50 | 50 | 45 | 13 | 3 | 0 | 15 | luaH_getint, luaV_finishget |
| 14 | GETFIELD |  | 8001cbe4 | 45 | 40 | 17 | 2 | 0 | 150 | luaH_getshortstr, luaV_finishget |
| 15 | SETTABUP |  | 8001cb58 | 68 | 48 | 25 | 6 | 0 | 18 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 16 | SETTABLE |  | 8001cefc | 93 | 73 | 21 | 10 | 0 | 179 | luaC_barrierback_, luaH_get, luaH_getint, luaV_finishset |
| 17 | SETI |  | 8001ce34 | 74 | 54 | 18 | 7 | 0 | 3 | luaC_barrierback_, luaH_getint, luaV_finishset |
| 18 | SETFIELD |  | 8001cdb4 | 65 | 45 | 22 | 6 | 0 | 42 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 19 | NEWTABLE |  | 8001cd08 | 48 | 48 | 33 | 4 | 0 | 39 | luaC_step, luaH_new, luaH_resize |
| 20 | SELF |  | 8001caa8 | 52 | 52 | 26 | 3 | 0 | 63 | luaH_getstr, luaV_finishget |
| 21 | ADDI | F1 | 8001ca44 | 33 | 31 | 13 | 2 | 123 | 13322 | __adddf3, __floatsidf |
| 22 | ADDK | F1 | 8001c9d4 | 55 | 51 | 15 | 6 | 0 | 10 | __adddf3, __floatdidf x2 |
| 23 | SUBK | F1 | 8001c984 | 55 | 51 | 15 | 6 | 0 | 0 | __floatdidf x2, __subdf3 |
| 24 | MULK | F1 | 8001db3c | 54 | 50 | 17 | 6 | 0 | 16 | __floatdidf x2, __muldf3, __muldi3 |
| 25 | MODK | F1 | 8001dad0 | 98 | 88 | 27 | 14 | 100 | 201 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 26 | POWK |  | 8001d804 | 61 | 57 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 27 | DIVK |  | 8001d7d8 | 48 | 46 | 9 | 5 | 0 | 5 | __divdf3, __floatdidf x2 |
| 28 | IDIVK | F1 | 8001d768 | 80 | 72 | 24 | 9 | 0 | 4 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 29 | BANDK |  | 8001d710 | 54 | 52 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 30 | BORK |  | 8001d6b8 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 31 | BXORK |  | 8001d660 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 32 | SHRI |  | 8001dd8c | 63 | 63 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 33 | SHLI |  | 8001dd30 | 62 | 60 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 34 | ADD | F1 | 8001d9c8 | 52 | 50 | 16 | 6 | 69 | 11354 | __adddf3, __floatdidf x2 |
| 35 | SUB | F1 | 8001d964 | 53 | 49 | 16 | 6 | 0 | 1 | __floatdidf x2, __subdf3 |
| 36 | MUL | F1 | 8001dcc8 | 53 | 49 | 16 | 6 | 9 | 921 | __floatdidf x2, __muldf3, __muldi3 |
| 37 | MOD | F1 | 8001dc58 | 99 | 89 | 19 | 14 | 0 | 629 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 38 | POW |  | 8001d4f0 | 57 | 55 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 39 | DIV |  | 8001d494 | 49 | 45 | 8 | 5 | 0 | 0 | __divdf3, __floatdidf x2 |
| 40 | IDIV | F1 | 8001deac | 79 | 69 | 19 | 9 | 0 | 1 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 41 | BAND |  | 8001de4c | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 42 | BOR |  | 8001da70 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 43 | BXOR |  | 8001da10 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 44 | SHL |  | 8001d5f0 | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 45 | SHR |  | 8001d57c | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 46 | MMBIN |  | 8001ddf0 | 23 | 23 | 23 | 0 | 0 | 2 | luaT_trybinTM |
| 47 | MMBINI |  | 8001d51c | 24 | 24 | 24 | 0 | 0 | 1 | luaT_trybiniTM |
| 48 | MMBINK |  | 8001d8fc | 26 | 26 | 26 | 0 | 0 | 0 | luaT_trybinassocTM |
| 49 | UNM |  | 8001d8a4 | 39 | 37 | 11 | 2 | 0 | 4 | luaT_trybinTM |
| 50 | BNOT |  | 8001df18 | 54 | 54 | 11 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor, luaT_trybinTM |
| 51 | NOT |  | 8001d864 | 20 | 20 | 16 | 2 | 0 | 0 |  |
| 52 | LEN |  | 8001dc14 | 17 | 17 | 17 | 0 | 0 | 47 | luaV_objlen |
| 53 | CONCAT |  | 8001dba8 | 27 | 27 | 21 | 2 | 0 | 12 | luaC_step, luaV_concat.part.0 |
| 54 | CLOSE |  | 8001df5c | 15 | 15 | 15 | 0 | 0 | 15 | luaF_close |
| 55 | TBC |  | 8001c958 | 11 | 11 | 11 | 0 | 0 | 0 | luaF_newtbcupval |
| 56 | JMP | F1 | 8001c6e4 | 9 | 9 | 9 | 0 | 122 | 872 |  |
| 57 | EQ | F1 | 8001c690 | 31 | 31 | 19 | 1 | 0 | 6 | luaV_equalobj |
| 58 | LT | F1 | 8001c894 | 160 | 160 | 11 | 16 | 0 | 17 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 59 | LE | F1 | 8001c60c | 166 | 166 | 11 | 16 | 0 | 676 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 60 | EQK | F1 | 8001c850 | 27 | 27 | 15 | 1 | 0 | 503 | luaV_equalobj |
| 61 | EQI | F1 | 8001c7f0 | 41 | 41 | 10 | 4 | 100 | 10835 | __eqdf2, __floatsidf |
| 62 | LTI | F1 | 8001c46c | 53 | 53 | 10 | 4 | 11 | 2000 | __floatsidf, __ledf2, luaT_callorderiTM |
| 63 | LEI | F1 | 8001c40c | 51 | 51 | 10 | 3 | 16 | 33 | __floatsidf, __ledf2, luaT_callorderiTM |
| 64 | GTI | F1 | 8001c5ac | 53 | 53 | 10 | 4 | 101 | 203 | __floatsidf, __gedf2, luaT_callorderiTM |
| 65 | GEI | F1 | 8001c548 | 52 | 52 | 10 | 3 | 0 | 10 | __floatsidf, __gedf2, luaT_callorderiTM |
| 66 | TEST | F1 | 8001c918 | 26 | 26 | 14 | 2 | 0 | 211 |  |
| 67 | TESTSET |  | 8001c4cc | 33 | 33 | 14 | 2 | 0 | 0 |  |
| 68 | CALL | F1 | 8001c79c | 42 | 23 | 17 | 3 | 3 | 2924 | luaD_precall, luaG_tracecall |
| 69 | TAILCALL |  | 8001c708 | 100 | 48 | 13 | 8 | 0 | 10008 | luaD_poscall, luaD_pretailcall, luaF_closeupval, luaG_tracecall |
| 70 | RETURN | F1 | 8001c360 | 87 | 47 | 31 | 7 | 1 | 28 | luaD_poscall, luaF_close, luaG_tracecall |
| 71 | RETURN0 | F1 | 8001c2bc | 72 | 38 | 3 | 6 | 0 | 2 | luaD_poscall, luaG_tracecall |
| 72 | RETURN1 | F1 | 8001c24c | 84 | 50 | 3 | 6 | 0 | 2013 | luaD_poscall, luaG_tracecall |
| 73 | FORLOOP | F1 | 8001c1ec | 55 | 55 | 7 | 4 | 0 | 577 | __adddf3, __gedf2 x2, __ledf2 |
| 74 | FORPREP | F1 | 8001c0f8 | 205 | 203 | 11 | 25 | 0 | 21 | __eqdf2, __gedf2 x5, __hidden___udivdi3 x2, __ledf2, luaG_forerror x3, luaG_runerror, luaV_tointeger x2, luaV_tonumber_ x4 |
| 75 | TFORPREP |  | 8001c00c | 71 | 15 | 34 | 4 | 0 | 12 | luaD_call, luaF_newtbcupval, luaG_traceexec, memcpy |
| 76 | TFORCALL |  | 8001c048 | 56 | 0 | 19 | 4 | 0 | 110 | luaD_call, luaG_traceexec, memcpy |
| 77 | TFORLOOP |  | 8001c0f0 | 34 | 2 | 2 | 3 | 0 | 0 | luaG_traceexec |
| 78 | SETLIST |  | 8001d2dc | 75 | 75 | 32 | 8 | 0 | 8 | luaC_barrierback_, luaH_realasize, luaH_resizearray |
| 79 | CLOSURE |  | 8001d12c | 79 | 77 | 34 | 7 | 0 | 43 | luaC_barrier_, luaC_step, luaF_findupval, luaF_newLclosure |
| 80 | VARARG |  | 8001d0ec | 16 | 16 | 16 | 0 | 0 | 6 | luaT_getvarargs |
| 81 | VARARGPREP |  | 8001ccc8 | 22 | 22 | 12 | 1 | 1 | 23 | luaD_hookcall, luaT_adjustvarargs |
| 82 | EXTRAARG |  | 8001c1e4 | 2 | 0 | 2 | 0 | 0 | 2 |  |
