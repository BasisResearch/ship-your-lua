-- IDIV by zero: luaG_runerror -> luaD_throw -> longjmp -> exit(1)
local a = 0
print(7 // 3)
print(7 // a)
