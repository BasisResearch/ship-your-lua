-- lcode.c numberK's key for the float is 2^53 + 2, which collides with b.
-- Run: ./c/luac -l -l -p experiments/compiler/constant-cache.lua
-- Constants 0 and 2 are the same float; LOADK uses both distinct indices.
local a = 9007199254740992.0
local b = 9007199254740994
local c = 9007199254740992.0
print(a, b, c)
