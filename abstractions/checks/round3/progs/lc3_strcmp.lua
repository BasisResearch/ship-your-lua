-- EQ/EQK/LT/LE on strings (luaV_equalobj, l_strcmp)
local a, b = "apple", "banana"
local c = "apple"
print(a == b, a == c, a == "apple", a ~= "pear")
print(a < b, b < a, a <= c, b <= a, "" < a, a < "applf")
