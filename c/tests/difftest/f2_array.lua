-- F2: array tables, length, constructor, SETLIST
local t = {10, 20, 30, 40, 50}
print(#t, t[1], t[5], t[6])
for i = 6, 100 do t[i] = i * i end
print(#t, t[100])
local s = 0
for i = 1, #t do s = s + t[i] end
print(s)
local m = {}
for i = 1, 5 do m[i] = {} for j = 1, 5 do m[i][j] = i * j end end
print(m[3][4], m[5][5], #m, #m[2])
